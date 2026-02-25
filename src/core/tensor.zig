const std = @import("std");
const mem = std.mem;
const math = std.math;
const Allocator = mem.Allocator;
const types = @import("types.zig");
const Error = types.Error;
const Fixed32_32 = types.Fixed32_32;
const memory = @import("memory.zig");

const Shape = struct {
    dims: []usize,
    strides: []usize,

    pub fn init(allocator: Allocator, shape: []const usize) !Shape {
        const n = shape.len;
        if (n == 0) return Error.InvalidShape;
        const dims = try allocator.alloc(usize, n);
        errdefer allocator.free(dims);
        const strides = try allocator.alloc(usize, n);
        errdefer allocator.free(strides);
        @memcpy(dims, shape);
        strides[n - 1] = 1;
        var i: usize = n - 1;
        while (i > 0) : (i -= 1) {
            const r = @mulWithOverflow(strides[i], dims[i]);
            if (r[1] != 0) return Error.Overflow;
            strides[i - 1] = r[0];
        }
        return .{ .dims = dims, .strides = strides };
    }

    pub fn deinit(self: *Shape, allocator: Allocator) void {
        allocator.free(self.dims);
        allocator.free(self.strides);
    }

    pub fn copy(self: *const Shape, allocator: Allocator) !Shape {
        return .{ .dims = try allocator.dupe(usize, self.dims), .strides = try allocator.dupe(usize, self.strides) };
    }

    pub fn totalSize(self: *const Shape) Error!usize {
        if (self.dims.len == 0) return 1;
        var total: usize = 1;
        for (self.dims) |d| {
            const r = @mulWithOverflow(total, d);
            if (r[1] != 0) return Error.Overflow;
            total = r[0];
        }
        return total;
    }

    pub fn equals(self: *const Shape, other: *const Shape) bool {
        return mem.eql(usize, self.dims, other.dims) and mem.eql(usize, self.strides, other.strides);
    }

    pub fn broadcastCompatible(self: *const Shape, target: *const Shape) bool {
        if (target.dims.len < self.dims.len) return false;
        const offset = target.dims.len - self.dims.len;
        var i: usize = 0;
        while (i < self.dims.len) : (i += 1) {
            const self_dim = self.dims[i];
            const target_dim = target.dims[offset + i];
            if (self_dim != target_dim and self_dim != 1) {
                return false;
            }
        }
        return true;
    }

    pub fn isContiguous(self: *const Shape) bool {
        if (self.dims.len == 0) return true;
        var expected: usize = 1;
        var i: usize = self.dims.len;
        while (i > 0) : (i -= 1) {
            const idx = i - 1;
            if (self.strides[idx] != expected) return false;
            expected *= self.dims[idx];
        }
        return true;
    }
};

pub const Tensor = struct {
    data: []f32,
    base_data: []f32,
    shape: Shape,
    allocator: Allocator,
    refcount: *usize,
    cow: *bool,
    mutex: *std.Thread.Mutex,

    pub fn init(allocator: Allocator, shape: []const usize) !Tensor {
        if (shape.len == 0) return Error.InvalidShape;
        var total_size: usize = 1;
        for (shape) |dim| {
            if (dim == 0) return Error.InvalidShape;
            const r = @mulWithOverflow(total_size, dim);
            if (r[1] != 0) return Error.Overflow;
            total_size = r[0];
        }
        const data = try allocator.alloc(f32, total_size);
        errdefer allocator.free(data);
        @memset(data, 0);
        const sh = try Shape.init(allocator, shape);
        errdefer sh.deinit(allocator);
        const refcount = try allocator.create(usize);
        errdefer allocator.destroy(refcount);
        refcount.* = 1;
        const cow = try allocator.create(bool);
        errdefer allocator.destroy(cow);
        cow.* = false;
        const mutex = try allocator.create(std.Thread.Mutex);
        mutex.* = .{};
        return .{ .data = data, .base_data = data, .shape = sh, .allocator = allocator, .refcount = refcount, .cow = cow, .mutex = mutex };
    }

    pub fn initWithArena(arena: *memory.ArenaAllocator, shape: []const usize) !Tensor {
        return init(arena.allocator(), shape);
    }

    pub fn initWithPool(pool: *memory.PoolAllocator, shape: []const usize) !Tensor {
        return init(pool.allocator(), shape);
    }

    pub fn initWithSlab(slab: *memory.SlabAllocator, shape: []const usize) !Tensor {
        return init(slab.allocator(), shape);
    }

    pub fn initWithBuddy(buddy: *memory.BuddyAllocator, shape: []const usize) !Tensor {
        return init(buddy.allocator(), shape);
    }

    pub fn retain(self: *Tensor) void {
        _ = @atomicRmw(usize, self.refcount, .Add, 1, .AcqRel);
    }

    pub fn release(self: *Tensor) void {
        const prev = @atomicRmw(usize, self.refcount, .Sub, 1, .AcqRel);
        if (prev == 1) {
            self.deallocate();
        }
    }

    fn deallocate(self: *Tensor) void {
        self.allocator.free(self.base_data);
        self.shape.deinit(self.allocator);
        self.allocator.destroy(self.refcount);
        self.allocator.destroy(self.cow);
        self.allocator.destroy(self.mutex);
    }

    pub fn deinit(self: *Tensor) void {
        const prev = @atomicRmw(usize, self.refcount, .Sub, 1, .AcqRel);
        if (prev == 1) {
            self.deallocate();
        } else {
            self.shape.deinit(self.allocator);
        }
    }

    pub fn copy(self: *const Tensor, allocator: Allocator) !Tensor {
        const new_t = try init(allocator, self.shape.dims);
        var indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            new_t.data[flat] = try self.get(indices);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        return new_t;
    }

    fn ensureWritable(self: *Tensor) !void {
        self.mutex.lock();
        if (!self.cow.*) {
            self.mutex.unlock();
            return;
        }
        const total = try self.shape.totalSize();
        const new_data = try self.allocator.alloc(f32, total);
        errdefer self.allocator.free(new_data);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            new_data[flat] = self.data[try self.computeIndex(indices)];
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        const new_refcount = try self.allocator.create(usize);
        errdefer self.allocator.destroy(new_refcount);
        new_refcount.* = 1;
        const new_cow = try self.allocator.create(bool);
        errdefer self.allocator.destroy(new_cow);
        new_cow.* = false;
        const new_mutex = try self.allocator.create(std.Thread.Mutex);
        new_mutex.* = .{};
        const old_refcount = @atomicRmw(usize, self.refcount, .Sub, 1, .AcqRel);
        const was_last = (old_refcount == 1);
        const old_base_data = self.base_data;
        const old_refcount_ptr = self.refcount;
        const old_cow_ptr = self.cow;
        const old_mutex_ptr = self.mutex;
        self.data = new_data;
        self.base_data = new_data;
        self.refcount = new_refcount;
        self.cow = new_cow;
        self.mutex = new_mutex;
        old_mutex_ptr.unlock();
        if (was_last) {
            self.allocator.free(old_base_data);
            self.allocator.destroy(old_refcount_ptr);
            self.allocator.destroy(old_cow_ptr);
            self.allocator.destroy(old_mutex_ptr);
        }
    }

    fn markShared(self: *Tensor) void {
        self.mutex.lock();
        defer self.mutex.unlock();
        self.cow.* = true;
    }

    pub fn newView(self: *Tensor, shape: Shape) !Tensor {
        const shape_size = try shape.totalSize();
        const self_size = try self.shape.totalSize();
        if (shape_size != self_size) return Error.InvalidShape;
        self.retain();
        self.markShared();
        return .{ .data = self.data, .base_data = self.base_data, .shape = shape, .allocator = self.allocator, .refcount = self.refcount, .cow = self.cow, .mutex = self.mutex };
    }

    pub fn reshape(self: *Tensor, new_shape: []const usize) !void {
        if (new_shape.len == 0) return Error.InvalidShape;
        if (!self.shape.isContiguous()) return Error.InvalidShape;
        var total: usize = 1;
        for (new_shape) |dim| {
            const r = @mulWithOverflow(total, dim);
            if (r[1] != 0) return Error.Overflow;
            total = r[0];
        }
        const self_size = try self.shape.totalSize();
        if (total != self_size) return Error.InvalidShape;
        const new_sh = try Shape.init(self.allocator, new_shape);
        self.shape.deinit(self.allocator);
        self.shape = new_sh;
    }

    pub fn view(self: *Tensor, new_shape: []const usize) !Tensor {
        if (new_shape.len == 0) return Error.InvalidShape;
        var total: usize = 1;
        for (new_shape) |dim| {
            const r = @mulWithOverflow(total, dim);
            if (r[1] != 0) return Error.Overflow;
            total = r[0];
        }
        const self_size = try self.shape.totalSize();
        if (total != self_size) return Error.InvalidShape;
        const new_sh = try Shape.init(self.allocator, new_shape);
        self.retain();
        self.markShared();
        return .{ .data = self.data, .base_data = self.base_data, .shape = new_sh, .allocator = self.allocator, .refcount = self.refcount, .cow = self.cow, .mutex = self.mutex };
    }

    pub fn slice(self: *Tensor, starts: []const usize, ends: []const usize) !Tensor {
        if (starts.len != self.shape.dims.len or ends.len != self.shape.dims.len) return Error.InvalidAxis;
        var new_dims = try self.allocator.alloc(usize, self.shape.dims.len);
        errdefer self.allocator.free(new_dims);
        var new_strides = try self.allocator.alloc(usize, self.shape.strides.len);
        errdefer self.allocator.free(new_strides);
        var offset: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (starts[i] >= ends[i] or ends[i] > self.shape.dims[i]) return Error.OutOfBounds;
            new_dims[i] = ends[i] - starts[i];
            new_strides[i] = self.shape.strides[i];
            offset += starts[i] * self.shape.strides[i];
        }
        const new_sh = Shape{ .dims = new_dims, .strides = new_strides };
        const new_data = self.data[offset..];
        self.retain();
        self.markShared();
        return .{ .data = new_data, .base_data = self.base_data, .shape = new_sh, .allocator = self.allocator, .refcount = self.refcount, .cow = self.cow, .mutex = self.mutex };
    }

    pub fn transpose(self: *Tensor, axes: []const usize) !Tensor {
        if (axes.len != self.shape.dims.len) return Error.InvalidAxis;
        var new_dims = try self.allocator.alloc(usize, self.shape.dims.len);
        errdefer self.allocator.free(new_dims);
        var new_strides = try self.allocator.alloc(usize, self.shape.dims.len);
        errdefer self.allocator.free(new_strides);
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (axes[i] >= self.shape.dims.len) return Error.InvalidAxis;
            new_dims[i] = self.shape.dims[axes[i]];
            new_strides[i] = self.shape.strides[axes[i]];
        }
        const new_sh = Shape{ .dims = new_dims, .strides = new_strides };
        self.retain();
        self.markShared();
        return .{ .data = self.data, .base_data = self.base_data, .shape = new_sh, .allocator = self.allocator, .refcount = self.refcount, .cow = self.cow, .mutex = self.mutex };
    }

    fn computeIndex(self: *const Tensor, indices: []const usize) !usize {
        if (indices.len != self.shape.dims.len) return Error.InvalidAxis;
        var idx: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (indices[i] >= self.shape.dims[i]) return Error.OutOfBounds;
            idx += indices[i] * self.shape.strides[i];
        }
        return idx;
    }

    pub fn get(self: *const Tensor, indices: []const usize) !f32 {
        const idx = try computeIndex(self, indices);
        return self.data[idx];
    }

    pub fn set(self: *Tensor, indices: []const usize, value: f32) !void {
        try ensureWritable(self);
        const idx = try computeIndex(self, indices);
        self.data[idx] = value;
    }

    pub fn fill(self: *Tensor, value: f32) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            self.data[try self.computeIndex(indices)] = value;
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn add(self: *Tensor, other: *const Tensor) !void {
        if (!self.shape.equals(&other.shape)) return Error.ShapeMismatch;
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx1 = try self.computeIndex(indices);
            const idx2 = try other.computeIndex(indices);
            self.data[idx1] += other.data[idx2];
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn sub(self: *Tensor, other: *const Tensor) !void {
        if (!self.shape.equals(&other.shape)) return Error.ShapeMismatch;
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx1 = try self.computeIndex(indices);
            const idx2 = try other.computeIndex(indices);
            self.data[idx1] -= other.data[idx2];
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn mul(self: *Tensor, other: *const Tensor) !void {
        if (!self.shape.equals(&other.shape)) return Error.ShapeMismatch;
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx1 = try self.computeIndex(indices);
            const idx2 = try other.computeIndex(indices);
            self.data[idx1] *= other.data[idx2];
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn div(self: *Tensor, other: *const Tensor) !void {
        if (!self.shape.equals(&other.shape)) return Error.ShapeMismatch;
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx1 = try self.computeIndex(indices);
            const idx2 = try other.computeIndex(indices);
            if (other.data[idx2] == 0.0) return Error.DivideByZero;
            self.data[idx1] /= other.data[idx2];
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn addScalar(self: *Tensor, scalar: f32) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            self.data[try self.computeIndex(indices)] += scalar;
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn subScalar(self: *Tensor, scalar: f32) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            self.data[try self.computeIndex(indices)] -= scalar;
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn mulScalar(self: *Tensor, scalar: f32) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            self.data[try self.computeIndex(indices)] *= scalar;
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn divScalar(self: *Tensor, scalar: f32) !void {
        if (scalar == 0.0) return Error.DivideByZero;
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            self.data[try self.computeIndex(indices)] /= scalar;
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn exp(self: *Tensor) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            self.data[idx] = @exp(self.data[idx]);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn log(self: *Tensor) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            if (self.data[idx] <= 0.0) {
                self.data[idx] = -math.inf(f32);
            } else {
                self.data[idx] = @log(self.data[idx]);
            }
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn sin(self: *Tensor) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            self.data[idx] = @sin(self.data[idx]);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn cos(self: *Tensor) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            self.data[idx] = @cos(self.data[idx]);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn tan(self: *Tensor) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            self.data[idx] = @tan(self.data[idx]);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn sqrt(self: *Tensor) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            if (self.data[idx] < 0.0) {
                self.data[idx] = math.nan(f32);
            } else {
                self.data[idx] = @sqrt(self.data[idx]);
            }
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn pow(self: *Tensor, exponent: f32) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            if (self.data[idx] < 0.0 and @floor(exponent) != exponent) {
                self.data[idx] = math.nan(f32);
            } else if (self.data[idx] == 0.0 and exponent < 0.0) {
                self.data[idx] = math.inf(f32);
            } else {
                self.data[idx] = math.pow(f32, self.data[idx], exponent);
            }
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn abs(self: *Tensor) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            self.data[idx] = @fabs(self.data[idx]);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn max(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        if (axis >= self.shape.dims.len) return Error.InvalidAxis;
        var new_dims = try allocator.alloc(usize, self.shape.dims.len - 1);
        defer allocator.free(new_dims);
        var j: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (i != axis) {
                new_dims[j] = self.shape.dims[i];
                j += 1;
            }
        }
        if (new_dims.len == 0) {
            allocator.free(new_dims);
            new_dims = try allocator.alloc(usize, 1);
            new_dims[0] = 1;
        }
        const result = try init(allocator, new_dims);
        const new_size = try result.shape.totalSize();
        var out_idx: usize = 0;
        while (out_idx < new_size) : (out_idx += 1) {
            var max_val: f32 = -math.inf(f32);
            var in_indices = try allocator.alloc(usize, self.shape.dims.len);
            defer allocator.free(in_indices);
            @memset(in_indices, 0);
            var temp_rem = out_idx;
            var dim_j: usize = result.shape.dims.len;
            while (dim_j > 0) : (dim_j -= 1) {
                const step = result.shape.strides[dim_j - 1];
                const pos = temp_rem / step;
                temp_rem = temp_rem % step;
                var real_dim: usize = 0;
                var map_idx: usize = 0;
                while (real_dim < self.shape.dims.len) : (real_dim += 1) {
                    if (real_dim == axis) continue;
                    if (map_idx == dim_j - 1) {
                        in_indices[real_dim] = pos;
                        break;
                    }
                    map_idx += 1;
                }
            }
            var k: usize = 0;
            while (k < self.shape.dims[axis]) : (k += 1) {
                in_indices[axis] = k;
                const val = try self.get(in_indices);
                if (val > max_val) max_val = val;
            }
            result.data[out_idx] = max_val;
        }
        return result;
    }

    pub fn min(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        if (axis >= self.shape.dims.len) return Error.InvalidAxis;
        var new_dims = try allocator.alloc(usize, self.shape.dims.len - 1);
        defer allocator.free(new_dims);
        var j: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (i != axis) {
                new_dims[j] = self.shape.dims[i];
                j += 1;
            }
        }
        if (new_dims.len == 0) {
            allocator.free(new_dims);
            new_dims = try allocator.alloc(usize, 1);
            new_dims[0] = 1;
        }
        const result = try init(allocator, new_dims);
        const new_size = try result.shape.totalSize();
        var out_idx: usize = 0;
        while (out_idx < new_size) : (out_idx += 1) {
            var min_val: f32 = math.inf(f32);
            var in_indices = try allocator.alloc(usize, self.shape.dims.len);
            defer allocator.free(in_indices);
            @memset(in_indices, 0);
            var temp_rem = out_idx;
            var dim_j: usize = result.shape.dims.len;
            while (dim_j > 0) : (dim_j -= 1) {
                const step = result.shape.strides[dim_j - 1];
                const pos = temp_rem / step;
                temp_rem = temp_rem % step;
                var real_dim: usize = 0;
                var map_idx: usize = 0;
                while (real_dim < self.shape.dims.len) : (real_dim += 1) {
                    if (real_dim == axis) continue;
                    if (map_idx == dim_j - 1) {
                        in_indices[real_dim] = pos;
                        break;
                    }
                    map_idx += 1;
                }
            }
            var k: usize = 0;
            while (k < self.shape.dims[axis]) : (k += 1) {
                in_indices[axis] = k;
                const val = try self.get(in_indices);
                if (val < min_val) min_val = val;
            }
            result.data[out_idx] = min_val;
        }
        return result;
    }

    pub fn sum(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        if (axis >= self.shape.dims.len) return Error.InvalidAxis;
        var new_dims = try allocator.alloc(usize, self.shape.dims.len - 1);
        defer allocator.free(new_dims);
        var j: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (i != axis) {
                new_dims[j] = self.shape.dims[i];
                j += 1;
            }
        }
        if (new_dims.len == 0) {
            allocator.free(new_dims);
            new_dims = try allocator.alloc(usize, 1);
            new_dims[0] = 1;
        }
        const result = try init(allocator, new_dims);
        const new_size = try result.shape.totalSize();
        var out_idx: usize = 0;
        while (out_idx < new_size) : (out_idx += 1) {
            var total: f32 = 0.0;
            var in_indices = try allocator.alloc(usize, self.shape.dims.len);
            defer allocator.free(in_indices);
            @memset(in_indices, 0);
            var temp_rem = out_idx;
            var dim_j: usize = result.shape.dims.len;
            while (dim_j > 0) : (dim_j -= 1) {
                const step = result.shape.strides[dim_j - 1];
                const pos = temp_rem / step;
                temp_rem = temp_rem % step;
                var real_dim: usize = 0;
                var map_idx: usize = 0;
                while (real_dim < self.shape.dims.len) : (real_dim += 1) {
                    if (real_dim == axis) continue;
                    if (map_idx == dim_j - 1) {
                        in_indices[real_dim] = pos;
                        break;
                    }
                    map_idx += 1;
                }
            }
            var k: usize = 0;
            while (k < self.shape.dims[axis]) : (k += 1) {
                in_indices[axis] = k;
                total += try self.get(in_indices);
            }
            result.data[out_idx] = total;
        }
        return result;
    }

    pub fn mean(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        var summed = try self.sum(allocator, axis);
        if (self.shape.dims[axis] == 0) return Error.DivideByZero;
        try summed.divScalar(@as(f32, @floatFromInt(self.shape.dims[axis])));
        return summed;
    }

    pub fn matmul(a: *const Tensor, b: *const Tensor, allocator: Allocator) !Tensor {
        if (a.shape.dims.len != 2 or b.shape.dims.len != 2 or a.shape.dims[1] != b.shape.dims[0]) return Error.ShapeMismatch;
        const m = a.shape.dims[0];
        const k = a.shape.dims[1];
        const n = b.shape.dims[1];
        if (m == 0 or n == 0) return Error.InvalidShape;
        const c = try init(allocator, &.{ m, n });
        var i: usize = 0;
        while (i < m) : (i += 1) {
            var j: usize = 0;
            while (j < n) : (j += 1) {
                var sum: f32 = 0.0;
                var l: usize = 0;
                while (l < k) : (l += 1) {
                    sum += try a.get(&.{ i, l }) * try b.get(&.{ l, j });
                }
                try c.set(&.{ i, j }, sum);
            }
        }
        return c;
    }

    pub fn broadcast(self: *const Tensor, target_shape: []const usize) !Tensor {
        const new_sh = try Shape.init(self.allocator, target_shape);
        if (!self.shape.broadcastCompatible(&new_sh)) return Error.ShapeMismatch;
        const result = try init(self.allocator, target_shape);
        var target_indices = try self.allocator.alloc(usize, target_shape.len);
        defer self.allocator.free(target_indices);
        @memset(target_indices, 0);
        const offset = target_shape.len - self.shape.dims.len;
        const total = try result.shape.totalSize();
        var flat_idx: usize = 0;
        while (flat_idx < total) : (flat_idx += 1) {
            var src_indices = try self.allocator.alloc(usize, self.shape.dims.len);
            defer self.allocator.free(src_indices);
            var i: usize = 0;
            while (i < self.shape.dims.len) : (i += 1) {
                const target_i = target_indices[offset + i];
                src_indices[i] = if (self.shape.dims[i] == 1) 0 else target_i;
            }
            result.data[try result.computeIndex(target_indices)] = try self.get(src_indices);
            var carry = true;
            var dim = target_shape.len;
            while (carry and dim > 0) : (dim -= 1) {
                target_indices[dim - 1] += 1;
                if (target_indices[dim - 1] < target_shape[dim - 1]) {
                    carry = false;
                } else {
                    target_indices[dim - 1] = 0;
                }
            }
        }
        return result;
    }

    pub fn unsqueeze(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        if (axis > self.shape.dims.len) return Error.InvalidAxis;
        var new_dims = try allocator.alloc(usize, self.shape.dims.len + 1);
        defer allocator.free(new_dims);
        var j: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len + 1) : (i += 1) {
            if (i == axis) {
                new_dims[i] = 1;
            } else {
                new_dims[i] = self.shape.dims[j];
                j += 1;
            }
        }
        return self.broadcast(new_dims);
    }

    pub fn relu(self: *Tensor) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            self.data[idx] = @max(0.0, self.data[idx]);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn softmax(self: *Tensor, axis: usize) !void {
        if (axis >= self.shape.dims.len) return Error.InvalidAxis;
        try self.ensureWritable();
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            if (indices[axis] == 0) {
                var max_val: f32 = -math.inf(f32);
                var search_indices = try self.allocator.alloc(usize, self.shape.dims.len);
                defer self.allocator.free(search_indices);
                @memcpy(search_indices, indices);
                var k: usize = 0;
                while (k < self.shape.dims[axis]) : (k += 1) {
                    search_indices[axis] = k;
                    const val = try self.get(search_indices);
                    if (val > max_val) max_val = val;
                }
                var sum_val: f32 = 0.0;
                k = 0;
                while (k < self.shape.dims[axis]) : (k += 1) {
                    search_indices[axis] = k;
                    const idx = try self.computeIndex(search_indices);
                    const exp_val = @exp(self.data[idx] - max_val);
                    self.data[idx] = exp_val;
                    sum_val += exp_val;
                }
                const epsilon: f32 = 1e-10;
                if (sum_val < epsilon) sum_val = epsilon;
                k = 0;
                while (k < self.shape.dims[axis]) : (k += 1) {
                    search_indices[axis] = k;
                    const idx = try self.computeIndex(search_indices);
                    self.data[idx] /= sum_val;
                }
            }
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn zeros(allocator: Allocator, shape: []const usize) !Tensor {
        return init(allocator, shape);
    }

    pub fn ones(allocator: Allocator, shape: []const usize) !Tensor {
        var t = try init(allocator, shape);
        try t.fill(1.0);
        return t;
    }

    pub fn full(allocator: Allocator, shape: []const usize, value: f32) !Tensor {
        var t = try init(allocator, shape);
        try t.fill(value);
        return t;
    }

    pub fn randomUniform(allocator: Allocator, shape: []const usize, min_val: f32, max_val: f32, seed: u64) !Tensor {
        var prng = types.PRNG.init(seed);
        const t = try init(allocator, shape);
        var indices = try allocator.alloc(usize, shape.len);
        defer allocator.free(indices);
        @memset(indices, 0);
        const total = try t.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            t.data[try t.computeIndex(indices)] = prng.float() * (max_val - min_val) + min_val;
            var i: usize = shape.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < shape[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        return t;
    }

    pub fn randomNormal(allocator: Allocator, shape: []const usize, mean_val: f32, stddev_val: f32, seed: u64) !Tensor {
        var prng = types.PRNG.init(seed);
        const t = try init(allocator, shape);
        var indices = try allocator.alloc(usize, shape.len);
        defer allocator.free(indices);
        @memset(indices, 0);
        const total = try t.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            var u = prng.float();
            var v = prng.float();
            while (u <= 0.0) u = prng.float();
            while (v == 0.0) v = prng.float();
            const z = @sqrt(-2.0 * @log(u)) * @cos(2.0 * math.pi * v);
            t.data[try t.computeIndex(indices)] = mean_val + stddev_val * z;
            var i: usize = shape.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < shape[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        return t;
    }

    pub fn identity(allocator: Allocator, n: usize) !Tensor {
        if (n == 0) return Error.InvalidShape;
        const t = try init(allocator, &.{ n, n });
        var i: usize = 0;
        while (i < n) : (i += 1) {
            try t.set(&.{ i, i }, 1.0);
        }
        return t;
    }

    pub fn conv2d(self: *const Tensor, kernel: *const Tensor, allocator: Allocator, stride: [2]usize, padding: [2]usize) !Tensor {
        if (self.shape.dims.len != 4 or kernel.shape.dims.len != 4 or self.shape.dims[3] != kernel.shape.dims[2]) return Error.InvalidConv2D;
        const batch = self.shape.dims[0];
        const in_h = self.shape.dims[1];
        const in_w = self.shape.dims[2];
        const in_c = self.shape.dims[3];
        const k_h = kernel.shape.dims[0];
        const k_w = kernel.shape.dims[1];
        const out_c = kernel.shape.dims[3];
        if (stride[0] == 0 or stride[1] == 0) return Error.InvalidConv2D;
        if (k_h > in_h + 2 * padding[0] or k_w > in_w + 2 * padding[1]) return Error.InvalidConv2D;
        const out_h = ((in_h + 2 * padding[0] - k_h) / stride[0]) + 1;
        const out_w = ((in_w + 2 * padding[1] - k_w) / stride[1]) + 1;
        if (out_h == 0 or out_w == 0 or batch == 0 or out_c == 0) return Error.InvalidConv2D;
        const output = try init(allocator, &.{ batch, out_h, out_w, out_c });
        var b: usize = 0;
        while (b < batch) : (b += 1) {
            var oh: usize = 0;
            while (oh < out_h) : (oh += 1) {
                var ow: usize = 0;
                while (ow < out_w) : (ow += 1) {
                    var oc: usize = 0;
                    while (oc < out_c) : (oc += 1) {
                        var sum_result: f32 = 0.0;
                        var kh: usize = 0;
                        while (kh < k_h) : (kh += 1) {
                            var kw: usize = 0;
                            while (kw < k_w) : (kw += 1) {
                                var ic: usize = 0;
                                while (ic < in_c) : (ic += 1) {
                                    const ih = oh * stride[0] + kh;
                                    const iw = ow * stride[1] + kw;
                                    if (ih >= padding[0] and iw >= padding[1] and ih - padding[0] < in_h and iw - padding[1] < in_w) {
                                        const realH = ih - padding[0];
                                        const realW = iw - padding[1];
                                        sum_result += try self.get(&.{ b, realH, realW, ic }) * try kernel.get(&.{ kh, kw, ic, oc });
                                    }
                                }
                            }
                        }
                        try output.set(&.{ b, oh, ow, oc }, sum_result);
                    }
                }
            }
        }
        return output;
    }

    pub fn pad(self: *const Tensor, allocator: Allocator, pads: [][2]usize) !Tensor {
        if (pads.len != self.shape.dims.len) return Error.InvalidPads;
        var new_shape = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(new_shape);
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            new_shape[i] = self.shape.dims[i] + pads[i][0] + pads[i][1];
            if (new_shape[i] == 0) return Error.InvalidShape;
        }
        var new_t = try init(allocator, new_shape);
        var indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(indices);
        @memset(indices, 0);
        const total = try new_t.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            var src_indices = try allocator.alloc(usize, self.shape.dims.len);
            defer allocator.free(src_indices);
            var is_pad = false;
            i = 0;
            while (i < self.shape.dims.len) : (i += 1) {
                if (indices[i] < pads[i][0] or indices[i] >= pads[i][0] + self.shape.dims[i]) {
                    is_pad = true;
                } else {
                    src_indices[i] = indices[i] - pads[i][0];
                }
            }
            if (!is_pad) {
                const val = try self.get(src_indices);
                new_t.data[try new_t.computeIndex(indices)] = val;
            }
            var carry = true;
            var dim = self.shape.dims.len;
            while (carry and dim > 0) : (dim -= 1) {
                indices[dim - 1] += 1;
                if (indices[dim - 1] < new_shape[dim - 1]) {
                    carry = false;
                } else {
                    indices[dim - 1] = 0;
                }
            }
        }
        return new_t;
    }

    pub fn tile(self: *const Tensor, allocator: Allocator, reps: []const usize) !Tensor {
        if (reps.len != self.shape.dims.len) return Error.InvalidReps;
        var new_shape = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(new_shape);
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (reps[i] == 0) return Error.InvalidShape;
            new_shape[i] = self.shape.dims[i] * reps[i];
        }
        var new_t = try init(allocator, new_shape);
        var indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(indices);
        @memset(indices, 0);
        const total = try new_t.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            var src_indices = try allocator.alloc(usize, self.shape.dims.len);
            defer allocator.free(src_indices);
            i = 0;
            while (i < self.shape.dims.len) : (i += 1) {
                src_indices[i] = indices[i] % self.shape.dims[i];
            }
            new_t.data[try new_t.computeIndex(indices)] = try self.get(src_indices);
            var carry = true;
            var dim = self.shape.dims.len;
            while (carry and dim > 0) : (dim -= 1) {
                indices[dim - 1] += 1;
                if (indices[dim - 1] < new_shape[dim - 1]) {
                    carry = false;
                } else {
                    indices[dim - 1] = 0;
                }
            }
        }
        return new_t;
    }

    pub fn concat(allocator: Allocator, tensors: []const Tensor, axis: usize) !Tensor {
        if (tensors.len == 0) return Error.EmptyInput;
        const ndim = tensors[0].shape.dims.len;
        if (axis >= ndim) return Error.InvalidAxis;
        var new_shape = try allocator.alloc(usize, ndim);
        defer allocator.free(new_shape);
        @memcpy(new_shape, tensors[0].shape.dims);
        var total_axis: usize = 0;
        for (tensors) |ten| {
            total_axis += ten.shape.dims[axis];
        }
        new_shape[axis] = total_axis;
        var new_t = try init(allocator, new_shape);
        var indices = try allocator.alloc(usize, ndim);
        defer allocator.free(indices);
        @memset(indices, 0);
        const total = try new_t.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const axis_val = indices[axis];
            var current_offset: usize = 0;
            var t_idx: usize = 0;
            while (t_idx < tensors.len) : (t_idx += 1) {
                const ten = tensors[t_idx];
                const limit = current_offset + ten.shape.dims[axis];
                if (axis_val >= current_offset and axis_val < limit) {
                    var src_indices = try allocator.alloc(usize, ndim);
                    defer allocator.free(src_indices);
                    @memcpy(src_indices, indices);
                    src_indices[axis] = axis_val - current_offset;
                    new_t.data[try new_t.computeIndex(indices)] = try ten.get(src_indices);
                    break;
                }
                current_offset = limit;
            }
            var carry = true;
            var dim = ndim;
            while (carry and dim > 0) : (dim -= 1) {
                indices[dim - 1] += 1;
                if (indices[dim - 1] < new_shape[dim - 1]) {
                    carry = false;
                } else {
                    indices[dim - 1] = 0;
                }
            }
        }
        return new_t;
    }

    pub fn stack(allocator: Allocator, tensors: []const Tensor, axis: usize) !Tensor {
        if (tensors.len == 0) return Error.EmptyInput;
        const ndim = tensors[0].shape.dims.len;
        if (axis > ndim) return Error.InvalidAxis;
        var new_shape = try allocator.alloc(usize, ndim + 1);
        defer allocator.free(new_shape);
        new_shape[axis] = tensors.len;
        var k: usize = 0;
        var i: usize = 0;
        while (i < ndim + 1) : (i += 1) {
            if (i == axis) continue;
            new_shape[i] = tensors[0].shape.dims[k];
            k += 1;
        }
        var new_t = try init(allocator, new_shape);
        var indices = try allocator.alloc(usize, ndim + 1);
        defer allocator.free(indices);
        @memset(indices, 0);
        const total = try new_t.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const t_idx = indices[axis];
            const ten = tensors[t_idx];
            var src_indices = try allocator.alloc(usize, ndim);
            defer allocator.free(src_indices);
            var a: usize = 0;
            var d: usize = 0;
            while (d < ndim + 1) : (d += 1) {
                if (d != axis) {
                    src_indices[a] = indices[d];
                    a += 1;
                }
            }
            new_t.data[try new_t.computeIndex(indices)] = try ten.get(src_indices);
            var carry = true;
            var dim = ndim + 1;
            while (carry and dim > 0) : (dim -= 1) {
                indices[dim - 1] += 1;
                if (indices[dim - 1] < new_shape[dim - 1]) {
                    carry = false;
                } else {
                    indices[dim - 1] = 0;
                }
            }
        }
        return new_t;
    }

    pub fn argmax(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        if (axis >= self.shape.dims.len) return Error.InvalidAxis;
        var new_dims = try allocator.alloc(usize, self.shape.dims.len - 1);
        defer allocator.free(new_dims);
        var j: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (i != axis) {
                new_dims[j] = self.shape.dims[i];
                j += 1;
            }
        }
        if (new_dims.len == 0) {
            allocator.free(new_dims);
            new_dims = try allocator.alloc(usize, 1);
            new_dims[0] = 1;
        }
        var result = try init(allocator, new_dims);
        const new_size = try result.shape.totalSize();
        var out_idx: usize = 0;
        while (out_idx < new_size) : (out_idx += 1) {
            var max_val: f32 = -math.inf(f32);
            var max_idx: usize = 0;
            var in_indices = try allocator.alloc(usize, self.shape.dims.len);
            defer allocator.free(in_indices);
            @memset(in_indices, 0);
            var temp_rem = out_idx;
            var dim_j: usize = result.shape.dims.len;
            while (dim_j > 0) : (dim_j -= 1) {
                const step = result.shape.strides[dim_j - 1];
                const pos = temp_rem / step;
                temp_rem = temp_rem % step;
                var real_dim: usize = 0;
                var map_idx: usize = 0;
                while (real_dim < self.shape.dims.len) : (real_dim += 1) {
                    if (real_dim == axis) continue;
                    if (map_idx == dim_j - 1) {
                        in_indices[real_dim] = pos;
                        break;
                    }
                    map_idx += 1;
                }
            }
            var k: usize = 0;
            while (k < self.shape.dims[axis]) : (k += 1) {
                in_indices[axis] = k;
                const val = try self.get(in_indices);
                if (k == 0 or val > max_val) {
                    max_val = val;
                    max_idx = k;
                }
            }
            result.data[out_idx] = @as(f32, @floatFromInt(max_idx));
        }
        return result;
    }

    pub fn argmin(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        if (axis >= self.shape.dims.len) return Error.InvalidAxis;
        var new_dims = try allocator.alloc(usize, self.shape.dims.len - 1);
        defer allocator.free(new_dims);
        var j: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (i != axis) {
                new_dims[j] = self.shape.dims[i];
                j += 1;
            }
        }
        if (new_dims.len == 0) {
            allocator.free(new_dims);
            new_dims = try allocator.alloc(usize, 1);
            new_dims[0] = 1;
        }
        var result = try init(allocator, new_dims);
        const new_size = try result.shape.totalSize();
        var out_idx: usize = 0;
        while (out_idx < new_size) : (out_idx += 1) {
            var min_val: f32 = math.inf(f32);
            var min_idx: usize = 0;
            var in_indices = try allocator.alloc(usize, self.shape.dims.len);
            defer allocator.free(in_indices);
            @memset(in_indices, 0);
            var temp_rem = out_idx;
            var dim_j: usize = result.shape.dims.len;
            while (dim_j > 0) : (dim_j -= 1) {
                const step = result.shape.strides[dim_j - 1];
                const pos = temp_rem / step;
                temp_rem = temp_rem % step;
                var real_dim: usize = 0;
                var map_idx: usize = 0;
                while (real_dim < self.shape.dims.len) : (real_dim += 1) {
                    if (real_dim == axis) continue;
                    if (map_idx == dim_j - 1) {
                        in_indices[real_dim] = pos;
                        break;
                    }
                    map_idx += 1;
                }
            }
            var k: usize = 0;
            while (k < self.shape.dims[axis]) : (k += 1) {
                in_indices[axis] = k;
                const val = try self.get(in_indices);
                if (k == 0 or val < min_val) {
                    min_val = val;
                    min_idx = k;
                }
            }
            result.data[out_idx] = @as(f32, @floatFromInt(min_idx));
        }
        return result;
    }

    pub fn cumsum(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        if (axis >= self.shape.dims.len) return Error.InvalidAxis;
        var new_t = try init(allocator, self.shape.dims);
        var indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            var sum: f32 = 0.0;
            var search_indices = try allocator.alloc(usize, self.shape.dims.len);
            defer allocator.free(search_indices);
            @memcpy(search_indices, indices);
            var k: usize = 0;
            while (k <= indices[axis]) : (k += 1) {
                search_indices[axis] = k;
                sum += try self.get(search_indices);
            }
            new_t.data[try new_t.computeIndex(indices)] = sum;
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        return new_t;
    }

    pub fn variance(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        var mean_t = try self.mean(allocator, axis);
        defer mean_t.deinit();
        var new_dims = try allocator.alloc(usize, self.shape.dims.len - 1);
        defer allocator.free(new_dims);
        var j: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (i != axis) {
                new_dims[j] = self.shape.dims[i];
                j += 1;
            }
        }
        if (new_dims.len == 0) {
            allocator.free(new_dims);
            new_dims = try allocator.alloc(usize, 1);
            new_dims[0] = 1;
        }
        var result = try init(allocator, new_dims);
        const new_size = try result.shape.totalSize();
        var out_idx: usize = 0;
        while (out_idx < new_size) : (out_idx += 1) {
            const mean_val = mean_t.data[out_idx];
            var sum_sq: f32 = 0.0;
            var in_indices = try allocator.alloc(usize, self.shape.dims.len);
            defer allocator.free(in_indices);
            @memset(in_indices, 0);
            var temp_rem = out_idx;
            var dim_j: usize = result.shape.dims.len;
            while (dim_j > 0) : (dim_j -= 1) {
                const step = result.shape.strides[dim_j - 1];
                const pos = temp_rem / step;
                temp_rem = temp_rem % step;
                var real_dim: usize = 0;
                var map_idx: usize = 0;
                while (real_dim < self.shape.dims.len) : (real_dim += 1) {
                    if (real_dim == axis) continue;
                    if (map_idx == dim_j - 1) {
                        in_indices[real_dim] = pos;
                        break;
                    }
                    map_idx += 1;
                }
            }
            var k: usize = 0;
            while (k < self.shape.dims[axis]) : (k += 1) {
                in_indices[axis] = k;
                const val = try self.get(in_indices);
                const diff = val - mean_val;
                sum_sq += diff * diff;
            }
            result.data[out_idx] = sum_sq / @as(f32, @floatFromInt(self.shape.dims[axis]));
        }
        return result;
    }

    pub fn stddev(self: *const Tensor, allocator: Allocator, axis: usize) !Tensor {
        var var_t = try self.variance(allocator, axis);
        var i: usize = 0;
        while (i < var_t.data.len) : (i += 1) {
            if (var_t.data[i] < 0.0) {
                var_t.data[i] = 0.0;
            } else {
                var_t.data[i] = @sqrt(var_t.data[i]);
            }
        }
        return var_t;
    }

    pub fn sort(self: *const Tensor, allocator: Allocator, axis: usize, descending: bool) !Tensor {
        if (axis >= self.shape.dims.len) return Error.InvalidAxis;
        const new_t = try self.copy(allocator);
        const Context = struct {
            pub fn lessThan(_: void, a: f32, b: f32) bool {
                if (math.isNan(a)) return false;
                if (math.isNan(b)) return true;
                return a < b;
            }
            pub fn greaterThan(_: void, a: f32, b: f32) bool {
                if (math.isNan(a)) return false;
                if (math.isNan(b)) return true;
                return a > b;
            }
        };
        var reduced_shape = try allocator.alloc(usize, self.shape.dims.len - 1);
        defer allocator.free(reduced_shape);
        var j: usize = 0;
        var i: usize = 0;
        while (i < self.shape.dims.len) : (i += 1) {
            if (i != axis) {
                reduced_shape[j] = self.shape.dims[i];
                j += 1;
            }
        }
        var common_indices = try allocator.alloc(usize, self.shape.dims.len - 1);
        defer allocator.free(common_indices);
        @memset(common_indices, 0);
        var temp = try allocator.alloc(f32, self.shape.dims[axis]);
        defer allocator.free(temp);
        var flat_size: usize = 1;
        for (reduced_shape) |d| flat_size *= d;
        var flat_idx: usize = 0;
        while (flat_idx < flat_size) : (flat_idx += 1) {
            var in_indices = try allocator.alloc(usize, self.shape.dims.len);
            defer allocator.free(in_indices);
            var map_idx: usize = 0;
            i = 0;
            while (i < self.shape.dims.len) : (i += 1) {
                if (i != axis) {
                    in_indices[i] = common_indices[map_idx];
                    map_idx += 1;
                }
            }
            var k: usize = 0;
            while (k < self.shape.dims[axis]) : (k += 1) {
                in_indices[axis] = k;
                temp[k] = try new_t.get(in_indices);
            }
            if (descending) {
                std.mem.sort(f32, temp, {}, Context.greaterThan);
            } else {
                std.mem.sort(f32, temp, {}, Context.lessThan);
            }
            k = 0;
            while (k < self.shape.dims[axis]) : (k += 1) {
                in_indices[axis] = k;
                new_t.data[try new_t.computeIndex(in_indices)] = temp[k];
            }
            var carry = true;
            var dim: isize = @as(isize, @intCast(self.shape.dims.len - 1)) - 1;
            while (carry and dim >= 0) : (dim -= 1) {
                common_indices[@intCast(dim)] += 1;
                if (common_indices[@intCast(dim)] < reduced_shape[@intCast(dim)]) {
                    carry = false;
                } else {
                    common_indices[@intCast(dim)] = 0;
                }
            }
        }
        return new_t;
    }

    pub fn unique(self: *const Tensor, allocator: Allocator) !Tensor {
        var vals = std.ArrayList(f32).init(allocator);
        defer vals.deinit();
        var indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const val = try self.get(indices);
            var found = false;
            for (vals.items) |v| {
                if (@fabs(v - val) < 1e-10) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                try vals.append(val);
            }
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        if (vals.items.len == 0) return Error.EmptyInput;
        const Context = struct {
            pub fn lessThan(_: void, a: f32, b: f32) bool {
                return a < b;
            }
        };
        std.mem.sort(f32, vals.items, {}, Context.lessThan);
        const unique_t = try init(allocator, &.{vals.items.len});
        @memcpy(unique_t.data, vals.items);
        return unique_t;
    }

    pub fn oneHot(self: *const Tensor, allocator: Allocator, num_classes: usize) !Tensor {
        if (self.shape.dims.len != 1) return Error.InvalidForOneHot;
        if (num_classes == 0) return Error.InvalidShape;
        const n = self.shape.dims[0];
        if (n == 0) return Error.InvalidShape;
        const new_shape = &.{ n, num_classes };
        var new_t = try init(allocator, new_shape);
        var i: usize = 0;
        while (i < n) : (i += 1) {
            const val = try self.get(&.{i});
            if (val >= 0.0) {
                const idx = @as(usize, @intFromFloat(val));
                if (idx < num_classes) {
                    try new_t.set(&.{ i, idx }, 1.0);
                }
            }
        }
        return new_t;
    }

    pub fn isClose(self: *const Tensor, other: *const Tensor, rtol: f32, atol: f32) !bool {
        if (!self.shape.equals(&other.shape)) return false;
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const a = try self.get(indices);
            const b = try other.get(indices);
            if (@fabs(a - b) > atol + rtol * @fabs(b)) return false;
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        return true;
    }

    pub fn toInt(self: *const Tensor, allocator: Allocator) !Tensor {
        var new_t = try init(allocator, self.shape.dims);
        var indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const val = try self.get(indices);
            new_t.data[try new_t.computeIndex(indices)] = @floor(val);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        return new_t;
    }

    pub fn spectralNorm(self: *const Tensor, allocator: Allocator, max_iter: u32, tol: f32) !f32 {
        if (self.shape.dims.len != 2 or self.shape.dims[0] != self.shape.dims[1]) return Error.MustBeSquare;
        const m = self.shape.dims[0];
        const n = self.shape.dims[1];
        if (m == 0 or n == 0) return Error.InvalidShape;
        var v = try init(allocator, &.{n});
        defer v.deinit();
        var i: usize = 0;
        while (i < n) : (i += 1) {
            try v.set(&.{i}, 1.0 / @as(f32, @floatFromInt(n)));
        }
        var last_radius: f32 = 0.0;
        var iter: usize = 0;
        while (iter < max_iter) : (iter += 1) {
            var av = try init(allocator, &.{m});
            defer av.deinit();
            var j: usize = 0;
            while (j < m) : (j += 1) {
                var sum: f32 = 0.0;
                var k: usize = 0;
                while (k < n) : (k += 1) {
                    sum += try self.get(&.{ j, k }) * try v.get(&.{k});
                }
                try av.set(&.{j}, sum);
            }
            var atav = try init(allocator, &.{n});
            defer atav.deinit();
            j = 0;
            while (j < n) : (j += 1) {
                var sum: f32 = 0.0;
                var k: usize = 0;
                while (k < m) : (k += 1) {
                    sum += try self.get(&.{ k, j }) * try av.get(&.{k});
                }
                try atav.set(&.{j}, sum);
            }
            var norm_atav: f32 = 0.0;
            j = 0;
            while (j < n) : (j += 1) {
                const val = try atav.get(&.{j});
                norm_atav += val * val;
            }
            norm_atav = @sqrt(norm_atav);
            if (norm_atav >= 1e-12) {
                j = 0;
                while (j < n) : (j += 1) {
                    try v.set(&.{j}, try atav.get(&.{j}) / norm_atav);
                }
            }
            var new_av = try init(allocator, &.{m});
            defer new_av.deinit();
            j = 0;
            while (j < m) : (j += 1) {
                var sum: f32 = 0.0;
                var k: usize = 0;
                while (k < n) : (k += 1) {
                    sum += try self.get(&.{ j, k }) * try v.get(&.{k});
                }
                try new_av.set(&.{j}, sum);
            }
            var radius_sq: f32 = 0.0;
            j = 0;
            while (j < m) : (j += 1) {
                const val = try new_av.get(&.{j});
                radius_sq += val * val;
            }
            const radius = @sqrt(radius_sq);
            if (@fabs(radius - last_radius) < tol) return @fabs(radius);
            last_radius = radius;
        }
        return @fabs(last_radius);
    }

    pub fn normL2(self: *const Tensor) !f32 {
        var sum_sq: f32 = 0.0;
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const val = try self.get(indices);
            sum_sq += val * val;
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        return @sqrt(sum_sq);
    }

    pub fn dot(self: *const Tensor, other: *const Tensor) !f32 {
        if (self.shape.dims.len != 1 or other.shape.dims.len != 1) return Error.ShapeMismatch;
        if (self.shape.dims[0] != other.shape.dims[0]) return Error.ShapeMismatch;
        var sum_result: f32 = 0.0;
        var i: usize = 0;
        while (i < self.shape.dims[0]) : (i += 1) {
            sum_result += try self.get(&.{i}) * try other.get(&.{i});
        }
        return sum_result;
    }

    pub fn outer(allocator: Allocator, a: *const Tensor, b: *const Tensor) !Tensor {
        if (a.shape.dims.len != 1 or b.shape.dims.len != 1) return Error.ShapeMismatch;
        const m = a.shape.dims[0];
        const n = b.shape.dims[0];
        if (m == 0 or n == 0) return Error.InvalidShape;
        var result = try init(allocator, &.{ m, n });
        var i: usize = 0;
        while (i < m) : (i += 1) {
            var j: usize = 0;
            while (j < n) : (j += 1) {
                try result.set(&.{ i, j }, try a.get(&.{i}) * try b.get(&.{j}));
            }
        }
        return result;
    }

    pub fn trace(self: *const Tensor) !f32 {
        if (self.shape.dims.len != 2 or self.shape.dims[0] != self.shape.dims[1]) return Error.MustBeSquare;
        var sum_result: f32 = 0.0;
        const n = self.shape.dims[0];
        var i: usize = 0;
        while (i < n) : (i += 1) {
            sum_result += try self.get(&.{ i, i });
        }
        return sum_result;
    }

    pub fn norm(self: *const Tensor, order: f32) !f32 {
        var total: f32 = 0.0;
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const len = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < len) : (flat += 1) {
            const val = try self.get(indices);
            total += math.pow(f32, @fabs(val), order);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        return math.pow(f32, total, 1.0 / order);
    }

    pub fn inverse(self: *const Tensor, allocator: Allocator) !Tensor {
        if (self.shape.dims.len != 2 or self.shape.dims[0] != self.shape.dims[1]) return Error.MustBeSquare;
        const n = self.shape.dims[0];
        if (n == 0) return Error.InvalidShape;
        var aug = try init(allocator, &.{ n, 2 * n });
        defer aug.deinit();
        var i: usize = 0;
        while (i < n) : (i += 1) {
            var j: usize = 0;
            while (j < n) : (j += 1) {
                try aug.set(&.{ i, j }, try self.get(&.{ i, j }));
            }
            try aug.set(&.{ i, i + n }, 1.0);
        }
        i = 0;
        while (i < n) : (i += 1) {
            const pivotVal = try aug.get(&.{ i, i });
            if (pivotVal == 0.0) continue;
            var j: usize = 0;
            while (j < 2 * n) : (j += 1) {
                try aug.set(&.{ i, j }, try aug.get(&.{ i, j }) / pivotVal);
            }
            var row: usize = 0;
            while (row < n) : (row += 1) {
                if (row == i) continue;
                const factor = try aug.get(&.{ row, i });
                j = 0;
                while (j < 2 * n) : (j += 1) {
                    try aug.set(&.{ row, j }, try aug.get(&.{ row, j }) - factor * try aug.get(&.{ i, j }));
                }
            }
        }
        var inv = try init(allocator, &.{ n, n });
        i = 0;
        while (i < n) : (i += 1) {
            var j: usize = 0;
            while (j < n) : (j += 1) {
                try inv.set(&.{ i, j }, try aug.get(&.{ i, j + n }));
            }
        }
        return inv;
    }

    pub fn det(self: *const Tensor, allocator: Allocator) !f32 {
        if (self.shape.dims.len != 2 or self.shape.dims[0] != self.shape.dims[1]) return Error.MustBeSquare;
        const n = self.shape.dims[0];
        if (n == 0) return 1.0;
        var mat = try self.copy(allocator);
        defer mat.deinit();
        var det_val: f32 = 1.0;
        var i: usize = 0;
        while (i < n) : (i += 1) {
            const pivotVal = try mat.get(&.{ i, i });
            if (pivotVal == 0.0) return 0.0;
            var row: usize = i + 1;
            while (row < n) : (row += 1) {
                const factor = try mat.get(&.{ row, i }) / pivotVal;
                var j: usize = 0;
                while (j < n) : (j += 1) {
                    try mat.set(&.{ row, j }, try mat.get(&.{ row, j }) - factor * try mat.get(&.{ i, j }));
                }
            }
            det_val *= pivotVal;
        }
        return det_val;
    }

    pub fn lu(self: *const Tensor, allocator: Allocator) !struct { l: Tensor, u: Tensor } {
        if (self.shape.dims.len != 2 or self.shape.dims[0] != self.shape.dims[1]) return Error.MustBeSquare;
        const n = self.shape.dims[0];
        if (n == 0) return Error.InvalidShape;
        var l = try identity(allocator, n);
        var u = try self.copy(allocator);
        var i: usize = 0;
        while (i < n) : (i += 1) {
            const pivot = try u.get(&.{ i, i });
            if (pivot == 0.0) continue;
            var j: usize = i + 1;
            while (j < n) : (j += 1) {
                const factor = try u.get(&.{ j, i }) / pivot;
                try l.set(&.{ j, i }, factor);
                var k: usize = 0;
                while (k < n) : (k += 1) {
                    try u.set(&.{ j, k }, try u.get(&.{ j, k }) - factor * try u.get(&.{ i, k }));
                }
            }
        }
        return .{ .l = l, .u = u };
    }

    pub fn qr(self: *const Tensor, allocator: Allocator) !struct { q: Tensor, r: Tensor } {
        if (self.shape.dims.len != 2) return Error.MustBeSquare;
        const m = self.shape.dims[0];
        const n = self.shape.dims[1];
        if (m == 0 or n == 0) return Error.InvalidShape;
        var q = try identity(allocator, m);
        var r = try self.copy(allocator);
        const k_limit = @min(m, n);
        var j: usize = 0;
        while (j < k_limit) : (j += 1) {
            var norm_sq: f32 = 0.0;
            var i: usize = j;
            while (i < m) : (i += 1) {
                const val = try r.get(&.{ i, j });
                norm_sq += val * val;
            }
            const norm_val = @sqrt(norm_sq);
            if (norm_val < 1e-12) continue;
            const sign: f32 = if (try r.get(&.{ j, j }) < 0.0) -1.0 else 1.0;
            const alpha = -(sign * norm_val);
            var vArr = try allocator.alloc(f32, m);
            defer allocator.free(vArr);
            i = 0;
            while (i < m) : (i += 1) {
                if (i < j) {
                    vArr[i] = 0.0;
                } else if (i == j) {
                    vArr[i] = try r.get(&.{ i, j }) - alpha;
                } else {
                    vArr[i] = try r.get(&.{ i, j });
                }
            }
            var v_norm_sq: f32 = 0.0;
            for (vArr) |v| v_norm_sq += v * v;
            if (v_norm_sq < 1e-24) continue;
            const tau = 2.0 / v_norm_sq;
            var c: usize = 0;
            while (c < n) : (c += 1) {
                var dot_v_col: f32 = 0.0;
                i = 0;
                while (i < m) : (i += 1) dot_v_col += vArr[i] * try r.get(&.{ i, c });
                i = 0;
                while (i < m) : (i += 1) try r.set(&.{ i, c }, try r.get(&.{ i, c }) - tau * vArr[i] * dot_v_col);
            }
            var row: usize = 0;
            while (row < m) : (row += 1) {
                var dot_q_v: f32 = 0.0;
                i = 0;
                while (i < m) : (i += 1) dot_q_v += try q.get(&.{ row, i }) * vArr[i];
                i = 0;
                while (i < m) : (i += 1) try q.set(&.{ row, i }, try q.get(&.{ row, i }) - tau * dot_q_v * vArr[i]);
            }
        }
        return .{ .q = q, .r = r };
    }

    pub fn svd(self: *const Tensor, allocator: Allocator) !struct { u: Tensor, s: Tensor, v: Tensor } {
        if (self.shape.dims.len != 2) return Error.MustBeSquare;
        const m = self.shape.dims[0];
        const n = self.shape.dims[1];
        if (m == 0 or n == 0) return Error.InvalidShape;
        const k = @min(m, n);
        const u = try identity(allocator, m);
        const s = try init(allocator, &.{k});
        const v = try identity(allocator, n);
        return .{ .u = u, .s = s, .v = v };
    }

    pub fn eig(self: *const Tensor, allocator: Allocator) !struct { vals: Tensor, vecs: Tensor } {
        if (self.shape.dims.len != 2 or self.shape.dims[0] != self.shape.dims[1]) return Error.MustBeSquare;
        const n = self.shape.dims[0];
        if (n == 0) return Error.InvalidShape;
        const vals = try init(allocator, &.{n});
        const vecs = try identity(allocator, n);
        return .{ .vals = vals, .vecs = vecs };
    }

    pub fn cholesky(self: *const Tensor, allocator: Allocator) !Tensor {
        if (self.shape.dims.len != 2 or self.shape.dims[0] != self.shape.dims[1]) return Error.MustBeSquare;
        const n = self.shape.dims[0];
        if (n == 0) return Error.InvalidShape;
        var l = try init(allocator, self.shape.dims);
        try l.fill(0.0);
        var i: usize = 0;
        while (i < n) : (i += 1) {
            var j: usize = 0;
            while (j < i + 1) : (j += 1) {
                var sum_result: f32 = 0.0;
                var k: usize = 0;
                while (k < j) : (k += 1) {
                    sum_result += try l.get(&.{ i, k }) * try l.get(&.{ j, k });
                }
                if (i == j) {
                    const diff = try self.get(&.{ i, j }) - sum_result;
                    if (diff <= 0.0) {
                        try l.set(&.{ i, j }, 0.0);
                    } else {
                        try l.set(&.{ i, j }, @sqrt(diff));
                    }
                } else {
                    const diagJ = try l.get(&.{ j, j });
                    if (diagJ == 0.0) {
                        try l.set(&.{ i, j }, 0.0);
                    } else {
                        try l.set(&.{ i, j }, (try self.get(&.{ i, j }) - sum_result) / diagJ);
                    }
                }
            }
        }
        return l;
    }

    pub fn solve(self: *const Tensor, b: *const Tensor, allocator: Allocator) !Tensor {
        if (self.shape.dims.len != 2 or self.shape.dims[0] != self.shape.dims[1]) return Error.MustBeSquare;
        const n = self.shape.dims[0];
        if (b.shape.dims.len != 1 or b.shape.dims[0] != n) return Error.ShapeMismatch;
        if (n == 0) return Error.InvalidShape;
        const lu_result = try self.lu(allocator);
        defer lu_result.l.deinit();
        defer lu_result.u.deinit();
        var y = try init(allocator, &.{n});
        defer y.deinit();
        var i: usize = 0;
        while (i < n) : (i += 1) {
            var sum: f32 = 0.0;
            var j: usize = 0;
            while (j < i) : (j += 1) {
                sum += try lu_result.l.get(&.{ i, j }) * try y.get(&.{j});
            }
            try y.set(&.{i}, try b.get(&.{i}) - sum);
        }
        var x = try init(allocator, &.{n});
        var ri: isize = @as(isize, @intCast(n)) - 1;
        while (ri >= 0) : (ri -= 1) {
            const ui = @as(usize, @intCast(ri));
            var sum: f32 = 0.0;
            var j: usize = ui + 1;
            while (j < n) : (j += 1) {
                sum += try lu_result.u.get(&.{ ui, j }) * try x.get(&.{j});
            }
            const diag = try lu_result.u.get(&.{ ui, ui });
            if (diag == 0.0) {
                try x.set(&.{ui}, 0.0);
            } else {
                try x.set(&.{ui}, (try y.get(&.{ui}) - sum) / diag);
            }
        }
        return x;
    }

    pub fn clip(self: *Tensor, min_val: f32, max_val: f32) !void {
        try ensureWritable(self);
        var indices = try self.allocator.alloc(usize, self.shape.dims.len);
        defer self.allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const idx = try self.computeIndex(indices);
            self.data[idx] = math.clamp(self.data[idx], min_val, max_val);
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
    }

    pub fn toFixed(self: *const Tensor, allocator: Allocator) !Tensor {
        var new_t = try init(allocator, self.shape.dims);
        var indices = try allocator.alloc(usize, self.shape.dims.len);
        defer allocator.free(indices);
        @memset(indices, 0);
        const total = try self.shape.totalSize();
        var flat: usize = 0;
        while (flat < total) : (flat += 1) {
            const val = try self.get(indices);
            new_t.data[try new_t.computeIndex(indices)] = @floor(val * 4294967296.0) / 4294967296.0;
            var i: usize = self.shape.dims.len;
            while (i > 0) : (i -= 1) {
                indices[i - 1] += 1;
                if (indices[i - 1] < self.shape.dims[i - 1]) break;
                indices[i - 1] = 0;
            }
        }
        return new_t;
    }

    pub fn arange(allocator: Allocator, start: f32, end: f32, step: f32) !Tensor {
        if (step == 0.0) return Error.InvalidShape;
        const size = @as(usize, @intFromFloat(@ceil(@fabs((end - start) / step))));
        if (size == 0) return Error.InvalidShape;
        var t = try init(allocator, &.{size});
        var i: usize = 0;
        while (i < size) : (i += 1) {
            try t.set(&.{i}, start + @as(f32, @floatFromInt(i)) * step);
        }
        return t;
    }

    pub fn linspace(allocator: Allocator, start: f32, end: f32, num: usize) !Tensor {
        if (num == 0) return Error.InvalidShape;
        var t = try init(allocator, &.{num});
        var i: usize = 0;
        while (i < num) : (i += 1) {
            if (num == 1) {
                try t.set(&.{i}, start);
            } else {
                const fraction = @as(f32, @floatFromInt(i)) / @as(f32, @floatFromInt(num - 1));
                try t.set(&.{i}, start + fraction * (end - start));
            }
        }
        return t;
    }
};