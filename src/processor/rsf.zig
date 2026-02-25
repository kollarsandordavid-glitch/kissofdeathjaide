const std = @import("std");
const Allocator = std.mem.Allocator;
const Tensor = @import("../core/tensor.zig").Tensor;
const memory = @import("../core/memory.zig");
const accel = @import("../hw/accel/accel_interface.zig");
const Thread = std.Thread;

pub const RSFLayerConfig = struct {
    clip_min: f32 = -5.0,
    clip_max: f32 = 5.0,
    seed_offset: u64 = 0,
    grad_mean: bool = true,
};

fn checkedMul(a: usize, b: usize) !usize {
    return std.math.mul(usize, a, b) catch return error.Overflow;
}

fn checkedMulU64(a: u64, b: u64) !u64 {
    return std.math.mul(u64, a, b) catch return error.Overflow;
}

fn checkedAddU64(a: u64, b: u64) !u64 {
    return std.math.add(u64, a, b) catch return error.Overflow;
}

fn validateTensor2D(t: *const Tensor) !void {
    if (t.shape.dims.len != 2) return error.ShapeMismatch;
    const rows = t.shape.dims[0];
    const cols = t.shape.dims[1];
    const expected = try checkedMul(rows, cols);
    if (t.data.len != expected) return error.DataLengthMismatch;
}

fn countNonFinite(data: []const f32) usize {
    var count: usize = 0;
    for (data) |v| {
        if (!std.math.isFinite(v)) count += 1;
    }
    return count;
}

fn sanitizeSlice(data: []f32) !void {
    for (data) |*v| {
        if (!std.math.isFinite(v.*)) v.* = 0.0;
    }
}

fn addBiasToSlice(data: []f32, bias: []const f32, batch_size: usize, dim: usize) !void {
    const required = try checkedMul(batch_size, dim);
    if (data.len < required) return error.DataLengthMismatch;
    if (bias.len < dim) return error.DataLengthMismatch;
    var offset: usize = 0;
    var b: usize = 0;
    while (b < batch_size) : (b += 1) {
        var d: usize = 0;
        while (d < dim) : (d += 1) {
            data[offset + d] += bias[d];
        }
        offset += dim;
    }
}

fn mulSliceInPlace(dst: []f32, src: []const f32) !void {
    if (dst.len != src.len) return error.DataLengthMismatch;
    var i: usize = 0;
    while (i < dst.len) : (i += 1) {
        dst[i] *= src[i];
    }
}

fn tensorsOverlap(a: *const Tensor, b: *const Tensor) bool {
    if (a.data.len == 0 or b.data.len == 0) return false;
    const a_start = @intFromPtr(a.data.ptr);
    const a_end = a_start + a.data.len * @sizeOf(f32);
    const b_start = @intFromPtr(b.data.ptr);
    const b_end = b_start + b.data.len * @sizeOf(f32);
    return a_start < b_end and b_start < a_end;
}

pub const RSFLayer = struct {
    s_weight: Tensor,
    t_weight: Tensor,
    s_bias: Tensor,
    t_bias: Tensor,
    s_weight_grad: ?Tensor,
    t_weight_grad: ?Tensor,
    s_bias_grad: ?Tensor,
    t_bias_grad: ?Tensor,
    dim: usize,
    allocator: Allocator,
    clip_min: f32,
    clip_max: f32,
    grad_mean: bool,
    deinitialized: bool,

    pub fn init(allocator: Allocator, dim: usize) !RSFLayer {
        return initWithConfig(allocator, dim, .{});
    }

    pub fn initWithArena(arena: *memory.ArenaAllocator, dim: usize, config: RSFLayerConfig) !RSFLayer {
        return initWithConfig(arena.allocator(), dim, config);
    }

    pub fn initWithPool(pool: *memory.PoolAllocator, dim: usize, config: RSFLayerConfig) !RSFLayer {
        return initWithConfig(pool.allocator(), dim, config);
    }

    pub fn initWithSlab(slab: *memory.SlabAllocator, dim: usize, config: RSFLayerConfig) !RSFLayer {
        return initWithConfig(slab.allocator(), dim, config);
    }

    pub fn initWithBuddy(buddy: *memory.BuddyAllocator, dim: usize, config: RSFLayerConfig) !RSFLayer {
        return initWithConfig(buddy.allocator(), dim, config);
    }

    pub fn initWithConfig(allocator: Allocator, dim: usize, config: RSFLayerConfig) !RSFLayer {
        if (dim == 0) return error.InvalidDimension;
        if (!std.math.isFinite(config.clip_min) or !std.math.isFinite(config.clip_max)) return error.NonFinite;
        if (!(config.clip_min < config.clip_max)) return error.InvalidConfig;
        if (config.clip_max > 20.0) return error.InvalidConfig;
        if (config.clip_min < -20.0) return error.InvalidConfig;

        _ = try checkedMul(dim, dim);

        const fan_in: f64 = @floatFromInt(dim);
        const fan_out: f64 = @floatFromInt(dim);
        const fan_sum = fan_in + fan_out;
        if (!(fan_sum > 0.0)) return error.InvalidDimension;

        const xavier_bound: f32 = @floatCast(@sqrt(6.0 / fan_sum));

        const weight_shape = [_]usize{ dim, dim };
        const bias_shape = [_]usize{ 1, dim };

        const seed1 = try checkedAddU64(42, config.seed_offset);
        const seed2 = try checkedAddU64(43, config.seed_offset);

        var s_w = try Tensor.randomUniform(allocator, &weight_shape, -xavier_bound, xavier_bound, seed1);
        errdefer s_w.deinit();

        var t_w = try Tensor.randomUniform(allocator, &weight_shape, -xavier_bound, xavier_bound, seed2);
        errdefer t_w.deinit();

        var s_b = try Tensor.zeros(allocator, &bias_shape);
        errdefer s_b.deinit();

        var t_b = try Tensor.zeros(allocator, &bias_shape);
        errdefer t_b.deinit();

        return RSFLayer{
            .s_weight = s_w,
            .t_weight = t_w,
            .s_bias = s_b,
            .t_bias = t_b,
            .s_weight_grad = null,
            .t_weight_grad = null,
            .s_bias_grad = null,
            .t_bias_grad = null,
            .dim = dim,
            .allocator = allocator,
            .clip_min = config.clip_min,
            .clip_max = config.clip_max,
            .grad_mean = config.grad_mean,
            .deinitialized = false,
        };
    }

    pub fn ensureGradients(self: *RSFLayer) !void {
        if (self.deinitialized) return error.NotInitialized;
        if (self.s_weight_grad != null) return;
        const weight_shape = [_]usize{ self.dim, self.dim };
        const bias_shape = [_]usize{ 1, self.dim };

        var swg = try Tensor.zeros(self.allocator, &weight_shape);
        errdefer swg.deinit();
        var twg = try Tensor.zeros(self.allocator, &weight_shape);
        errdefer twg.deinit();
        var sbg = try Tensor.zeros(self.allocator, &bias_shape);
        errdefer sbg.deinit();
        var tbg = try Tensor.zeros(self.allocator, &bias_shape);

        self.s_weight_grad = swg;
        self.t_weight_grad = twg;
        self.s_bias_grad = sbg;
        self.t_bias_grad = tbg;
    }

    pub fn deinit(self: *RSFLayer) void {
        if (self.deinitialized) return;
        self.s_weight.deinit();
        self.t_weight.deinit();
        self.s_bias.deinit();
        self.t_bias.deinit();
        if (self.s_weight_grad) |*g| g.deinit();
        if (self.t_weight_grad) |*g| g.deinit();
        if (self.s_bias_grad) |*g| g.deinit();
        if (self.t_bias_grad) |*g| g.deinit();
        self.s_weight_grad = null;
        self.t_weight_grad = null;
        self.s_bias_grad = null;
        self.t_bias_grad = null;
        self.deinitialized = true;
    }

    pub fn zeroGradients(self: *RSFLayer) void {
        if (self.deinitialized) return;
        if (self.s_weight_grad) |*g| for (g.data) |*v| {
            v.* = 0.0;
        };
        if (self.t_weight_grad) |*g| for (g.data) |*v| {
            v.* = 0.0;
        };
        if (self.s_bias_grad) |*g| for (g.data) |*v| {
            v.* = 0.0;
        };
        if (self.t_bias_grad) |*g| for (g.data) |*v| {
            v.* = 0.0;
        };
    }

    fn validatePair(self: *const RSFLayer, a: *const Tensor, b: *const Tensor) !usize {
        if (self.deinitialized) return error.NotInitialized;
        try validateTensor2D(a);
        try validateTensor2D(b);
        if (tensorsOverlap(a, b)) return error.AliasedBuffers;
        if (a.shape.dims[1] != self.dim or b.shape.dims[1] != self.dim) return error.ShapeMismatch;
        if (a.shape.dims[0] != b.shape.dims[0]) return error.ShapeMismatch;
        if (self.s_bias.data.len != self.dim or self.t_bias.data.len != self.dim) return error.ShapeMismatch;
        const batch_size = a.shape.dims[0];
        if (batch_size == 0) return error.InvalidBatchSize;
        _ = try checkedMul(batch_size, self.dim);
        return batch_size;
    }

    fn computeScale(self: *const RSFLayer, x2_in: *const Tensor, batch_size: usize) !Tensor {
        var x2_copy = try x2_in.copy(self.allocator);
        defer x2_copy.deinit();
        var x2_t = try x2_copy.transpose(&.{ 1, 0 });
        defer x2_t.deinit();

        var s_w_copy = try self.s_weight.copy(self.allocator);
        defer s_w_copy.deinit();
        var s_x2_t = try s_w_copy.matmul(&x2_t, self.allocator);
        defer s_x2_t.deinit();

        var scale = try s_x2_t.transpose(&.{ 1, 0 });

        try addBiasToSlice(scale.data, self.s_bias.data, batch_size, self.dim);
        try scale.clip(self.clip_min, self.clip_max);
        try scale.exp();

        for (scale.data) |v| {
            if (v == 0.0 or !std.math.isFinite(v)) return error.NumericFailure;
        }

        return scale;
    }

    fn computeTranslation(self: *const RSFLayer, x1: *const Tensor, batch_size: usize) !Tensor {
        var x1_copy = try x1.copy(self.allocator);
        defer x1_copy.deinit();
        var x1_t = try x1_copy.transpose(&.{ 1, 0 });
        defer x1_t.deinit();

        var t_w_copy = try self.t_weight.copy(self.allocator);
        defer t_w_copy.deinit();
        var t_x1_t = try t_w_copy.matmul(&x1_t, self.allocator);
        defer t_x1_t.deinit();

        var trans = try t_x1_t.transpose(&.{ 1, 0 });

        try addBiasToSlice(trans.data, self.t_bias.data, batch_size, self.dim);

        for (trans.data) |v| {
            if (!std.math.isFinite(v)) return error.NumericFailure;
        }

        return trans;
    }

    pub fn forward(self: *const RSFLayer, x1: *Tensor, x2: *Tensor) !void {
        const batch_size = try self.validatePair(x1, x2);

        var scale = try self.computeScale(x2, batch_size);
        defer scale.deinit();

        try mulSliceInPlace(x1.data, scale.data);

        if (countNonFinite(x1.data) > 0) return error.NumericFailure;

        var trans = try self.computeTranslation(x1, batch_size);
        defer trans.deinit();

        if (trans.data.len != x2.data.len) return error.ShapeMismatch;
        try x2.add(&trans);

        if (countNonFinite(x2.data) > 0) return error.NumericFailure;
    }

    pub fn inverse(self: *const RSFLayer, y1: *Tensor, y2: *Tensor) !void {
        const batch_size = try self.validatePair(y1, y2);

        var trans = try self.computeTranslation(y1, batch_size);
        defer trans.deinit();

        if (trans.data.len != y2.data.len) return error.ShapeMismatch;
        try y2.sub(&trans);

        if (countNonFinite(y2.data) > 0) return error.NumericFailure;

        var scale = try self.computeScale(y2, batch_size);
        defer scale.deinit();

        for (scale.data) |v| {
            if (v < 1e-30 or !std.math.isFinite(v)) return error.NumericFailure;
        }

        if (scale.data.len != y1.data.len) return error.ShapeMismatch;
        try y1.div(&scale);

        if (countNonFinite(y1.data) > 0) return error.NumericFailure;
    }

    pub fn backward(
        self: *RSFLayer,
        y1: *const Tensor,
        y2: *const Tensor,
        dy1_in: *const Tensor,
        dy2_in: *const Tensor,
        x1_out: *Tensor,
        x2_out: *Tensor,
        dx1_out: *Tensor,
        dx2_out: *Tensor,
    ) !void {
        const batch_size = try self.validatePair(y1, y2);
        _ = try self.validatePair(dy1_in, dy2_in);

        try validateTensor2D(x1_out);
        try validateTensor2D(x2_out);
        try validateTensor2D(dx1_out);
        try validateTensor2D(dx2_out);

        const bd = try checkedMul(batch_size, self.dim);

        if (x1_out.shape.dims[0] != batch_size or x2_out.shape.dims[0] != batch_size) return error.ShapeMismatch;
        if (dx1_out.shape.dims[0] != batch_size or dx2_out.shape.dims[0] != batch_size) return error.ShapeMismatch;
        if (x1_out.shape.dims[1] != self.dim or x2_out.shape.dims[1] != self.dim) return error.ShapeMismatch;
        if (dx1_out.shape.dims[1] != self.dim or dx2_out.shape.dims[1] != self.dim) return error.ShapeMismatch;
        if (x1_out.data.len != bd or x2_out.data.len != bd) return error.DataLengthMismatch;
        if (dx1_out.data.len != bd or dx2_out.data.len != bd) return error.DataLengthMismatch;

        try self.ensureGradients();

        var dy1 = try dy1_in.copy(self.allocator);
        defer dy1.deinit();

        var dy2 = try dy2_in.copy(self.allocator);
        defer dy2.deinit();

        if (countNonFinite(dy1.data) > 0) return error.NumericFailure;
        if (countNonFinite(dy2.data) > 0) return error.NumericFailure;

        var trans = try self.computeTranslation(y1, batch_size);
        defer trans.deinit();

        var x2 = try y2.copy(self.allocator);
        defer x2.deinit();
        try x2.sub(&trans);

        if (countNonFinite(x2.data) > 0) return error.NumericFailure;

        var dy2_t = try dy2.transpose(&.{ 1, 0 });
        defer dy2_t.deinit();

        var y1_copy_for_matmul = try y1.copy(self.allocator);
        defer y1_copy_for_matmul.deinit();
        var dt = try dy2_t.matmul(&y1_copy_for_matmul, self.allocator);
        defer dt.deinit();

        const grad_scale: f32 = if (self.grad_mean) blk: {
            const bs_f = @as(f32, @floatFromInt(batch_size));
            if (bs_f == 0.0) break :blk 1.0;
            const gs = 1.0 / bs_f;
            if (!std.math.isFinite(gs)) break :blk 1.0;
            break :blk gs;
        } else 1.0;

        if (self.t_weight_grad) |*twg| {
            if (dt.data.len != twg.data.len) return error.DataLengthMismatch;
            var i: usize = 0;
            while (i < dt.data.len) : (i += 1) {
                const val = dt.data[i] * grad_scale;
                if (std.math.isFinite(val)) {
                    twg.data[i] += val;
                }
            }
        }

        if (self.t_bias_grad) |*tbg| {
            if (tbg.data.len != self.dim) return error.DataLengthMismatch;
            var b: usize = 0;
            var offset: usize = 0;
            while (b < batch_size) : (b += 1) {
                var d: usize = 0;
                while (d < self.dim) : (d += 1) {
                    const val = dy2.data[offset + d] * grad_scale;
                    if (std.math.isFinite(val)) {
                        tbg.data[d] += val;
                    }
                }
                offset += self.dim;
            }
        }

        var t_weight_copy = try self.t_weight.copy(self.allocator);
        defer t_weight_copy.deinit();
        var t_weight_t = try t_weight_copy.transpose(&.{ 1, 0 });
        defer t_weight_t.deinit();

        var grad_from_t_t = try t_weight_t.matmul(&dy2_t, self.allocator);
        defer grad_from_t_t.deinit();

        var grad_from_t = try grad_from_t_t.transpose(&.{ 1, 0 });
        defer grad_from_t.deinit();

        if (grad_from_t.data.len != dy1.data.len) return error.DataLengthMismatch;
        try dy1.add(&grad_from_t);
        try sanitizeSlice(dy1.data);

        var x2_t = try x2.transpose(&.{ 1, 0 });
        defer x2_t.deinit();

        var s_weight_copy = try self.s_weight.copy(self.allocator);
        defer s_weight_copy.deinit();
        var s_pre_t = try s_weight_copy.matmul(&x2_t, self.allocator);
        defer s_pre_t.deinit();

        var s_pre = try s_pre_t.transpose(&.{ 1, 0 });
        defer s_pre.deinit();

        try addBiasToSlice(s_pre.data, self.s_bias.data, batch_size, self.dim);

        var exp_s = try s_pre.copy(self.allocator);
        defer exp_s.deinit();
        try exp_s.clip(self.clip_min, self.clip_max);
        try exp_s.exp();

        for (exp_s.data) |v| {
            if (v == 0.0 or !std.math.isFinite(v)) return error.NumericFailure;
        }

        var x1 = try y1.copy(self.allocator);
        defer x1.deinit();
        try x1.div(&exp_s);

        if (countNonFinite(x1.data) > 0) return error.NumericFailure;

        @memcpy(x1_out.data, x1.data);
        @memcpy(x2_out.data, x2.data);

        if (exp_s.data.len != dy1.data.len) return error.DataLengthMismatch;
        var i: usize = 0;
        while (i < bd) : (i += 1) {
            dx1_out.data[i] = dy1.data[i] * exp_s.data[i];
        }

        var ds = try Tensor.init(self.allocator, &.{ batch_size, self.dim });
        defer ds.deinit();
        i = 0;
        while (i < bd) : (i += 1) {
            const s_val = s_pre.data[i];
            if (!std.math.isFinite(s_val) or s_val < self.clip_min or s_val > self.clip_max) {
                ds.data[i] = 0.0;
                continue;
            }
            const dscale_val = dy1.data[i] * x1.data[i];
            const ds_val = dscale_val * exp_s.data[i];
            if (!std.math.isFinite(ds_val)) {
                ds.data[i] = 0.0;
            } else {
                ds.data[i] = ds_val;
            }
        }

        var ds_t = try ds.transpose(&.{ 1, 0 });
        defer ds_t.deinit();

        var ds_w = try ds_t.matmul(&x2, self.allocator);
        defer ds_w.deinit();

        if (self.s_weight_grad) |*swg| {
            if (ds_w.data.len != swg.data.len) return error.DataLengthMismatch;
            i = 0;
            while (i < ds_w.data.len) : (i += 1) {
                const val = ds_w.data[i] * grad_scale;
                if (std.math.isFinite(val)) {
                    swg.data[i] += val;
                }
            }
        }

        if (self.s_bias_grad) |*sbg| {
            if (sbg.data.len != self.dim) return error.DataLengthMismatch;
            var b: usize = 0;
            var offset: usize = 0;
            while (b < batch_size) : (b += 1) {
                var d: usize = 0;
                while (d < self.dim) : (d += 1) {
                    const val = ds.data[offset + d] * grad_scale;
                    if (std.math.isFinite(val)) {
                        sbg.data[d] += val;
                    }
                }
                offset += self.dim;
            }
        }

        var s_weight_copy2 = try self.s_weight.copy(self.allocator);
        defer s_weight_copy2.deinit();
        var s_weight_t = try s_weight_copy2.transpose(&.{ 1, 0 });
        defer s_weight_t.deinit();

        var grad_from_s_t = try s_weight_t.matmul(&ds_t, self.allocator);
        defer grad_from_s_t.deinit();

        var grad_from_s = try grad_from_s_t.transpose(&.{ 1, 0 });
        defer grad_from_s.deinit();

        if (grad_from_s.data.len != dy2.data.len) return error.DataLengthMismatch;
        i = 0;
        while (i < bd) : (i += 1) {
            dx2_out.data[i] = dy2.data[i] + grad_from_s.data[i];
        }

        if (countNonFinite(dx1_out.data) > 0) return error.NumericFailure;
        if (countNonFinite(dx2_out.data) > 0) return error.NumericFailure;
    }
};

pub const RSFConfig = struct {
    clip_min: f32 = -5.0,
    clip_max: f32 = 5.0,
    grad_mean: bool = true,
    max_dim: usize = 1 << 20,
    max_layers: usize = 1 << 20,
};

const SAVE_VERSION: u32 = 3;

const ControlBlock = struct {
    freed: std.atomic.Atomic(u8),
    allocator: Allocator,
    dim: usize,
    num_layers: usize,
    layers: []RSFLayer,
    cfg: RSFConfig,
    gpu_accel: ?accel.RSFAccelerator,
    gpu_available: std.atomic.Atomic(u8),
    gpu_weight_version: u64,
    cpu_weight_version: u64,
    mutex: Thread.Mutex,
    f16_buf: ?[]f16,
};

pub const RSF = struct {
    ctrl: ?*ControlBlock,

    pub fn init(allocator: Allocator, dim: usize, num_layers: usize) !RSF {
        return initWithConfig(allocator, dim, num_layers, .{});
    }

    pub fn initWithConfig(allocator: Allocator, dim: usize, num_layers: usize, cfg: RSFConfig) !RSF {
        if (dim == 0) return error.InvalidDimension;
        if (num_layers == 0) return error.InvalidLayerCount;
        if (dim > cfg.max_dim or num_layers > cfg.max_layers) return error.TooLarge;
        if (!std.math.isFinite(cfg.clip_min) or !std.math.isFinite(cfg.clip_max)) return error.NonFinite;
        if (!(cfg.clip_min < cfg.clip_max)) return error.InvalidConfig;

        const dim_sq = try checkedMul(dim, dim);
        _ = try checkedMul(dim, 2);

        var ctrl = try allocator.create(ControlBlock);
        errdefer allocator.destroy(ctrl);

        ctrl.* = .{
            .freed = std.atomic.Atomic(u8).init(0),
            .allocator = allocator,
            .dim = dim,
            .num_layers = num_layers,
            .layers = try allocator.alloc(RSFLayer, num_layers),
            .cfg = cfg,
            .gpu_accel = null,
            .gpu_available = std.atomic.Atomic(u8).init(0),
            .gpu_weight_version = 0,
            .cpu_weight_version = 1,
            .mutex = Thread.Mutex{},
            .f16_buf = null,
        };
        errdefer allocator.free(ctrl.layers);

        var initialized_count: usize = 0;
        errdefer {
            var j: usize = 0;
            while (j < initialized_count) : (j += 1) {
                ctrl.layers[j].deinit();
            }
        }

        var l: usize = 0;
        while (l < num_layers) : (l += 1) {
            const seed_base = try checkedMulU64(@as(u64, @intCast(l)), 10007);
            const layer_cfg = RSFLayerConfig{
                .clip_min = cfg.clip_min,
                .clip_max = cfg.clip_max,
                .seed_offset = seed_base,
                .grad_mean = cfg.grad_mean,
            };
            ctrl.layers[l] = try RSFLayer.initWithConfig(allocator, dim, layer_cfg);
            initialized_count += 1;
        }

        if (accel.RSFAccelerator.init(dim)) |gpu| {
            ctrl.gpu_accel = gpu;
            ctrl.gpu_available.store(1, .SeqCst);
            ctrl.gpu_weight_version = 0;
            ctrl.f16_buf = allocator.alloc(f16, dim_sq) catch null;
        } else |_| {}

        var rsf = RSF{ .ctrl = ctrl };
        rsf.syncAllLayersGPU(ctrl) catch {
            ctrl.gpu_available.store(0, .SeqCst);
            if (ctrl.gpu_accel) |*ga| {
                ga.deinit();
                ctrl.gpu_accel = null;
            }
            if (ctrl.f16_buf) |buf| {
                allocator.free(buf);
                ctrl.f16_buf = null;
            }
        };

        return rsf;
    }

    pub fn deinit(self: *RSF) void {
        const c = self.ctrl orelse return;
        self.ctrl = null;

        c.mutex.lock();

        if (c.freed.swap(1, .SeqCst) != 0) {
            c.mutex.unlock();
            return;
        }

        if (c.gpu_accel) |*ga| {
            ga.deinit();
            c.gpu_accel = null;
        }
        c.gpu_available.store(0, .SeqCst);

        if (c.f16_buf) |buf| {
            c.allocator.free(buf);
            c.f16_buf = null;
        }

        var i: usize = 0;
        while (i < c.num_layers) : (i += 1) {
            c.layers[i].deinit();
        }

        const alloc = c.allocator;
        const layers = c.layers;
        const ctrl_ptr = c;

        c.mutex.unlock();

        alloc.free(layers);
        alloc.destroy(ctrl_ptr);
    }

    fn withCtrlLocked(self: *const RSF) !*ControlBlock {
        const c = self.ctrl orelse return error.NotInitialized;
        c.mutex.lock();
        if (c.freed.load(.SeqCst) != 0) {
            c.mutex.unlock();
            return error.NotInitialized;
        }
        return c;
    }

    fn splitInto(ctrl: *const ControlBlock, x: *const Tensor, x1: *Tensor, x2: *Tensor) !usize {
        try validateTensor2D(x);
        const dim2 = try checkedMul(ctrl.dim, 2);
        if (x.shape.dims[1] != dim2) return error.ShapeMismatch;
        const batch_size = x.shape.dims[0];
        if (batch_size == 0) return error.InvalidBatchSize;

        try validateTensor2D(x1);
        try validateTensor2D(x2);
        if (x1.shape.dims[0] != batch_size or x2.shape.dims[0] != batch_size) return error.ShapeMismatch;
        if (x1.shape.dims[1] != ctrl.dim or x2.shape.dims[1] != ctrl.dim) return error.ShapeMismatch;

        const bd = try checkedMul(batch_size, ctrl.dim);
        if (x1.data.len != bd or x2.data.len != bd) return error.DataLengthMismatch;

        const bd2 = try checkedMul(batch_size, dim2);
        if (x.data.len != bd2) return error.DataLengthMismatch;

        var b: usize = 0;
        while (b < batch_size) : (b += 1) {
            const src_offset = b * dim2;
            const dst_offset = b * ctrl.dim;
            @memcpy(x1.data[dst_offset .. dst_offset + ctrl.dim], x.data[src_offset .. src_offset + ctrl.dim]);
            @memcpy(x2.data[dst_offset .. dst_offset + ctrl.dim], x.data[src_offset + ctrl.dim .. src_offset + dim2]);
        }

        return batch_size;
    }

    fn mergeFrom(ctrl: *const ControlBlock, x1: *const Tensor, x2: *const Tensor, out: *Tensor) !void {
        try validateTensor2D(out);
        try validateTensor2D(x1);
        try validateTensor2D(x2);
        if (x1.shape.dims[0] != x2.shape.dims[0]) return error.ShapeMismatch;
        if (x1.shape.dims[1] != ctrl.dim or x2.shape.dims[1] != ctrl.dim) return error.ShapeMismatch;

        const dim2 = try checkedMul(ctrl.dim, 2);
        if (out.shape.dims[0] != x1.shape.dims[0] or out.shape.dims[1] != dim2) return error.ShapeMismatch;

        const batch_size = x1.shape.dims[0];
        const bd = try checkedMul(batch_size, ctrl.dim);
        if (x1.data.len != bd or x2.data.len != bd) return error.DataLengthMismatch;

        const bd2 = try checkedMul(batch_size, dim2);
        if (out.data.len != bd2) return error.DataLengthMismatch;

        var b: usize = 0;
        while (b < batch_size) : (b += 1) {
            const src_offset = b * ctrl.dim;
            const dst_offset = b * dim2;
            @memcpy(out.data[dst_offset .. dst_offset + ctrl.dim], x1.data[src_offset .. src_offset + ctrl.dim]);
            @memcpy(out.data[dst_offset + ctrl.dim .. dst_offset + dim2], x2.data[src_offset .. src_offset + ctrl.dim]);
        }
    }

    pub fn isGPUAvailable(self: *const RSF) bool {
        const c = self.ctrl orelse return false;
        c.mutex.lock();
        defer c.mutex.unlock();
        if (c.freed.load(.SeqCst) != 0) return false;
        return c.gpu_available.load(.SeqCst) != 0;
    }

    fn syncLayerGPU(ctrl: *ControlBlock, layer_idx: usize) !void {
        if (ctrl.gpu_available.load(.SeqCst) == 0) return;
        if (ctrl.gpu_accel == null) return;
        var ga = &(ctrl.gpu_accel.?);
        const dim = ctrl.dim;
        const dim_sq = try checkedMul(dim, dim);
        if (layer_idx >= ctrl.num_layers) return error.InvalidLayerCount;
        const layer = &ctrl.layers[layer_idx];
        if (layer.s_weight.data.len != dim_sq) return error.DataLengthMismatch;
        if (layer.t_weight.data.len != dim_sq) return error.DataLengthMismatch;

        const f16_buf = ctrl.f16_buf orelse return error.GPUSyncFailed;
        if (f16_buf.len < dim_sq) return error.DataLengthMismatch;

        var fi: usize = 0;
        while (fi < dim_sq) : (fi += 1) {
            f16_buf[fi] = @floatCast(layer.s_weight.data[fi]);
        }
        try ga.setWeightsS(f16_buf, dim, dim);
        fi = 0;
        while (fi < dim_sq) : (fi += 1) {
            f16_buf[fi] = @floatCast(layer.t_weight.data[fi]);
        }
        try ga.setWeightsT(f16_buf, dim, dim);
    }

    fn syncAllLayersGPU(self: *RSF, ctrl: *ControlBlock) !void {
        _ = self;
        if (ctrl.gpu_available.load(.SeqCst) == 0) return;
        var l: usize = 0;
        while (l < ctrl.num_layers) : (l += 1) {
            syncLayerGPU(ctrl, l) catch {
                ctrl.gpu_available.store(0, .SeqCst);
                if (ctrl.gpu_accel) |*ga| {
                    ga.deinit();
                    ctrl.gpu_accel = null;
                }
                return error.GPUSyncFailed;
            };
        }
        ctrl.gpu_weight_version = ctrl.cpu_weight_version;
    }

    pub fn syncWeightsToGPU(self: *RSF) !void {
        const c = try self.withCtrlLocked();
        defer c.mutex.unlock();
        try self.syncAllLayersGPU(c);
    }

    pub fn zeroGradients(self: *RSF) !void {
        const c = try self.withCtrlLocked();
        defer c.mutex.unlock();
        var i: usize = 0;
        while (i < c.num_layers) : (i += 1) {
            c.layers[i].zeroGradients();
        }
    }

    pub fn forwardCPU(self: *RSF, x: *Tensor) !void {
        const c = try self.withCtrlLocked();
        defer c.mutex.unlock();
        try forwardOnCPU(c, x);
    }

    fn forwardOnCPU(ctrl: *ControlBlock, x: *Tensor) !void {
        try validateTensor2D(x);
        const dim2 = try checkedMul(ctrl.dim, 2);
        if (x.shape.dims[1] != dim2) return error.ShapeMismatch;

        const batch_size = x.shape.dims[0];
        if (batch_size == 0) return error.InvalidBatchSize;

        _ = try checkedMul(batch_size, ctrl.dim);

        var shape_half = [_]usize{ batch_size, ctrl.dim };
        var x1 = try Tensor.init(ctrl.allocator, &shape_half);
        defer x1.deinit();
        var x2 = try Tensor.init(ctrl.allocator, &shape_half);
        defer x2.deinit();

        _ = try splitInto(ctrl, x, &x1, &x2);

        var i: usize = 0;
        while (i < ctrl.num_layers) : (i += 1) {
            try ctrl.layers[i].forward(&x1, &x2);
        }

        try mergeFrom(ctrl, &x1, &x2, x);
    }

    pub fn forward(self: *RSF, x: *Tensor) !void {
        const c = try self.withCtrlLocked();
        defer c.mutex.unlock();

        try validateTensor2D(x);
        const dim2 = try checkedMul(c.dim, 2);
        if (x.shape.dims[1] != dim2) return error.ShapeMismatch;

        const batch_size = x.shape.dims[0];
        if (batch_size == 0) return error.InvalidBatchSize;

        if (c.gpu_available.load(.SeqCst) != 0 and c.gpu_weight_version == c.cpu_weight_version) {
            if (c.gpu_accel) |*ga| {
                if (ga.forwardFromTensor(x, c.allocator)) |result| {
                    var gpu_result = result;
                    defer gpu_result.deinit();
                    if (gpu_result.data.len == x.data.len and gpu_result.shape.dims.len == x.shape.dims.len) {
                        var shape_match = true;
                        var si: usize = 0;
                        while (si < x.shape.dims.len) : (si += 1) {
                            if (gpu_result.shape.dims[si] != x.shape.dims[si]) {
                                shape_match = false;
                                break;
                            }
                        }
                        if (shape_match) {
                            @memcpy(x.data, gpu_result.data);
                            return;
                        }
                    }
                } else |_| {}
            }
        }

        try forwardOnCPU(c, x);
    }

    pub fn inverse(self: *RSF, y: *Tensor) !void {
        const c = try self.withCtrlLocked();
        defer c.mutex.unlock();

        try validateTensor2D(y);
        const dim2 = try checkedMul(c.dim, 2);
        if (y.shape.dims[1] != dim2) return error.ShapeMismatch;

        const batch_size = y.shape.dims[0];
        if (batch_size == 0) return error.InvalidBatchSize;

        var shape_half = [_]usize{ batch_size, c.dim };
        var y1 = try Tensor.init(c.allocator, &shape_half);
        defer y1.deinit();
        var y2 = try Tensor.init(c.allocator, &shape_half);
        defer y2.deinit();

        _ = try splitInto(c, y, &y1, &y2);

        var idx = c.num_layers;
        while (idx > 0) : (idx -= 1) {
            try c.layers[idx - 1].inverse(&y1, &y2);
        }

        try mergeFrom(c, &y1, &y2, y);
    }

    pub fn backward(self: *RSF, grad_output: *const Tensor, input: *const Tensor, grad_input_out: *Tensor) !void {
        const c = try self.withCtrlLocked();
        defer c.mutex.unlock();

        try validateTensor2D(grad_output);
        try validateTensor2D(input);
        try validateTensor2D(grad_input_out);

        const dim2 = try checkedMul(c.dim, 2);
        if (input.shape.dims[1] != dim2) return error.ShapeMismatch;
        if (grad_output.shape.dims[0] != input.shape.dims[0] or grad_output.shape.dims[1] != input.shape.dims[1]) return error.ShapeMismatch;
        if (grad_input_out.shape.dims[0] != input.shape.dims[0] or grad_input_out.shape.dims[1] != input.shape.dims[1]) return error.ShapeMismatch;
        if (grad_input_out.data.len != input.data.len) return error.DataLengthMismatch;

        const batch_size = input.shape.dims[0];
        if (batch_size == 0) return error.InvalidBatchSize;

        var shape_half = [_]usize{ batch_size, c.dim };

        var x = try input.copy(c.allocator);
        defer x.deinit();
        try forwardOnCPU(c, &x);

        var y1 = try Tensor.init(c.allocator, &shape_half);
        defer y1.deinit();
        var y2 = try Tensor.init(c.allocator, &shape_half);
        defer y2.deinit();
        _ = try splitInto(c, &x, &y1, &y2);

        var dy = try grad_output.copy(c.allocator);
        defer dy.deinit();

        var dy1 = try Tensor.init(c.allocator, &shape_half);
        defer dy1.deinit();
        var dy2 = try Tensor.init(c.allocator, &shape_half);
        defer dy2.deinit();
        _ = try splitInto(c, &dy, &dy1, &dy2);

        var cur_y1 = try y1.copy(c.allocator);
        defer cur_y1.deinit();
        var cur_y2 = try y2.copy(c.allocator);
        defer cur_y2.deinit();
        var cur_dy1 = try dy1.copy(c.allocator);
        defer cur_dy1.deinit();
        var cur_dy2 = try dy2.copy(c.allocator);
        defer cur_dy2.deinit();

        var x1_prev = try Tensor.init(c.allocator, &shape_half);
        defer x1_prev.deinit();
        var x2_prev = try Tensor.init(c.allocator, &shape_half);
        defer x2_prev.deinit();
        var dx1_prev = try Tensor.init(c.allocator, &shape_half);
        defer dx1_prev.deinit();
        var dx2_prev = try Tensor.init(c.allocator, &shape_half);
        defer dx2_prev.deinit();

        var saved_grads = try c.allocator.alloc([4]?[]f32, c.num_layers);
        defer c.allocator.free(saved_grads);
        for (saved_grads) |*sg| {
            sg[0] = null;
            sg[1] = null;
            sg[2] = null;
            sg[3] = null;
        }
        defer {
            for (saved_grads) |*sg| {
                if (sg[0]) |s| c.allocator.free(s);
                if (sg[1]) |s| c.allocator.free(s);
                if (sg[2]) |s| c.allocator.free(s);
                if (sg[3]) |s| c.allocator.free(s);
            }
        }

        var l: usize = 0;
        while (l < c.num_layers) : (l += 1) {
            var layer = &c.layers[l];
            try layer.ensureGradients();
            if (layer.s_weight_grad) |g| {
                saved_grads[l][0] = try c.allocator.dupe(f32, g.data);
            }
            if (layer.t_weight_grad) |g| {
                saved_grads[l][1] = try c.allocator.dupe(f32, g.data);
            }
            if (layer.s_bias_grad) |g| {
                saved_grads[l][2] = try c.allocator.dupe(f32, g.data);
            }
            if (layer.t_bias_grad) |g| {
                saved_grads[l][3] = try c.allocator.dupe(f32, g.data);
            }
        }

        var idx = c.num_layers;
        var backward_ok = true;
        while (idx > 0) : (idx -= 1) {
            c.layers[idx - 1].backward(&cur_y1, &cur_y2, &cur_dy1, &cur_dy2, &x1_prev, &x2_prev, &dx1_prev, &dx2_prev) catch {
                backward_ok = false;
                break;
            };

            const tmp_y1_data = cur_y1.data;
            cur_y1.data = x1_prev.data;
            x1_prev.data = tmp_y1_data;

            const tmp_y2_data = cur_y2.data;
            cur_y2.data = x2_prev.data;
            x2_prev.data = tmp_y2_data;

            const tmp_dy1_data = cur_dy1.data;
            cur_dy1.data = dx1_prev.data;
            dx1_prev.data = tmp_dy1_data;

            const tmp_dy2_data = cur_dy2.data;
            cur_dy2.data = dx2_prev.data;
            dx2_prev.data = tmp_dy2_data;
        }

        if (!backward_ok) {
            l = 0;
            while (l < c.num_layers) : (l += 1) {
                var layer = &c.layers[l];
                if (saved_grads[l][0]) |s| {
                    if (layer.s_weight_grad) |*g| @memcpy(g.data, s);
                }
                if (saved_grads[l][1]) |s| {
                    if (layer.t_weight_grad) |*g| @memcpy(g.data, s);
                }
                if (saved_grads[l][2]) |s| {
                    if (layer.s_bias_grad) |*g| @memcpy(g.data, s);
                }
                if (saved_grads[l][3]) |s| {
                    if (layer.t_bias_grad) |*g| @memcpy(g.data, s);
                }
            }
            return error.NumericFailure;
        }

        try mergeFrom(c, &cur_dy1, &cur_dy2, grad_input_out);
    }

    pub fn save(self: *const RSF, path: []const u8) !void {
        const c = try self.withCtrlLocked();

        const snap_num_layers = c.num_layers;
        const snap_dim = c.dim;
        const snap_cfg = c.cfg;
        const snap_alloc = c.allocator;

        const layer_data = try snap_alloc.alloc(LayerSnapshot, snap_num_layers);
        defer {
            for (layer_data) |*ld| {
                snap_alloc.free(ld.s_w);
                snap_alloc.free(ld.t_w);
                snap_alloc.free(ld.s_b);
                snap_alloc.free(ld.t_b);
            }
            snap_alloc.free(layer_data);
        }

        var i: usize = 0;
        while (i < snap_num_layers) : (i += 1) {
            const layer = &c.layers[i];
            layer_data[i] = LayerSnapshot{
                .s_w = try snap_alloc.dupe(f32, layer.s_weight.data),
                .t_w = try snap_alloc.dupe(f32, layer.t_weight.data),
                .s_b = try snap_alloc.dupe(f32, layer.s_bias.data),
                .t_b = try snap_alloc.dupe(f32, layer.t_bias.data),
                .clip_min = layer.clip_min,
                .clip_max = layer.clip_max,
                .grad_mean = layer.grad_mean,
                .s_w_shape = .{ layer.s_weight.shape.dims[0], layer.s_weight.shape.dims[1] },
                .t_w_shape = .{ layer.t_weight.shape.dims[0], layer.t_weight.shape.dims[1] },
                .s_b_shape = .{ layer.s_bias.shape.dims[0], layer.s_bias.shape.dims[1] },
                .t_b_shape = .{ layer.t_bias.shape.dims[0], layer.t_bias.shape.dims[1] },
            };
        }

        c.mutex.unlock();

        var tmp_name_buf: [512]u8 = undefined;
        const ts = std.time.milliTimestamp();
        const abs_ts: u64 = if (ts < 0) 0 else @intCast(ts);
        const tmp_name = try std.fmt.bufPrint(&tmp_name_buf, "{s}.{d}.tmp", .{ path, abs_ts });

        var file = try std.fs.cwd().createFile(tmp_name, .{ .mode = 0o600 });
        errdefer {
            file.close();
            std.fs.cwd().deleteFile(tmp_name) catch {};
        }

        var buffered = std.io.bufferedWriter(file.writer());
        const w = buffered.writer();

        try w.writeAll("RSF0");
        try w.writeInt(u32, SAVE_VERSION, .Little);
        try w.writeInt(u64, @intCast(snap_num_layers), .Little);
        try w.writeInt(u64, @intCast(snap_dim), .Little);

        var hasher = std.hash.Crc32.init();

        const clip_min_bits = @as(u32, @bitCast(snap_cfg.clip_min));
        const clip_max_bits = @as(u32, @bitCast(snap_cfg.clip_max));
        try w.writeInt(u32, clip_min_bits, .Little);
        try w.writeInt(u32, clip_max_bits, .Little);
        const gm_byte: u8 = if (snap_cfg.grad_mean) 1 else 0;
        try w.writeByte(gm_byte);
        try w.writeInt(u64, @intCast(snap_cfg.max_dim), .Little);
        try w.writeInt(u64, @intCast(snap_cfg.max_layers), .Little);

        hasher.update(std.mem.asBytes(&clip_min_bits));
        hasher.update(std.mem.asBytes(&clip_max_bits));
        hasher.update(&.{gm_byte});

        i = 0;
        while (i < snap_num_layers) : (i += 1) {
            const ld = &layer_data[i];
            const cm_bits = @as(u32, @bitCast(ld.clip_min));
            const cx_bits = @as(u32, @bitCast(ld.clip_max));
            try w.writeInt(u32, cm_bits, .Little);
            try w.writeInt(u32, cx_bits, .Little);
            const lgm: u8 = if (ld.grad_mean) 1 else 0;
            try w.writeByte(lgm);

            hasher.update(std.mem.asBytes(&cm_bits));
            hasher.update(std.mem.asBytes(&cx_bits));
            hasher.update(&.{lgm});

            try writeTensorData(w, &hasher, ld.s_w, &ld.s_w_shape);
            try writeTensorData(w, &hasher, ld.t_w, &ld.t_w_shape);
            try writeTensorData(w, &hasher, ld.s_b, &ld.s_b_shape);
            try writeTensorData(w, &hasher, ld.t_b, &ld.t_b_shape);
        }

        try w.writeInt(u32, hasher.final(), .Little);

        try buffered.flush();
        try file.sync();
        file.close();

        try std.fs.cwd().rename(tmp_name, path);
    }

    pub fn load(allocator: Allocator, path: []const u8) !RSF {
        return loadWithConfig(allocator, path, null);
    }

    pub fn loadWithConfig(allocator: Allocator, path: []const u8, policy: ?RSFConfig) !RSF {
        const file = try std.fs.cwd().openFile(path, .{ .mode = .read_only });
        defer file.close();

        var r = file.reader();

        var magic: [4]u8 = undefined;
        try r.readNoEof(&magic);
        if (!std.mem.eql(u8, &magic, "RSF0")) return error.BadFileFormat;

        const version = try r.readInt(u32, .Little);
        if (version != 1 and version != 2 and version != SAVE_VERSION) return error.UnsupportedVersion;

        const num_layers_u64 = try r.readInt(u64, .Little);
        const dim_u64 = try r.readInt(u64, .Little);
        if (num_layers_u64 == 0) return error.InvalidLayerCount;
        if (dim_u64 == 0) return error.InvalidDimension;

        const effective_max_dim: u64 = if (policy) |p| @intCast(p.max_dim) else (1 << 20);
        const effective_max_layers: u64 = if (policy) |p| @intCast(p.max_layers) else (1 << 20);

        if (num_layers_u64 > effective_max_layers or dim_u64 > effective_max_dim) return error.TooLarge;

        const num_layers: usize = @intCast(num_layers_u64);
        const dim: usize = @intCast(dim_u64);

        _ = try checkedMul(dim, dim);
        _ = try checkedMul(dim, 2);

        const clip_min: f32 = @bitCast(try r.readInt(u32, .Little));
        const clip_max: f32 = @bitCast(try r.readInt(u32, .Little));
        const grad_mean = (try r.readByte()) != 0;

        if (!std.math.isFinite(clip_min) or !std.math.isFinite(clip_max) or !(clip_min < clip_max)) return error.InvalidConfig;

        var load_max_dim: usize = if (policy) |p| p.max_dim else (1 << 20);
        var load_max_layers: usize = if (policy) |p| p.max_layers else (1 << 20);

        if (version >= 2) {
            const saved_max_dim = try r.readInt(u64, .Little);
            const saved_max_layers = try r.readInt(u64, .Little);
            if (policy == null) {
                load_max_dim = @max(load_max_dim, @as(usize, @intCast(@min(saved_max_dim, @as(u64, std.math.maxInt(usize))))));
                load_max_layers = @max(load_max_layers, @as(usize, @intCast(@min(saved_max_layers, @as(u64, std.math.maxInt(usize))))));
            }
        }

        var rsf = try RSF.initWithConfig(allocator, dim, num_layers, .{
            .clip_min = clip_min,
            .clip_max = clip_max,
            .grad_mean = grad_mean,
            .max_dim = load_max_dim,
            .max_layers = load_max_layers,
        });
        errdefer rsf.deinit();

        const c = rsf.ctrl orelse return error.NotInitialized;

        var hasher = std.hash.Crc32.init();
        const clip_min_bits = @as(u32, @bitCast(clip_min));
        const clip_max_bits = @as(u32, @bitCast(clip_max));
        hasher.update(std.mem.asBytes(&clip_min_bits));
        hasher.update(std.mem.asBytes(&clip_max_bits));
        hasher.update(&.{if (grad_mean) @as(u8, 1) else @as(u8, 0)});

        var i: usize = 0;
        while (i < c.num_layers) : (i += 1) {
            const layer_clip_min: f32 = @bitCast(try r.readInt(u32, .Little));
            const layer_clip_max: f32 = @bitCast(try r.readInt(u32, .Little));
            const layer_grad_mean = (try r.readByte()) != 0;
            if (!std.math.isFinite(layer_clip_min) or !std.math.isFinite(layer_clip_max) or !(layer_clip_min < layer_clip_max)) return error.InvalidConfig;
            if (layer_clip_max > 20.0 or layer_clip_min < -20.0) return error.InvalidConfig;

            const lcm_bits = @as(u32, @bitCast(layer_clip_min));
            const lcx_bits = @as(u32, @bitCast(layer_clip_max));
            hasher.update(std.mem.asBytes(&lcm_bits));
            hasher.update(std.mem.asBytes(&lcx_bits));
            const lgm_byte: u8 = if (layer_grad_mean) 1 else 0;
            hasher.update(&.{lgm_byte});

            var s_w_new = try Tensor.load(allocator, r);
            errdefer s_w_new.deinit();
            var t_w_new = try Tensor.load(allocator, r);
            errdefer t_w_new.deinit();
            var s_b_new = try Tensor.load(allocator, r);
            errdefer s_b_new.deinit();
            var t_b_new = try Tensor.load(allocator, r);

            if (s_w_new.shape.dims.len != 2 or s_w_new.shape.dims[0] != dim or s_w_new.shape.dims[1] != dim) {
                t_b_new.deinit();
                return error.ShapeMismatch;
            }
            if (t_w_new.shape.dims.len != 2 or t_w_new.shape.dims[0] != dim or t_w_new.shape.dims[1] != dim) {
                t_b_new.deinit();
                return error.ShapeMismatch;
            }
            if (s_b_new.shape.dims.len != 2 or s_b_new.shape.dims[0] != 1 or s_b_new.shape.dims[1] != dim) {
                t_b_new.deinit();
                return error.ShapeMismatch;
            }
            if (t_b_new.shape.dims.len != 2 or t_b_new.shape.dims[0] != 1 or t_b_new.shape.dims[1] != dim) {
                t_b_new.deinit();
                return error.ShapeMismatch;
            }

            const dim_sq = try checkedMul(dim, dim);
            if (s_w_new.data.len != dim_sq or t_w_new.data.len != dim_sq) {
                t_b_new.deinit();
                return error.DataLengthMismatch;
            }
            if (s_b_new.data.len != dim or t_b_new.data.len != dim) {
                t_b_new.deinit();
                return error.DataLengthMismatch;
            }

            hashTensorData(&hasher, s_w_new.data);
            hashTensorData(&hasher, t_w_new.data);
            hashTensorData(&hasher, s_b_new.data);
            hashTensorData(&hasher, t_b_new.data);

            var layer = &c.layers[i];

            layer.s_weight.deinit();
            layer.t_weight.deinit();
            layer.s_bias.deinit();
            layer.t_bias.deinit();

            layer.s_weight = s_w_new;
            layer.t_weight = t_w_new;
            layer.s_bias = s_b_new;
            layer.t_bias = t_b_new;

            layer.clip_min = layer_clip_min;
            layer.clip_max = layer_clip_max;
            layer.grad_mean = layer_grad_mean;

            if (layer.s_weight_grad) |*g| {
                for (g.data) |*v| v.* = 0.0;
            }
            if (layer.t_weight_grad) |*g| {
                for (g.data) |*v| v.* = 0.0;
            }
            if (layer.s_bias_grad) |*g| {
                for (g.data) |*v| v.* = 0.0;
            }
            if (layer.t_bias_grad) |*g| {
                for (g.data) |*v| v.* = 0.0;
            }
        }

        if (version >= 2) {
            const stored_checksum = try r.readInt(u32, .Little);
            if (version >= SAVE_VERSION) {
                if (stored_checksum != hasher.final()) return error.ChecksumMismatch;
            }
        }

        var eof_buf: [1]u8 = undefined;
        const eof_read = try r.read(&eof_buf);
        if (eof_read != 0) return error.TrailingData;

        c.cfg.clip_min = clip_min;
        c.cfg.clip_max = clip_max;
        c.cfg.grad_mean = grad_mean;

        c.cpu_weight_version += 1;
        rsf.syncAllLayersGPU(c) catch |e| {
            _ = e;
            c.gpu_available.store(0, .SeqCst);
            if (c.gpu_accel) |*ga| {
                ga.deinit();
                c.gpu_accel = null;
            }
        };

        return rsf;
    }
};

const LayerSnapshot = struct {
    s_w: []f32,
    t_w: []f32,
    s_b: []f32,
    t_b: []f32,
    clip_min: f32,
    clip_max: f32,
    grad_mean: bool,
    s_w_shape: [2]usize,
    t_w_shape: [2]usize,
    s_b_shape: [2]usize,
    t_b_shape: [2]usize,
};

fn writeTensorData(w: anytype, hasher: *std.hash.Crc32, data: []const f32, shape: *const [2]usize) !void {
    try w.writeInt(u64, 2, .Little);
    try w.writeInt(u64, @intCast(shape[0]), .Little);
    try w.writeInt(u64, @intCast(shape[1]), .Little);
    for (data) |v| {
        const bits = @as(u32, @bitCast(v));
        try w.writeInt(u32, bits, .Little);
        hasher.update(std.mem.asBytes(&bits));
    }
}

fn hashTensorData(hasher: *std.hash.Crc32, data: []const f32) void {
    for (data) |v| {
        const bits = @as(u32, @bitCast(v));
        hasher.update(std.mem.asBytes(&bits));
    }
}
