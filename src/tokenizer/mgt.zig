const std = @import("std");
const mem = std.mem;
const Allocator = mem.Allocator;
const testing = std.testing;
const core_tensor = @import("../core/tensor.zig");
const core_memory = @import("../core/memory.zig");

pub const MGT = struct {
    token_to_id: std.StringHashMap(u32),
    id_to_token: std.AutoHashMap(u32, []const u8),
    prefixes: std.StringHashMap(u32),
    suffixes: std.StringHashMap(u32),
    roots: std.StringHashMap(u32),
    bpe_pairs: std.StringHashMap(BPEMerge),
    anchors: std.StringHashMap(u64),
    allocated_strings: std.ArrayList([]u8),
    allocator: Allocator,
    next_token_id: u32,

    const BPEMerge = struct {
        token_id: u32,
        priority: u32,
    };

    const SPECIAL_TOKENS = struct {
        const PAD: u32 = 0;
        const UNK: u32 = 1;
        const BOS: u32 = 2;
        const EOS: u32 = 3;
    };

    pub fn init(allocator: Allocator, vocab: []const []const u8, anchors: []const []const u8) !MGT {
        var token_to_id = std.StringHashMap(u32).init(allocator);
        errdefer token_to_id.deinit();
        var id_to_token = std.AutoHashMap(u32, []const u8).init(allocator);
        errdefer id_to_token.deinit();
        const prefixes = std.StringHashMap(u32).init(allocator);
        errdefer prefixes.deinit();
        const suffixes = std.StringHashMap(u32).init(allocator);
        errdefer suffixes.deinit();
        const roots = std.StringHashMap(u32).init(allocator);
        errdefer roots.deinit();
        const bpe_pairs = std.StringHashMap(BPEMerge).init(allocator);
        errdefer bpe_pairs.deinit();
        const anch_map = std.StringHashMap(u64).init(allocator);
        errdefer anch_map.deinit();
        var allocated = std.ArrayList([]u8).init(allocator);
        errdefer {
            for (allocated.items) |str| {
                allocator.free(str);
            }
            allocated.deinit();
        }

        const special = [_][]const u8{ "[PAD]", "[UNK]", "[BOS]", "[EOS]" };
        var i: usize = 0;
        for (special) |tok| {
            const tok_copy = try allocator.dupe(u8, tok);
            errdefer allocator.free(tok_copy);
            try allocated.append(tok_copy);
            try token_to_id.put(tok_copy, @intCast(i));
            try id_to_token.put(@intCast(i), tok_copy);
            i += 1;
        }

        var next_id: u32 = 4;
        for (vocab) |word| {
            if (!token_to_id.contains(word)) {
                const word_copy = try allocator.dupe(u8, word);
                errdefer allocator.free(word_copy);
                try allocated.append(word_copy);
                try token_to_id.put(word_copy, next_id);
                try id_to_token.put(next_id, word_copy);
                next_id += 1;
            }
        }

        var mgt = MGT{
            .token_to_id = token_to_id,
            .id_to_token = id_to_token,
            .prefixes = prefixes,
            .suffixes = suffixes,
            .roots = roots,
            .bpe_pairs = bpe_pairs,
            .anchors = anch_map,
            .allocated_strings = allocated,
            .allocator = allocator,
            .next_token_id = next_id,
        };
        errdefer mgt.deinit();

        try mgt.initMorphemes();

        for (anchors) |anch| {
            const tid = if (mgt.token_to_id.get(anch)) |t| t else try mgt.addToken(anch);
            const h: u64 = @intCast(tid);
            const anch_key = mgt.id_to_token.get(tid).?;
            try mgt.anchors.put(anch_key, h);
        }

        return mgt;
    }

    pub fn initWithArena(arena: *core_memory.ArenaAllocator, vocab: []const []const u8, anchors_list: []const []const u8) !MGT {
        return init(arena.allocator(), vocab, anchors_list);
    }

    pub fn initWithPool(pool: *core_memory.PoolAllocator, vocab: []const []const u8, anchors_list: []const []const u8) !MGT {
        return init(pool.allocator(), vocab, anchors_list);
    }

    pub fn initWithBuddy(buddy: *core_memory.BuddyAllocator, vocab: []const []const u8, anchors_list: []const []const u8) !MGT {
        return init(buddy.allocator(), vocab, anchors_list);
    }

    fn initMorphemes(self: *MGT) !void {
        const prefix_list = [_][]const u8{
            "un",  "re",   "pre",  "dis",  "mis",  "over", "under", "out",
            "sub", "inter", "fore", "de",   "trans", "super", "semi", "anti",
            "mid", "non",  "ex",   "post", "pro",  "co",   "en",   "em",
            "meg", "el", "fel", "le", "be", "ki", "rá", "át", "szét", "vissza",
            "ide", "oda", "alá", "fölé", "közé", "egy", "össze", "tul", "hozzá", "körül",
            "alig", "éppen", "majd", "csak", "is", "leg", "legesleg"
        };

        for (prefix_list) |prefix| {
            if (!self.token_to_id.contains(prefix)) {
                const id = try self.addToken(prefix);
                try self.prefixes.put(self.id_to_token.get(id).?, id);
            }
        }

        const suffix_list = [_][]const u8{
            "ing", "ed",  "er",   "est",  "ly",   "tion", "sion", "ness",
            "ment", "ful", "less", "ous",  "ive",  "able", "ible", "al",
            "ial", "y",   "s",    "es",   "en",   "ize",  "ise",  "ate",
            "ság", "ség", "ságú", "ségű", "é", "je", "ja", "ban", "ben",
            "ba", "be", "ból", "ből", "hoz", "hez", "höz", "tól", "től",
            "nak", "nek", "val", "vel", "ért", "ul", "ül", "ként", "án",
            "én", "ig", "at", "et", "tat", "tet", "ott", "ett", "atlan",
            "etlen", "talan", "telen", "ál", "él", "oz", "ez", "öd", "ed",
            "gyet", "get", "j", "unk", "jatok", "játok", "i", "ni", "nként",
            "kor", "ra", "re"
        };

        for (suffix_list) |suffix| {
            if (!self.token_to_id.contains(suffix)) {
                const id = try self.addToken(suffix);
                try self.suffixes.put(self.id_to_token.get(id).?, id);
            }
        }
    }

    pub fn deinit(self: *MGT) void {
        self.token_to_id.deinit();
        self.id_to_token.deinit();
        self.prefixes.deinit();
        self.suffixes.deinit();
        self.roots.deinit();
        self.bpe_pairs.deinit();
        self.anchors.deinit();
        for (self.allocated_strings.items) |str| {
            self.allocator.free(str);
        }
        self.allocated_strings.deinit();
    }

    fn isWhitespace(c: u8) bool {
        return c == ' ' or c == '\n' or c == '\t' or c == '\r';
    }

    fn isPunctuation(c: u8) bool {
        return c == '.' or c == ',' or c == '!' or c == '?' or c == ';' or
               c == ':' or c == '"' or c == '\'' or c == '(' or c == ')' or
               c == '{' or c == '}';
    }

    fn isSpecialTokenStart(text: []const u8, pos: usize) bool {
        if (pos >= text.len or text[pos] != '[') return false;
        const specials = [_][]const u8{ "[PAD]", "[UNK]", "[BOS]", "[EOS]" };
        for (specials) |special| {
            if (pos + special.len <= text.len and mem.eql(u8, text[pos..pos + special.len], special)) {
                return true;
            }
        }
        return false;
    }

    fn getSpecialTokenLen(text: []const u8, pos: usize) ?usize {
        if (pos >= text.len or text[pos] != '[') return null;
        const specials = [_][]const u8{ "[PAD]", "[UNK]", "[BOS]", "[EOS]" };
        for (specials) |special| {
            if (pos + special.len <= text.len and mem.eql(u8, text[pos..pos + special.len], special)) {
                return special.len;
            }
        }
        return null;
    }

    fn utf8CharLen(first_byte: u8) u8 {
        if (first_byte & 0x80 == 0) return 1;
        if (first_byte & 0xE0 == 0xC0) return 2;
        if (first_byte & 0xF0 == 0xE0) return 3;
        if (first_byte & 0xF8 == 0xF0) return 4;
        return 1;
    }

    pub fn encode(self: *MGT, text: []const u8, out_tokens: *std.ArrayList(u32)) !void {
        var i: usize = 0;
        while (i < text.len) {
            if (isSpecialTokenStart(text, i)) {
                if (getSpecialTokenLen(text, i)) |special_len| {
                    const special_token = text[i..i + special_len];
                    if (self.token_to_id.get(special_token)) |tid| {
                        try out_tokens.append(tid);
                    }
                    i += special_len;
                    continue;
                }
            }

            if (isWhitespace(text[i])) {
                if (self.token_to_id.get(" ")) |space_tid| {
                    try out_tokens.append(space_tid);
                }
                i += 1;
                continue;
            }

            var word_end = i;
            while (word_end < text.len) {
                const c = text[word_end];
                if (isWhitespace(c) or isPunctuation(c)) break;
                if (isSpecialTokenStart(text, word_end)) break;
                const char_len = utf8CharLen(c);
                if (word_end + char_len > text.len) break;
                word_end += char_len;
            }

            if (word_end > i) {
                const word = text[i..word_end];

                if (try self.morphDecompose(word, out_tokens)) |decomposed| {
                    if (decomposed) {
                        i = word_end;
                        continue;
                    }
                }

                if (self.token_to_id.get(word)) |tid| {
                    try out_tokens.append(tid);
                } else {
                    const subword_tokens = try self.subwordSplit(word);
                    defer self.allocator.free(subword_tokens);
                    for (subword_tokens) |tok| {
                        try out_tokens.append(tok);
                    }
                }
                i = word_end;
            }

            if (i < text.len and isPunctuation(text[i])) {
                const char_len = utf8CharLen(text[i]);
                if (i + char_len > text.len) break;
                const punct_str = text[i..i+char_len];
                if (self.token_to_id.get(punct_str)) |tid| {
                    try out_tokens.append(tid);
                } else {
                    const tid = try self.addToken(punct_str);
                    try out_tokens.append(tid);
                }
                i += char_len;
            }
        }
    }

    fn findLongestPrefix(self: *MGT, word: []const u8) ?struct { prefix: []const u8, len: usize } {
        var max_len: usize = 0;
        var best: ?[]const u8 = null;

        var prefix_it = self.prefixes.iterator();
        while (prefix_it.next()) |entry| {
            const prefix = entry.key_ptr.*;
            if (word.len > prefix.len and mem.startsWith(u8, word, prefix)) {
                if (prefix.len > max_len) {
                    max_len = prefix.len;
                    best = prefix;
                }
            }
        }

        if (best) |p| {
            return .{ .prefix = p, .len = max_len };
        }
        return null;
    }

    fn findLongestSuffix(self: *MGT, word: []const u8) ?struct { suffix: []const u8, len: usize } {
        var max_len: usize = 0;
        var best: ?[]const u8 = null;

        var suffix_it = self.suffixes.iterator();
        while (suffix_it.next()) |entry| {
            const suffix = entry.key_ptr.*;
            if (word.len > suffix.len and mem.endsWith(u8, word, suffix)) {
                if (suffix.len > max_len) {
                    max_len = suffix.len;
                    best = suffix;
                }
            }
        }

        if (best) |s| {
            return .{ .suffix = s, .len = max_len };
        }
        return null;
    }

    fn morphDecompose(self: *MGT, word: []const u8, out_tokens: *std.ArrayList(u32)) !?bool {
        if (word.len < 4) return null;

        const prefix_result = self.findLongestPrefix(word);
        const suffix_result = self.findLongestSuffix(word);

        const prefix_len = if (prefix_result) |p| p.len else 0;
        const suffix_len = if (suffix_result) |s| s.len else 0;

        if (prefix_len == 0 and suffix_len == 0) return null;

        const root_start = prefix_len;
        const root_end = word.len - suffix_len;

        if (root_end <= root_start or root_end - root_start < 2) return null;

        const root = word[root_start..root_end];

        var temp_tokens = std.ArrayList(u32).init(self.allocator);
        defer temp_tokens.deinit();

        if (prefix_result) |p| {
            if (self.token_to_id.get(p.prefix)) |tid| {
                try temp_tokens.append(tid);
            } else {
                return null;
            }
        }

        if (self.token_to_id.get(root)) |tid| {
            try temp_tokens.append(tid);
        } else {
            const root_id = try self.addToken(root);
            const root_str = self.id_to_token.get(root_id).?;
            try self.roots.put(root_str, root_id);
            try temp_tokens.append(root_id);
        }

        if (suffix_result) |s| {
            if (self.token_to_id.get(s.suffix)) |tid| {
                try temp_tokens.append(tid);
            } else {
                return null;
            }
        }

        try out_tokens.appendSlice(temp_tokens.items);
        return true;
    }

    fn addToken(self: *MGT, token: []const u8) !u32 {
        if (self.token_to_id.get(token)) |existing| {
            return existing;
        }

        const token_copy = try self.allocator.dupe(u8, token);
        errdefer self.allocator.free(token_copy);
        try self.allocated_strings.append(token_copy);
        errdefer _ = self.allocated_strings.pop();

        try self.token_to_id.put(token_copy, self.next_token_id);
        errdefer _ = self.token_to_id.remove(token_copy);

        try self.id_to_token.put(self.next_token_id, token_copy);

        const id = self.next_token_id;
        self.next_token_id += 1;
        return id;
    }

    fn encodeBPE(self: *MGT, text: []const u8) ![]u32 {
        if (text.len == 0) return self.allocator.alloc(u32, 0);

        var tokens = std.ArrayList(u32).init(self.allocator);
        var byte_tokens = std.ArrayList([]const u8).init(self.allocator);
        defer {
            for (byte_tokens.items) |bt| {
                self.allocator.free(bt);
            }
            byte_tokens.deinit();
        }

        for (text) |byte| {
            const byte_str = try std.fmt.allocPrint(self.allocator, "<{x:0>2}>", .{byte});
            try byte_tokens.append(byte_str);
        }

        while (byte_tokens.items.len > 1) {
            var best_priority: u32 = std.math.maxInt(u32);
            var best_idx: ?usize = null;

            var i: usize = 0;
            while (i + 1 < byte_tokens.items.len) : (i += 1) {
                const pair = try std.fmt.allocPrint(
                    self.allocator,
                    "{s}{s}",
                    .{ byte_tokens.items[i], byte_tokens.items[i + 1] },
                );
                defer self.allocator.free(pair);

                if (self.bpe_pairs.get(pair)) |merge| {
                    if (merge.priority < best_priority) {
                        best_priority = merge.priority;
                        best_idx = i;
                    }
                }
            }

            if (best_idx == null) break;

            const idx = best_idx.?;
            const merged = try std.fmt.allocPrint(
                self.allocator,
                "{s}{s}",
                .{ byte_tokens.items[idx], byte_tokens.items[idx + 1] },
            );

            self.allocator.free(byte_tokens.items[idx]);
            self.allocator.free(byte_tokens.items[idx + 1]);

            byte_tokens.items[idx] = merged;
            _ = byte_tokens.orderedRemove(idx + 1);
        }

        for (byte_tokens.items) |bt| {
            if (self.token_to_id.get(bt)) |tid| {
                try tokens.append(tid);
            } else {
                const tid = try self.addToken(bt);
                try tokens.append(tid);
            }
        }

        return try tokens.toOwnedSlice();
    }

    const PairKey = struct {
        byte1: u8,
        byte2: u8,
    };
    const MergeItem = struct { key: PairKey, freq: u32 };

    const LessThanContext = struct {
        fn lessThan(_: @This(), a: MergeItem, b: MergeItem) bool {
            return b.freq < a.freq;
        }
    };

    pub fn trainBPE(self: *MGT, corpus: []const []const u8, num_merges: u32) !void {
        var pair_freqs = std.AutoHashMap(PairKey, u32).init(self.allocator);
        defer pair_freqs.deinit();

        for (corpus) |text| {
            var i: usize = 0;
            while (i + 1 < text.len) : (i += 1) {
                const key = PairKey{ .byte1 = text[i], .byte2 = text[i + 1] };
                const result = try pair_freqs.getOrPut(key);
                if (result.found_existing) {
                    result.value_ptr.* += 1;
                } else {
                    result.value_ptr.* = 1;
                }
            }
        }

        var merge_list = std.ArrayList(MergeItem).init(self.allocator);
        defer merge_list.deinit();

        var pair_iter = pair_freqs.iterator();
        while (pair_iter.next()) |entry| {
            try merge_list.append(.{ .key = entry.key_ptr.*, .freq = entry.value_ptr.* });
        }

        if (merge_list.items.len == 0) return;

        std.mem.sort(MergeItem, merge_list.items, LessThanContext{}, LessThanContext.lessThan);

        var merge_count: u32 = 0;
        for (merge_list.items) |entry| {
            if (merge_count >= num_merges or entry.freq < 2) break;

            var buf1: [16]u8 = undefined;
            const b1_str = try std.fmt.bufPrint(&buf1, "<{x:0>2}>", .{entry.key.byte1});
            var buf2: [16]u8 = undefined;
            const b2_str = try std.fmt.bufPrint(&buf2, "<{x:0>2}>", .{entry.key.byte2});

            var buf_pair: [32]u8 = undefined;
            const pair_str = try std.fmt.bufPrint(&buf_pair, "{s}{s}", .{b1_str, b2_str});

            const merge_token_id = try self.addToken(pair_str);

            const key_ptr = self.id_to_token.get(merge_token_id).?;
            try self.bpe_pairs.put(key_ptr, .{
                .token_id = merge_token_id,
                .priority = merge_count,
            });

            merge_count += 1;
        }
    }

    pub fn decode(self: *MGT, tokens: []const u32, out_text: *std.ArrayList(u8)) !void {
        for (tokens) |tok| {
            if (self.id_to_token.get(tok)) |token_str| {
                if (mem.startsWith(u8, token_str, "<") and mem.endsWith(u8, token_str, ">") and token_str.len > 2) {
                    const hex = token_str[1 .. token_str.len - 1];
                    if (std.fmt.parseInt(u8, hex, 16)) |byte| {
                        try out_text.append(byte);
                    } else |_| {
                        try out_text.appendSlice(token_str);
                    }
                } else if (mem.eql(u8, token_str, "[PAD]") or
                    mem.eql(u8, token_str, "[UNK]") or
                    mem.eql(u8, token_str, "[BOS]") or
                    mem.eql(u8, token_str, "[EOS]"))
                {
                    continue;
                } else {
                    try out_text.appendSlice(token_str);
                }
            } else {
                try out_text.appendSlice("[UNK]");
            }
        }
    }

    pub fn longestMatch(self: *MGT, text: []const u8, start: usize) usize {
        var max_len: usize = 0;
        var len: usize = 1;

        while (start + len <= text.len) : (len += 1) {
            const substr = text[start .. start + len];
            if (self.token_to_id.contains(substr)) {
                max_len = len;
            }
        }

        return max_len;
    }

    pub fn vocabSize(self: *const MGT) usize {
        return self.token_to_id.count();
    }

    pub fn addVocabWord(self: *MGT, word: []const u8, is_anchor: bool) !void {
        const id = try self.addToken(word);
        if (is_anchor) {
            const h: u64 = @intCast(id);
            const key = self.id_to_token.get(id).?;
            try self.anchors.put(key, h);
        }
    }

    pub fn removeVocabWord(self: *MGT, word: []const u8) void {
        if (self.token_to_id.get(word)) |id| {
            if (self.id_to_token.get(id)) |allocated_ptr| {
                _ = self.token_to_id.remove(word);
                _ = self.id_to_token.remove(id);
                _ = self.anchors.remove(word);
                _ = self.prefixes.remove(word);
                _ = self.suffixes.remove(word);
                _ = self.roots.remove(word);

                var idx: usize = 0;
                while (idx < self.allocated_strings.items.len) : (idx += 1) {
                    const str = self.allocated_strings.items[idx];
                    if (str.ptr == allocated_ptr.ptr) {
                        self.allocator.free(str);
                        _ = self.allocated_strings.orderedRemove(idx);
                        break;
                    }
                }
            }
        }
    }

    pub fn tokenizeWithAnchors(self: *MGT, text: []const u8, out_tokens: *std.ArrayList(u32), out_anchors: *std.ArrayList(usize)) !void {
        var i: usize = 0;
        while (i < text.len) {
            const match_len = self.longestMatch(text, i);
            if (match_len > 0) {
                const word = text[i .. i + match_len];
                if (self.token_to_id.get(word)) |tid| {
                    try out_tokens.append(tid);
                    if (self.anchors.contains(word)) {
                        try out_anchors.append(i);
                    }
                    i += match_len;
                    continue;
                }
            }

            const bpe_tokens = try self.encodeBPE(text[i..i+1]);
            defer self.allocator.free(bpe_tokens);
            for (bpe_tokens) |tok| {
                try out_tokens.append(tok);
            }
            i += 1;
        }
    }

    pub fn detokenize(self: *MGT, tokens: []const u32) ![]u8 {
        var text = std.ArrayList(u8).init(self.allocator);
        try self.decode(tokens, &text);
        return try text.toOwnedSlice();
    }

    pub fn encodeBatch(self: *MGT, texts: []const []const u8, allocator: Allocator) ![][]u32 {
        const results = try allocator.alloc([]u32, texts.len);
        errdefer allocator.free(results);
        var i: usize = 0;
        errdefer {
            for (results[0..i]) |r| {
                allocator.free(r);
            }
        }
        for (texts) |text| {
            var tokens = std.ArrayList(u32).init(allocator);
            try self.encode(text, &tokens);
            results[i] = try tokens.toOwnedSlice();
            i += 1;
        }
        return results;
    }

    pub fn batchDetokenize(self: *MGT, token_lists: []const []const u32, allocator: Allocator) ![][]u8 {
        const results = try allocator.alloc([]u8, token_lists.len);
        errdefer allocator.free(results);
        var i: usize = 0;
        errdefer {
            for (results[0..i]) |r| {
                allocator.free(r);
            }
        }
        for (token_lists) |tokens| {
            results[i] = try self.detokenize(tokens);
            i += 1;
        }
        return results;
    }

    pub fn saveVocab(self: *MGT, path: []const u8) !void {
        var file = try std.fs.cwd().createFile(path, .{});
        defer file.close();
        var writer = file.writer();

        const size = self.vocabSize();
        try writer.writeInt(u32, @as(u32, @intCast(size)), .Little);

        var it = self.token_to_id.iterator();
        while (it.next()) |entry| {
            const word = entry.key_ptr.*;
            const id = entry.value_ptr.*;
            try writer.writeInt(u32, @as(u32, @intCast(word.len)), .Little);
            try writer.writeAll(word);
            try writer.writeInt(u32, id, .Little);
        }

        try writer.writeInt(u32, @as(u32, @intCast(self.bpe_pairs.count())), .Little);
        var bpe_it = self.bpe_pairs.iterator();
        while (bpe_it.next()) |entry| {
            const key = entry.key_ptr.*;
            const merge = entry.value_ptr.*;
            try writer.writeInt(u32, @as(u32, @intCast(key.len)), .Little);
            try writer.writeAll(key);
            try writer.writeInt(u32, merge.token_id, .Little);
            try writer.writeInt(u32, merge.priority, .Little);
        }

        const writeStringMap = struct {
            fn write(map: std.StringHashMap(u32), w: anytype) !void {
                try w.writeInt(u32, @as(u32, @intCast(map.count())), .Little);
                var iter = map.iterator();
                while (iter.next()) |e| {
                    try w.writeInt(u32, @as(u32, @intCast(e.key_ptr.*.len)), .Little);
                    try w.writeAll(e.key_ptr.*);
                    try w.writeInt(u32, e.value_ptr.*, .Little);
                }
            }
        };

        try writeStringMap.write(self.prefixes, writer);
        try writeStringMap.write(self.suffixes, writer);
        try writeStringMap.write(self.roots, writer);

        try writer.writeInt(u32, @as(u32, @intCast(self.anchors.count())), .Little);
        var anch_it = self.anchors.iterator();
        while (anch_it.next()) |entry| {
            const key = entry.key_ptr.*;
            try writer.writeInt(u32, @as(u32, @intCast(key.len)), .Little);
            try writer.writeAll(key);
            try writer.writeInt(u64, entry.value_ptr.*, .Little);
        }
    }

    pub fn loadVocab(self: *MGT, path: []const u8) !void {
        const file = try std.fs.cwd().openFile(path, .{});
        defer file.close();
        var reader = file.reader();

        const size = try reader.readInt(u32, .Little);
        var i: usize = 0;
        while (i < size) : (i += 1) {
            const word_len = try reader.readInt(u32, .Little);
            const word_buf = try self.allocator.alloc(u8, word_len);
            errdefer self.allocator.free(word_buf);
            try reader.readNoEof(word_buf);
            const id = try reader.readInt(u32, .Little);

            try self.allocated_strings.append(word_buf);
            try self.token_to_id.put(word_buf, id);
            try self.id_to_token.put(id, word_buf);

            if (id >= self.next_token_id) {
                self.next_token_id = id + 1;
            }
        }

        const bpe_count = try reader.readInt(u32, .Little);
        var j: usize = 0;
        while (j < bpe_count) : (j += 1) {
            const key_len = try reader.readInt(u32, .Little);
            const key_buf = try self.allocator.alloc(u8, key_len);
            errdefer self.allocator.free(key_buf);
            try reader.readNoEof(key_buf);
            const token_id = try reader.readInt(u32, .Little);
            const priority = try reader.readInt(u32, .Little);

            try self.allocated_strings.append(key_buf);
            try self.bpe_pairs.put(key_buf, .{ .token_id = token_id, .priority = priority });
        }

        const readStringMap = struct {
            fn read(map: *std.StringHashMap(u32), r: anytype, alloc: Allocator, alloc_list: *std.ArrayList([]u8)) !void {
                const count = try r.readInt(u32, .Little);
                var k: usize = 0;
                while (k < count) : (k += 1) {
                    const len = try r.readInt(u32, .Little);
                    const buf = try alloc.alloc(u8, len);
                    errdefer alloc.free(buf);
                    try r.readNoEof(buf);
                    const id = try r.readInt(u32, .Little);

                    try alloc_list.append(buf);
                    try map.put(buf, id);
                }
            }
        };

        try readStringMap.read(&self.prefixes, reader, self.allocator, &self.allocated_strings);
        try readStringMap.read(&self.suffixes, reader, self.allocator, &self.allocated_strings);
        try readStringMap.read(&self.roots, reader, self.allocator, &self.allocated_strings);

        const anch_count = try reader.readInt(u32, .Little);
        var l: usize = 0;
        while (l < anch_count) : (l += 1) {
            const key_len = try reader.readInt(u32, .Little);
            const key_buf = try self.allocator.alloc(u8, key_len);
            errdefer self.allocator.free(key_buf);
            try reader.readNoEof(key_buf);
            const val = try reader.readInt(u64, .Little);

            try self.allocated_strings.append(key_buf);
            try self.anchors.put(key_buf, val);
        }
    }

    pub fn unknownReplacement(self: *MGT, context: []const u8) u32 {
        _ = self;
        _ = context;
        return SPECIAL_TOKENS.UNK;
    }

    pub fn subwordSplit(self: *MGT, word: []const u8) ![]u32 {
        var tokens = std.ArrayList(u32).init(self.allocator);
        var i: usize = 0;
        while (i < word.len) {
            const match = self.longestMatch(word, i);
            if (match > 0) {
                const found_word = word[i .. i + match];
                if (self.token_to_id.get(found_word)) |tid| {
                    try tokens.append(tid);
                    i += match;
                    continue;
                }
            }

            const bpe_tokens = try self.encodeBPE(word[i..i+1]);
            defer self.allocator.free(bpe_tokens);
            for (bpe_tokens) |tok| {
                try tokens.append(tok);
            }
            i += 1;
        }
        return try tokens.toOwnedSlice();
    }

    pub fn mergeSubwords(self: *MGT, subwords: []const []const u32) ![]u32 {
        var merged = std.ArrayList(u32).init(self.allocator);
        for (subwords) |sw| {
            try merged.appendSlice(sw);
        }
        return try merged.toOwnedSlice();
    }

    pub fn validateTokens(self: *MGT, tokens: []const u32) bool {
        for (tokens) |tok| {
            if (tok >= self.next_token_id) return false;
        }
        return true;
    }

    pub fn coverage(self: *MGT, corpus: []const u8) f32 {
        var covered: usize = 0;
        var i: usize = 0;
        while (i < corpus.len) {
            const m = self.longestMatch(corpus, i);
            if (m > 0) {
                covered += m;
                i += m;
            } else {
                i += 1;
            }
        }
        if (corpus.len == 0) return 0.0;
        return @as(f32, @floatFromInt(covered)) / @as(f32, @floatFromInt(corpus.len));
    }

    pub fn encodeToTensor(self: *MGT, text: []const u8, allocator: Allocator) !core_tensor.Tensor {
        var tokens = std.ArrayList(u32).init(allocator);
        defer tokens.deinit();
        try self.encode(text, &tokens);
        const shape = [_]usize{tokens.items.len};
        var tensor = try core_tensor.Tensor.init(allocator, &shape);
        {
            var i: usize = 0;
            while (i < tokens.items.len) : (i += 1) {
                const tok = tokens.items[i];
                tensor.data[i] = @floatFromInt(tok);
            }
        }
        return tensor;
    }

    pub fn encodeBatchToTensor(self: *MGT, texts: []const []const u8, allocator: Allocator) !core_tensor.Tensor {
        var all_tokens = std.ArrayList(u32).init(allocator);
        defer all_tokens.deinit();
        var max_len: usize = 0;
        var batch_lens = std.ArrayList(usize).init(allocator);
        defer batch_lens.deinit();
        for (texts) |text| {
            var tokens = std.ArrayList(u32).init(allocator);
            defer tokens.deinit();
            try self.encode(text, &tokens);
            if (tokens.items.len > max_len) max_len = tokens.items.len;
            try batch_lens.append(tokens.items.len);
            try all_tokens.appendSlice(tokens.items);
        }
        if (max_len == 0) max_len = 1;
        const shape = [_]usize{ texts.len, max_len };
        var tensor = try core_tensor.Tensor.init(allocator, &shape);
        @memset(tensor.data, 0);
        var offset: usize = 0;
        {
            var batch_idx: usize = 0;
            while (batch_idx < batch_lens.items.len) : (batch_idx += 1) {
                const blen = batch_lens.items[batch_idx];
                var j: usize = 0;
                while (j < blen) : (j += 1) {
                    tensor.data[batch_idx * max_len + j] = @floatFromInt(all_tokens.items[offset + j]);
                }
                offset += blen;
            }
        }
        return tensor;
    }

    pub fn decodeFromTensor(self: *MGT, tensor: *const core_tensor.Tensor, allocator: Allocator) ![]u8 {
        var tokens = try allocator.alloc(u32, tensor.data.len);
        defer allocator.free(tokens);
        {
            var i: usize = 0;
            while (i < tensor.data.len) : (i += 1) {
                const val = tensor.data[i];
                if (std.math.isNan(val) or std.math.isInf(val) or val < 0.0) {
                    tokens[i] = SPECIAL_TOKENS.UNK;
                } else {
                    tokens[i] = @intFromFloat(val);
                }
            }
        }
        var out_text = std.ArrayList(u8).init(allocator);
        try self.decode(tokens, &out_text);
        return try out_text.toOwnedSlice();
    }
};

test "MGT encode decode" {
    const gpa = testing.allocator;
    const vocab = &.{ "hello", "world", " " };
    const anchors = &.{"hello"};
    var mgt = try MGT.init(gpa, vocab, anchors);
    defer mgt.deinit();
    var tokens = std.ArrayList(u32).init(gpa);
    defer tokens.deinit();
    try mgt.encode("hello world", &tokens);
    try testing.expect(tokens.items.len >= 2);
    var text = std.ArrayList(u8).init(gpa);
    defer text.deinit();
    try mgt.decode(tokens.items, &text);
}

test "MGT add remove vocab" {
    const gpa = testing.allocator;
    var mgt = try MGT.init(gpa, &.{}, &.{});
    defer mgt.deinit();
    try mgt.addVocabWord("test", true);
    try testing.expect(mgt.anchors.contains("test"));
    mgt.removeVocabWord("test");
    try testing.expect(!mgt.anchors.contains("test"));
}

test "MGT longest match" {
    const gpa = testing.allocator;
    var mgt = try MGT.init(gpa, &.{ "hello", "hell" }, &.{});
    defer mgt.deinit();
    const len = mgt.longestMatch("hello", 0);
    try testing.expectEqual(@as(usize, 5), len);
}

test "MGT batch encode" {
    var gpa = testing.allocator;
    var mgt = try MGT.init(gpa, &.{ "a", "b" }, &.{});
    defer mgt.deinit();
    const texts = &.{ "a", "b" };
    const batches = try mgt.encodeBatch(texts, gpa);
    defer {
        for (batches) |batch| {
            gpa.free(batch);
        }
        gpa.free(batches);
    }
    try testing.expect(batches.len == 2);
}

test "MGT subword split" {
    var gpa = testing.allocator;
    var mgt = try MGT.init(gpa, &.{ "hel", "lo" }, &.{});
    defer mgt.deinit();
    const sub = try mgt.subwordSplit("hello");
    defer gpa.free(sub);
    try testing.expect(sub.len >= 1);
}

test "MGT coverage" {
    const gpa = testing.allocator;
    var mgt = try MGT.init(gpa, &.{ "hello", "world" }, &.{});
    defer mgt.deinit();
    const cov = mgt.coverage("hello world");
    try testing.expect(cov > 0.0);
}

test "MGT validate" {
    const gpa = testing.allocator;
    var mgt = try MGT.init(gpa, &.{"a"}, &.{});
    defer mgt.deinit();
    const valid = mgt.validateTokens(&.{0});
    try testing.expect(valid);
}

test "MGT tokenize with anchors" {
    const gpa = testing.allocator;
    const vocab = &.{ "test", "anchor" };
    const anchors = &.{"anchor"};
    var mgt = try MGT.init(gpa, vocab, anchors);
    defer mgt.deinit();
    var tokens = std.ArrayList(u32).init(gpa);
    defer tokens.deinit();
    var anchor_positions = std.ArrayList(usize).init(gpa);
    defer anchor_positions.deinit();
    try mgt.tokenizeWithAnchors("testanchor", &tokens, &anchor_positions);
    try testing.expect(tokens.items.len >= 1);
}

test "MGT batch detokenize" {
    var gpa = testing.allocator;
    var mgt = try MGT.init(gpa, &.{ "a", "b" }, &.{});
    defer mgt.deinit();
    const token_lists = &[_][]const u32{
        &.{4},
        &.{5},
    };
    const results = try mgt.batchDetokenize(token_lists, gpa);
    defer {
        for (results) |result| {
            gpa.free(result);
        }
        gpa.free(results);
    }
    try testing.expect(results.len == 2);
}

test "MGT vocab size" {
    const gpa = testing.allocator;
    var mgt = try MGT.init(gpa, &.{ "a", "b", "c" }, &.{});
    defer mgt.deinit();
    const size = mgt.vocabSize();
    try testing.expect(size >= 3);
}

test "MGT save and load vocab" {
    const gpa = testing.allocator;
    var mgt = try MGT.init(gpa, &.{ "test", "vocab" }, &.{});
    defer mgt.deinit();
    try mgt.saveVocab("test_vocab.bin");
    defer {
        std.fs.cwd().deleteFile("test_vocab.bin") catch |err| {
            std.log.warn("Failed to delete test file: {}", .{err});
        };
    }
    var mgt2 = try MGT.init(gpa, &.{}, &.{});
    defer mgt2.deinit();
    try mgt2.loadVocab("test_vocab.bin");
    try testing.expect(mgt2.vocabSize() >= 1);
}

test "MGT merge subwords" {
    var gpa = testing.allocator;
    var mgt = try MGT.init(gpa, &.{}, &.{});
    defer mgt.deinit();
    const sub1 = &[_]u32{ 1, 2 };
    const sub2 = &[_]u32{ 3, 4 };
    const subwords = &[_][]const u32{ sub1, sub2 };
    const merged = try mgt.mergeSubwords(subwords);
    defer gpa.free(merged);
    try testing.expectEqual(@as(usize, 4), merged.len);
}

test "MGT unknown replacement" {
    const gpa = testing.allocator;
    var mgt = try MGT.init(gpa, &.{}, &.{});
    defer mgt.deinit();
    const replacement = mgt.unknownReplacement("context");
    try testing.expectEqual(MGT.SPECIAL_TOKENS.UNK, replacement);
}

test "MGT morphological decomposition" {
    const gpa = testing.allocator;
    var mgt = try MGT.init(gpa, &.{ "run", "walk" }, &.{});
    defer mgt.deinit();
    var tokens = std.ArrayList(u32).init(gpa);
    defer tokens.deinit();
    try mgt.encode("running", &tokens);
    try testing.expect(tokens.items.len >= 2);
}

test "MGT BPE training" {
    const gpa = testing.allocator;
    var mgt = try MGT.init(gpa, &.{}, &.{});
    defer mgt.deinit();
    const corpus = &.{ "hello", "help", "held" };
    try mgt.trainBPE(corpus, 10);
    try testing.expect(mgt.bpe_pairs.count() > 0);
}

test "MGT deterministic encoding" {
    const gpa = testing.allocator;
    var mgt = try MGT.init(gpa, &.{ "test", "data" }, &.{});
    defer mgt.deinit();

    var tokens1 = std.ArrayList(u32).init(gpa);
    defer tokens1.deinit();
    try mgt.encode("test data", &tokens1);

    var tokens2 = std.ArrayList(u32).init(gpa);
    defer tokens2.deinit();
    try mgt.encode("test data", &tokens2);

    try testing.expectEqualSlices(u32, tokens1.items, tokens2.items);
}