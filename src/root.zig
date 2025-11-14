const std = @import("std");

var allocator_backing = std.heap.GeneralPurposeAllocator(.{}){};
pub const allocator: std.mem.Allocator = allocator_backing.allocator();

var temp_allocator_backing = std.heap.ArenaAllocator.init(std.heap.page_allocator);
pub const temp_allocator = temp_allocator_backing.allocator();

pub fn resetTempAllocator() void {
    _ = temp_allocator_backing.reset(.retain_capacity);
}

pub fn tmpSlice(comptime T: type, n: usize) []T {
    return temp_allocator.alloc(T, n) catch @panic("TempAllocatorOutOfMemory");
}
// const any = @import("any.zig");

// The two types Array and TmpArray exists for convenience because it is really annoying
// to handle allocation errors and pass allocators explicitly all the time;
pub fn Array(T: type) type {
    return DynamicArray(T, false);
}
pub fn TmpArray(T: type) type {
    return DynamicArray(T, true);
}

fn DynamicArray(comptime T: type, comptime is_tmp: bool) type {
    if (@sizeOf(T) == 0) {
        @compileError("DynamicArray should only be used with types of non-zero size!");
    }

    return struct {
        const Slice = []T;
        const Self = @This();
        const gpa = if (is_tmp) temp_allocator else allocator;

        items: Slice = &.{},
        cap: usize = 0,

        pub fn init() Self {
            return Self{};
        }
        pub fn deinit(self: *Self) void {
            if (comptime is_tmp) return;
            gpa.free(self.allocatedSlice());
            self.* = Self{};
        }

        pub fn deinitWith(self: *Self, deinit_fn: fn (el: *T) void) void {
            for (self.items) |*item| {
                deinit_fn(item);
            }
            if (comptime is_tmp) return;
            gpa.free(self.allocatedSlice());
        }

        pub fn allocatedSlice(self: Self) Slice {
            return self.items.ptr[0..self.cap];
        }

        pub fn shrink(self: *Self) void {
            if (comptime is_tmp) return;
            const new_cap = self.items.len;
            const old_memory = self.allocatedSlice();
            if (gpa.remap(old_memory, new_cap)) |new_items| {
                self.cap = new_cap;
                self.items = new_items;
            } else {
                const new_memory = gpa.alloc(T, new_cap) catch @panic("OutOfMemory");
                @memcpy(new_memory, self.items);
                gpa.free(old_memory);
                self.items = new_memory;
                self.cap = new_memory.len;
            }
        }

        pub inline fn len(self: Self) usize {
            return self.items.len;
        }

        pub fn clone(self: Self) Self {
            var res = Self.init();
            if (self.items.len > 0) res.appendSlice(self.items);
            return res;
        }

        pub fn clear(self: *Self) void {
            if (self.items.len == 0) return;
            @memset(self.items, undefined);
            self.items.len = 0;
        }

        pub fn appendSlice(self: *Self, items: []const T) void {
            const new_len = self.items.len + items.len;
            if (new_len > self.cap) {
                self.reserve(calculateNewCapacity(self.cap, new_len));
            }
            @memcpy(self.items.ptr[self.items.len..new_len], items);
            self.items.len = new_len;
        }

        pub fn appendNTimes(
            self: *Self,
            n: usize,
            item: T,
        ) void {
            const new_len = self.items.len + n;
            if (new_len > self.cap) {
                self.reserve(calculateNewCapacity(self.cap, new_len));
            }
            @memset(self.items.ptr[self.items.len..new_len], item);
            self.items.len = new_len;
        }

        pub fn append(self: *Self, item: T) void {
            const new_len = self.items.len + 1;
            if (new_len > self.cap) {
                self.reserve(calculateNewCapacity(self.cap, new_len));
            }
            self.items.ptr[self.items.len] = item;
            self.items.len = new_len;
        }

        pub fn makeZeroTerminated(self: *Self) void {
            if (comptime T == u8) {
                self.append(0);
                self.items.len -= 1;
            } else {
                @compileError("Can only make DynamicArray(u8) zero-terminated!");
            }
        }

        pub fn reserve(self: *Self, new_cap: usize) void {
            if (new_cap <= self.cap) return;

            // Here we avoid copying allocated but unused bytes by
            // attempting a resize in place, and falling back to allocating
            // a new buffer and doing our own copy. With a realloc() call,
            // the allocator implementation would pointlessly copy our
            // extra capacity.
            const old_memory = self.allocatedSlice();
            if (gpa.remap(old_memory, new_cap)) |new_memory| {
                self.items.ptr = new_memory.ptr;
                self.cap = new_memory.len;
            } else {
                const new_memory = gpa.alloc(T, new_cap) catch @panic("OutOfMemory");
                @memcpy(new_memory[0..self.items.len], self.items);
                gpa.free(old_memory);
                self.items.ptr = new_memory.ptr;
                self.cap = new_memory.len;
            }
        }

        pub fn swapRemove(self: *Self, i: usize) T {
            std.debug.assert(i < self.items.len);
            const val = self.items[i];
            if (i != self.items.len - 1) {
                self.items[i] = self.items[self.items.len - 1];
            }
            self.items.len -= 1;
            self.items.ptr[self.items.len] = undefined;
            return val;
        }

        pub fn orderedRemove(self: *Self, i: usize) T {
            std.debug.assert(i < self.items.len);
            const val = self.items[i];
            if (i != self.items.len - 1) {
                @memmove(self.items[i .. self.items.len - 1], self.items[i + 1 .. self.items.len]);
            }
            self.items.len -= 1;
            self.items.ptr[self.items.len] = undefined;
            return val;
        }

        pub fn replaceRange(self: *Self, range_start: usize, range_len: usize, new_items: []const T) void {
            const range_end = range_start + range_len;
            std.debug.assert(range_end <= self.items.len);

            const range = self.items.ptr[range_start..range_end];
            if (new_items.len == range_len) {
                // just replace the items that are already there:
                @memcpy(range, new_items);
            } else if (new_items.len < range_len) {
                // remove more items than new ones are inserted:
                @memcpy(range[0..new_items.len], new_items);
                self.removeRange(range_start + new_items.len, range.len - new_items.len);
            } else {
                // here new_items.len > range_len, so we might need to resize:
                const new_len = self.items.len + new_items.len - range_len;
                if (new_len > self.cap) {
                    self.reserve(calculateNewCapacity(self.cap, new_len));
                }

                // now we can first move the items behind the range:
                const new_range_end = range_start + new_items.len;
                if (new_range_end >= self.items.len) {
                    // no overlap, memcpy:
                    @memcpy(
                        self.items.ptr[new_range_end..new_len],
                        self.items.ptr[range_end..self.items.len],
                    );
                } else {
                    // overlap, memmove:
                    @memmove(
                        self.items.ptr[new_range_end..new_len],
                        self.items.ptr[range_end..self.items.len],
                    );
                }
                self.items.len = new_len;

                // finally copy new_items into their place:
                @memcpy(self.items.ptr[range_start..new_range_end], new_items);
            }
        }

        pub fn removeRange(self: *Self, range_start: usize, range_len: usize) void {
            const range_end = range_start + range_len;
            std.debug.assert(range_end <= self.items.len);

            const rest_range = self.items[range_end..];
            if (rest_range.len > 0) {
                const rest_range_dest = self.items[range_start .. range_start + rest_range.len];
                if (range_len >= rest_range.len) {
                    @memcpy(rest_range_dest, rest_range);
                } else {
                    @memmove(rest_range_dest, rest_range);
                }
            }
            self.items.len -= range_len;
        }

        pub fn pop(self: *Self) ?T {
            if (self.items.len == 0) return null;
            const val = self.items[self.items.len - 1];
            self.items.len -= 1;
            self.items.ptr[self.items.len] = undefined;
            return val;
        }

        const init_capacity: usize = @max(1, std.atomic.cache_line / @sizeOf(T));
        fn calculateNewCapacity(current: usize, minimum: usize) usize {
            var new = current;
            while (true) {
                new +|= new / 2 + init_capacity;
                if (new >= minimum)
                    return new;
            }
        }
    };
}

pub fn readFileToBytes(filename: []const u8, alloc: std.mem.Allocator) ![]u8 {
    var file = std.fs.cwd().openFile(filename, .{}) catch |e| {
        std.log.err("{s}: {s}", .{ @errorName(e), filename });
        return e;
    };
    defer file.close();
    return file.readToEndAlloc(alloc, 1024 * 1024 * 1024);
}

pub fn timestamp_seed() u64 {
    const ts = std.time.nanoTimestamp();
    const two_vals: [2]u64 = @bitCast(ts);
    return two_vals[0] ^ two_vals[1];
}

pub fn Global(comptime T: type) type {
    return struct {
        var singleton: ?T = null;

        pub fn set(val: T) void {
            if (singleton != null) @panic("Singleton for type " ++ @typeName(T) ++ " already set!");
            singleton = val;
        }
        pub fn unset() void {
            assertSet();
            singleton = null;
        }

        pub fn get() T {
            assertSet();
            return singleton.?;
        }
        fn assertSet() void {
            if (singleton == null) @panic("Singleton for type " ++ @typeName(T) ++ " not set!");
        }
    };
}

// returns true if the type has a function eq(Self, Self) bool
pub fn typeHasEqFn(comptime T: type) bool {
    switch (@typeInfo(T)) {
        .@"struct", .@"enum", .@"union", .@"opaque" => {
            if (!@hasDecl(T, "eq")) return false;
            switch (@typeInfo(@TypeOf(@field(T, "eq")))) {
                .@"fn" => |function| {
                    return function.params.len == 2 and function.params[0].type == T and function.params[1].type == T and function.return_type == bool;
                },
                else => {
                    return false;
                },
            }
        },
        else => return false,
    }
}

pub fn typeIsSimple(comptime T: type) bool {
    return switch (@typeInfo(T)) {
        .int, .float, .bool => true,
        .array => |info| typeIsSimple(info.child),
        .@"struct" => |info| {
            if (info.layout == .@"extern" or info.layout == .@"packed") return true;
            inline for (info.fields) |field_info| {
                if (!typeIsSimple(field_info.type)) return false;
            }
            return true;
        },
        .@"enum" => true,
        .@"union" => |info| info.layout == .@"extern",
        .vector => true,
        .optional => |info| {
            return typeIsSimple(info.child);
        },
        else => false,
    };
}

pub fn typeIsComparable(comptime T: type) bool {
    std.debug.print("{s}", .{@typeName(T)});
    if (typeHasEqFn(T)) return true;

    return switch (@typeInfo(T)) {
        .int, .float, .bool => true,
        .@"struct" => |info| {
            if (info.layout == .@"packed") return true;
            inline for (info.fields) |field_info| {
                if (!typeIsComparable(field_info.type)) return false;
            }
            return true;
        },
        .@"union" => |info| {
            if (info.tag_type == null) return false; // cannot compare untagged union
            inline for (info.fields) |field_info| {
                if (!typeIsComparable(field_info.type)) return false;
            }
            return true;
        },
        .array => |info| {
            return typeIsComparable(info.child);
        },
        .vector => {
            return true;
        },
        .pointer => |info| {
            return switch (info.size) {
                .one, .slice => typeIsComparable(info.child),
                .many, .c => false,
            };
        },
        .optional => |info| {
            return typeIsComparable(info.child);
        },
        else => false,
    };
}

pub fn byteEq(a: anytype, b: @TypeOf(a)) bool {
    const bytes_a = std.mem.asBytes(&a);
    const bytes_b = std.mem.asBytes(&b);
    return std.mem.eql(u8, bytes_a, bytes_b);
}

pub fn eq(a: anytype, b: @TypeOf(a)) bool {
    const T = @TypeOf(a);
    // // use custom `eq` function
    if (comptime typeHasEqFn(T)) return T.eq(a, b);
    // just compare bytes:
    if (comptime typeIsSimple(T)) return byteEq(a, b);
    // do nested compare:
    switch (@typeInfo(T)) {
        .@"struct" => |info| {
            if (info.layout == .@"packed") return a == b;
            inline for (info.fields) |field_info| {
                const field_is_equal = eq(@field(a, field_info.name), @field(b, field_info.name));
                if (!field_is_equal) return false;
            }
            return true;
        },
        .@"union" => |info| {
            if (info.tag_type) |UnionTag| {
                const tag_a: UnionTag = a;
                const tag_b: UnionTag = b;
                if (tag_a != tag_b) return false;

                return switch (a) {
                    inline else => |val, tag| return eq(val, @field(b, @tagName(tag))),
                };
            }
            @compileError("cannot compare untagged union type " ++ @typeName(T));
        },
        .array => {
            if (a.len != b.len) return false;
            for (a, 0..) |e, i|
                if (!eq(e, b[i])) return false;
            return true;
        },
        .vector => {
            @compileError("vectors should always be simple types and this not compared in nested fashion!");
        },
        .pointer => |info| {
            return switch (info.size) {
                .one => return eq(a.*, b.*),
                .slice => {
                    if (a.len != b.len) return false;
                    var i: usize = 0;
                    while (i < a.len) : (i += 1) {
                        if (!eq(a[i], b[i])) return false;
                    }
                    return true;
                },
                .c, .many => @compileError("Cannot compare c or multi pointer"),
            };
        },
        .optional => {
            if (a == null and b == null) return true;
            if (a == null or b == null) return false;
            return eq(a.?, b.?);
        },
        else => @compileError("type cannot be compared:" ++ @typeName(T)),
    }
}

const EMPTY_STRING: [:0]const u8 = "";
pub fn castToCString(str: []const u8) [*:0]const u8 {
    if (str.len == 0) return EMPTY_STRING;
    if (str.ptr[str.len] != 0) std.debug.panicExtra(null, "Expected string to be null terminated but it is not: \"{s}\"!", .{str});
    return @ptrCast(str.ptr);
}

test "eq_string_slice" {
    const str1: []const u8 = "Hello World!";
    var str2 = Array(u8).init();
    defer str2.deinit();
    str2.appendSlice("Hello World!");

    try std.testing.expect(eq(str1, str2.items));
}

// works only for dense enums!
pub fn EnumArray(comptime E: type, comptime T: type) type {
    return struct {
        const len = EnumCount(E);
        default_value: T,
        values: [len]T,

        const Self = @This();
        pub fn init(default_value: T) Self {
            var self: Self = undefined;
            self.default_value = default_value;
            for (&self.values) |*slot| {
                slot.* = default_value;
            }
            return self;
        }
        pub fn clear(self: *Self) void {
            for (self.values) |*slot| {
                slot.* = self.default_value;
            }
        }
        pub inline fn set(self: *Self, key: E, val: T) void {
            self.values[@intFromEnum(key)] = val;
        }
        pub inline fn get(self: Self, key: E) T {
            return self.values[@intFromEnum(key)];
        }
        pub inline fn getPtr(self: *Self, key: E) *T {
            return &self.values[@intFromEnum(key)];
        }
    };
}

// enum allowed to be sparse, but all values need to be >= 0
fn EnumCount(comptime E: type) usize {
    const enum_info = switch (@typeInfo(E)) {
        .@"enum" => |enum_info| enum_info,
        else => @compileError(@typeName(E) ++ " is not enum type!"),
    };
    var max_value: usize = 0;
    for (enum_info.fields) |f| {
        if (f.value < 0) @compileError("enum values should be all > 0 for " ++ @typeName(E));
        const value: usize = @intCast(f.value);
        if (value > max_value) {
            max_value = value;
        }
    }
    return max_value + 1;
}

pub fn combinePaths(
    alloc: std.mem.Allocator,
    parent_file_path: []const u8,
    child_file_path: []const u8,
    parent_is_dir: bool,
) ![]u8 {
    if (std.fs.path.isAbsolute(child_file_path)) {
        return try alloc.dupe(u8, child_file_path);
    }
    const dir = if (parent_is_dir) parent_file_path else (std.fs.path.dirname(parent_file_path) orelse ".");
    const resolved = try std.fs.path.resolve(allocator, &.{ dir, child_file_path });
    // std.debug.print("{s} + {s} = {s}\n", .{ parent_file_path, child_file_path, resolved });
    return resolved;
}

test "combine_paths" {
    const alloc = std.testing.allocator;
    try std.testing.expect(std.mem.eql(u8, try combinePaths(alloc, "shaders/pbr.wgsl", "./utils.wgsl", false), "shaders/utils.wgsl"));
    try std.testing.expect(std.mem.eql(u8, try combinePaths(alloc, "shaders/pbr.wgsl", "utils.wgsl", false), "shaders/utils.wgsl"));
    try std.testing.expect(std.mem.eql(u8, try combinePaths(alloc, "./shaders/pbr.wgsl", "./utils.wgsl", false), "shaders/utils.wgsl"));
    try std.testing.expect(std.mem.eql(u8, try combinePaths(alloc, "./shaders/pbr.wgsl", "../others/utils.wgsl", false), "others/utils.wgsl"));
    try std.testing.expect(std.mem.eql(u8, try combinePaths(alloc, "./shaders/pbr.wgsl", "../../what.wgsl", false), "../what.wgsl"));
}

/// Wrapper around std.HashMap treating the key as bytes. Allows for e.g. floats as keys
pub fn MemHashMap(comptime K: type, V: type) type {
    const Context = struct {
        const Self = @This();
        pub fn hash(_: Self, val: K) u64 {
            return std.hash.Fnv1a_64.hash(&std.mem.toBytes(val));
        }
        pub fn eql(_: Self, a: K, b: K) bool {
            return std.mem.eql(u8, &std.mem.toBytes(a), &std.mem.toBytes(b));
        }
    };
    return std.HashMap(K, V, Context, 80);
}

// Inline Any storage that stores the typeid for typesafe access.
pub fn InlineAny(comptime SIZE: usize, comptime MAX_ALIGN: usize) type {
    return struct {
        data: [SIZE]u8 align(MAX_ALIGN) = undefined,
        ty_id: TypeId = TypeId.none,

        const Self = @This();
        pub fn get(self: *const Self, comptime T: type) ?T {
            // no checkType here, just return null.
            const ty_id = TypeId.of(T);
            if (self.ty_id == ty_id) {
                const data_ptr: *const T = @ptrCast(@alignCast(&self.data));
                return data_ptr.*;
            } else {
                return null;
            }
        }

        pub fn set(self: *Self, comptime T: type, value: T) void {
            comptime {
                checkType(T);
            }
            self.ty_id = TypeId.of(T);
            const data_ptr: *T = @ptrCast(@alignCast(&self.data));
            data_ptr.* = value;
        }

        pub fn unset(self: *Self) void {
            self.data = undefined;
            self.ty_id = TypeId.none;
        }

        pub fn getOrSet(self: *Self, comptime T: type, default_value: T) *T {
            comptime {
                checkType(T);
            }
            const data_ptr: *T = @ptrCast(@alignCast(&self.data));
            const ty_id = TypeId.of(T);
            if (self.ty_id != ty_id) {
                self.ty_id = ty_id;
                data_ptr.* = default_value;
            }
            return data_ptr;
        }

        fn checkType(comptime T: type) void {
            if (@sizeOf(T) > SIZE) @compileError("Type " ++ @typeName(T) ++ " is too large for " ++ @typeName(Self));
            if (@alignOf(T) > MAX_ALIGN) @compileError("Align of Type" ++ @typeName(T) ++ " too large, can be at most 16");
        }
    };
}

// A unique id for each type.
pub const TypeId = enum(u64) {
    none = 0,
    _,

    const Self = @This();

    pub fn of(comptime T: type) Self {
        const ptr = &struct {
            comptime {
                _ = T;
            }
            var id: u8 = undefined;
        }.id;
        return @enumFromInt(@as(u64, @intFromPtr(ptr)));
    }
};
