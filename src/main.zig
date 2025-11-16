const std = @import("std");
const base = @import("base");

const TypeId = base.TypeId;
const InlineAny = base.InlineAny(24, 8);
const UtfChar = base.UtfChar;

pub fn main() !void {
    // example of using TypeId:
    std.debug.print(
        "Foo: {}\nu32: {}\nbool: {}\nTypeId: {}\n",
        .{
            TypeId.of(Foo), TypeId.of(u32), TypeId.of(bool), TypeId.of(TypeId),
        },
    );

    // example of using InlineAny:
    var any: InlineAny = .{};
    any.set(Foo, Foo{ .age = 7, .name = "Harald" });
    std.debug.print("Foo: {any}\n", .{any.get(Foo)});
    const num = any.getOrSet(u32, 99);
    std.debug.print("Num before: {any}\n", .{num.*});
    num.* += 123;
    std.debug.print("Num after: {any}\n", .{any.get(u32)});
    std.debug.print("Foo: {any}\n", .{any.get(Foo)});

    // example replace range:

    var nums = base.Array(u32).init();
    nums.reserve(8);
    nums.appendSlice(&.{ 0, 1, 2, 3, 4, 5, 6 });
    std.debug.print("nums: {any}   cap: {}\n", .{ nums.items, nums.cap });
    nums.replaceRange(2, 2, &.{ 99, 99, 99, 99 });
    std.debug.print("nums: {any}   cap: {}\n", .{ nums.items, nums.cap });
    nums.replaceRange(3, 3, &.{77});
    std.debug.print("nums: {any}   cap: {}\n", .{ nums.items, nums.cap });

    nums.replaceRange(7, 0, &.{ 1, 2, 3 });
    std.debug.print("nums: {any}   cap: {}\n", .{ nums.items, nums.cap });

    const other = UtfChar.of('U');
    std.debug.print("other: {s}\n", .{other.get()});

    mainBucketArrayExample();
}

const Foo = struct {
    age: u32,
    name: []const u8,
};

fn mainBucketArrayExample() void {
    var bucket_arr = base.BucketArray(u32){};
    defer bucket_arr.deinit();

    var element_pointers: base.Array(*u32) = .{};

    for (0..100) |i| {
        const el_ptr = bucket_arr.append(@intCast(i));
        element_pointers.append(el_ptr);
    }
    _ = bucket_arr.append(999);

    std.debug.print("Added all the numbers:\n", .{});
    var iter = bucket_arr.iterator();
    while (iter.next()) |v| {
        std.debug.print("{*} = {}\n", .{ v, v.* });
    }

    var rng = std.Random.DefaultPrng.init(3293292);

    var n_freed: usize = 0;
    for (element_pointers.items) |ptr| {
        if (std.Random.float(rng.random(), f32) > 0.4) {
            std.debug.print("Try free {}\n", .{ptr.*});
            base.BucketArray(u32).free(ptr);
            n_freed += 1;
        }
    }

    // for (0..n_freed) |i| {
    //     _ = bucket_arr.append(100000 + @as(u32, @intCast(i)));
    // }

    std.debug.print("Removed some numbers and filled back with 1000xx:\n", .{});
    iter = bucket_arr.iterator();
    var i: usize = 0;
    while (iter.next()) |v| {
        const bucket_id = base.BucketArray(u32).locate(v).bucket.id;
        std.debug.print("{}:  in bucket {}   {*} = {}\n", .{ i, bucket_id, v, v.* });
        i += 1;
    }
}
