const std = @import("std");
const base = @import("base");

const TypeId = base.TypeId;
const InlineAny = base.InlineAny(24, 8);

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
}

const Foo = struct {
    age: u32,
    name: []const u8,
};
