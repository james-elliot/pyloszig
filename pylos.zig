const std = @import("std");

//const allocator = std.heap.page_allocator;

var gpa = std.heap.GeneralPurposeAllocator(.{}){};
const allocator = gpa.allocator();

const stdin = std.io.getStdIn().reader();
const stdout = std.io.getStdOut().writer();
const stderr = std.io.getStdErr().writer();

const o64: u64 = 1;
const o32: u32 = 1;

// Looks like, for finding the shortest solution, it is better not to use bmove...
const USE_BMOVE: bool = false;

// 27 bits use 2GB
const NB_BITS: u8 = 25;

const Vals = i16;
const Vals_min: Vals = std.math.minInt(Vals);
const Vals_max: Vals = std.math.maxInt(Vals);
const Depth = u8;
const Colors = u1;
const Sigs = u64;
// Level 0
//  0  1  2  3
//  4  5  6  7
//  8  9 10 11
// 12 13 14 15
// Level 1
// 16 17 18
// 19 20 21
// 22 23 24
// Level 2
// 25 26
// 27 28
// Level 3
// 29
// bit  0:15 level 0 white, 16:24 level 1 white, 25:28 level 2 white, 29: level 3 white
// bit 32:47 level 0 black, 48:56 level 1 black, 57:60 level 2 black, 61: level 3 black
const Move = u64;
const Move2 = packed struct { low: u32, high: u32 };
const Move3 = [2]u32;
const InvalidMove: Move = std.math.maxInt(Move);
const Win = Vals_max - 1;
const Bwin = Win - 1;
const WHITE: Colors = 0;
const BLACK: Colors = 1;
const NB_COLS: usize = @as(usize, @intCast(BLACK)) + 1;
const NB_LEVELS: usize = 4;
const Moves = [64]Move;
const MAX_PAWNS: u64 = 15;

const HASH_SIZE: usize = 1 << NB_BITS;
const HASH_MASK: Sigs = HASH_SIZE - 1;
var hashesv: [NB_COLS][NB_LEVELS][]Sigs = undefined;
var hash_black: Sigs = undefined;

const HashElem = packed struct {
    sig: Sigs,
    v_inf: Vals,
    v_sup: Vals,
    base: Depth,
    dist: Depth,
    bmove: Move,
};

const ZHASH = HashElem{
    .sig = 0,
    .v_inf = Vals_min,
    .v_sup = Vals_max,
    .base = 0,
    .dist = 0,
    .bmove = InvalidMove,
};

var hashes: []HashElem = undefined;

fn retrieve(hv: Sigs, v_inf: *Vals, v_sup: *Vals, bmove: *Move, dist: Depth) bool {
    const ind: usize = hv & HASH_MASK;
    if (hashes[ind].sig == hv) {
        bmove.* = hashes[ind].bmove;
        if (hashes[ind].dist == dist) {
            v_inf.* = hashes[ind].v_inf;
            v_sup.* = hashes[ind].v_sup;
            //            return true;
            return false;
        }
    }
    return false;
}

fn store(hv: Sigs, alpha: Vals, beta: Vals, g: Vals, dist: Depth, base: Depth, bmove: Move) void {
    const ind = hv & HASH_MASK;
    if ((hashes[ind].base != base) or (hashes[ind].dist <= dist)) {
        if ((hashes[ind].sig != hv) or (hashes[ind].dist != dist)) {
            hashes[ind].dist = dist;
            hashes[ind].v_inf = Vals_min;
            hashes[ind].v_sup = Vals_max;
            hashes[ind].sig = hv;
        }
        hashes[ind].base = base;
        hashes[ind].bmove = bmove;
        if ((g > alpha) and (g < beta)) {
            hashes[ind].v_inf = g;
            hashes[ind].v_sup = g;
        } else if (g <= alpha) {
            hashes[ind].v_sup = @min(g, hashes[ind].v_sup);
        } else if (g >= beta) {
            hashes[ind].v_inf = @max(g, hashes[ind].v_inf);
        }
    }
}

fn compute_hash(m: Move, color: Colors) Sigs {
    //    var h: Sigs = 0;
    if (m == 0) return 0;
    if (color == 0) return 0;
    return 0;
}

var best_move: Move = undefined;
fn updateab(color: Colors, depth: Depth, base: Depth, v: Vals, a: *Vals, b: *Vals, g: *Vals, p: u64, lmove: *Move) bool {
    if (color == WHITE) {
        if (v > g.*) {
            g.* = v;
            lmove.* = @as(Move, @intCast(p));
            if (depth == base) best_move = lmove.*;
        }
        a.* = @max(a.*, g.*);
    } else {
        if (v < g.*) {
            g.* = v;
            lmove.* = @as(Move, @intCast(p));
            if (depth == base) best_move = lmove.*;
        }
        b.* = @min(b.*, g.*);
    }
    return (a.* >= b.*);
}

fn eval(m: Move, c: Colors) Vals {
    const mt = [2]u32{ @intCast(m & 0xffffffff), @intCast(m >> 32) };
    if (@popCount(mt[c]) == MAX_PAWNS) {
        if (c == WHITE) return -Win / 3 else return Win / 3;
    }
    return 0;
}

const MaskB = [30]std.ArrayList(u32);
const MaskU = [30]u32;
const MaskO = [30]u32;
// mbs[i] is an array of all the masks of the squares that contains pos i
var mbs: MaskB = undefined;
// mus[i] is a mask of all positions under pos i
// useful to know if it is possible to play a marble on i (all positions below must be occupied)
var mus: MaskU = [_]u32{0} ** 30;
// mos[i] is a mask of all positions over pos i
// useful to know if a marble in i can be moved elsewhere (all positions over must be unoccupied)
var mos: MaskO = [_]u32{0} ** 30;

fn set_bits(n: u8, t: []u8) void {
    const nn = @as(u5, @intCast(n));
    for (t) |v| {
        const nv = @as(u5, @intCast(v));
        mus[n] |= o32 << nv;
        mos[v] |= o32 << nn;
    }
    for (t) |v| {
        mbs[v].append(mus[n]) catch unreachable;
    }
}

fn init_squares() void {
    for (0..30) |i| {
        mbs[i] = std.ArrayList(u32).init(allocator);
    }
    set_bits(16, @constCast(&[_]u8{ 0, 1, 4, 5 }));
    set_bits(17, @constCast(&[_]u8{ 1, 2, 5, 6 }));
    set_bits(18, @constCast(&[_]u8{ 2, 3, 6, 7 }));
    set_bits(19, @constCast(&[_]u8{ 4, 5, 8, 9 }));
    set_bits(20, @constCast(&[_]u8{ 5, 6, 9, 10 }));
    set_bits(21, @constCast(&[_]u8{ 6, 7, 10, 11 }));
    set_bits(22, @constCast(&[_]u8{ 8, 9, 12, 13 }));
    set_bits(23, @constCast(&[_]u8{ 9, 10, 13, 14 }));
    set_bits(24, @constCast(&[_]u8{ 10, 11, 14, 15 }));

    set_bits(25, @constCast(&[_]u8{ 16, 17, 19, 20 }));
    set_bits(26, @constCast(&[_]u8{ 17, 18, 20, 21 }));
    set_bits(27, @constCast(&[_]u8{ 19, 20, 22, 23 }));
    set_bits(28, @constCast(&[_]u8{ 20, 21, 23, 24 }));

    set_bits(29, @constCast(&[_]u8{ 25, 26, 27, 28 }));

    //    for (mbs[9].items, 0..) |v, i| {
    //        stderr.print("Pos:{d}\n", .{i}) catch unreachable;
    //        print_pos(v) catch unreachable;
    //    }
}

fn free_pos(m: u32, all: u32) u32 {
    var f: u32 = 0;
    var vm = m;
    while (vm != 0) {
        const i = @as(u5, @intCast(@ctz(vm)));
        vm ^= (o32 << i);
        if ((all & mos[i]) == 0) {
            f |= (o32 << i);
        }
    }
    return f;
}

fn gen_moves(m: Move, c: Colors, tb: *Moves, nb: *usize, tg: *Moves, ng: *usize) void {
    const mt = [2]u32{ @intCast(m & 0xffffffff), @intCast(m >> 32) };
    const all = mt[0] | mt[1];
    var nall = ~all & 0x3fffffff;
    const have_mar = @popCount(mt[c]) < MAX_PAWNS;
    const free = free_pos(mt[c], all);

    nb.* = 0;
    ng.* = 0;
    while (nall != 0) {
        const i = @ctz(nall);
        nall ^= (o32 << @as(u5, @intCast(i)));
        if ((i < 16) or ((mus[i] & all) == mus[i])) {
            const ni2 = if (c == WHITE) i else i + 32;
            if (have_mar) {
                tb[nb.*] = m | (o64 << ni2);
                nb.* += 1;
            }
            if (i >= 16) {
                //Attention a penser à ne pas prendre les billes du carré elles-mêmes
                var f = free;
                while (f != 0) {
                    const j = @ctz(f);
                    f ^= o32 << @as(u5, @intCast(j));
                    const nj = if (c == WHITE) j else j + 32;
                    tg[ng.*] = (m ^ (o64 << nj)) | (o64 << ni2);
                    ng.* += 1;
                }
            }
        }
    }
}

var hit: u64 = 0;
var nodes: u64 = 0;
fn ab(alp: Vals, bet: Vals, color: Colors, maxdepth: Depth, depth: Depth, base: Depth, m: Move) Vals {
    const oppcol = 1 - color;
    if (depth == maxdepth) return eval(m, color);
    nodes += 1;
    var alpha = alp;
    var beta = bet;
    var bmove: Move = InvalidMove;
    const hv = compute_hash(m, color);
    var v_inf: Vals = undefined;
    var v_sup: Vals = undefined;
    if (retrieve(hv, &v_inf, &v_sup, &bmove, maxdepth - depth)) {
        if (depth == 255) {
            if (depth == base) best_move = bmove;
            if (v_inf == v_sup) return v_inf;
            if (v_inf >= beta) return v_inf;
            if (v_sup <= alpha) return v_sup;
            alpha = @max(alpha, v_inf);
            beta = @min(beta, v_sup);
            hit += 1;
        }
    }

    if (!USE_BMOVE) bmove = InvalidMove;

    var a = alpha;
    var b = beta;
    var lmove: Move = InvalidMove;

    var g: Vals = if (color == WHITE) Vals_min else Vals_max;
    outer: {
        if (bmove != InvalidMove) {
            const v = ab(a, b, oppcol, maxdepth, depth + 1, base, bmove);
            if (updateab(color, depth, base, v, &a, &b, &g, bmove, &lmove)) break :outer;
        }
        var t: Moves = undefined;
        var nb: usize = undefined;
        var tg: Moves = undefined;
        var ng: usize = undefined;
        gen_moves(m, color, &t, &nb, &tg, &ng);
        if (nb == 0) if (color == WHITE) return -Win else return Win;
        stderr.print("nb={d}\n", .{nb}) catch unreachable;
        for (0..nb) |i| {
            const v = ab(a, b, oppcol, maxdepth, depth + 1, base, t[i]);
            stderr.print("i={d} v={d} m={x}\n", .{ i, v, t[i] }) catch unreachable;
            if (updateab(color, depth, base, v, &a, &b, &g, t[i], &lmove)) break :outer;
            stderr.print("a={d} b={d} g={d} best={x}\n", .{ a, b, g, best_move }) catch unreachable;
        }
    }
    store(hv, alpha, beta, g, maxdepth - depth, base, lmove);
    return g;
}

fn print_level(m: Move, l: usize) !void {
    const mt = [2]u32{ @intCast(m & 0xffffffff), @intCast(m >> 32) };
    const all = mt[0] | mt[1];
    //    const mt2: *Move3 = @ptrCast(@constCast(&m));
    //    if (mt2[0] == mt[0]) try stderr.print("Ok\n", .{}) else try stderr.print("NOk\n", .{});
    const size: usize = (4 - l);
    var base: usize = 0;
    const freew = free_pos(mt[0], all);
    const freeb = free_pos(mt[1], all);
    for (0..l) |j| {
        base += (4 - j) * (4 - j);
    }
    try stderr.print("Level={d}\n", .{l});
    for (0..size * size) |i| {
        if ((i % size) == 0) try stderr.print("{d:2}:", .{i + base + 1});
        const ni = @as(u5, @intCast(i + base));
        if ((mt[0] & (o32 << ni)) != 0) {
            if ((freew & (o32 << ni)) != 0) try stderr.print(" X", .{}) else try stderr.print(" x", .{});
        } else if ((mt[1] & (o32 << ni)) != 0) {
            if ((freeb & (o32 << ni)) != 0) try stderr.print(" O", .{}) else try stderr.print(" o", .{});
        } else {
            try stderr.print(" .", .{});
        }
        if ((i % size) == (size - 1)) try stderr.print("\n", .{});
    }
}

fn print_pos(m: Move) !void {
    try stderr.print("pos={x}\n", .{m});
    for (0..4) |i| {
        try print_level(m, i);
    }
}

pub fn main() !void {
    var args = std.process.args();
    _ = args.next();
    const sturn = args.next().?;
    var turn = std.fmt.parseInt(u8, sturn, 10) catch 0;
    if ((turn != 1) and (turn != 2)) std.posix.exit(255);

    init_squares();

    const RndGen = std.Random.DefaultPrng;
    hashes = try allocator.alloc(HashElem, HASH_SIZE);
    defer allocator.free(hashes);
    for (hashes) |*a| a.* = ZHASH;
    var rnd = RndGen.init(0);
    for (0..NB_COLS) |i| {
        for (0..NB_LEVELS) |j| {
            const nj: u6 = @as(u6, @intCast(j * j));
            const nb: usize = o64 << nj;
            hashesv[i][j] = try allocator.alloc(Sigs, nb);
            for (0..nb) |k| {
                hashesv[i][j][k] = rnd.random().int(Sigs);
            }
        }
    }
    hash_black = rnd.random().int(Sigs);

    var base: Depth = 0;
    var t: i64 = undefined;
    var ret: Vals = undefined;
    var buf: [1000]u8 = undefined;
    var oppmove: i64 = undefined;
    var color: Colors = undefined;
    var maxdepth: Depth = undefined;
    var m: Move = 0;
    color = if (turn == 1) WHITE else BLACK;
    while (true) {
        if (turn == 1) {
            var total_time: i64 = 0;
            maxdepth = base + 1;
            ret = 0;
            //            while ((total_time < 2000) and (@abs(ret) < Bwin)) {
            while ((maxdepth - base <= 1) and (@abs(ret) < Bwin)) {
                best_move = InvalidMove;
                t = std.time.milliTimestamp();
                hit = 0;
                nodes = 0;
                ret = ab(Vals_min, Vals_max, color, maxdepth, base, base, m);
                if (best_move == InvalidMove) {
                    try stderr.print("Game Lost\n", .{});
                    std.posix.exit(0);
                }
                t = std.time.milliTimestamp() - t;
                total_time += t;
                try stderr.print("depth={d} t={d}ms ret={d} nodes={d} hit={d} best_move={x}\n", .{ maxdepth - base, t, ret, nodes, hit, best_move });
                maxdepth += 1;
            }
            try print_pos(best_move);
            m = best_move;
            base += 1;
            color = if (color == WHITE) BLACK else WHITE;
        }
        turn = 1;
        var mt = [2]u32{ @intCast(m & 0xffffffff), @intCast(m >> 32) };
        var newpos = m;
        var tb: Moves = undefined;
        var nb: usize = undefined;
        var tg: Moves = undefined;
        var ng: usize = undefined;
        gen_moves(m, color, &tb, &nb, &tg, &ng);
        if (nb == 0) {
            try stderr.print("Game Won\n", .{});
            std.posix.exit(0);
        }
        outer: while (true) {
            while (true) {
                try stderr.print("Your move:", .{});
                if (try stdin.readUntilDelimiterOrEof(&buf, '\n')) |v| oppmove = std.fmt.parseInt(i64, v, 10) catch 64;
                if (@abs(oppmove) < 31) break;
            }
            if (oppmove == 0) {
                for (0..nb) |i| {
                    if (newpos == tb[i]) {
                        try stderr.print("Valid move\n", .{});
                        break :outer;
                    }
                }
                try stderr.print("Invalid move\n", .{});
                mt = [2]u32{ @intCast(m & 0xffffffff), @intCast(m >> 32) };
            } else if (oppmove < 0) {
                oppmove += 1;
                const move: u5 = @intCast(-oppmove);
                if ((mt[color] & (o32 << move)) != 0) mt[color] ^= (o32 << move);
            } else {
                oppmove -= 1;
                const move: u5 = @intCast(oppmove);
                if (((mt[0] | mt[1]) & (o32 << move)) == 0) mt[color] ^= (o32 << move);
            }
            newpos = @as(u64, @intCast(mt[0])) | (@as(u64, @intCast(mt[1])) << 32);
            try print_pos(newpos);
        }
        try stderr.print("Coucou\n", .{});
        m = newpos;
        try print_pos(m);
        base += 1;
        color = if (color == WHITE) BLACK else WHITE;
    }
}

//const Inner = struct { a: u32, b: bool };
//var toto = [_][20]Inner{[_]Inner{.{ .a = 1, .b = true }} ** 20} ** 10;
