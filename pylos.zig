const std = @import("std");

const stdin = std.io.getStdIn().reader();
const stdout = std.io.getStdOut().writer();
const stderr = std.io.getStdErr().writer();

const USE_BMOVE: bool = false; // Looks like, for finding the shortest solution, it is better not to use bmove...

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

fn gen_moves(m: Move, c: Colors, t: *Moves) usize {
    const mt = [2]u32{ @intCast(m & 0xffffffff), @intCast(m >> 32) };
    const all = mt[0] | mt[1];
    var nb: usize = 0;
    const one: u64 = 1;
    for (0..4 * 4) |i| {
        const ni = @as(u5, @intCast(i));
        if ((all & (one << ni)) == 0) {
            const ni2: u6 = @as(u6, @intCast(if (c == WHITE) i else i + 32));
            t[i] = m | (one << ni2);
            print_pos(t[i]) catch unreachable;
            nb += 1;
        }
    }
    return nb;
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
        if (depth == base) best_move = bmove;
        if (v_inf == v_sup) return v_inf;
        if (v_inf >= beta) return v_inf;
        if (v_sup <= alpha) return v_sup;
        alpha = @max(alpha, v_inf);
        beta = @min(beta, v_sup);
        hit += 1;
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
        const nb = gen_moves(m, color, &t);
        for (0..nb) |i| {
            const v = ab(a, b, oppcol, maxdepth, depth + 1, base, t[i]);
            if (updateab(color, depth, base, v, &a, &b, &g, t[i], &lmove)) break :outer;
        }
    }
    store(hv, alpha, beta, g, maxdepth - depth, base, lmove);
    return g;
}

fn print_pos(m: Move) !void {
    try stderr.print("move={x}\n", .{m});
    const mt = [2]u32{ @intCast(m & 0xffffffff), @intCast(m >> 32) };
    //    const all = mt[0] | mt[1];
    const one: u64 = 1;
    for (0..16) |i| {
        const ni = @as(u5, @intCast(i));
        if ((mt[0] & (one << ni)) == 1) {
            try stderr.print("X", .{});
        } else if ((mt[1] & (one << ni)) == 1) {
            try stderr.print("O", .{});
        } else {
            try stderr.print(".", .{});
        }
        if ((i % 4) == 3) try stderr.print("\n", .{});
    }
}

pub fn main() !void {
    var args = std.process.args();
    _ = args.next();
    const sturn = args.next().?;
    var turn = std.fmt.parseInt(u8, sturn, 10) catch 0;
    if ((turn != 1) and (turn != 2)) std.posix.exit(255);

    const allocator = std.heap.page_allocator;
    const RndGen = std.Random.DefaultPrng;
    hashes = try allocator.alloc(HashElem, HASH_SIZE);
    defer allocator.free(hashes);
    for (hashes) |*a| a.* = ZHASH;
    var rnd = RndGen.init(0);
    for (0..NB_COLS) |i| {
        for (0..NB_LEVELS) |j| {
            const one: usize = 1;
            const nj: u6 = @as(u6, @intCast(j * j));
            const nb: usize = one << nj;
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
    var oppmove: Move = undefined;
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
            while ((maxdepth - base <= 2) and (@abs(ret) < Bwin)) {
                best_move = InvalidMove;
                t = std.time.milliTimestamp();
                hit = 0;
                nodes = 0;
                ret = ab(Vals_min, Vals_max, color, maxdepth, base, base, m);
                if (best_move == InvalidMove) break;
                t = std.time.milliTimestamp() - t;
                total_time += t;
                try stderr.print("depth={d} t={d}ms ret={d} nodes={d} hit={d} best_move={d}\n", .{ maxdepth - base, t, ret, nodes, hit, best_move });
                maxdepth += 1;
            }
            try print_pos(best_move);
            m = best_move;
            base += 1;
            color = if (color == WHITE) BLACK else WHITE;
        }
        turn = 1;
        while (true) {
            try stderr.print("Your move:", .{});
            if (try stdin.readUntilDelimiterOrEof(&buf, '\n')) |v| oppmove = std.fmt.parseInt(Move, v, 10) catch InvalidMove;
            m = oppmove;
            break;
        }
        try print_pos(oppmove);
        base += 1;
        color = if (color == WHITE) BLACK else WHITE;
    }
}

//const Inner = struct { a: u32, b: bool };
//var toto = [_][20]Inner{[_]Inner{.{ .a = 1, .b = true }} ** 20} ** 10;
