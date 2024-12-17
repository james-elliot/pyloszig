const std = @import("std");
const C = std.c;

//const allocator = std.heap.page_allocator;
var gpa = std.heap.GeneralPurposeAllocator(.{}){};
const allocator = gpa.allocator();

const stdin = std.io.getStdIn().reader();
const stdout = std.io.getStdOut().writer();
const stderr = std.io.getStdErr().writer();

const o64: u64 = 1;
const o32: u32 = 1;
const o16: u16 = 1;

const USE_HASH: bool = true;
const USE_BPOS: bool = true;
const CHECK_BPOS: bool = false;
// 27 bits use 2GB
const NB_BITS: u8 = 26;

const Vals = i16;
const Vals_min: Vals = std.math.minInt(Vals);
const Vals_max: Vals = std.math.maxInt(Vals);
const GET_OUT = Vals_min;
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
const Pos = u64;
const Pos2 = [2]u32;
const Pos4 = [4]u16;
const InvalidPos: Pos = std.math.maxInt(Pos);
const Win = 32700;
const Bwin = 32600;
const WHITE: Colors = 0;
const BLACK: Colors = 1;
const NB_COLS: usize = @as(usize, @intCast(BLACK)) + 1;
const NB_LEVELS: usize = 4;
const Poss = [256]Pos;
const MAX_PAWNS: u64 = 15;

const HASH_SIZE: usize = 1 << NB_BITS;
const HASH_MASK: Sigs = HASH_SIZE - 1;
var hashesv: [4][1 << 16]Sigs = undefined;
var hash_black: Sigs = undefined;
var hash_init: Sigs = undefined;

const HashElem = packed struct {
    sig: Sigs,
    v_inf: Vals,
    v_sup: Vals,
    base: Depth,
    dist: Depth,
    bpos: Pos,
};

const ZHASH = HashElem{
    .sig = 0,
    .v_inf = -Vals_max,
    .v_sup = Vals_max,
    .base = 0,
    .dist = 0,
    .bpos = InvalidPos,
};

var hashes: []HashElem = undefined;

fn retrieve(hv: Sigs, v_inf: *Vals, v_sup: *Vals, bpos: *Pos, dist: Depth) bool {
    const ind: usize = hv & HASH_MASK;
    if (hashes[ind].sig == hv) {
        bpos.* = hashes[ind].bpos;
        if (hashes[ind].dist == dist) {
            v_inf.* = hashes[ind].v_inf;
            v_sup.* = hashes[ind].v_sup;
            return true;
        }
    }
    return false;
}

fn store(hv: Sigs, alpha: Vals, beta: Vals, g: Vals, dist: Depth, base: Depth, bpos: Pos) void {
    const ind = hv & HASH_MASK;
    if ((hashes[ind].base != base) or (hashes[ind].dist <= dist)) {
        if ((hashes[ind].sig != hv) or (hashes[ind].dist != dist)) {
            hashes[ind].dist = dist;
            hashes[ind].v_inf = -Vals_max;
            hashes[ind].v_sup = Vals_max;
            hashes[ind].sig = hv;
        }
        hashes[ind].base = base;
        hashes[ind].bpos = bpos;
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

fn compute_sym() void {
    for (0..1 << 16) |n| {
        const v = @as(u16, n);
        var nv: u16 = 0;
        while (v != 0) {
            const i = @ctz(n);
            v ^= (o16 << i);
            nv |= (o16 << (16 - i));
        }
    }
}

fn compute_hash(m: Pos, color: Colors) Sigs {
    const p: Pos4 = @bitCast(m);
    const v = hash_init ^ hashesv[0][p[0]] ^ hashesv[1][p[1]] ^ hashesv[2][p[2]] ^ hashesv[3][p[3]];
    if (color == WHITE) return v else return v ^ hash_black;
}

var best_pos: Pos = undefined;
fn updateab(color: Colors, depth: Depth, base: Depth, v: Vals, a: *Vals, b: *Vals, g: *Vals, p: Pos, lpos: *Pos) bool {
    if (color == WHITE) {
        if (v > g.*) {
            g.* = v;
            lpos.* = p;
            if (depth == base) best_pos = lpos.*;
        }
        a.* = @max(a.*, g.*);
    } else {
        if (v < g.*) {
            g.* = v;
            lpos.* = p;
            if (depth == base) best_pos = lpos.*;
        }
        b.* = @min(b.*, g.*);
    }
    return (a.* >= b.*);
}

fn eval(m: Pos) Vals {
    const mt: Pos2 = @bitCast(m);
    return @as(Vals, @popCount(mt[1])) - @as(Vals, @popCount(mt[0]));
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
// useful to know if a marble in i can be posd elsewhere (all positions over must be unoccupied)
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

//Check if marble of color c put at pos p which has generated position m makes one (or more) "same color" squares
fn gen_dbsquare(c: Colors, p: usize, m: Pos, t: *Poss, n: *usize) void {
    const mt: Pos2 = @bitCast(m);
    var free: ?u32 = null;
    var n0: usize = 0;
    var t0: Poss = undefined;
    for (mbs[p].items) |v| outer: {
        if (v & mt[c] == v) {
            if (free == null) free = free_pos(mt[c], mt[0] | mt[1]);
            var mask: u32 = v & free.?;
            while (mask != 0) {
                const i = @ctz(mask);
                mask ^= (o32 << @as(u5, @intCast(i)));
                const ni = if (c == WHITE) i else i + 32;
                var mask2 = mask;
                while (mask2 != 0) {
                    const j = @ctz(mask2);
                    mask2 ^= (o32 << @as(u5, @intCast(j)));
                    const nj = if (c == WHITE) j else j + 32;
                    t[n.*] = m ^ (o64 << ni) ^ (o64 << nj);
                    n.* += 1;
                    if (n.* == t.len) break :outer;
                }
                t0[n0] = (m ^ (o64 << ni));
                n0 += 1;
            }
        }
    }
    if ((n0 + n.*) >= t.len) {
        stderr.print("p={d} c={d}\n", .{ p, c }) catch unreachable;
        C.exit(255);
    }
    for (0..n0) |i| {
        t[n.*] = t0[i];
        n.* += 1;
    }
}

fn gen_poss(m: Pos, c: Colors, tb: *Poss, nb: *usize, tg: *Poss, ng: *usize, tv: *Poss, nv: *usize) void {
    const mt: Pos2 = @bitCast(m);
    const all = mt[0] | mt[1];
    var nall = ~all & 0x3fffffff;
    const have_marbles = @popCount(mt[c]) < MAX_PAWNS;
    const free = free_pos(mt[c], all);
    nv.* = 0;
    nb.* = 0;
    ng.* = 0;
    while (nall != 0) {
        const i = @ctz(nall);
        nall ^= (o32 << @as(u5, @intCast(i)));
        if ((i < 16) or ((mus[i] & all) == mus[i])) {
            const ni2 = if (c == WHITE) i else i + 32;
            if (have_marbles) {
                const nm = m | (o64 << ni2);
                tb[nb.*] = nm;
                nb.* += 1;
                gen_dbsquare(c, i, nm, tv, nv);
            }
            if (i >= 16) {
                //Attention a penser à ne pas prendre les billes du carré elles-mêmes
                var f = free & ~mus[i];
                while (f != 0) {
                    const j = @ctz(f);
                    f ^= o32 << @as(u5, @intCast(j));
                    // Marble must go one level up
                    if ((j <= 15) or ((i >= 25) and (j <= 24)) or (i == 29)) {
                        // stderr.print("i:{d} j:{d}\n", .{ i, j }) catch unreachable;
                        const nj = if (c == WHITE) j else j + 32;
                        const nm2 = (m ^ (o64 << nj)) | (o64 << ni2);
                        tg[ng.*] = nm2;
                        ng.* += 1;
                        gen_dbsquare(c, i, nm2, tv, nv);
                    }
                }
            }
        }
    }
}

var hit: u64 = 0;
var nodes: u64 = 0;
fn ab(alp: Vals, bet: Vals, color: Colors, maxdepth: Depth, depth: Depth, base: Depth, m: Pos) Vals {
    const oppcol = 1 - color;
    if (depth == maxdepth) return eval(m);
    nodes += 1;
    var alpha = alp;
    var beta = bet;
    var bpos: Pos = InvalidPos;
    var cpos: Pos = InvalidPos;
    const hv = compute_hash(m, color);
    var v_inf: Vals = undefined;
    var v_sup: Vals = undefined;
    if (USE_HASH and (retrieve(hv, &v_inf, &v_sup, &bpos, maxdepth - depth))) {
        cpos = bpos;
        if (depth == base) best_pos = bpos;
        if (v_inf == v_sup) return v_inf;
        if (v_inf >= beta) return v_inf;
        if (v_sup <= alpha) return v_sup;
        alpha = @max(alpha, v_inf);
        beta = @min(beta, v_sup);
        hit += 1;
        if (!USE_BPOS) bpos = InvalidPos;
    }

    var a = alpha;
    var b = beta;
    var lpos: Pos = InvalidPos;

    var g: Vals = if (color == WHITE) -Vals_max else Vals_max;
    outer: {
        if (bpos != InvalidPos) {
            const v = ab(a, b, oppcol, maxdepth, depth + 1, base, bpos);
            if (get_out) return GET_OUT;
            if (updateab(color, depth, base, v, &a, &b, &g, bpos, &lpos)) break :outer;
        }
        var tb: Poss = undefined;
        var nb: usize = undefined;
        var tg: Poss = undefined;
        var ng: usize = undefined;
        var tv: Poss = undefined;
        var nv: usize = undefined;
        gen_poss(m, color, &tb, &nb, &tg, &ng, &tv, &nv);
        inner: {
            if ((CHECK_BPOS) and (cpos != InvalidPos)) {
                for (0..nv) |i|
                    if (cpos == tv[i]) break :inner;
                for (0..ng) |i|
                    if (tg[i] != bpos) break :inner;
                for (0..nb) |i|
                    if (tb[i] != bpos) break :inner;
                stderr.print("Groumpf\n", .{}) catch unreachable;
            }
        }
        if ((nb + ng) == 0) {
            const mt: Pos2 = @bitCast(m);
            const v = @as(Vals, @popCount(mt[1])) - @as(Vals, @popCount(mt[0]));
            if (color == WHITE) return -Win + v else return Win + v;
        }
        for (0..nv) |i| {
            if (tv[i] != bpos) {
                const v = ab(a, b, oppcol, maxdepth, depth + 1, base, tv[i]);
                if (get_out) return GET_OUT;
                if (updateab(color, depth, base, v, &a, &b, &g, tv[i], &lpos)) break :outer;
            }
        }
        for (0..ng) |i| {
            if (tg[i] != bpos) {
                const v = ab(a, b, oppcol, maxdepth, depth + 1, base, tg[i]);
                if (get_out) return GET_OUT;
                if (updateab(color, depth, base, v, &a, &b, &g, tg[i], &lpos)) break :outer;
            }
        }
        for (0..nb) |i| {
            if (tb[i] != bpos) {
                const v = ab(a, b, oppcol, maxdepth, depth + 1, base, tb[i]);
                if (get_out) return GET_OUT;
                if (updateab(color, depth, base, v, &a, &b, &g, tb[i], &lpos)) break :outer;
            }
        }
    }
    store(hv, alpha, beta, g, maxdepth - depth, base, lpos);
    return g;
}

fn print_level(m: Pos, l: usize) !void {
    const mt: Pos2 = @bitCast(m);
    const all = mt[0] | mt[1];
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

fn print_pos(m: Pos) !void {
    try stderr.print("pos={x}\n", .{m});
    for (0..4) |i| {
        try print_level(m, i);
    }
}

fn essai() !void {
    const m: u64 = 0x942900102a42;
    try print_pos(m);
    var tb: Poss = undefined;
    var nb: usize = undefined;
    var tg: Poss = undefined;
    var ng: usize = undefined;
    var tv: Poss = undefined;
    var nv: usize = undefined;
    gen_poss(m, 0, &tb, &nb, &tg, &ng, &tv, &nv);
    try stderr.print("nb={d} ng={d} nv={d}\n", .{ nb, ng, nv });
    C.exit(255);
}

var get_out: bool = false;
pub fn update_out(s: i32) callconv(.c) void {
    if (s == C.SIG.ALRM) get_out = true;
}

pub fn main() !void {
    var args = std.process.args();
    _ = args.next();
    const sturn = args.next().?;
    var turn = std.fmt.parseInt(u8, sturn, 10) catch 0;
    if ((turn != 1) and (turn != 2)) {
        try stderr.print("turn is 1 or 2\n", .{});
        C.exit(255);
    }
    const stime = args.next().?;
    const time = std.fmt.parseInt(u32, stime, 10) catch 0;
    if (time == 0) {
        try stderr.print("time is >0\n", .{});
        C.exit(255);
    }

    const sigact = C.Sigaction{
        .handler = .{ .handler = update_out },
        //        .handler = .{ .handler = C.SIG.DFL },
        .mask = C.empty_sigset,
        .flags = 0,
    };
    const sres = C.sigaction(std.c.SIG.ALRM, &sigact, null);
    if (sres != 0) {
        try stderr.print("Can't install handler\n", .{});
        C.exit(255);
    }

    init_squares();
    //    try essai();

    const RndGen = std.Random.DefaultPrng;
    hashes = try allocator.alloc(HashElem, HASH_SIZE);
    defer allocator.free(hashes);
    for (hashes) |*a| a.* = ZHASH;
    var rnd = RndGen.init(0);
    for (0..4) |i| {
        for (0..1 << 16) |j| {
            hashesv[i][j] = rnd.random().int(Sigs);
        }
    }
    hash_black = rnd.random().int(Sigs);
    hash_init = rnd.random().int(Sigs);

    var base: Depth = 0;
    var t: i64 = undefined;
    var ret: Vals = undefined;
    var buf: [1000]u8 = undefined;
    var opppos: i64 = undefined;
    var color: Colors = if (turn == 1) WHITE else BLACK;
    var maxdepth: Depth = undefined;
    var m: Pos = 0;
    while (true) {
        if (turn == 1) {
            var total_time: i64 = 0;
            maxdepth = base + 1;
            ret = 0;
            _ = C.alarm(time);
            get_out = false;
            var old_best = InvalidPos;
            while (!get_out and (@abs(ret) < Bwin)) {
                //while ((total_time < 10000) and (@abs(ret) < Bwin)) {
                //while ((maxdepth - base <= 1) and (@abs(ret) < Bwin)) {
                best_pos = InvalidPos;
                t = std.time.milliTimestamp();
                hit = 0;
                nodes = 0;
                ret = ab(-Vals_max, Vals_max, color, maxdepth, base, base, m);
                if (get_out) best_pos = old_best else old_best = best_pos;
                if (best_pos == InvalidPos) {
                    try stderr.print("Game Lost\n", .{});
                    C.exit(0);
                }
                t = std.time.milliTimestamp() - t;
                total_time += t;
                try stderr.print("depth={d} t={d}ms ret={d} nodes={d} hit={d} best_pos={x}\n", .{ maxdepth - base, t, ret, nodes, hit, best_pos });
                maxdepth += 1;
            }
            try print_pos(best_pos);
            m = best_pos;
            base += 1;
            color = if (color == WHITE) BLACK else WHITE;
        }
        turn = 1;
        var mt: Pos2 = @bitCast(m);
        var newpos = m;
        var tb: Poss = undefined;
        var nb: usize = undefined;
        var tg: Poss = undefined;
        var ng: usize = undefined;
        var tv: Poss = undefined;
        var nv: usize = undefined;
        gen_poss(m, color, &tb, &nb, &tg, &ng, &tv, &nv);
        if (ng != 0) {
            try stderr.print("Good poss:{d}\n", .{ng});
        }
        if ((nb + ng) == 0) {
            try stderr.print("Game Won\n", .{});
            C.exit(0);
        }
        outer: while (true) {
            while (true) {
                try stderr.print("Your pos:", .{});
                if (try stdin.readUntilDelimiterOrEof(&buf, '\n')) |v| opppos = std.fmt.parseInt(i64, v, 10) catch 64;
                if (@abs(opppos) < 31) break;
            }
            if (opppos == 0) {
                for (0..nb) |i| {
                    if (newpos == tb[i]) {
                        try stderr.print("Valid pos\n", .{});
                        break :outer;
                    }
                }
                for (0..ng) |i| {
                    if (newpos == tg[i]) {
                        try stderr.print("Valid pos\n", .{});
                        break :outer;
                    }
                }
                try stderr.print("Invalid pos\n", .{});
                mt = @bitCast(m);
            } else if (opppos < 0) {
                opppos += 1;
                const pos: u5 = @intCast(-opppos);
                if ((mt[color] & (o32 << pos)) != 0) mt[color] ^= (o32 << pos);
            } else {
                opppos -= 1;
                const pos: u5 = @intCast(opppos);
                if (((mt[0] | mt[1]) & (o32 << pos)) == 0) mt[color] ^= (o32 << pos);
            }
            newpos = @as(u64, @intCast(mt[0])) | (@as(u64, @intCast(mt[1])) << 32);
            try print_pos(newpos);
        }
        m = newpos;
        try print_pos(m);
        base += 1;
        color = if (color == WHITE) BLACK else WHITE;
    }
}

//const Inner = struct { a: u32, b: bool };
//var toto = [_][20]Inner{[_]Inner{.{ .a = 1, .b = true }} ** 20} ** 10;
//std.os.linux.ITIMER.REAL;
//    var vt: std.os.linux.itimerspec = undefined;
//  var vt2: std.os.linux.itimerspec = undefined;
//vt.it_value.sec = 2;
//vt.it_value.nsec = 0;
//vt.it_interval.sec = 0;
//vt.it_interval.nsec = 0;
//const errc = std.os.linux.setitimer(@intFromEnum(std.os.linux.ITIMER.REAL), &vt, &vt2);
//if (errc != 0) {
//    try stderr.print("Can't set timer\n", .{});
//    C.exit(255);
//}
//    const mt3: *Pos2 = @ptrCast(@constCast(&m));
//    const mt2 = [2]u32{ @intCast(m & 0xffffffff), @intCast(m >> 32) };
