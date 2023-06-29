const std = @import("std");

// 27 bits use 2GB
const NB_BITS: u8 = 30;
const SIZEX: usize = 7;
const SIZEY: usize = 6;
// 6x7 NB_BITS=29 170s
// 7x6 NB_BITS=30 367s

const Vals = i8;
const Vals_min: Vals = std.math.minInt(i8);
const Vals_max: Vals = std.math.maxInt(i8);
const Depth = u8;
const Colors = i8;
const Sigs = u64;

const FOUR: usize = 4;
const MAXDEPTH: Depth = SIZEX * SIZEY - 1;
const WHITE: Colors = 1;
const BLACK = -WHITE;
const EMPTY: Colors = 0;
const HASH_SIZE: usize = 1 << NB_BITS;
const HASH_MASK: Sigs = HASH_SIZE - 1;

var first_hash: Sigs = undefined;
var hashesw: [SIZEX][SIZEY]Sigs = undefined;
var hashesb: [SIZEX][SIZEY]Sigs = undefined;

const HashElem = packed struct {
    sig: Sigs,
    v_inf: Vals,
    v_sup: Vals,
    d: Depth,
};

const ZHASH = HashElem{
    .sig = 0,
    .v_inf = 0,
    .v_sup = 0,
    .d = 0,
};

var hashes: []HashElem = undefined;
var tab = [_][SIZEY]Colors{[_]Colors{EMPTY} ** SIZEY} ** SIZEX;
var first = [_]usize{0} ** SIZEX;

fn retrieve(hv: Sigs, v_inf: *Vals, v_sup: *Vals) bool {
    const ind: usize = hv & HASH_MASK;
    if (hashes[ind].sig == hv) {
        v_inf.* = hashes[ind].v_inf;
        v_sup.* = hashes[ind].v_sup;
        return true;
    } else {
        return false;
    }
}

fn store(hv: Sigs, alpha: Vals, beta: Vals, g: Vals, depth: Depth) void {
    const ind = hv & HASH_MASK;
    const d = MAXDEPTH + 2 - depth;
    if (hashes[ind].d <= d) {
        if (hashes[ind].sig != hv) {
            hashes[ind].d = d;
            hashes[ind].v_inf = Vals_min;
            hashes[ind].v_sup = Vals_max;
            hashes[ind].sig = hv;
        }
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

fn eval(x: usize, y: usize, color: Colors) bool {
    // For vertical search, search only below
    if (y >= FOUR - 1) {
        var nb: u32 = 1;
        var j = y - 1;
        while (true) {
            if (tab[x][j] == color) nb += 1 else break;
            if (j == 0) break;
            j -= 1;
        }
        if (nb >= FOUR) return true;
    }
    {
        // Horizontal search
        var nb: u32 = 1;
        if (x > 0) {
            var i = x - 1;
            while (true) {
                if (tab[i][y] == color) nb += 1 else break;
                if (i == 0) break;
                i -= 1;
            }
        }
        if (x < SIZEX - 1) {
            var i = x + 1;
            while (true) {
                if (tab[i][y] == color) nb += 1 else break;
                if (i == SIZEX - 1) break;
                i += 1;
            }
        }
        if (nb >= FOUR) return true;
    }
    {
        // diag1
        var nb: u32 = 1;
        if ((x < SIZEX - 1) and (y < SIZEY - 1)) {
            var i = x + 1;
            var j = y + 1;
            while (true) {
                if (tab[i][j] == color) nb += 1 else break;
                if ((i == SIZEX - 1) or (j == SIZEY - 1)) break;
                i += 1;
                j += 1;
            }
        }
        if ((x > 0) and (y > 0)) {
            var i = x - 1;
            var j = y - 1;
            while (true) {
                if (tab[i][j] == color) nb += 1 else break;
                if ((i == 0) or (j == 0)) break;
                i -= 1;
                j -= 1;
            }
        }
        if (nb >= FOUR) return true;
    }
    {
        // diag2
        var nb: u32 = 1;
        if ((x < SIZEX - 1) and (y > 0)) {
            var i = x + 1;
            var j = y - 1;
            while (true) {
                if (tab[i][j] == color) nb += 1 else break;
                if ((i == SIZEX - 1) or (j == 0)) break;
                i += 1;
                j -= 1;
            }
        }
        if ((x > 0) and (y < SIZEY - 1)) {
            var i = x - 1;
            var j = y + 1;
            while (true) {
                if (tab[i][j] == color) nb += 1 else break;
                if ((i == 0) or (j == SIZEY - 1)) break;
                i -= 1;
                j += 1;
            }
        }
        if (nb >= FOUR) return true;
    }
    return false;
}

fn ab(
    alpha: Vals,
    beta: Vals,
    color: Colors,
    depth: Depth,
    hv: Sigs,
    hv2: Sigs,
) Vals {
    const indexes = comptime init: {
        var t: [SIZEX]usize = undefined;
        for (&t, 0..) |*b, ix| b.* = (SIZEX - 1) / 2 + (ix + 1) / 2 * (2 * (ix % 2)) - (ix + 1) / 2;
        break :init t;
    };
    var a = alpha;
    var b = beta;
    var v_inf: Vals = undefined;
    var v_sup: Vals = undefined;
    if (retrieve(@min(hv, hv2), &v_inf, &v_sup)) {
        if (v_inf == v_sup) return v_inf;
        if (v_inf >= b) return v_inf;
        if (v_sup <= a) return v_sup;
        a = @max(a, v_inf);
        b = @min(b, v_sup);
    }
    for (indexes) |x| {
        const y = first[x];
        if ((y != SIZEY) and (eval(x, y, color))) return color;
    }
    if (depth == MAXDEPTH) return 0;

    var g: Vals = if (color == WHITE) Vals_min else Vals_max;
    var nhv: Sigs = undefined;
    var nhv2: Sigs = undefined;
    for (indexes) |x| {
        const y = first[x];
        if (y < SIZEY) {
            tab[x][y] = color;
            first[x] += 1;
            if (color == WHITE) {
                nhv = hv ^ hashesw[x][y];
                nhv2 = hv2 ^ hashesw[SIZEX - 1 - x][y];
            } else {
                nhv = hv ^ hashesb[x][y];
                nhv2 = hv2 ^ hashesb[SIZEX - 1 - x][y];
            }
            const v = ab(a, b, -color, depth + 1, nhv, nhv2);
            first[x] -= 1;
            tab[x][y] = EMPTY;
            if (color == WHITE) {
                if (v > g) {
                    g = v;
                    if (g > a) {
                        a = g;
                        if (a >= b) {
                            break;
                        }
                    }
                }
            } else {
                if (v < g) {
                    g = v;
                    if (g < b) {
                        b = g;
                        if (a >= b) {
                            break;
                        }
                    }
                }
            }
        }
    }
    store(@min(hv, hv2), alpha, beta, g, depth);
    return g;
}

pub fn main() !void {
    const stdout = std.io.getStdOut().writer();
    const allocator = std.heap.page_allocator;
    const RndGen = std.rand.DefaultPrng;
    hashes = try allocator.alloc(HashElem, HASH_SIZE);
    defer allocator.free(hashes);
    for (hashes) |*a| a.* = ZHASH;
    var rnd = RndGen.init(0);
    for (&hashesw) |*b| {
        for (b) |*a| a.* = rnd.random().int(Sigs);
    }
    for (&hashesb) |*b| {
        for (b) |*a| a.* = rnd.random().int(Sigs);
    }
    first_hash = rnd.random().int(Sigs);
    var t = std.time.milliTimestamp();
    const ret = ab(Vals_min, Vals_max, WHITE, 0, first_hash, first_hash);
    t = std.time.milliTimestamp() - t;
    try stdout.print("{d}\n", .{t});
    try stdout.print("{d}\n", .{ret});
}

//const Inner = struct { a: u32, b: bool };
//var toto = [_][20]Inner{[_]Inner{.{ .a = 1, .b = true }} ** 20} ** 10;
