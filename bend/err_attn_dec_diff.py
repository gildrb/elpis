#!/usr/bin/env python3
"""
Source link of bend/err_attn_dec.bend (decode / verify attention after ext 3030 against stock 355c6ee) to
the kernels it models, and scans of its laws.

  1. Fragments: every source line the model cites (E3: stock + patches/exl3/series + patches/exl3-ext/series,
     which ends with 3030; S: stock 355c6ee) holds the quoted text at the quoted line.
  2. Compiled code (H_sass3030): a compile of E3:exllamav3_ext/attn_verify.cu (nvcc, sm_86, -O3
     --use_fast_math) shows the instruction counts per source line the model counts.
  3. Replay: a transcription of the 3030 kernels' index arithmetic (tile loop, fresh-C P V groups, the
     6-level tile tree, the binary-counter combine) gives, per key, the own / fold / tree / depth counts;
     they equal the model's closed forms (e_own, e_fold, e_tsum = tdepth(6, ..), e_depth = tdepth(9, ..))
     for every key of every scanned L, and stay within e_OE, e_n0, e_TE, e_D.
  4. Bend evaluation: the Bend definitions evaluated at sample L and keys equal the Python mirror.
  5. Domination scan: every 3030 route (replayed counts, the replayed denominator maximum) is dominated at
     x = 128 by a stock route (bend/err_attn_diff.py's transcription of the stock kernels), for L = 1..4400
     and sampled L up to 2^20; e_OE <= own0 + laterk0 and e_rt <= s_rt (law dec_totals) for L = 1..2^20.

Usage: python3 -I -B err_attn_dec_diff.py [--stock DIR] [--elpis DIR] [--no-compiled] [--no-bend] [--mutate NAME]
Exit 0 = every check passed. --mutate perturbs one quoted 3030 line; the run must FAIL.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import err_attn_diff as D  # noqa: E402  stock transcription, tree builder, dom, compiled-code helpers

BEND = "/nix/store/55nz1ar98qk8l616m93qcamgd4vs36vc-bend-2.0.35/bin/bend"
check, fail, cdiv = D.check, D.fail, D.cdiv
S_E = 20

FRAGS = [
    # ---- 3030 split kernel ----
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        112,
        "__device__ __forceinline__ void mma16816_z(float* c, const uint32_t* a, uint32_t b0, uint32_t b1)",
    ),
    ("E", "exllamav3_ext/attn_verify.cu", 115, "{%10,%10,%10,%10};"),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        148,
        "__device__ __forceinline__ float pow2i(float d)",
    ),
    ("E", "exllamav3_ext/attn_verify.cu", 150, "int e = __float2int_rn(d) + 127;"),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        151,
        "return e > 0 ? __int_as_float(e << 23) : 0.f;",
    ),
    ("E", "exllamav3_ext/attn_verify.cu", 359, "const int n0 = (cta + it * S) * AV_T;"),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        451,
        "x[2 * i + hr][e] = ok ? sc[i][2 * hr + e] * scale_log2 : NEG_INF;",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        475,
        "float m_new = fmaxf(m[s], floorf(tmax));",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        481,
        "alpha[s] = m[s] == NEG_INF ? 0.f : (m_new == m[s] ? 1.f : pow2i(m[s] - m_use));",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        482,
        "cs[s] = tmax == NEG_INF ? 0.f : ex2(t_use - m_use);",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        483,
        "float p0 = x[s][0] == NEG_INF ? 0.f : ex2(x[s][0] - t_use);",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        484,
        "float p1 = x[s][1] == NEG_INF ? 0.f : ex2(x[s][1] - t_use);",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        485,
        "*reinterpret_cast<uint32_t*>(ps + r * PSTR + warp * 8 + 2 * t) = pack_h2(p0, p1);",
    ),
    ("E", "exllamav3_ext/attn_verify.cu", 486, "float ssum = p0 + p1;"),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        487,
        "ssum += __shfl_xor_sync(0xffffffffu, ssum, 1);",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        488,
        "ssum += __shfl_xor_sync(0xffffffffu, ssum, 2);",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        501,
        "float tsum = ((red_sum[r] + red_sum[AV_ROWS + r]) + (red_sum[2 * AV_ROWS + r] + red_sum[3 * AV_ROWS + r]))",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        502,
        "+ ((red_sum[4 * AV_ROWS + r] + red_sum[5 * AV_ROWS + r]) + (red_sum[6 * AV_ROWS + r] + red_sum[7 * AV_ROWS + r]));",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        503,
        "l[s] = fmaf(tsum, cs[s], l[s] * alpha[s]);",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        511,
        "for (int kk = 0; kk < AV_T / 16; ++kk)",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        535,
        "if (kk == 0) mma16816_z(pv[i][j], pa[i], b0, b1);",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        536,
        "else mma16816(pv[i][j], pa[i], b0, b1);",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        545,
        "acc[i][j][0] = fmaf(pv[i][j][0], cs[2 * i], acc[i][j][0] * alpha[2 * i]);",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        548,
        "acc[i][j][3] = fmaf(pv[i][j][3], cs[2 * i + 1], acc[i][j][3] * alpha[2 * i + 1]);",
    ),
    # ---- 3030 combine ----
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        660,
        "if (d < live) sw[d] = sw[d] == NEG_INF ? -1.f : pow2i(sw[d] - m_use);",
    ),
    ("E", "exllamav3_ext/attn_verify.cu", 669, "if (w < 0.f) continue;"),
    ("E", "exllamav3_ext/attn_verify.cu", 670, "float a = v * w;"),
    ("E", "exllamav3_ext/attn_verify.cu", 671, "float c = sl[s] * w;"),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        676,
        "const bool full = ((n >> k) & 1) != 0;",
    ),
    ("E", "exllamav3_ext/attn_verify.cu", 679, "a = ta[k] + a;"),
    ("E", "exllamav3_ext/attn_verify.cu", 680, "c = tl[k] + c;"),
    ("E", "exllamav3_ext/attn_verify.cu", 684, "ta[k] = a;"),
    ("E", "exllamav3_ext/attn_verify.cu", 696, "acc = ta[k] + acc;"),
    ("E", "exllamav3_ext/attn_verify.cu", 697, "lsum = tl[k] + lsum;"),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        699,
        "oh[d] = __float2half_rn(acc / (lsum == 0.f ? 1.f : lsum));",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        731,
        "mma16816_z(c, a[0], hb[0][0], hb[0][1]);",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        732,
        "mma16816(c, a[1], hb[1][0], hb[1][1]);",
    ),
    ("E", "exllamav3_ext/attn_verify.cu", 738, "= __float2half_rn(y);"),
    ("E", "exllamav3_ext/attn_verify.cuh", 46, "#define AV_NW 8"),
    ("E", "exllamav3_ext/attn_verify.cuh", 47, "#define AV_T 64"),
    ("E", "exllamav3_ext/attn_verify.cuh", 55, "return (L + AV_T - 1) / AV_T;"),
    ("E", "exllamav3_ext/attn_verify.cuh", 61, "return (n_tiles - x + S - 1) / S;"),
    ("E", "exllamav3_ext/attn_verify.cuh", 67, "return n_tiles < S ? n_tiles : S;"),
    (
        "E",
        "modules/attention_fn/bc_attn.py",
        440,
        "av_splits = max(1, _get_sm_count(dev) // kvh)",
    ),
    # ---- stock (quoted by the model; bend/err_attn_diff.py checks the rest of the stock lines) ----
    (
        "S",
        "modules/attention_fn/triton_paged.py",
        961,
        'alpha = tl.where(m == -float("inf"), 0.0, tl.exp(m - m_exp))',
    ),
    (
        "S",
        "modules/attention_fn/triton_paged.py",
        1054,
        'w = tl.where(m_s == -float("inf"), 0.0, tl.exp(m_s - m_safe))',
    ),
    ("S", "modules/attention_fn/triton_paged.py", 718, "y = tl.dot(x2, h)"),
    (
        "S",
        "exllamav3_ext/libtorch/attention.cpp",
        391,
        "int bound = bt_width * page_size + q_len;",
    ),
    (
        "S",
        "exllamav3_ext/libtorch/attention.cpp",
        392,
        "*num_splits = MAX(1, MIN(splits_cap, CEIL_DIVIDE(bound, 4 * block_n)));",
    ),
    (
        "S",
        "exllamav3_ext/libtorch/attention.cpp",
        393,
        "*split_len = CEIL_DIVIDE(CEIL_DIVIDE(bound, *num_splits), block_n) * block_n;",
    ),
    (
        "S",
        "generator/generator.py",
        965,
        "max_pages_batch = (max_seq_len + PAGE_SIZE - 1) // PAGE_SIZE",
    ),
    (
        "S",
        "generator/generator.py",
        966,
        "max_pages_batch = (max_pages_batch + 15) // 16 * 16",
    ),
    (
        "S",
        "generator/job.py",
        377,
        "max_seq_len = max(max_seq_len, len(seq.sequence_ids))",
    ),
    ("S", "modules/attention_fn/bc_attn.py", 278, "block_n = max(16, 8192 // hd_pad)"),
    (
        "S",
        "modules/attention_fn/bc_attn.py",
        288,
        "splits_cap = max(1, min(target // programs, 128))",
    ),
]

MUTATIONS = {
    # the warp partials summed in sequence again: fragment E3:attn_verify.cu:501 fails
    "seq_tsum": (
        "exllamav3_ext/attn_verify.cu",
        501,
        "((red_sum[r] + red_sum[AV_ROWS + r]) +",
        "(((red_sum[r] + red_sum[AV_ROWS + r]) +",
    ),
    # alpha back to ex2: fragment E3:attn_verify.cu:481 fails
    "alpha_ex2": (
        "exllamav3_ext/attn_verify.cu",
        481,
        "pow2i(m[s] - m_use)",
        "ex2(m[s] - m_use)",
    ),
    # running max not rounded down: fragment E3:attn_verify.cu:475 fails
    "no_floor": ("exllamav3_ext/attn_verify.cu", 475, "floorf(tmax)", "tmax"),
}


def check_frags(trees: dict):
    for side, rel, line, text in FRAGS:
        lines = (trees[side] / rel).read_text().splitlines()
        got = lines[line - 1].strip() if line <= len(lines) else "EOF"
        check(
            line <= len(lines) and text in lines[line - 1],
            f"{side}:{rel}:{line} does not hold {text!r} (holds {got!r})",
        )
    print(f"fragments: {len(FRAGS)} quoted lines hold their text")


# ---------------------------------------------------------------------------------------------
# 2. Compiled code


def check_compiled(elpis: Path, td: Path):
    cub = td / "av3030.cubin"
    r = subprocess.run(
        [
            "/tmp/cpu-lock.sh",
            "nvcc",
            *D.cuda_includes(),
            "-arch=sm_86",
            "-O3",
            "--use_fast_math",
            "-lineinfo",
            "-cubin",
            "-o",
            str(cub),
            str(elpis / "exllamav3_ext/attn_verify.cu"),
        ],
        capture_output=True,
        text=True,
    )
    check(r.returncode == 0, f"nvcc failed: {r.stderr[-2000:]}")
    sass = subprocess.run(
        ["nvdisasm", "-gi", "-c", str(cub)], capture_output=True, text=True, check=True
    ).stdout
    fns = re.split(r"\n\s*\.section\s+\.text\.", sass)
    fn = {f.split(",", 1)[0]: f for f in fns[1:]}

    def count(rows, line, op):
        return sum(
            1
            for ln, i in rows
            if ln == line and re.search(rf"(^|\s){re.escape(op)}", i)
        )

    for name in ("attn_verify_split_k3v3", "attn_verify_split_k3v3_tree"):
        sp = D.sass_by_line(fn[name], "attn_verify.cu")
        check(count(sp, 475, "FRND") == 6, f"{name}: floorf -> 6 FRND per tile")
        check(
            count(sp, 141, "MUFU.EX2") == 18,
            f"{name}: 18 MUFU.EX2 per tile (12 p + 6 cs), none for alpha",
        )
        check(count(sp, 481, "MUFU.EX2") == 0, f"{name}: alpha without ex2")
        check(
            count(sp, 501, "FADD") + count(sp, 502, "FADD") == 42,
            f"{name}: 7 FADD per row slot in the warp tree",
        )
        check(count(sp, 503, "FFMA") == 6, f"{name}: l = one FFMA per row slot")
        check(
            count(sp, 117, "HMMA.16816.F32") == 12
            and count(sp, 536, "HMMA.16816.F32") == 36,
            f"{name}: P V = 12 zero-C + 36 accumulating HMMA",
        )
        check(
            sum(count(sp, ln, "FFMA") for ln in range(545, 549)) == 48,
            f"{name}: 48 fold FFMA",
        )
    cg = D.sass_by_line(fn["attn_verify_combine_gate"], "attn_verify.cu")
    check(count(cg, 141, "MUFU.EX2") == 0, "combine: no ex2 for the weights")
    check(
        count(cg, 670, "FMUL") >= 1 and count(cg, 671, "FMUL") >= 1,
        "combine: v w, l w FMUL",
    )
    check(
        count(cg, 679, "FADD") >= 9 and count(cg, 696, "FADD") >= 9,
        "combine: tree FADD",
    )
    check(
        count(cg, 699, "MUFU.RCP") == 1 and count(cg, 699, "FMUL") == 1,
        "combine: acc / lsum = RCP + FMUL",
    )
    check(
        count(cg, 117, "HMMA.16816.F32") == 4 and count(cg, 732, "HMMA.16816.F32") == 4,
        "combine: rotation 4 + 4 HMMA",
    )
    check(
        not any(ln == 637 and "FFMA" in i for ln, i in cg),
        "combine: no FFMA rotation chain",
    )
    print(
        "3030 compiled (nvcc sm_86 -O3 --use_fast_math): FRND, ex2 for p and cs only, warp tree, fold FFMA, "
        "zero-C P V HMMA, exact-weight combine tree, two-step HMMA rotation"
    )


# ---------------------------------------------------------------------------------------------
# 3. Model mirror (the Bend definitions) and kernel replay


def bit(b):
    return 1 if b else 0


def half(x):
    return x // 2


def halfup(n):
    return (n + 1) // 2


def flip(x):
    return x ^ 1


def tdepth(K, x, n):
    c = 0
    for _ in range(K):
        c += bit(flip(x) < n)
        x, n = half(x), halfup(n)
    return c


def tbound(K, n):
    c = 0
    for _ in range(K):
        c += bit(1 < n)
        n = halfup(n)
    return c


def m_T(L):
    return cdiv(L, 64)


def m_nsl(L):
    return min(m_T(L), S_E)


def m_nt(L, x, q):
    return min(64, max(0, L - 64 * (x + 20 * q)))


def m_own(L, x, q, g):
    nt = m_nt(L, x, q)
    lg = cdiv(nt, 16)
    return bit(0 < g or 16 * g + 2 <= nt) + max(0, max(0, lg - g) - 1)


def m_later(L, x, q):
    return max(0, max(0, cdiv(max(0, m_T(L) - x), S_E) - 1) - q)


def m_fold(L, x, q):
    return 1 + m_later(L, x, q)


def m_depth(L, x):
    return tdepth(9, x, m_nsl(L))


def m_tsum(L, x, q, g, r):
    return tdepth(6, 16 * g + r, m_nt(L, x, q))


def m_n0(L):
    return cdiv(m_T(L), S_E)


def m_D(L):
    return tbound(9, m_nsl(L))


def m_TE(L):
    return tbound(6, L)


def m_OE(L):
    return max(0, min(4, cdiv(L, 16)) - bit(L == 1))


def m_dr(L):
    return 2 + m_TE(L) + m_n0(L) + m_D(L)


def s_geo(L):
    B = cdiv(cdiv(L, 256), 16) * 16 * 256 + 1
    ns = max(1, min(41, cdiv(B, 128)))
    sl = cdiv(cdiv(B, ns), 32) * 32
    nlive = cdiv(L, sl)
    ls0 = min(L, sl)
    gt = cdiv(min(L, 32), 16)
    own0 = bit(1 < L) + max(0, gt - 1)
    laterk0 = max(0, cdiv(ls0, 16) - gt)
    later0 = max(0, cdiv(ls0, 32) - 1)
    after0 = max(0, nlive - 1)
    ts0 = bit(1 < L) + bit(4 < L) + bit(2 < L) + bit(16 < L) + bit(8 < L)
    dr0 = 2 + ts0 + later0 + 1 + after0
    return dict(
        sl=sl,
        nlive=nlive,
        own0=own0,
        laterk0=laterk0,
        later0=later0,
        after0=after0,
        dr0=dr0,
    )


def m_rt(L):
    return (m_OE(L) + 16) + ((m_n0(L) + m_D(L)) + m_dr(L))


def s_rt(L):
    s = s_geo(L)
    return (s["own0"] + s["laterk0"] + 16) + (
        (s["later0"] + 1 + s["after0"]) + s["dr0"]
    )


# ---- kernel replay (index arithmetic of E3:attn_verify.cu, H_zero applied) ----


def r_own(L, j):
    """t32 steps of key j's P V: fresh accumulator per tile, k16 groups kk = 0..3 in order"""
    t0 = (j // 64) * 64
    live = [k for k in range(4) if t0 + 16 * k < L]
    g = (j - t0) // 16
    in_group = min(16, L - (t0 + 16 * g))
    c = int(
        g > 0 or in_group >= 2
    )  # the C before step g holds a live product, or the step sums >= 2
    return c + sum(1 for k in live if k > g)


def r_fold(L, j):
    T = cdiv(L, 64)
    i = j // 64
    x, q = i % S_E, i // S_E
    return 1 + sum(1 for qq in range(q + 1, T) if x + S_E * qq < T)


def r_tsum(L, j):
    """adds key j's p takes in the tile sum: p0 + p1, lane xor 1, xor 2 (8 keys per warp), then the
    pairwise warp tree ((w0 + w1) + (w2 + w3)) + ((w4 + w5) + (w6 + w7))"""
    t0 = (j // 64) * 64
    n = min(64, L - t0)
    u = j - t0

    def nonempty(a, b):
        return a < n and a < b

    c = 0
    for size in (1, 2, 4, 8, 16, 32):
        blk = (u // size) * size
        partner = blk ^ size
        c += nonempty(partner, partner + size)
    return c


def r_depth(nsl, x):
    """adds slot x's term takes in the binary-counter merge of slots 0 .. nsl - 1 (all merged)"""
    stack = {}
    n = 0
    mine = None  # level whose block holds x, or 'acc'
    adds = 0
    for s in range(nsl):
        cur_has = s == x
        k = 0
        while (n >> k) & 1:
            if cur_has or mine == k:  # both blocks non-empty: the add rounds x's term
                adds += 1
                cur_has = True
                if mine == k:
                    mine = None
            k += 1
        if cur_has:
            mine = k
        n += 1
    acc_live = False
    acc_has = False
    for k in range(12):
        if (n >> k) & 1:
            if acc_live and (acc_has or mine == k):
                adds += 1
            if mine == k:
                acc_has = True
            acc_live = True
    return adds


def keys_of(L):
    T = cdiv(L, 64)
    ks = set(range(min(L, 128))) | set(range(max(0, L - 70), L))
    ks |= (
        {64 * t + o for t in range(T) for o in (0, 17, 63) if 64 * t + o < L}
        if T <= 1200
        else set()
    )
    ks |= {
        64 * t + o
        for t in range(0, T, max(1, T // 600))
        for o in (0, 33)
        if 64 * t + o < L
    }
    return sorted(ks)


def coords(j):
    i = j // 64
    return i % S_E, i // S_E, (j - 64 * i) // 16, (j - 64 * i) % 16


def check_replay():
    Ls = sorted(
        set(
            list(range(1, 2100))
            + [
                4095,
                4096,
                4097,
                8191,
                8192,
                8193,
                24576,
                24577,
                65536,
                131072,
                262144,
                270336,
            ]
        )
    )
    nk = 0
    for L in Ls:
        nsl = m_nsl(L)
        for j in keys_of(L):
            x, q, g, r = coords(j)
            got = (r_own(L, j), r_fold(L, j), r_tsum(L, j), r_depth(nsl, x))
            want = (
                m_own(L, x, q, g),
                m_fold(L, x, q),
                m_tsum(L, x, q, g, r),
                m_depth(L, x),
            )
            check(
                got == want,
                f"L={L} key {j}: replay (own, fold, tsum, depth) {got} != model {want}",
            )
            check(
                got[0] <= m_OE(L)
                and got[1] <= m_n0(L)
                and got[2] <= m_TE(L)
                and got[3] <= m_D(L),
                f"L={L} key {j}: counts {got} exceed the bounds",
            )
            nk += 1
    print(
        f"replay: {nk} (L, key) pairs: own / fold / tile tree / combine tree equal the model and stay within the bounds"
    )


# ---------------------------------------------------------------------------------------------
# 4. Bend evaluation of the model at sample points

SAMPLE_L = [
    1,
    2,
    3,
    5,
    16,
    17,
    33,
    64,
    65,
    128,
    129,
    500,
    1281,
    4096,
    4097,
    8192,
    24577,
]


def check_bend(td: Path):
    rows = []
    for L in SAMPLE_L:
        rows.append(
            f"Dec.e_OE({L}n), Dec.e_n0({L}n), Dec.e_D({L}n), Dec.e_TE({L}n), Dec.e_dr({L}n), Dec.e_rt({L}n), "
            f"Dec.s_own0({L}n), Dec.s_laterk0({L}n), Dec.s_later0({L}n), Dec.s_after0({L}n), Dec.s_dr0({L}n), Dec.s_rt({L}n)"
        )
    keyrows = []
    for L, j in (
        (2, 1),
        (65, 64),
        (65, 3),
        (500, 130),
        (1281, 1280),
        (1281, 17),
        (4097, 4096),
        (8192, 2600),
    ):
        x, q, g, r = coords(j)
        keyrows.append(
            f"Dec.e_own({L}n, {x}n, {q}n, {g}n), Dec.e_fold({L}n, {x}n, {q}n), Dec.e_depth({L}n, {x}n), "
            f"Dec.e_tsum({L}n, {x}n, {q}n, {g}n, {r}n)"
        )
    src = (
        "import Base\nimport " + str(HERE / "err_attn_dec.bend") + " as Dec\n\n"
        "def main() -> List<&2, List<&2, Nat>>:\n  ["
        + ",\n   ".join(f"[{x}]" for x in rows + keyrows)
        + "]\n"
    )
    f = td / "dec_eval.bend"
    f.write_text(src)
    out = subprocess.run([BEND, str(f)], capture_output=True, text=True, timeout=1800)
    check(
        out.returncode == 0,
        f"bend evaluation failed: {out.stdout[-1500:]}{out.stderr[-1500:]}",
    )
    got = [
        [int(v) for v in re.findall(r"(\d+)n", row)]
        for row in re.findall(r"\[([^\[\]]*)\]", out.stdout)
    ]
    want = []
    for L in SAMPLE_L:
        s = s_geo(L)
        want.append([
            m_OE(L),
            m_n0(L),
            m_D(L),
            m_TE(L),
            m_dr(L),
            m_rt(L),
            s["own0"],
            s["laterk0"],
            s["later0"],
            s["after0"],
            s["dr0"],
            s_rt(L),
        ])
    for L, j in (
        (2, 1),
        (65, 64),
        (65, 3),
        (500, 130),
        (1281, 1280),
        (1281, 17),
        (4097, 4096),
        (8192, 2600),
    ):
        x, q, g, r = coords(j)
        want.append([
            m_own(L, x, q, g),
            m_fold(L, x, q),
            m_depth(L, x),
            m_tsum(L, x, q, g, r),
        ])
    check(got == want, f"Bend evaluation {got} != Python mirror {want}")
    print(
        f"bend evaluation: {len(SAMPLE_L)} sample L and 8 sample keys equal the Python mirror"
    )


# ---------------------------------------------------------------------------------------------
# 5. Domination scan


def elpis_routes(L):
    keys = keys_of(L)
    nsl = m_nsl(L)
    den = 2 + max(
        r_tsum(L, j) + r_fold(L, j) + r_depth(nsl, coords(j)[0]) for j in keys
    )
    den = max(den, 2 + max(r_fold(L, j) + r_depth(nsl, coords(j)[0]) for j in keys))
    check(den <= m_dr(L), f"L={L}: replayed denominator {den} > e_dr {m_dr(L)}")
    dpath = D.add(D.P(t32=2, r16=1), D.P(r32=den, t32=16, ex2=1))
    tail = D.add(dpath, D.P(rcp=1, r32=1), D.P(r16=3, t32=2))
    xs = D.P(r32=2, ex2=1)
    out = {}
    for j in keys:
        x = coords(j)[0]
        ch = D.P(t32=r_own(L, j), r32=r_fold(L, j) + r_depth(nsl, x))
        out[("DQ", j)] = D.add(D.P(t32=18, r16=1), xs, D.P(r16=1), ch, tail)
        out[("DK", j)] = D.add(D.P(r32=1, r16=1), D.P(t32=16), xs, D.P(r16=1), ch, tail)
        out[("DV", j)] = D.add(D.P(r32=1, r16=1), ch, tail)
        out[("DC", j)] = D.add(
            D.P(t32=18, r16=1), xs, D.P(r32=r_fold(L, j) + r_depth(nsl, x)), tail
        )
    out[("DG",)] = D.P(r32=1, ex2=1, r16=4, rcp=1)
    return out


def scan():
    Ls = sorted(
        set(
            list(range(1, 4401))
            + list(range(4401, 1 << 20, 4999))
            + [8192, 24576, 262144, 270336, 1 << 20]
        )
    )
    bad = 0
    for L in Ls:
        S, _, _ = D.routes(L, "s", [0])
        cand = list(S.values())
        for k, e in elpis_routes(L).items():
            if not any(D.dom(128, e, s) for s in cand):
                bad += 1
                print(f"  NOT DOMINATED: L={L} {k} {e}")
    check(bad == 0, f"{bad} routes not dominated")
    worst = min((s_rt(L) - m_rt(L), L) for L in range(1, (1 << 20) + 1))
    check(worst[0] >= 0, f"e_rt > s_rt at L = {worst[1]}")
    check(
        all(m_OE(L) <= s_geo(L)["own0"] + s_geo(L)["laterk0"] for L in range(1, 70000)),
        "e_OE > own0 + laterk0",
    )
    print(
        f"scan: every 3030 route dominated at x = 128 for {len(Ls)} L (1..4400 dense, sampled to 2^20); "
        f"e_rt <= s_rt for L = 1..2^20 (min slack {worst[0]} at L = {worst[1]})"
    )


# ---------------------------------------------------------------------------------------------


def main(argv: list) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--stock", type=Path, default=D.STOCK)
    ap.add_argument("--elpis", type=Path)
    ap.add_argument("--no-compiled", action="store_true")
    ap.add_argument("--no-bend", action="store_true")
    ap.add_argument("--mutate", choices=sorted(MUTATIONS))
    a = ap.parse_args(argv[1:])
    with tempfile.TemporaryDirectory() as td:
        tdp = Path(td)
        elpis = a.elpis or D.build_elpis(
            a.stock, tdp, stop_before=None
        )  # the full series, 3030 included
        if a.mutate:
            rel, line, old, new = MUTATIONS[a.mutate]
            if a.elpis:
                dst = tdp / "mutE"
                shutil.copytree(elpis, dst, symlinks=True)
                elpis = dst
            lines = (elpis / rel).read_text().split("\n")
            check(
                lines[line - 1].count(old) == 1,
                f"mutation {a.mutate}: anchor not on line {line}",
            )
            lines[line - 1] = lines[line - 1].replace(old, new)
            (elpis / rel).write_text("\n".join(lines))
        check_frags({"S": a.stock, "E": elpis})
        if not a.no_compiled:
            check_compiled(elpis, tdp)
        check_replay()
        if not a.no_bend:
            check_bend(tdp)
        scan()
    print("err_attn_dec_diff: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
