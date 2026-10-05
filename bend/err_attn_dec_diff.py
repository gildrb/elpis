#!/usr/bin/env python3
# Copyright (c) 2026 Gil Rodrigues
"""Source link of bend/err_attn_dec.bend to the kernels it models, and its law scans.

The model: decode / verify attention after ext 3030 against stock 355c6ee.

  1. Fragments: every source line the model cites (E3: stock + patches/exl3/series +
     patches/exl3-ext/series, which ends with 3030; S: stock 355c6ee) holds the
     quoted text at the quoted line.
  2. Compiled code (H_sass3030): a compile of E3:exllamav3_ext/attn_verify.cu (nvcc,
     sm_86, -O3 --use_fast_math) shows the instruction counts per source line the
     model counts.
  3. Replay: a transcription of the 3030 kernels' index arithmetic (tile loop,
     fresh-C P V groups, the 6-level tile tree, the binary-counter combine) gives,
     per key, the own / fold / tree / depth counts; they equal the model's closed
     forms (e_own, e_fold, e_tsum = tdepth(6, ..), e_depth = tdepth(9, ..)) for every
     key of every scanned L, and stay within e_OE, e_n0, e_TE, e_D.
  4. Bend evaluation: the Bend definitions evaluated at sample L and keys equal the
     Python mirror.
  5. Domination scan: every 3030 route (replayed counts, the replayed denominator
     maximum) is dominated at x = 128 by a stock route (bend/err_attn_diff.py's
     transcription of the stock kernels), for L = 1..4400 and sampled L up to 2^20;
     e_OE <= own0 + laterk0 and e_rt <= s_rt (law dec_totals) for L = 1..2^20.

Usage: python3 -I -B err_attn_dec_diff.py --stock DIR [--elpis DIR]
           [--no-compiled | --cuda-include DIR...] [--no-bend] [--mutate NAME]
  --stock: the stock exllamav3 package directory at 355c6ee (OUT/stock of
  bend/engine_trees.py).
  --cuda-include: an nvcc include directory (repeat it as necessary), as in
  bend/err_attn_diff.py. The compiled checks use nvcc and nvdisasm from PATH; the
  Bend evaluation uses the `bend` on PATH (bend/source_link.py).
Exit 0 = every check passed. --mutate perturbs one quoted 3030 line; the run must
FAIL.
"""

from __future__ import annotations

import argparse
import re
import shutil
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import err_attn_diff as ead  # stock transcription, tree builder, dom, compiled code
import source_link

HERE = Path(__file__).resolve().parent
fail, cdiv = ead.fail, ead.cdiv
S_E = 20

FRAGS = [
    # ---- 3030 split kernel ----
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        112,
        (
            "__device__ __forceinline__ void mma16816_z(float* c, const uint32_t* "
            "a, uint32_t b0, uint32_t b1)"
        ),
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
        (
            "alpha[s] = m[s] == NEG_INF ? 0.f : (m_new == m[s] ? 1.f : pow2i(m[s] "
            "- m_use));"
        ),
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
        (
            "*reinterpret_cast<uint32_t*>(ps + r * PSTR + warp * 8 + 2 * t) = "
            "pack_h2(p0, p1);"
        ),
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
        (
            "float tsum = ((red_sum[r] + red_sum[AV_ROWS + r]) + (red_sum[2 * "
            "AV_ROWS + r] + red_sum[3 * AV_ROWS + r]))"
        ),
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        502,
        (
            "+ ((red_sum[4 * AV_ROWS + r] + red_sum[5 * AV_ROWS + r]) + (red_sum[6 "
            "* AV_ROWS + r] + red_sum[7 * AV_ROWS + r]));"
        ),
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
        (
            "acc[i][j][3] = fmaf(pv[i][j][3], cs[2 * i + 1], acc[i][j][3] * alpha[2 "
            "* i + 1]);"
        ),
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
    # ---- stock (quoted by the model; bend/err_attn_diff.py checks the rest of the
    # stock lines) ----
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


def check_frags(trees: ead.Trees) -> None:
    """Check that every quoted line holds its text.

    Args:
        trees: the source trees by tag.

    """
    for tag, rel, line, text in FRAGS:
        lines = (trees[tag] / rel).read_text().splitlines()
        got = lines[line - 1].strip() if line <= len(lines) else "EOF"
        if not (line <= len(lines) and text in lines[line - 1]):
            fail(f"{tag}:{rel}:{line} does not hold {text!r} (holds {got!r})")
    sys.stdout.write(f"fragments: {len(FRAGS)} quoted lines hold their text\n")


# ---------------------------------------------------------------------------------
# 2. Compiled code

# A count condition: ((source line, opcode), ...) summed, "eq" or "ge", the count.
Cond = tuple[tuple[tuple[int, str], ...], str, int]

HMMA = "HMMA.16816.F32"
# per split kernel: (conditions, message)
SPLIT_FACTS: tuple[tuple[tuple[Cond, ...], str], ...] = (
    ((((((475, "FRND"),), "eq", 6)),), "floorf -> 6 FRND per tile"),
    (
        ((((141, "MUFU.EX2"),), "eq", 18),),
        "18 MUFU.EX2 per tile (12 p + 6 cs), none for alpha",
    ),
    ((((((481, "MUFU.EX2"),), "eq", 0)),), "alpha without ex2"),
    (
        ((((501, "FADD"), (502, "FADD")), "eq", 42),),
        "7 FADD per row slot in the warp tree",
    ),
    ((((((503, "FFMA"),), "eq", 6)),), "l = one FFMA per row slot"),
    (
        ((((117, HMMA),), "eq", 12), (((536, HMMA),), "eq", 36)),
        "P V = 12 zero-C + 36 accumulating HMMA",
    ),
    (
        ((tuple((ln, "FFMA") for ln in range(545, 549)), "eq", 48),),
        "48 fold FFMA",
    ),
)
COMBINE_FACTS: tuple[tuple[tuple[Cond, ...], str], ...] = (
    ((((((141, "MUFU.EX2"),), "eq", 0)),), "combine: no ex2 for the weights"),
    (
        ((((670, "FMUL"),), "ge", 1), (((671, "FMUL"),), "ge", 1)),
        "combine: v w, l w FMUL",
    ),
    (
        ((((679, "FADD"),), "ge", 9), (((696, "FADD"),), "ge", 9)),
        "combine: tree FADD",
    ),
    (
        ((((699, "MUFU.RCP"),), "eq", 1), (((699, "FMUL"),), "eq", 1)),
        "combine: acc / lsum = RCP + FMUL",
    ),
    (
        ((((117, HMMA),), "eq", 4), (((732, HMMA),), "eq", 4)),
        "combine: rotation 4 + 4 HMMA",
    ),
)
OLD_ROT_LINE = 637  # the pre-3030 32-FFMA back-rotation


def holds(rows: ead.Rows, conds: tuple[Cond, ...]) -> bool:
    """Tell whether every count condition holds.

    Args:
        rows: (source line, instruction) pairs.
        conds: the conditions.

    Returns:
        True when all hold.

    """
    for at, cmp, n in conds:
        total = sum(len(ead.ops_at(rows, line, op)) for line, op in at)
        if not (total == n if cmp == "eq" else total >= n):
            return False
    return True


def check_compiled(elpis: Path, td: Path, includes: list[Path]) -> None:
    """Compile the 3030 attn_verify.cu and check its SASS.

    Args:
        elpis: the elpis package directory.
        td: a scratch directory.
        includes: the nvcc include directories.

    """
    cub = td / "av3030.cubin"
    err = ead.compile_cubin(
        includes,
        ["-arch=sm_86", "-O3", "--use_fast_math", "-lineinfo"],
        cub,
        elpis / "exllamav3_ext/attn_verify.cu",
    )
    if err is not None:
        fail(f"nvcc failed: {err[-2000:]}")
    sass = ead.disasm(["-gi", "-c"], cub)
    fns = re.split(r"\n\s*\.section\s+\.text\.", sass)
    fn = {f.split(",", 1)[0]: f for f in fns[1:]}
    for name in ("attn_verify_split_k3v3", "attn_verify_split_k3v3_tree"):
        sp = ead.sass_by_line(fn[name], "attn_verify.cu")
        for conds, msg in SPLIT_FACTS:
            if not holds(sp, conds):
                fail(f"{name}: {msg}")
    cg = ead.sass_by_line(fn["attn_verify_combine_gate"], "attn_verify.cu")
    for conds, msg in COMBINE_FACTS:
        if not holds(cg, conds):
            fail(msg)
    if any(ln == OLD_ROT_LINE and "FFMA" in i for ln, i in cg):
        fail("combine: no FFMA rotation chain")
    sys.stdout.write(
        "3030 compiled (nvcc sm_86 -O3 --use_fast_math): FRND, ex2 for p "
        "and cs only, warp tree, fold FFMA, "
        "zero-C P V HMMA, exact-weight combine tree, two-step HMMA rotation\n"
    )


# ---------------------------------------------------------------------------------
# 3. Model mirror (the Bend definitions) and kernel replay


def half(x: int) -> int:
    """Halve rounding down.

    Args:
        x: the number.

    Returns:
        x // 2.

    """
    return x // 2


def halfup(n: int) -> int:
    """Halve rounding up.

    Args:
        n: the number.

    Returns:
        (n + 1) // 2.

    """
    return (n + 1) // 2


def flip(x: int) -> int:
    """Flip the lowest bit.

    Args:
        x: the number.

    Returns:
        x ^ 1.

    """
    return x ^ 1


def tdepth(levels: int, x: int, n: int) -> int:
    """Count the adds leaf x takes in a levels-deep pairwise tree of n live leaves.

    Args:
        levels: the tree depth.
        x: the leaf.
        n: the live leaves.

    Returns:
        The adds.

    """
    c = 0
    for _ in range(levels):
        c += int(flip(x) < n)
        x, n = half(x), halfup(n)
    return c


def tbound(levels: int, n: int) -> int:
    """Bound tdepth over the leaves.

    Args:
        levels: the tree depth.
        n: the live leaves.

    Returns:
        The bound.

    """
    c = 0
    for _ in range(levels):
        c += int(n > 1)
        n = halfup(n)
    return c


def m_t(n_keys: int) -> int:
    """Count the 64-key tiles (Bend m_T).

    Args:
        n_keys: the row length L.

    Returns:
        The tiles.

    """
    return cdiv(n_keys, 64)


def m_nsl(n_keys: int) -> int:
    """Count the live split slots.

    Args:
        n_keys: the row length L.

    Returns:
        The slots.

    """
    return min(m_t(n_keys), S_E)


def m_nt(n_keys: int, x: int, q: int) -> int:
    """Count the live keys of slot x's q-th tile.

    Args:
        n_keys: the row length L.
        x: the slot.
        q: the tile of the slot.

    Returns:
        The keys.

    """
    return min(64, max(0, n_keys - 64 * (x + 20 * q)))


def m_own(n_keys: int, x: int, q: int, g: int) -> int:
    """Mirror e_own.

    Args:
        n_keys: the row length L.
        x: the slot.
        q: the tile of the slot.
        g: the k16 group.

    Returns:
        The t32 steps of the key's P V.

    """
    nt = m_nt(n_keys, x, q)
    lg = cdiv(nt, 16)
    return int(g > 0 or 16 * g + 2 <= nt) + max(0, max(0, lg - g) - 1)


def m_later(n_keys: int, x: int, q: int) -> int:
    """Count the tiles of slot x after its q-th.

    Args:
        n_keys: the row length L.
        x: the slot.
        q: the tile of the slot.

    Returns:
        The later tiles.

    """
    return max(0, max(0, cdiv(max(0, m_t(n_keys) - x), S_E) - 1) - q)


def m_fold(n_keys: int, x: int, q: int) -> int:
    """Mirror e_fold.

    Args:
        n_keys: the row length L.
        x: the slot.
        q: the tile of the slot.

    Returns:
        The fold roundings.

    """
    return 1 + m_later(n_keys, x, q)


def m_depth(n_keys: int, x: int) -> int:
    """Mirror e_depth.

    Args:
        n_keys: the row length L.
        x: the slot.

    Returns:
        The combine-tree adds.

    """
    return tdepth(9, x, m_nsl(n_keys))


def m_tsum(n_keys: int, x: int, q: int, g: int, r: int) -> int:
    """Mirror e_tsum.

    Args:
        n_keys: the row length L.
        x: the slot.
        q: the tile of the slot.
        g: the k16 group.
        r: the key in the group.

    Returns:
        The tile-tree adds.

    """
    return tdepth(6, 16 * g + r, m_nt(n_keys, x, q))


def m_n0(n_keys: int) -> int:
    """Mirror e_n0.

    Args:
        n_keys: the row length L.

    Returns:
        The tiles of slot 0.

    """
    return cdiv(m_t(n_keys), S_E)


def m_d(n_keys: int) -> int:
    """Mirror e_D.

    Args:
        n_keys: the row length L.

    Returns:
        The combine-tree bound.

    """
    return tbound(9, m_nsl(n_keys))


def m_te(n_keys: int) -> int:
    """Mirror e_TE.

    Args:
        n_keys: the row length L.

    Returns:
        The tile-tree bound.

    """
    return tbound(6, n_keys)


def m_oe(n_keys: int) -> int:
    """Mirror e_OE.

    Args:
        n_keys: the row length L.

    Returns:
        The own-steps bound.

    """
    return max(0, min(4, cdiv(n_keys, 16)) - int(n_keys == 1))


def m_dr(n_keys: int) -> int:
    """Mirror e_dr.

    Args:
        n_keys: the row length L.

    Returns:
        The denominator's r32 bound.

    """
    return 2 + m_te(n_keys) + m_n0(n_keys) + m_d(n_keys)


def s_geo(n_keys: int) -> dict[str, int]:
    """Mirror the stock geometry of key 0.

    Args:
        n_keys: the row length L.

    Returns:
        sl, nlive, own0, laterk0, later0, after0 and dr0.

    """
    bound = cdiv(cdiv(n_keys, 256), 16) * 16 * 256 + 1
    ns = max(1, min(41, cdiv(bound, 128)))
    sl = cdiv(cdiv(bound, ns), 32) * 32
    nlive = cdiv(n_keys, sl)
    ls0 = min(n_keys, sl)
    gt = cdiv(min(n_keys, 32), 16)
    own0 = int(n_keys > 1) + max(0, gt - 1)
    laterk0 = max(0, cdiv(ls0, 16) - gt)
    later0 = max(0, cdiv(ls0, 32) - 1)
    after0 = max(0, nlive - 1)
    ts0 = sum(n_keys > off for off in STOCK_XORS)
    dr0 = 2 + ts0 + later0 + 1 + after0
    return {
        "sl": sl,
        "nlive": nlive,
        "own0": own0,
        "laterk0": laterk0,
        "later0": later0,
        "after0": after0,
        "dr0": dr0,
    }


STOCK_XORS = (1, 4, 2, 16, 8)  # tl.sum's xor offsets over the 32-key tile


def m_rt(n_keys: int) -> int:
    """Mirror e_rt.

    Args:
        n_keys: the row length L.

    Returns:
        The 3030 route total.

    """
    return (m_oe(n_keys) + 16) + ((m_n0(n_keys) + m_d(n_keys)) + m_dr(n_keys))


def s_rt(n_keys: int) -> int:
    """Mirror s_rt.

    Args:
        n_keys: the row length L.

    Returns:
        The stock route total.

    """
    s = s_geo(n_keys)
    return (s["own0"] + s["laterk0"] + 16) + (
        (s["later0"] + 1 + s["after0"]) + s["dr0"]
    )


# ---- kernel replay (index arithmetic of E3:attn_verify.cu, H_zero applied) ----

MIN_SUMMED = 2  # a k16 step with two live products rounds


def r_own(n_keys: int, j: int) -> int:
    """Count the t32 steps of key j's P V.

    Fresh accumulator per tile, k16 groups kk = 0..3 in order.

    Args:
        n_keys: the row length L.
        j: the key.

    Returns:
        The steps.

    """
    t0 = (j // 64) * 64
    live = [k for k in range(4) if t0 + 16 * k < n_keys]
    g = (j - t0) // 16
    in_group = min(16, n_keys - (t0 + 16 * g))
    # the C before step g holds a live product, or the step sums >= 2
    c = int(g > 0 or in_group >= MIN_SUMMED)
    return c + sum(1 for k in live if k > g)


def r_fold(n_keys: int, j: int) -> int:
    """Count the fold roundings of key j's tile.

    Args:
        n_keys: the row length L.
        j: the key.

    Returns:
        The roundings.

    """
    n_tiles = cdiv(n_keys, 64)
    i = j // 64
    x, q = i % S_E, i // S_E
    return 1 + sum(1 for qq in range(q + 1, n_tiles) if x + S_E * qq < n_tiles)


def r_tsum(n_keys: int, j: int) -> int:
    """Count the adds key j's p takes in the tile sum.

    p0 + p1, lane xor 1, xor 2 (8 keys per warp), then the pairwise warp tree
    ((w0 + w1) + (w2 + w3)) + ((w4 + w5) + (w6 + w7)).

    Args:
        n_keys: the row length L.
        j: the key.

    Returns:
        The adds.

    """
    t0 = (j // 64) * 64
    n = min(64, n_keys - t0)
    u = j - t0
    c = 0
    for size in (1, 2, 4, 8, 16, 32):
        blk = (u // size) * size
        partner = blk ^ size
        c += partner < n and partner < partner + size
    return c


def r_depth(nsl: int, x: int) -> int:
    """Count the adds slot x's term takes in the binary-counter merge.

    The merge of slots 0 .. nsl - 1 (all merged).

    Args:
        nsl: the live slots.
        x: the slot.

    Returns:
        The adds.

    """
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


DENSE_TILES = 1200  # up to this many tiles, three keys of every tile


def keys_of(n_keys: int) -> list[int]:
    """Pick the keys the replay examines.

    Args:
        n_keys: the row length L.

    Returns:
        The keys, sorted.

    """
    n_tiles = cdiv(n_keys, 64)
    ks = set(range(min(n_keys, 128))) | set(range(max(0, n_keys - 70), n_keys))
    ks |= (
        {64 * t + o for t in range(n_tiles) for o in (0, 17, 63) if 64 * t + o < n_keys}
        if n_tiles <= DENSE_TILES
        else set()
    )
    ks |= {
        64 * t + o
        for t in range(0, n_tiles, max(1, n_tiles // 600))
        for o in (0, 33)
        if 64 * t + o < n_keys
    }
    return sorted(ks)


def coords(j: int) -> tuple[int, int, int, int]:
    """Place key j: slot, tile of the slot, k16 group, key in the group.

    Args:
        j: the key.

    Returns:
        x, q, g, r.

    """
    i = j // 64
    return i % S_E, i // S_E, (j - 64 * i) // 16, (j - 64 * i) % 16


REPLAY_LENGTHS = sorted({
    *range(1, 2100),
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
})


def check_replay() -> None:
    """Check the kernel replay against the model mirror and its bounds."""
    nk = 0
    for n_keys in REPLAY_LENGTHS:
        nsl = m_nsl(n_keys)
        for j in keys_of(n_keys):
            x, q, g, r = coords(j)
            got = (
                r_own(n_keys, j),
                r_fold(n_keys, j),
                r_tsum(n_keys, j),
                r_depth(nsl, x),
            )
            want = (
                m_own(n_keys, x, q, g),
                m_fold(n_keys, x, q),
                m_tsum(n_keys, x, q, g, r),
                m_depth(n_keys, x),
            )
            if got != want:
                fail(
                    f"L={n_keys} key {j}: replay (own, fold, tsum, depth) {got} "
                    f"!= model {want}"
                )
            if not (
                got[0] <= m_oe(n_keys)
                and got[1] <= m_n0(n_keys)
                and got[2] <= m_te(n_keys)
                and got[3] <= m_d(n_keys)
            ):
                fail(f"L={n_keys} key {j}: counts {got} exceed the bounds")
            nk += 1
    sys.stdout.write(
        f"replay: {nk} (L, key) pairs: own / fold / tile tree / combine tree "
        "equal the model and stay within the bounds\n"
    )


# ---------------------------------------------------------------------------------
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
SAMPLE_KEYS = (
    (2, 1),
    (65, 64),
    (65, 3),
    (500, 130),
    (1281, 1280),
    (1281, 17),
    (4097, 4096),
    (8192, 2600),
)


def bend_source() -> str:
    """Write the Bend program that evaluates the model at the sample points.

    Returns:
        The program.

    """
    rows = [
        f"Dec.e_OE({n}n), Dec.e_n0({n}n), Dec.e_D({n}n), Dec.e_TE({n}n), "
        f"Dec.e_dr({n}n), Dec.e_rt({n}n), "
        f"Dec.s_own0({n}n), Dec.s_laterk0({n}n), Dec.s_later0({n}n), "
        f"Dec.s_after0({n}n), "
        f"Dec.s_dr0({n}n), Dec.s_rt({n}n)"
        for n in SAMPLE_L
    ]
    keyrows = []
    for n, j in SAMPLE_KEYS:
        x, q, g, r = coords(j)
        keyrows.append(
            f"Dec.e_own({n}n, {x}n, {q}n, {g}n), Dec.e_fold({n}n, {x}n, {q}n), "
            f"Dec.e_depth({n}n, {x}n), "
            f"Dec.e_tsum({n}n, {x}n, {q}n, {g}n, {r}n)"
        )
    return (
        "import Base\nimport " + str(HERE / "err_attn_dec.bend") + " as Dec\n\n"
        "def main() -> List<&2, List<&2, Nat>>:\n  ["
        + ",\n   ".join(f"[{x}]" for x in [*rows, *keyrows])
        + "]\n"
    )


def mirror_values() -> list[list[int]]:
    """Evaluate the Python mirror at the sample points.

    Returns:
        The rows the Bend program prints.

    """
    want = []
    for n in SAMPLE_L:
        s = s_geo(n)
        want.append([
            m_oe(n),
            m_n0(n),
            m_d(n),
            m_te(n),
            m_dr(n),
            m_rt(n),
            s["own0"],
            s["laterk0"],
            s["later0"],
            s["after0"],
            s["dr0"],
            s_rt(n),
        ])
    for n, j in SAMPLE_KEYS:
        x, q, g, r = coords(j)
        want.append([
            m_own(n, x, q, g),
            m_fold(n, x, q),
            m_depth(n, x),
            m_tsum(n, x, q, g, r),
        ])
    return want


def check_bend(td: Path) -> None:
    """Evaluate the Bend model at the sample points and compare with the mirror.

    Args:
        td: a scratch directory.

    """
    f = td / "dec_eval.bend"
    f.write_text(bend_source())
    out = source_link.run(
        [source_link.bend(), str(f)],
        capture_output=True,
        text=True,
        timeout=1800,
        check=False,
    )
    if out.returncode != 0:
        fail(f"bend evaluation failed: {out.stdout[-1500:]}{out.stderr[-1500:]}")
    got = [
        [int(v) for v in re.findall(r"(\d+)n", row)]
        for row in re.findall(r"\[([^\[\]]*)\]", out.stdout)
    ]
    want = mirror_values()
    if got != want:
        fail(f"Bend evaluation {got} != Python mirror {want}")
    sys.stdout.write(
        f"bend evaluation: {len(SAMPLE_L)} sample L and 8 sample keys equal "
        "the Python mirror\n"
    )


# ---------------------------------------------------------------------------------
# 5. Domination scan


def elpis_routes(n_keys: int) -> ead.Routes:
    """Build every 3030 rounding route at one L from the replay.

    Args:
        n_keys: the row length L.

    Returns:
        The routes.

    """
    keys = keys_of(n_keys)
    nsl = m_nsl(n_keys)
    den = 2 + max(
        r_tsum(n_keys, j) + r_fold(n_keys, j) + r_depth(nsl, coords(j)[0]) for j in keys
    )
    den = max(
        den,
        2 + max(r_fold(n_keys, j) + r_depth(nsl, coords(j)[0]) for j in keys),
    )
    if not (den <= m_dr(n_keys)):
        fail(f"L={n_keys}: replayed denominator {den} > e_dr {m_dr(n_keys)}")
    vec, add = ead.vec, ead.add
    dpath = add(vec(t32=2, r16=1), vec(r32=den, t32=16, ex2=1))
    tail = add(dpath, vec(rcp=1, r32=1), vec(r16=3, t32=2))
    xs = vec(r32=2, ex2=1)
    out: ead.Routes = {}
    for j in keys:
        x = coords(j)[0]
        ch = vec(t32=r_own(n_keys, j), r32=r_fold(n_keys, j) + r_depth(nsl, x))
        out["DQ", j] = add(vec(t32=18, r16=1), xs, vec(r16=1), ch, tail)
        out["DK", j] = add(vec(r32=1, r16=1), vec(t32=16), xs, vec(r16=1), ch, tail)
        out["DV", j] = add(vec(r32=1, r16=1), ch, tail)
        out["DC", j] = add(
            vec(t32=18, r16=1),
            xs,
            vec(r32=r_fold(n_keys, j) + r_depth(nsl, x)),
            tail,
        )
    out["DG",] = vec(r32=1, ex2=1, r16=4, rcp=1)
    return out


SCAN_LENGTHS = sorted({
    *range(1, 4401),
    *range(4401, 1 << 20, 4999),
    8192,
    24576,
    262144,
    270336,
    1 << 20,
})


def scan() -> None:
    """Scan L: every 3030 route dominated, and the route totals ordered."""
    bad = 0
    for n_keys in SCAN_LENGTHS:
        s_routes, _, _ = ead.routes(n_keys, "s", [0])
        cand = list(s_routes.values())
        for k, e in elpis_routes(n_keys).items():
            if not any(ead.dom(128, e, s) for s in cand):
                bad += 1
                sys.stdout.write(f"  NOT DOMINATED: L={n_keys} {k} {e}\n")
    if bad != 0:
        fail(f"{bad} routes not dominated")
    worst = min((s_rt(n) - m_rt(n), n) for n in range(1, (1 << 20) + 1))
    if not (worst[0] >= 0):
        fail(f"e_rt > s_rt at L = {worst[1]}")
    if not (
        all(m_oe(n) <= s_geo(n)["own0"] + s_geo(n)["laterk0"] for n in range(1, 70000))
    ):
        fail("e_OE > own0 + laterk0")
    sys.stdout.write(
        f"scan: every 3030 route dominated at x = 128 for {len(SCAN_LENGTHS)} L "
        "(1..4400 dense, sampled to 2^20); "
        f"e_rt <= s_rt for L = 1..2^20 (min slack {worst[0]} at L = {worst[1]})\n"
    )


# ---------------------------------------------------------------------------------


def main(argv: list[str]) -> int:
    """Run every check.

    Args:
        argv: the command line.

    Returns:
        The exit status.

    """
    ap = argparse.ArgumentParser()
    ap.add_argument("--stock", type=Path, required=True)
    ap.add_argument("--elpis", type=Path)
    ap.add_argument("--no-compiled", action="store_true")
    ap.add_argument("--no-bend", action="store_true")
    ap.add_argument("--cuda-include", type=Path, action="append", default=[])
    ap.add_argument("--mutate", choices=sorted(MUTATIONS))
    a = ap.parse_args(argv[1:])
    with tempfile.TemporaryDirectory() as td:
        tdp = Path(td)
        # the full series, 3030 included
        elpis = a.elpis or ead.build_elpis(a.stock, tdp, stop_before=None)
        if a.mutate:
            rel, line, old, new = MUTATIONS[a.mutate]
            if a.elpis:
                dst = tdp / "mutE"
                shutil.copytree(elpis, dst, symlinks=True)
                elpis = dst
            lines = (elpis / rel).read_text().split("\n")
            if lines[line - 1].count(old) != 1:
                fail(f"mutation {a.mutate}: anchor not on line {line}")
            lines[line - 1] = lines[line - 1].replace(old, new)
            (elpis / rel).write_text("\n".join(lines))
        check_frags({"S": a.stock, "E": elpis})
        if not a.no_compiled:
            check_compiled(elpis, tdp, a.cuda_include)
        check_replay()
        if not a.no_bend:
            check_bend(tdp)
        scan()
    sys.stdout.write("err_attn_dec_diff: PASS\n")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
