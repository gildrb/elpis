#!/usr/bin/env python3
"""
Finite source link of bend/err_prefill.bend (prefill rounding-error paths) to the sources it transcribes.

Checks, failing closed:
  1. every cited "FILE:line" of the model holds the expected text (stock 355c6ee sources, the stock Triton
     PTX / TTGIR of the served prefill and combine kernels, the elpis patches);
  2. the counts the model's segments use: elpis sums a thread's 8 p sequentially (loops nt < 4, e < 2 around
     one f_add) and quad-reduces twice at the end; stock's tl.sum is one pair add, two shuffle levels, a shared
     cross-warp pass with two more shuffle levels (PTX); 16 QK and 2 PV MMA k-steps per tile in both;
  3. ext 3022 patches pattn_kernel.cuh and pattn8_kernel.cuh with the same arithmetic lines (3020 is the
     8-warp mapping of 3010's per-warp text, pattn8_sched_laws.bend);
  4. the 5111 fused conv kernel keeps the stock output kernel's arithmetic lines in order and adds only the
     in-kernel .to(tl.bfloat16) of the fp32 x;
  5. no patch of patches/exl3-ext/series touches vendor/fla (the chunked delta rule) and 5111's
     gated_delta_rule.py hunk adds no arithmetic (q / k / v plumbing only).
Text evidence, not a proof. `--mutate NAME` corrupts one expectation, which must be rejected.

Usage: python3 bend/err_prefill_diff.py [--mutate NAME] [STOCK_DIR [PTX_DIR]]
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

WT = Path(__file__).resolve().parent.parent
EXT = WT / "patches/exl3-ext"
STOCK_DEFAULT = Path("/tmp/kernel-work/PrecisionLaw/stock/exllamav3")
PTX_DEFAULT = Path("/tmp/kernel-work/PrefixPersist/p3022/ptx")

# (file key, line, expected substring)
CITES = [
    # stock Triton prefill (TP)
    ("TP", 1317, "scores = tl.dot(q_tile, k_tile)"),
    ("TP", 1323, "scores = scores * qk_scale_log2e"),
    ("TP", 1340, "p = tl.exp2(scores - m_exp[:, None])"),
    ("TP", 1343, 'alpha = tl.where(m == -float("inf"), 0.0, tl.exp2(m - m_exp))'),
    ("TP", 1345, "alpha = tl.exp2(m - m_exp)"),
    ("TP", 1346, "l = l * alpha + tl.sum(p, axis = 1)"),
    ("TP", 1376, "acc = acc * alpha[:, None] + tl.dot(p.to(v_tile.dtype), v_tile)"),
    ("TP", 1476, "span = tl.cdiv(tl.cdiv(n_hi - n_lo, num_splits), BLOCK_N) * BLOCK_N"),
    ("TP", 1477, "s_lo = n_lo + split * span"),
    ("TP", 1849, "if num_splits is None:"),
    ("TP", 1871, "num_splits = min(num_splits, max_splits)"),
    ("TP", 1533, "n_full = tl.maximum(((q_abs_min + 1) // BLOCK_N) * BLOCK_N, 0)"),
    ("TP", 1554, "if IS_SPLIT:"),
    ("TP", 1564, "tl.store(partial_ml + ml_base + tl.arange(0, BLOCK_M) * 2 + 1, l)"),
    ("TP", 1573, "out_tile = acc / tl.where(l[:, None] == 0.0, 1.0, l[:, None])"),
    ("TP", 1577, "tl.store(out_ptrs, out_tile"),
    ("TP", 1628, 'w = tl.where(m_s == -float("inf"), 0.0, tl.exp2(m_s - m_safe))'),
    ("TP", 1630, "acc += o_s * w[:, None]"),
    ("TP", 1631, "l_sum += l_s * w"),
    (
        "TP",
        1635,
        "out_tile = acc / tl.where(l_sum[:, None] == 0.0, 1.0, l_sum[:, None])",
    ),
    ("TP", 1806, "ext.dequant_cache_paged_window("),
    ("TP", 1825, "cfg = (64, 32, 8, 2)"),
    ("TP", 1858, "if bound_kv >= 8192 and programs:"),
    ("TP", 1869, "max_partial_bytes = 128 * 1024 * 1024"),
    # stock PTX (served constexprs, sm_86)
    ("PTX", 1838, "mma.sync.aligned.m16n8k16.row.col.f32.f16.f16.f32 { %r731"),
    ("PTX", 2039, "mma.sync.aligned.m16n8k16.row.col.f32.f16.f16.f32 { %r757"),
    ("PTX", 2042, "mul.f32 \t%r1127, %r731, 0f3DB8AA3B"),
    ("PTX", 2234, "fma.rn.f32 \t%r1187, %r731, 0f3DB8AA3B, %r1186"),
    ("PTX", 2258, "ex2.approx.ftz.f32"),
    ("PTX", 2275, "sub.f32"),
    ("PTX", 2297, "add.f32 \t%r1242, %r1210, %r1211"),
    ("PTX", 2307, "shfl.sync.bfly.b32 \t%r1250, %r1242, 2, 31, -1"),
    ("PTX", 2313, "shfl.sync.bfly.b32 \t%r1252, %r1251, 1, 31, -1"),
    ("PTX", 2404, "st.shared.b32 [ %r181 + 0 ], %r1027"),
    ("PTX", 2429, "ld.shared.b32 %r1035"),
    ("PTX", 2431, "shfl.sync.bfly.b32 \t%r1274, %r1035, 2, 31, -1"),
    ("PTX", 2437, "shfl.sync.bfly.b32 \t%r1276, %r1275, 1, 31, -1"),
    ("PTX", 2440, "add.f32 \t%r1036, %r1275, %r1276"),
    ("PTX", 2457, "fma.rn.f32 \t%r2572, %r2572, %r1241, %r1284"),
    ("PTX", 2703, "mul.f32 \t%r2492, %r2492, %r1234"),
    ("PTX", 2768, "cvt.rn.f16x2.f32"),
    (
        "PTX",
        2800,
        "mma.sync.aligned.m16n8k16.row.col.f32.f16.f16.f32 { %r2492, %r2493, %r2494, %r2495 }",
    ),
    (
        "PTX",
        2848,
        "mma.sync.aligned.m16n8k16.row.col.f32.f16.f16.f32 { %r2492, %r2493, %r2494, %r2495 }",
    ),
    ("PTX", 4107, "mul.f32 \t%r1975, %r1456, 0f3DB8AA3B"),
    ("PTX", 4382, "sub.f32 \t%r2058"),
    ("PTX", 5192, "div.full.f32"),
    # stock combine PTX
    ("CPTX", 186, "sub.f32"),
    ("CPTX", 188, "ex2.approx.ftz.f32"),
    ("CPTX", 522, "fma.rn.f32"),
    ("CPTX", 587, "fma.rn.f32"),
    ("CPTX", 943, "div.full.f32"),
    ("CPTX", 1400, "cvt.rn.f16.f32"),
    # stock TTGIR
    ("TTG", 208, "%acc_127 = arith.mulf %arg21, %acc_126"),
    ("TTG", 213, "tt.dot %acc_130, %v_tile_131, %acc_127"),
    ("TTG", 327, "arith.truncf %out_tile_77"),
    # elpis 3010 / 3022
    ("P3010", 181, "ex2.approx.ftz.f32"),
    ("P3010", 283, "for (int g = 0; g < 8; ++g)"),
    ("P3010", 287, "for (int s = 0; s < 2; ++s)"),
    ("P3010", 305, "mma_f32(sc[nt], a[0], bk[0], bk[1]);"),
    ("P3010", 306, "mma_f32(sc[nt], a[1], bk[2], bk[3]);"),
    ("P3010", 364, "pa[kk][0] = pack_h2(sc[2 * kk][0], sc[2 * kk][1]);"),
    ("P3022", 127, "const int q_abs64 = total - q_len + (p0 & ~63);"),
    ("P3022", 128, "const int n_full = max(((q_abs64 + 1) / PA_BN) * PA_BN, 0);"),
    ("P3022", 154, "+        *reinterpret_cast<uint4*>(qs + swz(row, ch * 8)) = u;"),
    ("P3022", 178, "const bool interior = n0 + PA_BN <= n_full;"),
    ("P3022", 190, "sc[nt][e] = f_mul(sc[nt][e], scale_log2);"),
    ("P3022", 230, "alpha[r] = is_ninf(m[r]) ? 0.f : ex2(f_sub(m[r], m_use));"),
    ("P3022", 231, "float sum = 0.f;"),
    ("P3022", 233, "for (int nt = 0; nt < 4; ++nt)"),
    ("P3022", 235, "for (int e = 0; e < 2; ++e)"),
    (
        "P3022",
        239,
        "float p = ex2(interior ? f_fma(x, scale_log2, f_neg(m_use)) : f_sub(x, m_use));",
    ),
    ("P3022", 242, "+                    sum = f_add(sum, p);"),
    ("P3022", 245, "+            l[r] = f_fma(l[r], alpha[r], sum);"),
    ("P3022", 268, "float tp[4] = {0.f, 0.f, 0.f, 0.f};"),
    ("P3022", 269, "mma_f32(tp, pa[0], bv[0][2 * hn], bv[0][2 * hn + 1]);"),
    ("P3022", 270, "mma_f32(tp, pa[1], bv[1][2 * hn], bv[1][2 * hn + 1]);"),
    (
        "P3022",
        271,
        "o[0] = f_fma_pv(o[0], alpha[0], tp[0]); o[1] = f_fma_pv(o[1], alpha[0], tp[1]);",
    ),
    (
        "P3022",
        283,
        "+        l[r] = f_add(l[r], __shfl_xor_sync(0xffffffffu, l[r], 1));",
    ),
    (
        "P3022",
        284,
        "+        l[r] = f_add(l[r], __shfl_xor_sync(0xffffffffu, l[r], 2));",
    ),
    (
        "P3022",
        294,
        "pack_h2(f_div_full(acc[j][2 * r], l[r]), f_div_full(acc[j][2 * r + 1], l[r]))",
    ),
    ("P3022", 512, "kv_append_len, float(softmax_scale) * 1.4426950408889634, 0)"),
    # GDN conv
    ("CONV", 9, "MAX_CUDA_SEQLEN = 32"),
    ("CONV", 145, "acc = tl.zeros((BLOCK_D, BLOCK_S), dtype = tl.float32)"),
    ("CONV", 165, "acc += vals * w[:, None]"),
    ("CONV", 169, "acc += b[:, None]"),
    ("CONV", 171, "acc = acc * tl.sigmoid(acc)"),
    ("CONV", 280, "if seq_len <= 256:"),
    ("CONV", 283, "_causal_conv1d_update_slotted_kernel[grid]("),
    ("CONV", 306, "_causal_conv1d_update_slotted_output_kernel[output_grid]("),
    ("CONV", 387, "seqlen <= MAX_CUDA_SEQLEN and"),
    ("CONV", 395, "ext.cuda_causal_conv1d_update("),
    ("GDN", 1106, "mixed_qkv = qkv.transpose(1, 2).to(torch.bfloat16).contiguous()"),
    (
        "P5111",
        39,
        "bsz == 1 and seqlen > 256 and seqlen >= self.num_v_heads and not save_history and",
    ),
    ("P5111", 125, "acc = tl.zeros((BLOCK_D, BLOCK_S), dtype = tl.float32)"),
    ("P5111", 142, ").to(tl.bfloat16)"),
    ("P5111", 145, "acc += vals * w[:, None]"),
    ("P5111", 149, "acc += b[:, None]"),
    ("P5111", 151, "acc = acc * tl.sigmoid(acc)"),
    (
        "P5111",
        159,
        "tl.store(out + dst, acc, mask = mask_d[:, None] & mask_s[None, :])",
    ),
    # prefill GEMM (stock f16acc)
    ("HF", 30, "KSLICE = 32"),
    ("HF", 62, "a += f.x;"),
    ("HF", 258, "uint32_t h[2] = {};"),
    ("HF", 259, "mma_f16(h, af[0][i], bf[0][j]);"),
    ("HF", 260, "mma_f16(h, af[1][i], bf[1][j]);"),
    ("HF", 261, "add_half_pair(acc[i][j][0], acc[i][j][1], h[0]);"),
]

# model expressions err_prefill.bend must contain (the segment counts above)
MODEL = [
    "def e_later() -> Eb.Path:\n  Eb.Path{2n, 0n, 0n, 0n, 0n, 1n, 0n, 0n}",
    "def den_later() -> Eb.Path:\n  Eb.Path{2n, 0n, 0n, 0n, 0n, 1n, 0n, 0n}",
    "def e_den_in() -> Eb.Path:\n  Eb.Path{9n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}",
    "def s_later() -> Eb.Path:\n  Eb.Path{2n, 2n, 0n, 0n, 0n, 1n, 0n, 0n}",
    "def s_den_in() -> Eb.Path:\n  Eb.Path{5n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}",
    "def fixed() -> Eb.Path:\n  Eb.Path{0n, 0n, 2n, 0n, 0n, 0n, 1n, 0n}",
]

MUTATIONS = {
    "elpis_sequential_sum": (
        "P3022",
        235,
        "for (int e = 0; e < 2; ++e)",
        "for (int e = 0; e < 4; ++e)",
    ),
    "stock_pv_fused": (
        "TTG",
        213,
        "tt.dot %acc_130, %v_tile_131, %acc_127",
        "tt.dot %acc_130, %v_tile_131, %cst_2",
    ),
    "model_den": ("MODEL", 2, "Eb.Path{9n,", "Eb.Path{7n,"),
}


def fail(msg: str) -> None:
    raise SystemExit(f"err_prefill_diff: FAIL: {msg}")


def lines_of(p: Path) -> list[str]:
    if not p.is_file():
        fail(f"missing source {p}")
    return p.read_text().splitlines()


def added(patch: list[str], file_marker: str) -> list[str]:
    """'+' lines of the hunks of one file of a patch (file_marker in the +++ line)."""
    out, on = [], False
    for ln in patch:
        if ln.startswith("+++ "):
            on = file_marker in ln
            continue
        if on and ln.startswith("+"):
            out.append(ln[1:].strip())
    return out


ARITH = re.compile(
    r"\b(f_fma_pv|f_fma|f_add|f_sub|f_mul|f_max|f_div_full|ex2|mma_f32|pack_h2|is_zero|is_ninf)\("
)


def main(argv: list[str]) -> None:
    args = argv[1:]
    mutate = None
    if len(args) >= 2 and args[0] == "--mutate":
        mutate, args = args[1], args[2:]
    stock = Path(args[0]) if len(args) > 0 else STOCK_DEFAULT
    ptx = Path(args[1]) if len(args) > 1 else PTX_DEFAULT
    files = {
        "TP": stock / "modules/attention_fn/triton_paged.py",
        "CONV": stock / "modules/gated_delta_net_fn/conv1d.py",
        "GDN": stock / "modules/gated_delta_net.py",
        "HF": stock / "exllamav3_ext/hgemm_f16acc.cu",
        "PTX": ptx / "stock_prefill_sm86.ptx",
        "CPTX": ptx / "stock_combine_sm86.ptx",
        "TTG": ptx / "stock_prefill_sm86.ttgir",
        "P3010": EXT / "3010-prefill-pattn.patch",
        "P3022": EXT / "3022-prefill-pattn-fp32acc.patch",
        "P5111": EXT / "5111-gdn-prefill-fuse-nom4096.patch",
    }
    text = {k: lines_of(p) for k, p in files.items()}
    model = (WT / "bend/err_prefill.bend").read_text()
    cites = list(CITES)
    model_exp = list(MODEL)
    if mutate is not None:
        if mutate not in MUTATIONS:
            fail(f"unknown mutation {mutate!r}")
        key, line, old, new = MUTATIONS[mutate]
        if key == "MODEL":
            model_exp[line] = model_exp[line].replace(old, new)
        else:
            cites = [
                (k, n, new if (k, n, e) == (key, line, old) else e) for k, n, e in cites
            ]
        print(f"err_prefill_diff: applied mutation {mutate}")

    # 1. cited lines
    for key, n, e in cites:
        src = text[key]
        if n < 1 or n > len(src) or e not in src[n - 1]:
            got = src[n - 1].strip() if 1 <= n <= len(src) else "<none>"
            fail(f"{key}:{n}: expected {e!r}, found {got!r}")
    print(
        f"err_prefill_diff: {len(cites)} cited source lines hold the transcribed text"
    )

    # 2. counts: stock loop-1 body (PTX 1252-2906): 64 QK + 32 PV MMAs (16 + 2 k-steps over 4 x 1 and 4 x 4
    # fragments of the warp), 8 pair adds feeding the tree, exactly one fp32 fma per row for l
    body = text["PTX"][1251:2906]
    n_mma = sum(
        "mma.sync.aligned.m16n8k16.row.col.f32.f16.f16.f32" in ln for ln in body
    )
    if n_mma != 96:
        fail(
            f"PTX loop 1: {n_mma} f32 MMAs, want 96 (64 Q K^T: 16 k-steps x 4 m-tiles; 32 P V: 2 k-steps x 16)"
        )
    # tl.sum(p) of the row slots a thread holds (PTX 2297-2440): 8 pair adds, 2 shuffle-add levels for each of the
    # 8 slots, then the cross-warp slot: 2 more shuffle-add levels -> depth 1 + 2 + 2 = 5 per p
    red = text["PTX"][2296:2440]
    n_shfl = sum("shfl.sync.bfly.b32" in ln for ln in red)
    n_add = sum(re.match(r"\s*add\.f32\s", ln) is not None for ln in red)
    if (n_shfl, n_add) != (18, 26):
        fail(f"PTX tl.sum region: {n_shfl} shuffles, {n_add} adds (want 18, 26)")
    for m in model_exp:
        if m not in model:
            fail(f"err_prefill.bend: model segment missing: {m!r}")
    print(
        f"err_prefill_diff: {len(model_exp)} model segments present; PTX loop has 96 fp32 MMAs"
    )

    # 3. 3022: identical arithmetic in pattn_kernel.cuh and pattn8_kernel.cuh
    p22 = text["P3022"]
    a1 = [
        ln for ln in added(p22, "b/exllamav3_ext/pattn_kernel.cuh") if ARITH.search(ln)
    ]
    a2 = [
        ln for ln in added(p22, "b/exllamav3_ext/pattn8_kernel.cuh") if ARITH.search(ln)
    ]
    a1 = [ln for ln in a1 if not ln.startswith("__device__")]
    if a1 != a2:
        fail(
            f"3022 arithmetic differs between pattn_kernel.cuh and pattn8_kernel.cuh:\n{a1}\n{a2}"
        )
    print(
        f"err_prefill_diff: 3022 adds the same {len(a1)} arithmetic lines to pattn and pattn8"
    )

    # 4. 5111 fused conv keeps the stock output kernel's arithmetic lines in order
    conv = text["CONV"]
    s0 = next(
        i
        for i, ln in enumerate(conv)
        if "def _causal_conv1d_update_slotted_output_kernel(" in ln
    )
    s1 = next(
        i for i in range(s0, len(conv)) if "acc = acc * tl.sigmoid(acc)" in conv[i]
    )
    stock_ar = [
        ln.strip() for ln in conv[s0 : s1 + 1] if re.search(r"\bacc\b.*=|\bacc \+=", ln)
    ]
    f22 = added(text["P5111"], "b/modules/gated_delta_net_fn/conv1d.py")
    f0 = next(
        i
        for i, ln in enumerate(f22)
        if ln.startswith("def _conv1d_prefill_qkv_output_kernel(")
    )
    f1 = next(i for i in range(f0, len(f22)) if "acc = acc * tl.sigmoid(acc)" in f22[i])
    fused_ar = [ln for ln in f22[f0 : f1 + 1] if re.search(r"\bacc\b.*=|\bacc \+=", ln)]
    if stock_ar != fused_ar:
        fail(f"5111 conv arithmetic differs from stock:\n{stock_ar}\n{fused_ar}")
    casts = [
        ln
        for ln in f22[f0 : f1 + 1]
        if "tl.bfloat16" in ln or "tl.float32" in ln and "acc" not in ln
    ]
    if casts != [").to(tl.bfloat16)"]:
        fail(f"5111 conv: unexpected casts {casts}")
    print(
        f"err_prefill_diff: 5111 conv keeps the stock {len(stock_ar)} accumulator lines; one added bf16 cast"
    )

    # 5. chunked delta rule untouched
    series = [
        ln.split()[-1] for ln in (EXT / "series").read_text().splitlines() if ln.strip()
    ]
    for name in series:
        for ln in lines_of(EXT / name):
            if ln.startswith("+++ ") and "vendor/" in ln:
                fail(f"{name} touches {ln}")
    rule = added(text["P5111"], "b/modules/gated_delta_net_fn/gated_delta_rule.py")
    bad = [
        ln
        for ln in rule
        if re.search(r"tl\.|exp|l2norm|float|bfloat16|\*|chunk_gated_delta_rule\(", ln)
    ]
    if bad:
        fail(f"5111 gated_delta_rule.py adds arithmetic: {bad}")
    print(
        f"err_prefill_diff: {len(series)} series patches leave vendor/fla untouched; 5111 rule hunk is plumbing"
    )
    print("err_prefill_diff: OK")


if __name__ == "__main__":
    main(sys.argv)
