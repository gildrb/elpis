#!/usr/bin/env python3
"""
Source-link check of bend/err_gemm.bend (rounding-step Paths of the served decode GEMMs).

The Bend model transcribes, per leaf, the rounding steps of stock ExLlamaV3 355c6ee (STOCK) and of
the elpis extension series applied to it (patches/exl3/series, then patches/exl3-ext/series, in
order). This script
  1. builds the elpis tree in a temporary directory (copy of STOCK, `patch -p1` of every series
     patch, failing on any rejected hunk);
  2. checks that the series leaves the shared numerics files byte-identical (hadamard_inner.cuh,
     codebook.cuh, exl3_dq.cuh, exl3_gemm_inner.cuh, exl3_gemm_kernel.cuh, exl3_gemv_int8*), the
     model's "same code on both sides" premise;
  3. checks every source fragment the model transcribes (whitespace-normalised, verbatim) in STOCK
     and in the elpis tree.
Exit status 0 iff every check passes.

Usage: python3 -B bend/err_gemm_diff.py [--stock STOCK]
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DEFAULT_STOCK = "/tmp/kernel-work/PrecisionLaw/stock/exllamav3"
SERIES = [REPO / "patches/exl3", REPO / "patches/exl3-ext"]
SHARED = [
    "exllamav3_ext/quant/hadamard_inner.cuh",
    "exllamav3_ext/quant/codebook.cuh",
    "exllamav3_ext/quant/exl3_dq.cuh",
    "exllamav3_ext/quant/exl3_gemm_inner.cuh",
    "exllamav3_ext/quant/exl3_gemm_kernel.cuh",
    "exllamav3_ext/quant/exl3_gemv_int8.cu",
    "exllamav3_ext/quant/exl3_gemv_int8_kernel.cuh",
]
# (file, fragment, what err_gemm.bend reads from it)
STOCK_FRAGMENTS = [
    (
        "exllamav3_ext/quant/hadamard_inner.cuh",
        "v.x = __hmul2(v.x, scales.x);",
        "had_in pre-scale / had_hf post-scale r16",
    ),
    (
        "exllamav3_ext/quant/hadamard_inner.cuh",
        "float s0 = v0 + v1;",
        "butterfly level 1 (r32)",
    ),
    (
        "exllamav3_ext/quant/hadamard_inner.cuh",
        "float h0 = s0 + s1;",
        "butterfly level 2 (r32)",
    ),
    (
        "exllamav3_ext/quant/hadamard_inner.cuh",
        "for (int i = 1; i < 32; i <<= 1)",
        "5 shuffle levels",
    ),
    (
        "exllamav3_ext/quant/hadamard_inner.cuh",
        "h0 = __uint_as_float(i0) + ph0;",
        "one fp32 add per shuffle level",
    ),
    (
        "exllamav3_ext/quant/hadamard_inner.cuh",
        "v.x = __floats2half2_rn(h0 * r_scale, h1 * r_scale);",
        "* r_scale (r32), to fp16 (r16)",
    ),
    (
        "exllamav3_ext/quant/hadamard_inner.cuh",
        "v.x *= r_scale;",
        "had_ff / had_fh * r_scale (r32)",
    ),
    (
        "exllamav3_ext/quant/hadamard_inner.cuh",
        "v.x *= __low2float(scales.x);",
        "had_ff post-scale (r32)",
    ),
    (
        "exllamav3_ext/quant/hadamard_inner.cuh",
        "o.x = __floats2half2_rn(v.x, v.y);",
        "had_fh to fp16 (r16)",
    ),
    (
        "exllamav3_ext/quant/hadamard_inner.cuh",
        "o.x = __hmul2(o.x, scales.x);",
        "had_fh post-scale (r16)",
    ),
    (
        "exllamav3_ext/quant/codebook.cuh",
        "return __hfma2(__halves2half2(h0.as_half, h1.as_half), k_inv_h2, k_bias_h2);",
        "dq: one hfma (r16)",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_inner.cuh",
        "dq_dispatch<bits, cb>(shb, lane_id << 3, frag_b[buf][n2], frag_b[buf][n2 + 1]);",
        "stock decode",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_inner.cuh",
        "frag_c[0][n][0] += f0.x; frag_c[0][n][1] += f0.y;",
        "fold into fp32",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_inner.cuh",
        "int lock_i = tiles_k - slice2_k - 1;",
        "lock order (descending k)",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_inner.cuh",
        "if (!sub_k && !first)",
        "read-back of the running partial",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_inner.cuh",
        "frag_c[m][n][0] += interm.x;",
        "partial add (r32)",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_inner.cuh",
        "half2 sum = __floats2half2_rn(frag_c[0][n][0], frag_c[0][n][1]);",
        "fp16 partial / C store (r16)",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_inner.cuh",
        "if (slice2_k == tiles_k - 1 || slice2_iters == 1) { reduce(); slice2_k0 = slice2_k + 1; }",
        "one run per column piece",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_inner.cuh",
        "barrier_release(lock, lock_d, last); clear_frag_c();",
        "fold into a cleared accumulator",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_kernel.cuh",
        "<bits, c_fp32, cb, TILESIZE_M, TILESIZE_K, TILESIZE_N, SH_STAGES, FRAG_STAGES, false>",
        "mgemm: no shmem output had",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_kernel.cuh",
        "had_hf_r_128_inner<false, true>",
        "mgemm fp16 output pass",
    ),
    (
        "exllamav3_ext/quant/exl3_gemv_int8_kernel.cuh",
        "had_hf_r_128_inner<true, false>(Ar + (kb0 << 4) + (sp << 7), sh_ah + (sp << 7), suh + (kb0 << 4) + (sp << 7), 0.088388347648f);",
        "int8 input had",
    ),
    ("exllamav3_ext/quant/exl3_gemv_int8_kernel.cuh", "float rq = 1.0f / q_s;", "rcp"),
    (
        "exllamav3_ext/quant/exl3_gemv_int8_kernel.cuh",
        "int v = __float2int_rn(a * rq);",
        "a * rq (r32), q8",
    ),
    (
        "exllamav3_ext/quant/exl3_gemv_int8_kernel.cuh",
        "acc[i] += q_s * (float) __ldcg(p + lane * 4 + i);",
        "cvt (r32) + slice fma (r32)",
    ),
    (
        "exllamav3_ext/quant/exl3_gemv_int8_kernel.cuh",
        "tmp[lane * 4 + i] = k_inv * acc[i] + corr;",
        "affine fma (r32)",
    ),
    ("exllamav3_ext/gdn.cu", "sum = fmaf(xf.x, wf.x, sum);", "stock b/a lane chain"),
    (
        "exllamav3_ext/gdn.cu",
        "for (int j = lane; j < k / 2; j += 32)",
        "stock b/a: k / 2 / 32 half2 per lane",
    ),
    (
        "exllamav3_ext/gdn.cu",
        "sum += __shfl_down_sync(0xffffffff, sum, offset);",
        "5 shuffle adds",
    ),
    ("exllamav3_ext/gdn.cu", "if (bias) sum += __half2float(bias[row]);", "bias add"),
    (
        "architecture/qwen3_5.py",
        "interm_dtype = torch.half, out_dtype = torch.float, )",
        "gate / up fp16, down fp32 C",
    ),
]
ELPIS_FRAGMENTS = [
    (
        "exllamav3_ext/quant/exl3_gemm_m16g_kernel.cuh",
        "had_hf_r_128_inner<true, false> ( A + r * 128,",
        "m16g input had",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_m16g_kernel.cuh",
        "acc[t][mt][0] += __low2float(hacc[t][mt][0]);",
        "fold (r32)",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_m16g_kernel.cuh",
        "hacc[t][mt][0] = hzero;",
        "run restarts from 0",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_m16g_kernel.cuh",
        "if ((x_off & (FO * X_ITER - 1)) == 0) fold();",
        "fold every FO tiles",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_m16g_kernel.cuh",
        "const int seg_end = min(e_b, (g_cur + 1) * KT) - s_b;",
        "a segment lies in one group",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_m16g_kernel.cuh",
        "if (row < size_m) __stcg(slot + row * GW + t * 16 + (c >> 1) * 8, acc[t][mt][c]);",
        "exact fp32 slot store",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_m16g_kernel.cuh",
        "for (int c = 1; c < nc; ++c)",
        "finisher slot order",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_m16g_kernel.cuh",
        "v.x += u.x; v.y += u.y; v.z += u.z; v.w += u.w;",
        "finisher adds (r32)",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_m16g_kernel.cuh",
        "had_ff_r_128_inner<false, true> ( s0,",
        "m16g fp32 output",
    ),
    (
        "exllamav3_ext/quant/exl3_gemm_m16g_kernel.cuh",
        "had_fh_r_128_inner<false, true> ( s0,",
        "m16g fp16 output",
    ),
    (
        "exllamav3_ext/quant/exl3_m16_decode.cuh",
        "frag0[0] = decode_3inst_2<cb>(w0, w1);",
        "diet decode = decode_3inst_2",
    ),
    (
        "exllamav3_ext/quant/exl3_mlp_m16_kernel.cuh",
        "(exl3_m16_had_load / _store = had_hf_r_128_inner<true, false>)",
        "first input-had job",
    ),
    (
        "exllamav3_ext/quant/exl3_tail_m16_kernel.cuh",
        "if ((x_off & (FO * X_ITER - 1)) == 0) fold();",
        "tail fold every FO tiles",
    ),
    (
        "exllamav3_ext/quant/exl3_tail_m16_kernel.cuh",
        "acc4.x += w4.x; acc4.y += w4.y; acc4.z += w4.z; acc4.w += w4.w;",
        "tail finisher adds",
    ),
    (
        "exllamav3_ext/quant/exl3_tail_m16_kernel.cuh",
        "had_ff_r_128_inner<false, true>(sl0, yo, p.svh_o + col0, 0.088388347648f);",
        "o_proj had_ff",
    ),
    (
        "exllamav3_ext/quant/exl3_tail_m16_kernel.cuh",
        "had_hf_r_128_inner<true, false>(xn, q.xh_g + (size_t) r * K1 + col0, q.suh_g + col0, 0.088388347648f);",
        "gate input had",
    ),
    (
        "exllamav3_ext/quant/exl3_tail_m16_kernel.cuh",
        "had_fh_r_128_inner<false, true> ( sl0, (mat ? p.u : p.g)",
        "gate / up had_fh",
    ),
    (
        "exllamav3_ext/quant/exl3_tail_m16_kernel.cuh",
        "had_hf_r_128_inner<true, false> ( q.a + (size_t) r * K2 + col0,",
        "down input had",
    ),
    (
        "exllamav3_ext/quant/exl3_tail_m16_kernel.cuh",
        "had_ff_r_128_inner<false, true>(sl0, D + (size_t) r * N2 + col0, q.svh_d + col0, 0.088388347648f);",
        "down had_ff",
    ),
    (
        "exllamav3_ext/gdn.cu",
        "pb[s] = fmaf(xf.x, wbf.x, pb[s]); pb[s] = fmaf(xf.y, wbf.y, pb[s]);",
        "b/a partial fma chain",
    ),
    (
        "exllamav3_ext/gdn.cu",
        "pb[s] += __shfl_down_sync(0xffffffff, pb[s], offset);",
        "b/a shuffle tree",
    ),
    (
        "exllamav3_ext/gdn.cu",
        "bv += ks_part[w * 2 * GR_KS_ROWS + t];",
        "b/a warp-partial sum",
    ),
    ("exllamav3_ext/gdn.cu", "bv += __half2float(ba_bias[h]);", "b/a bias add"),
]


def norm(text: str) -> str:
    return re.sub(r"\s+", " ", text)


def series_patches(d: Path) -> list[Path]:
    return [
        d / line.split()[1]
        for line in (d / "series").read_text().splitlines()
        if line.strip()
    ]


def build(stock: Path, out: Path) -> list[str]:
    shutil.copytree(stock, out)
    errors = []
    for d in SERIES:
        for p in series_patches(d):
            r = subprocess.run(
                ["patch", "-p1", "-s", "-f", "--no-backup-if-mismatch", "-i", str(p)],
                cwd=out,
                capture_output=True,
                text=True,
            )
            if r.returncode != 0:
                errors.append(
                    f"patch failed: {p.name}: {r.stdout.strip()} {r.stderr.strip()}"
                )
    return errors


def check(tree: Path, frags, label: str) -> int:
    bad = 0
    for rel, frag, what in frags:
        f = tree / rel
        ok = f.is_file() and norm(frag) in norm(f.read_text())
        print(f"{'IDENTICAL' if ok else 'MISSING  '} {label} {rel}: {what}")
        bad += not ok
    return bad


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--stock", default=DEFAULT_STOCK)
    a = ap.parse_args()
    stock = Path(a.stock)
    bad = 0
    with tempfile.TemporaryDirectory() as tmp:
        tree = Path(tmp) / "elpis"
        for e in build(stock, tree):
            print(e)
            bad += 1
        for rel in SHARED:
            same = (stock / rel).read_bytes() == (tree / rel).read_bytes()
            print(f"{'IDENTICAL' if same else 'CHANGED  '} shared {rel}")
            bad += not same
        bad += check(stock, STOCK_FRAGMENTS, "stock")
        bad += check(tree, ELPIS_FRAGMENTS, "elpis")
    print(f"{bad} failure(s)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
