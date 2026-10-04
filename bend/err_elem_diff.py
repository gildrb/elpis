#!/usr/bin/env python3
"""
Finite source link of bend/err_elem.bend (rounding-error paths of the decode norms, residual adds,
SiLU * up and the inter-kernel dtypes) to the stock ExLlamaV3 355c6ee package and to the elpis
package (the stock package with patches/exl3/series and patches/exl3-ext/series applied by the
repository's own applier, built here in a temporary directory).

Checks, failing closed:
  1. every "S:<file>:<lines>" / "E:<file>:<lines>" citation in bend/err_elem.bend is listed in
     CITES below, and each CITES fragment occurs (whitespace-normalized) on the cited lines of the
     cited tree;
  2. the helpers both rms_norm_kernels use are token-identical in stock and elpis norm.cu
     (sum_sq4, apply4, write_half4, reduce_dyn), the rmf expression is the same text, and the
     elpis register branch accumulates columns t + i * blockDim.x, i < REG_COLS = 2, in order;
  3. elpis exl3_mlp_silu_h2 / exl3_mlp_act_mul_h2 are stock _silu(half2) / the act_mul_kernel_h
     ACT_SILU tail with names changed, and the operation lists stock_act_ops / elpis_act_ops in
     bend/err_elem.bend are the intrinsic sequence of the respective source bodies;
  4. the shape constants of bend/err_elem.bend (cols 1280, nthreads 1024, reduce_steps 10,
     tail_extra bounds 8 / 32) follow from the sources (N0, NCH, NUM_THREADS, launch formula);
  5. the m1map route records name the modeled kernels on the served routes (elpis verify:
     rms_norm_kernel input / final norm, exl3_tail_m16_kernel tail; stock M = 1: rms_norm_kernel
     norms, act_mul_kernel_h);
  6. with --sass SO [--cuobjdump BIN]: the compiled rms_norm_kernel<RES_IN, float, half, bf16,
     float> divides by MUFU.RCP + FFMA before MUFU.RSQ, and exl3_tail_m16_kernel<0, 2> loads the
     constant 0x394ccccd (RN(1/5120)) into the FFMA before its MUFU.RSQ (hypothesis H_sass).
Text evidence, not a proof. `--mutate NAME` applies a deliberate source mutation that must be rejected.

Usage: python3 bend/err_elem_diff.py [--mutate NAME] [--sass SO [--cuobjdump BIN]] [--m1map DIR] STOCK_PACKAGE_DIR
  STOCK_PACKAGE_DIR: the stock exllamav3 package directory at 355c6ee (OUT/stock of bend/engine_trees.py).
  DIR: the m1map output directory (m1map-map.json, m1map-stock.json): kernel maps that a GPU run of the
    served engine records. The repository alone cannot make it. Without --m1map, check 5 does not run and
    the script says so.
  BIN: the cuobjdump executable; without --cuobjdump, the cuobjdump on PATH.
"""

from __future__ import annotations

import importlib.util
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
MODEL = REPO / "bend/err_elem.bend"

NORM = "exllamav3_ext/norm.cu"
TAIL = "exllamav3_ext/quant/exl3_tail_m16_kernel.cuh"
MLP16 = "exllamav3_ext/quant/exl3_mlp_m16_kernel.cuh"
ACTK = "exllamav3_ext/activation_kernels.cuh"
ACTCU = "exllamav3_ext/activation.cu"
TRANS = "modules/transformer.py"
QWEN = "architecture/qwen3_5.py"

# (side, file, first line, last line, fragment): the fragment occurs on lines first..last.
CITES = [
    ("S", "ext.py", 92, 92, '"-lineinfo", "-O3", "--use_fast_math",'),
    ("E", "ext.py", 92, 92, '"-lineinfo", "-O3", "--use_fast_math",'),
    (
        "S",
        NORM,
        377,
        377,
        "int threads = MIN(NUM_THREADS, CEIL_DIVIDE(dim / 4, 32) * 32);",
    ),
    (
        "E",
        NORM,
        431,
        431,
        "int threads = MIN(NUM_THREADS, CEIL_DIVIDE(dim / 4, 32) * 32);",
    ),
    ("S", "modules/transformer.py", 168, 168, "self.mlp_norm.can_fuse_residual(x, y)"),
    (
        "S",
        TRANS,
        182,
        182,
        "y = self.mlp_norm.forward(y_resid, params, out_dtype = torch.half, residual_in = x)",
    ),
    (
        "S",
        "exllamav3_ext/libtorch/mlp.cpp",
        81,
        82,
        "if (act_silu) silu_mul_gr(g, u, a_n, act_limit, graph);",
    ),
    ("S", TRANS, 195, 195, "x += y"),
    (
        "S",
        "modules/embedding.py",
        19,
        19,
        "out_dtype: torch.dtype | None = torch.float,",
    ),
    (
        "S",
        TRANS,
        156,
        156,
        "y = self.attn_norm.forward(x, params, out_dtype = torch.half)",
    ),
    ("S", QWEN, 351, 351, "out_dtype = torch.float,"),
    ("S", QWEN, 382, 382, "out_dtype = torch.float,"),
    ("S", QWEN, 435, 435, "interm_dtype = torch.half,"),
    (
        "S",
        ACTCU,
        71,
        71,
        "act_mul_kernel_h<ACT_SILU><<<blocks, NUM_THREADS, 0, stream>>>",
    ),
    ("S", ACTCU, 47, 47, "TORCH_CHECK_DTYPE(z, kHalf);"),
    ("S", QWEN, 436, 436, "out_dtype = torch.float,"),
    ("S", QWEN, 463, 463, "out_dtype = torch.half,"),
    ("E", TRANS, 128, 128, "x.dtype != torch.float"),
    (
        "E",
        TAIL,
        74,
        74,
        "void exl3_tail_m16_kernel(const half* __restrict__ Ao, float* X, float* D, Exl3TailM16Args p)",
    ),
    (
        "E",
        TRANS,
        233,
        233,
        "y = self.attn_norm.forward(pending[1], params, out_dtype = torch.half, residual_in = x)",
    ),
    (
        "E",
        TRANS,
        235,
        235,
        "y = self.attn_norm.forward(x, params, out_dtype = torch.half)",
    ),
    ("E", TAIL, 49, 49, "float* yo;"),
    ("E", TAIL, 50, 50, "half* xn;"),
    (
        "E",
        TAIL,
        680,
        681,
        "xo[0] = __halves2half2(__float2half_rn(x4.x), __float2half_rn(x4.y)); xo[1] = __halves2half2(__float2half_rn(x4.z), __float2half_rn(x4.w));",
    ),
    ("E", TAIL, 61, 62, "half* g; half* u;"),
    ("E", TAIL, 751, 751, "half2* ap = (half2*) (q.a + o);"),
    (
        "E",
        TAIL,
        819,
        819,
        "had_ff_r_128_inner<false, true>(sl0, D + (size_t) r * N2 + col0, q.svh_d + col0, 0.088388347648f);",
    ),
    ("E", QWEN, 463, 463, "out_dtype = torch.half,"),
    (
        "E",
        TAIL,
        611,
        615,
        "y4.x += r4.x; y4.y += r4.y; y4.z += r4.z; y4.w += r4.w; *xp = y4;",
    ),
    ("E", NORM, 227, 230, "x4.x += r4.x; x4.y += r4.y; x4.z += r4.z; x4.w += r4.w;"),
    (
        "E",
        NORM,
        319,
        319,
        "if constexpr (res_mode == RES_IN) add_resid_in(x4[i], r4[i], column);",
    ),
    ("E", TRANS, 257, 257, "x += y"),
    ("E", TRANS, 296, 296, "x += y"),
    ("S", NORM, 209, 212, "x4.x += r4.x; x4.y += r4.y; x4.z += r4.z; x4.w += r4.w;"),
    (
        "S",
        NORM,
        101,
        108,
        "lsum = fma(f4.x, f4.x, lsum); lsum = fma(f4.y, f4.y, lsum); lsum = fma(f4.z, f4.z, lsum); lsum = fma(f4.w, f4.w, lsum);",
    ),
    (
        "S",
        NORM,
        103,
        106,
        "lsum = fma(f4.x, f4.x, lsum); lsum = fma(f4.y, f4.y, lsum); lsum = fma(f4.z, f4.z, lsum); lsum = fma(f4.w, f4.w, lsum);",
    ),
    (
        "E",
        NORM,
        119,
        122,
        "lsum = fma(f4.x, f4.x, lsum); lsum = fma(f4.y, f4.y, lsum); lsum = fma(f4.z, f4.z, lsum); lsum = fma(f4.w, f4.w, lsum);",
    ),
    (
        "S",
        NORM,
        285,
        285,
        "for (int column = t; column < columns; column += blockDim.x)",
    ),
    (
        "E",
        NORM,
        294,
        295,
        "constexpr int REG_COLS = 2; if (columns <= REG_COLS * (int) blockDim.x)",
    ),
    (
        "E",
        NORM,
        313,
        321,
        "for (int i = 0; i < REG_COLS; ++i) { int column = t + i * blockDim.x; if (column < columns) {",
    ),
    (
        "S",
        NORM,
        140,
        151,
        "for (int offset = 16; offset > 0; offset /= 2) sum += __shfl_xor_sync(0xffffffff, sum, offset); int num_warps = blockDim.x / 32; if (num_warps == 1) return sum;",
    ),
    (
        "E",
        NORM,
        156,
        167,
        "for (int offset = 16; offset > 0; offset /= 2) sum += __shfl_xor_sync(0xffffffff, sum, offset); int num_warps = blockDim.x / 32; if (num_warps == 1) return sum;",
    ),
    (
        "S",
        NORM,
        293,
        293,
        "float rmf = rsqrtf(sum / (float) dim + epsilon) * constant_scale;",
    ),
    (
        "E",
        NORM,
        324,
        324,
        "float rmf = rsqrtf(sum / (float) dim + epsilon) * constant_scale;",
    ),
    (
        "E",
        TAIL,
        643,
        643,
        "const float rmf = rsqrtf(sum / (float) N0 + p.eps) * p.nscale;",
    ),
    (
        "S",
        NORM,
        112,
        115,
        "x4.x = x4.x * w4.x * rmf; x4.y = x4.y * w4.y * rmf; x4.z = x4.z * w4.z * rmf; x4.w = x4.w * w4.w * rmf;",
    ),
    (
        "E",
        NORM,
        128,
        131,
        "x4.x = x4.x * w4.x * rmf; x4.y = x4.y * w4.y * rmf; x4.z = x4.z * w4.z * rmf; x4.w = x4.w * w4.w * rmf;",
    ),
    ("E", NORM, 266, 266, "apply4(x4, w4, rmf);"),
    (
        "E",
        TAIL,
        674,
        677,
        "x4.x = x4.x * w4.x * rmf; x4.y = x4.y * w4.y * rmf; x4.z = x4.z * w4.z * rmf; x4.w = x4.w * w4.w * rmf;",
    ),
    (
        "S",
        NORM,
        79,
        79,
        "__halves2half2(__float2half_rn(f4.x), __float2half_rn(f4.y)),",
    ),
    (
        "E",
        NORM,
        95,
        95,
        "__halves2half2(__float2half_rn(f4.x), __float2half_rn(f4.y)),",
    ),
    (
        "S",
        NORM,
        239,
        242,
        "w4.x += constant_bias; w4.y += constant_bias; w4.z += constant_bias; w4.w += constant_bias;",
    ),
    (
        "E",
        NORM,
        255,
        258,
        "w4.x += constant_bias; w4.y += constant_bias; w4.z += constant_bias; w4.w += constant_bias;",
    ),
    (
        "E",
        TAIL,
        669,
        672,
        "w4.x += p.nbias; w4.y += p.nbias; w4.z += p.nbias; w4.w += p.nbias;",
    ),
    ("S", NORM, 195, 195, "bool single = columns <= blockDim.x;"),
    (
        "S",
        NORM,
        282,
        307,
        "else { float sum = 0.0f; for (int column = t; column < columns; column += blockDim.x)",
    ),
    (
        "E",
        TAIL,
        579,
        685,
        "// ---- F0: o_proj finish + residual add + per-chunk sums of squares.",
    ),
    (
        "E",
        TAIL,
        616,
        620,
        "float ss = 0.0f; ss = fma(y4.x, y4.x, ss); ss = fma(y4.y, y4.y, ss); ss = fma(y4.z, y4.z, ss); ss = fma(y4.w, y4.w, ss);",
    ),
    (
        "E",
        TAIL,
        621,
        622,
        "for (int o = 16; o > 0; o >>= 1) ss += __shfl_xor_sync(0xffffffff, ss, o);",
    ),
    ("E", TAIL, 623, 623, "if (lane == 0) __stcg(p.ssq + r * NCH + g * 4 + ch, ss);"),
    (
        "E",
        TAIL,
        639,
        640,
        "float sum = __ldcg(p.ssq + r * NCH + lane); if (lane + 32 < NCH) sum += __ldcg(p.ssq + r * NCH + lane + 32);",
    ),
    (
        "E",
        TAIL,
        641,
        642,
        "for (int o = 16; o > 0; o >>= 1) sum += __shfl_xor_sync(0xffffffff, sum, o);",
    ),
    (
        "S",
        ACTK,
        22,
        31,
        "half2 one = __float2half2_rn(1.0f); half2 neg_x = __hneg2(x); half2 e = h2exp(neg_x); half2 sum = __hadd2(one, e); half2 r = h2rcp(sum); half2 result = __hmul2(x, r);",
    ),
    ("S", ACTK, 169, 185, "x2 = _silu(x2);"),
    ("S", ACTK, 169, 185, "((half2*) z)[idx] = __hmul2(x2, y2);"),
    ("E", MLP16, 138, 160, "half2 r = h2rcp(sum); half2 result = __hmul2(x, r);"),
    ("E", MLP16, 138, 160, "return __hmul2(x2, y2);"),
    (
        "E",
        TAIL,
        752,
        753,
        "ap[0] = exl3_mlp_act_mul_h2(gp[0], up[0], q.act_limit); ap[1] = exl3_mlp_act_mul_h2(gp[1], up[1], q.act_limit);",
    ),
]

MUTATIONS = {
    # tail N phase: the lane + 32 chunk add widened (one more add for more chunks)
    "tail_extra": (
        TAIL,
        "if (lane + 32 < NCH) sum += __ldcg(p.ssq + r * NCH + lane + 32);",
        "if (lane + 24 < NCH) sum += __ldcg(p.ssq + r * NCH + lane + 24);",
    ),
    # elpis reduce_dyn: one butterfly level more
    "reduce_dyn": (
        NORM,
        "    for (int offset = 16; offset > 0; offset /= 2) sum += __shfl_xor_sync(0xffffffff, sum, offset);\n    int num_warps",
        "    for (int offset = 32; offset > 0; offset /= 2) sum += __shfl_xor_sync(0xffffffff, sum, offset);\n    int num_warps",
    ),
    # elpis silu: sigmoid multiplied before the reciprocal
    "silu_order": (
        MLP16,
        "    half2 r = h2rcp(sum);\n    half2 result = __hmul2(x, r);",
        "    half2 result = __hmul2(x, sum);\n    half2 r = h2rcp(result);",
    ),
    # elpis register branch: three columns per thread
    "reg_cols": (NORM, "constexpr int REG_COLS = 2;", "constexpr int REG_COLS = 3;"),
}


def fail(msg: str) -> None:
    raise SystemExit(f"err_elem_diff: FAIL: {msg}")


def flat(text: str) -> str:
    text = re.sub(r"//[^\n]*", "", text)
    return re.sub(r"\s+", " ", text).strip()


def norm_lines(text: str) -> list[str]:
    out = []
    for line in text.split("\n"):
        line = re.sub(r"//.*", "", line).strip()
        line = re.sub(r"\s+", " ", line)
        if line:
            out.append(line)
    return out


def seg(text: str, start: str, end: str, what: str) -> str:
    i = text.find(start)
    if i < 0 or text.find(start, i + 1) >= 0:
        fail(f"{what}: start anchor {start!r} must occur exactly once")
    j = text.find(end, i + len(start))
    if j < 0:
        fail(f"{what}: end anchor {end!r} not found")
    return text[i:j]


def build_elpis(stock: Path, work: Path) -> Path:
    """The stock package with patches/exl3 and the pinned patches/exl3-ext series applied."""
    sys.path.insert(0, str(REPO))
    spec = importlib.util.spec_from_file_location(
        "ext", REPO / "patches/exl3-ext/ext.py"
    )
    ext = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ext)
    manifest = ext.load()
    source = manifest["source"]
    if ext.tree_digest(stock / source["tree"]) != source["tree_sha256"]:
        fail(f"{stock}: extension sources differ from the pinned 355c6ee tree")
    root = ext.engine_copy(stock, work / "elpis")
    ext.apply_series(manifest, root)
    return root


def citations(model: str) -> set[tuple[str, str, int]]:
    out = set()
    for m in re.finditer(r"\b([SE]):([\w./]+\.(?:cu|cuh|py|cpp|h)):([\d,\-]+)", model):
        side, path = m.group(1), m.group(2)
        for part in m.group(3).strip(",-").split(","):
            if not part:
                continue
            a, _, b = part.partition("-")
            for n in range(int(a), int(b or a) + 1):
                out.add((side, path, n))
    return out


def check_cites(trees: dict[str, Path], model: str) -> None:
    covered = set()
    for side, path, a, b, frag in CITES:
        lines = (trees[side] / path).read_text().split("\n")
        if b > len(lines):
            fail(f"{side}:{path}:{a}-{b}: past end of file")
        window = flat("\n".join(lines[a - 1 : b]))
        if flat(frag) not in window:
            fail(
                f"{side}:{path}:{a}-{b}: {frag!r} not found (lines read: {window[:200]!r})"
            )
        covered |= {(side, path, n) for n in range(a, b + 1)}
    missing = sorted(c for c in citations(model) if c not in covered)
    if missing:
        fail(f"citations without a checked fragment: {missing[:10]}")
    print(
        f"err_elem_diff: {len(CITES)} cited fragments found; every citation of err_elem.bend covered"
    )


def check_helpers(s: dict[str, str], e: dict[str, str]) -> None:
    for name, start, end in (
        (
            "sum_sq4",
            "__device__ inline float sum_sq4",
            "__device__ inline void apply4(",
        ),
        (
            "apply4",
            "__device__ inline void apply4(",
            "__device__ inline void apply4_nw",
        ),
        (
            "write_half4",
            "__device__ inline void write_half4",
            "__device__ inline void write_bfloat164",
        ),
        ("reduce_dyn", "__device__ inline float reduce_dyn", "// res_mode 0"),
    ):
        a = norm_lines(seg(s[NORM], start, end, f"stock {name}"))
        b = norm_lines(seg(e[NORM], start, end, f"elpis {name}"))
        if a != b:
            fail(f"{name}: stock and elpis bodies differ")
    reg = flat(
        seg(
            e[NORM],
            "constexpr int REG_COLS = 2;",
            "else\n    {",
            "elpis register branch",
        )
    )
    want = (
        "float sum = 0.0f; #pragma unroll for (int i = 0; i < REG_COLS; ++i) { int column = t + i * blockDim.x;"
        " if (column < columns) { if constexpr (res_mode == RES_IN) add_resid_in(x4[i], r4[i], column);"
        " sum = sum_sq4(sum, x4[i]); } } sum = reduce_dyn(sum, warp_id, lane_id);"
        " float rmf = rsqrtf(sum / (float) dim + epsilon) * constant_scale;"
    )
    if want not in reg:
        fail("elpis register branch: accumulation loop / rmf text changed")
    strided = flat(
        seg(
            s[NORM],
            "        float sum = 0.0f;\n        for (int column = t;",
            "apply_out(x4, column, rmf);",
            "stock strided branch",
        )
    )
    want = (
        "float sum = 0.0f; for (int column = t; column < columns; column += blockDim.x) { float4 x4;"
        " read_in(x4, x + row_off + 4 * column); if constexpr (res_mode == RES_IN) add_resid_in(x4, column);"
        " sum = sum_sq4(sum, x4); } sum = reduce_dyn(sum, warp_id, lane_id);"
        " float rmf = rsqrtf(sum / (float) dim + epsilon) * constant_scale;"
    )
    if want not in strided:
        fail("stock strided branch: accumulation loop / rmf text changed")
    print(
        "err_elem_diff: sum_sq4 / apply4 / write_half4 / reduce_dyn identical; both accumulation orders as modeled"
    )


def intrinsic_ops(body: str) -> list[str]:
    seq = []
    for m in re.finditer(
        r"__hneg2\(|h2exp\(|__hadd2\(one, e\)|h2rcp\(|__hmul2\(x, r\)|__hmul2\(x2, y2\)",
        body,
    ):
        t = m.group(0)
        seq.append(
            {
                "__hneg2(": "HNeg",
                "h2exp(": "HExp",
                "__hadd2(one, e)": "HAdd1",
                "h2rcp(": "HRcp",
                "__hmul2(x, r)": "HMulX",
                "__hmul2(x2, y2)": "HMulY",
            }[t]
        )
    return seq


def bend_list(model: str, name: str) -> list[str]:
    m = re.search(rf"def {name}\(\) -> List<AOp>:\n  \[([^\]]*)\]", model)
    if not m:
        fail(f"err_elem.bend: {name} not found")
    return [x.strip().removesuffix("{}") for x in m.group(1).split(",")]


def check_act(s: dict[str, str], e: dict[str, str], model: str) -> None:
    st_silu = norm_lines(
        seg(
            s[ACTK],
            "__device__ __forceinline__ half2 _silu(half2 x)",
            "__device__ __forceinline__ float _silu(float x)",
            "stock _silu(half2)",
        )
    )
    el_silu = norm_lines(
        seg(
            e[MLP16],
            "__device__ __forceinline__ half2 exl3_mlp_silu_h2(half2 x)",
            "// act_mul_kernel_h<ACT_SILU> body",
            "elpis silu",
        )
    )
    if [x.replace("_silu(", "exl3_mlp_silu_h2(") for x in st_silu] != el_silu:
        fail("exl3_mlp_silu_h2 is not stock _silu(half2) renamed")
    st_tail = norm_lines(
        seg(
            s[ACTK],
            "    if (act_limit != 0.0f)\n    {\n        y2 = __hmax2",
            "\n}\n",
            "stock act tail",
        )
    )
    el_body = seg(
        e[MLP16],
        "half2 exl3_mlp_act_mul_h2(half2 x2, half2 y2, const float act_limit)",
        "\n}\n",
        "elpis act",
    )
    el_tail = norm_lines(el_body[el_body.index("    if (act_limit != 0.0f)") :])
    if [x.replace("((half2*) z)[idx] = ", "return ") for x in st_tail] != el_tail:
        fail("exl3_mlp_act_mul_h2's clamp / product is not act_mul_kernel_h's")
    if "x2 = exl3_mlp_silu_h2(x2);" not in flat(el_body):
        fail("exl3_mlp_act_mul_h2 does not apply the silu first")
    st_ops = intrinsic_ops(
        seg(
            s[ACTK],
            "__device__ __forceinline__ half2 _silu(half2 x)",
            "__device__ __forceinline__ float _silu(float x)",
            "stock _silu",
        )
    ) + intrinsic_ops(
        seg(
            s[ACTK],
            "    if (act_limit != 0.0f)\n    {\n        y2 = __hmax2",
            "\n}\n",
            "stock act tail",
        )
    )
    el_ops = intrinsic_ops(
        seg(
            e[MLP16],
            "__device__ __forceinline__ half2 exl3_mlp_silu_h2(half2 x)",
            "// act_mul_kernel_h<ACT_SILU> body",
            "elpis silu",
        )
    ) + intrinsic_ops(el_body[el_body.index("    if (act_limit != 0.0f)") :])
    if bend_list(model, "stock_act_ops") != st_ops:
        fail(
            f"stock_act_ops {bend_list(model, 'stock_act_ops')} != source sequence {st_ops}"
        )
    if bend_list(model, "elpis_act_ops") != el_ops:
        fail(
            f"elpis_act_ops {bend_list(model, 'elpis_act_ops')} != source sequence {el_ops}"
        )
    print(
        f"err_elem_diff: activation bodies identical; operation lists = source sequences {st_ops}"
    )


def bend_const(model: str, name: str) -> int:
    m = re.search(rf"def {name}\(\) -> Nat:\n  (\d+)n", model)
    if not m:
        fail(f"err_elem.bend: constant {name} not found")
    return int(m.group(1))


def check_shape(e: dict[str, str], s: dict[str, str], model: str) -> None:
    sched = e["exllamav3_ext/quant/exl3_tail_m16_sched.h"]
    n0 = int(re.search(r"#define EXL3_TAIL_SCHED_N0 (\d+)", sched).group(1))
    nch = int(re.search(r"#define EXL3_TAIL_SCHED_NCH (\d+)", sched).group(1))
    for side, t in (("stock", s), ("elpis", e)):
        if "#define NUM_THREADS 1024" not in t[NORM]:
            fail(f"{side} norm.cu: NUM_THREADS is not 1024")
    cols = n0 // 4
    threads = min(1024, -(-cols // 32) * 32)
    warps = threads // 32
    if bend_const(model, "cols") != cols or bend_const(model, "nthreads") != threads:
        fail(f"cols / nthreads in err_elem.bend != {cols} / {threads}")
    if bend_const(model, "reduce_steps") != 5 + (5 if warps > 1 else 0):
        fail("reduce_steps != reduce_dyn's adds at the served block size")
    if nch * 128 != n0 or not (32 < nch <= 64):
        fail(f"NCH {nch} does not fit the lane / lane + 32 reading of the tail")
    if f"Bool.or(Nat.is_lt(ch, {nch - 32}n), Nat.is_le(32n, ch))" not in model:
        fail(
            f"tail_extra must be ch < {nch - 32} or ch >= 32 (lane + 32 < NCH = {nch})"
        )
    if (
        "Nat.add(Nat.sub(4n, comp_ix(k)), Nat.add(5n, Nat.add(guard(b), 5n)))"
        not in model
    ):
        fail("tail_ssq: 4 - k fmas + 5 shuffles + chunk add + 5 shuffles changed")
    print(
        f"err_elem_diff: shape N0 = {n0} -> cols {cols}, threads {threads} ({warps} warps), NCH = {nch}"
    )


def check_routes(m1map: Path) -> None:
    mp = json.loads((m1map / "m1map-map.json").read_text())["kernel_map"]
    st = json.loads((m1map / "m1map-stock.json").read_text())["kernel_map"]
    want_v = {
        "T|gdn|attn_norm": "rms_norm_kernel",
        "T|attn|attn_norm": "rms_norm_kernel",
        "T|-|model.language_model.norm": "rms_norm_kernel",
        "T|gdn|tail(o_proj + residual + norm + mlp)": "exl3_tail_m16_kernel",
        "T|attn|tail(o_proj + residual + norm + mlp)": "exl3_tail_m16_kernel",
    }
    for key, kern in want_v.items():
        got = set(mp[key]["verify"])
        if got != {kern}:
            fail(f"elpis verify {key}: kernels {sorted(got)} != {{{kern}}}")
        if mp[key]["verify"][kern]["rows"] != [8]:
            fail(f"elpis verify {key}: rows {mp[key]['verify'][kern]['rows']}")
    want_s = {
        "T|gdn|attn_norm": {"rms_norm_kernel"},
        "T|attn|attn_norm": {"rms_norm_kernel"},
        "T|gdn|mlp_norm": {"rms_norm_kernel"},
        "T|attn|mlp_norm": {"rms_norm_kernel"},
        "T|-|model.language_model.norm": {"rms_norm_kernel"},
    }
    for key, kerns in want_s.items():
        if set(st[key]["m1_stock"]) != kerns:
            fail(f"stock M = 1 {key}: {sorted(st[key]['m1_stock'])}")
    for key in ("T|gdn|mlp", "T|attn|mlp"):
        if "act_mul_kernel_h" not in st[key]["m1_stock"]:
            fail(f"stock M = 1 {key}: no act_mul_kernel_h")
    print(
        "err_elem_diff: m1map routes name the modeled kernels (elpis verify rows 8, stock M = 1)"
    )


def sass_section(dump: str, fn: str) -> list[str]:
    out, on = [], False
    for line in dump.splitlines():
        if "Function :" in line:
            on = line.strip().endswith(fn)
        if on:
            out.append(line)
    return out


def check_sass(so: Path, cuobjdump: str) -> None:
    norm_fn = (
        "_Z15rms_norm_kernelILi2Ef6__half13__nv_bfloat16fEvPKT0_PKT2_PT1_PT3_fiiffi"
    )
    dump = subprocess.run(
        [cuobjdump, "-sass", "-fun", norm_fn, str(so)],
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    sec = [l for l in sass_section(dump, norm_fn) if not l.strip().startswith("/* 0x")]
    ops = [re.sub(r"^\s*/\*[0-9a-f]+\*/\s*", "", l).strip() for l in sec]
    rsq = [i for i, o in enumerate(ops) if o.startswith("MUFU.RSQ")]
    if not rsq:
        fail("rms_norm_kernel: no MUFU.RSQ")
    for i in rsq:
        before = ops[max(0, i - 12) : i]
        if not any(o.startswith("FFMA") for o in before) or not any(
            o.startswith("MUFU.RCP") for o in ops[max(0, i - 40) : i]
        ):
            fail("rms_norm_kernel: rmf is not MUFU.RCP + FFMA + MUFU.RSQ")
    tail_fn = "_Z20exl3_tail_m16_kernelILi0ELi2EEvPK6__halfPfS3_15Exl3TailM16Args"
    dump = subprocess.run(
        [cuobjdump, "-sass", "-fun", tail_fn, str(so)],
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    ops = [
        re.sub(r"^\s*/\*[0-9a-f]+\*/\s*", "", l).strip()
        for l in sass_section(dump, tail_fn)
        if not l.strip().startswith("/* 0x")
    ]
    rsq = [i for i, o in enumerate(ops) if o.startswith("MUFU.RSQ")]
    if len(rsq) != 1:
        fail(f"exl3_tail_m16_kernel: {len(rsq)} MUFU.RSQ (want 1)")
    win = ops[rsq[0] - 12 : rsq[0]]
    mov = [o for o in win if re.match(r"MOV R\d+, 0x394ccccd", o)]
    if not mov:
        fail("exl3_tail_m16_kernel: no RN(1/5120) constant before MUFU.RSQ")
    reg = re.match(r"MOV (R\d+),", mov[0]).group(1)
    if not any(o.startswith("FFMA") and f", {reg}," in o for o in win):
        fail("exl3_tail_m16_kernel: the constant does not feed an FFMA before MUFU.RSQ")
    if any(o.startswith("MUFU.RCP") for o in win):
        fail("exl3_tail_m16_kernel: a MUFU.RCP feeds the tail rmf")
    print(
        f"err_elem_diff: SASS ({so.name}): norm rmf = MUFU.RCP + FFMA + MUFU.RSQ; tail rmf = FFMA by 0x394ccccd + MUFU.RSQ"
    )


def main(argv: list[str]) -> None:
    args = argv[1:]
    mutate = so = None
    cuobjdump = None
    m1map = None
    while args and args[0].startswith("--"):
        flag = args.pop(0)
        if flag == "--mutate":
            mutate = args.pop(0)
        elif flag == "--sass":
            so = Path(args.pop(0))
        elif flag == "--cuobjdump":
            cuobjdump = args.pop(0)
        elif flag == "--m1map":
            m1map = Path(args.pop(0))
        else:
            fail(f"unknown flag {flag}")
    if len(args) != 1:
        fail(
            "usage: err_elem_diff.py [--mutate NAME] [--sass SO [--cuobjdump BIN]] [--m1map DIR] STOCK_PACKAGE_DIR"
        )
    if so is not None and cuobjdump is None:
        cuobjdump = shutil.which("cuobjdump")
        if cuobjdump is None:
            fail("--sass needs cuobjdump: it is not on PATH and --cuobjdump is not given")
    stock = Path(args[0])
    model = MODEL.read_text()
    with tempfile.TemporaryDirectory(prefix="err-elem-diff-") as tmp:
        elpis = build_elpis(stock, Path(tmp))
        files = {
            NORM,
            TAIL,
            MLP16,
            ACTK,
            ACTCU,
            "exllamav3_ext/quant/exl3_tail_m16_sched.h",
        }
        s = {f: (stock / f).read_text() for f in files if (stock / f).exists()}
        e = {f: (elpis / f).read_text() for f in files}
        if mutate is not None:
            if mutate not in MUTATIONS:
                fail(f"unknown mutation {mutate!r}")
            path, old, new = MUTATIONS[mutate]
            if e[path].count(old) != 1:
                fail(f"mutation anchor occurs {e[path].count(old)} times")
            e[path] = e[path].replace(old, new)
            (elpis / path).write_text(e[path])
            print(f"err_elem_diff: applied mutation {mutate}")
        check_cites({"S": stock, "E": elpis}, model)
        check_helpers(s, e)
        check_act(s, e, model)
        check_shape(e, s, model)
        if m1map is None:
            print(
                "err_elem_diff: m1map route check NOT RUN (no --m1map; the m1map dir is GPU-made and not in the repository)"
            )
        else:
            check_routes(m1map)
        if so is not None:
            check_sass(so, cuobjdump)
    print("err_elem_diff: OK")


if __name__ == "__main__":
    main(sys.argv)
