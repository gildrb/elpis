#!/usr/bin/env python3
"""
Source link of bend/err_attn.bend (decode-attention rounding-error paths) to the kernels it models.

  1. Fragments: every source line the model cites (S: stock 355c6ee, E: the patched elpis tree) holds
     the quoted text at the quoted line.
  2. Pre stage: the floating-point lines of attn_pre_kernel (E:exllamav3_ext/attn_small.cu) are
     rope_kernel's (S:exllamav3_ext/rope.cu) verbatim, and the combine's gate sigmoid is
     _sigmoid's (S:exllamav3_ext/activation_kernels.cuh).
  3. Compiled code (H_ptx, H_sass): the image's Triton 3.6.0 cache for the stock kernels (sha256
     pinned) and a compile of E:exllamav3_ext/attn_verify.cu (nvcc, sm_86, -O3 --use_fast_math) show
     the instruction facts the model counts.
  4. Geometry: a Python transcription of both kernels' tile / split / combine index arithmetic
     (H_zero applied) gives, at L = 2, the Geo constants geo_e2 / geo_s2 and the paths quoted by
     elpis_worst2_path / stock_worst2_path; and it scans L, reporting where the elpis routes are
     dominated (they are not at any L scanned) and where the routes with stock's output stage are not.

Usage: python3 -I -B err_attn_diff.py --stock DIR [--elpis DIR] [--no-compiled | --triton DIR [--cuda-include DIR]...]
                                       [--mutate NAME]
  --stock: the stock exllamav3 package directory at 355c6ee (OUT/stock of bend/engine_trees.py).
  --triton: the Triton 3.6.0 cache directory that holds the stock decode kernels SPLIT_DIR and COMB_DIR (sha256
  pinned in PINS). A run of the stock engine on a GPU in the image writes it; the repository alone cannot make it.
  It is required unless --no-compiled is given.
  --cuda-include: an nvcc include directory (repeat it as necessary), for a CUDA 12.9 toolkit whose nvcc does not
  find cuda_runtime.h and the CCCL headers itself (for example nixpkgs cuda_cudart and cuda_cccl include dirs).
  The compiled checks use nvcc and nvdisasm from PATH.
  --elpis defaults to a fresh tree: the stock tree + patches/exl3/series + patches/exl3-ext/series up to
  but EXCLUDING 3030-attn-verify-dominate.patch (patch -p1 -F0, any reject fails): this script and
  bend/err_attn.bend / err_attn_finding_laws.bend document the decode-attention kernel BEFORE ext 3030
  (the finding that motivated 3030). The 3030 kernel is modelled by bend/err_attn_dec.bend and linked by
  bend/err_attn_dec_diff.py. --mutate perturbs one quoted engine line; the run must FAIL.
Exit 0 = every check passed.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent
sys.path.insert(0, str(HERE))
import source_link  # noqa: E402

SPLIT_DIR = "XFUF7JHJC7RHFKH3IJV3P3JGHFWLXAP2UKCMV6XIPVRNJQNK44LQ"
COMB_DIR = "IPYAKBVPWH2TMNDZAVKWMKD5DXYMLEGCS2H64XAZZQAUFZEPTUCQ"
PINS = {
    f"{SPLIT_DIR}/_paged_attn_decode_split_kernel.ptx": "747328ab6485b2c4a0585cc318fe84ebe6c9ae0f1f06e63679d63b6ef2062b7b",
    f"{SPLIT_DIR}/_paged_attn_decode_split_kernel.cubin": "73fad9809fc0c8b0802f1ee25277869ae2d37fc1d2ac394d8c6cd40922982205",
    f"{SPLIT_DIR}/_paged_attn_decode_split_kernel.ttgir": "a9e69b14c2c704892e52bf08907e1fc44719795c90fc605c6672a657f6cdc7bc",
    f"{COMB_DIR}/_paged_attn_decode_combine_kernel.ptx": "01b143e2ff92646b79be4381253696bfec6a92ba2fa88d17a78b2c5a8b1e2ac0",
    f"{COMB_DIR}/_paged_attn_decode_combine_kernel.cubin": "cbde1f785d22259e7eda5aa04066f4274c8153782becc91b3edc1b6526ffe6a4",
}
STOCK_TRITON_PAGED = "910379b663acb08711c3be207cd3e9ed96658527cc110a6ce39c793f997836d9"


def fail(msg: str):
    raise SystemExit(f"err_attn_diff: FAIL: {msg}")


def check(cond: bool, msg: str):
    if not cond:
        fail(msg)


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


# ---------------------------------------------------------------------------------------------
# 1. Fragments: (tree, file, line, text)

FRAGS = [
    # ---- elpis split kernel (ext 3003 / 3006 / 3012) ----
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        64,
        "return __fsub_rn(__uint_as_float((raw << 1) | 0x4A800000u), BIAS);",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        70,
        "return __fmul_rn(__half2float(s), 1.0f / (float) (1 << (BITS - 1)));",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        82,
        "half2 h = __floats2half2_rn(__fmul_rn(centered<BITS>(r0), scf), __fmul_rn(centered<BITS>(r1), scf));",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        94,
        "return __fmul_rn(centered<BITS>(r), scf);",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        106,
        "mma.sync.aligned.m16n8k16.row.col.f32.f16.f16.f32",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        132,
        'asm("ex2.approx.ftz.f32 %0, %1;" : "=f"(y) : "f"(x));',
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        300,
        "mma16816(c, a[0], hb[nt][0][0], hb[nt][0][1]);",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        301,
        "mma16816(c, a[1], hb[nt][1][0], hb[nt][1][1]);",
    ),
    ("E", "exllamav3_ext/attn_verify.cu", 303, "= pack_h2(c[0], c[1]);"),
    ("E", "exllamav3_ext/attn_verify.cu", 401, "for (int g = 0; g < 8; ++g)"),
    ("E", "exllamav3_ext/attn_verify.cu", 405, "for (int h = 0; h < 2; ++h)"),
    ("E", "exllamav3_ext/attn_verify.cu", 414, "mma16816(sc[i], a, b0, b1);"),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        433,
        "x[2 * i + hr][e] = ok ? sc[i][2 * hr + e] * scale_log2 : NEG_INF;",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        457,
        "alpha[s] = m[s] == NEG_INF ? 0.f : (m_new == m[s] ? 1.f : ex2(m[s] - m_use));",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        458,
        "float p0 = x[s][0] == NEG_INF ? 0.f : ex2(x[s][0] - m_use);",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        460,
        "*reinterpret_cast<uint32_t*>(ps + r * PSTR + warp * 8 + 2 * t) = pack_h2(p0, p1);",
    ),
    ("E", "exllamav3_ext/attn_verify.cu", 461, "float ssum = p0 + p1;"),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        462,
        "ssum += __shfl_xor_sync(0xffffffffu, ssum, 1);",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        463,
        "ssum += __shfl_xor_sync(0xffffffffu, ssum, 2);",
    ),
    ("E", "exllamav3_ext/attn_verify.cu", 473, "float tsum = red_sum[r];"),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        475,
        "for (int w = 1; w < AV_NW; ++w) tsum += red_sum[w * AV_ROWS + r];",
    ),
    ("E", "exllamav3_ext/attn_verify.cu", 476, "l[s] = l[s] * alpha[s] + tsum;"),
    ("E", "exllamav3_ext/attn_verify.cu", 483, "acc[i][j][0] *= alpha[2 * i];"),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        491,
        "for (int kk = 0; kk < AV_T / 16; ++kk)",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        505,
        "for (int j = 0; j < 4; ++j) vv[e][j] = deq_one<VB>(vt + warp * VB, 8 * j + gid, scf);",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        510,
        "uint32_t b0 = pack_h2(vv[0][j], vv[1][j]);",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        513,
        "for (int i = 0; i < 3; ++i) mma16816(acc[i][j], pa[i], b0, b1);",
    ),
    # ---- elpis combine (ext 3006 / 3007) ----
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        619,
        "if (d < live) sw[d] = sw[d] == NEG_INF ? -1.f : ex2(sw[d] - m_use);",
    ),
    ("E", "exllamav3_ext/attn_verify.cu", 628, "acc = fmaf(v, w, acc);"),
    ("E", "exllamav3_ext/attn_verify.cu", 629, "lsum = fmaf(sl[s], w, lsum);"),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        631,
        "oh[d] = __float2half_rn(acc / (lsum == 0.f ? 1.f : lsum));",
    ),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        637,
        "for (int i = 0; i < 32; ++i) y = fmaf(__half2float(oh[g0 + i]), __half2float(h32[i * 32 + jn]), y);",
    ),
    ("E", "exllamav3_ext/attn_verify.cu", 638, "= __float2half_rn(y);"),
    (
        "E",
        "exllamav3_ext/attn_verify.cu",
        650,
        "x2 = __hmul2(x2, av_gate_sigmoid(y2));",
    ),
    ("E", "exllamav3_ext/attn_verify.cuh", 40, "#define AV_NW 8"),
    ("E", "exllamav3_ext/attn_verify.cuh", 41, "#define AV_T 64"),
    ("E", "exllamav3_ext/attn_verify.cuh", 49, "return (L + AV_T - 1) / AV_T;"),
    ("E", "exllamav3_ext/attn_verify.cuh", 55, "return (n_tiles - x + S - 1) / S;"),
    ("E", "exllamav3_ext/attn_verify.cuh", 61, "return n_tiles < S ? n_tiles : S;"),
    (
        "E",
        "modules/attention_fn/bc_attn.py",
        440,
        "av_splits = max(1, _get_sm_count(dev) // kvh)",
    ),
    (
        "E",
        "modules/attention_fn/bc_attn.py",
        481,
        "float(self.sm_scale) * math.log2(math.e),",
    ),
    ("E", "ext.py", 92, '"-lineinfo", "-O3", "--use_fast_math",'),
    # ---- elpis pre kernel (ext 3007) ----
    ("E", "exllamav3_ext/attn_small.cu", 93, "sin = __sinf(fr * pf) * attn_factor;"),
    ("E", "exllamav3_ext/attn_small.cu", 177, "float r1 = v1 * cos - v2 * sin;"),
    ("E", "exllamav3_ext/attn_small.cu", 178, "float r2 = v2 * cos + v1 * sin;"),
    ("E", "exllamav3_ext/attn_small.cu", 208, "float sum = v1 * v1 + v2 * v2;"),
    ("E", "exllamav3_ext/attn_small.cu", 209, "sum = warp_reduce_sum_f(sum);"),
    (
        "E",
        "exllamav3_ext/attn_small.cu",
        214,
        "for (int i = 1; i < warps; ++i) sum += sums[warps * t_head + i];",
    ),
    (
        "E",
        "exllamav3_ext/attn_small.cu",
        216,
        "float rmf = rsqrtf(sum / (float) head_dim + norm_eps);",
    ),
    (
        "E",
        "exllamav3_ext/attn_small.cu",
        236,
        "half2 w = __hadd2(*wptr, norm_constant_bias_h2);",
    ),
    ("E", "exllamav3_ext/attn_small.cu", 238, "v = __hmul2(w, v);"),
    (
        "E",
        "exllamav3_ext/attn_small.cu",
        290,
        "quant_block_x4<BITS>(sh_head + cc * 128, k_cache + (size_t) base * BITS, k_scales + base, sp, active, compand_a);",
    ),
    # ---- stock Triton decode (S:modules/attention_fn/triton_paged.py) ----
    ("S", "modules/attention_fn/triton_paged.py", 718, "y = tl.dot(x2, h)"),
    (
        "S",
        "modules/attention_fn/triton_paged.py",
        719,
        "return tl.reshape(y.to(tl.float16), (ROWS, head_dim))",
    ),
    (
        "S",
        "modules/attention_fn/triton_paged.py",
        805,
        "return ((raw.to(tl.float32) - mh) * (scx.to(tl.float32) * inv_m)).to(tl.float16)",
    ),
    (
        "S",
        "modules/attention_fn/triton_paged.py",
        848,
        "return ((raw.to(tl.float32) - mh) * (scx.to(tl.float32) * inv_m)).to(tl.float16)",
    ),
    (
        "S",
        "modules/attention_fn/triton_paged.py",
        912,
        "q_tile = _rot_h32(q_tile, h32, BLOCK_ROWS, HD_PAD)",
    ),
    (
        "S",
        "modules/attention_fn/triton_paged.py",
        943,
        "scores = tl.dot(q_tile, k_tile) * scale",
    ),
    (
        "S",
        "modules/attention_fn/triton_paged.py",
        959,
        "p = tl.exp(scores - m_exp[:, None])",
    ),
    (
        "S",
        "modules/attention_fn/triton_paged.py",
        961,
        'alpha = tl.where(m == -float("inf"), 0.0, tl.exp(m - m_exp))',
    ),
    (
        "S",
        "modules/attention_fn/triton_paged.py",
        962,
        "l_new = l * alpha + tl.sum(p, axis=1)",
    ),
    (
        "S",
        "modules/attention_fn/triton_paged.py",
        973,
        "acc = acc * alpha[:, None] + tl.dot(p.to(v_tile.dtype), v_tile)",
    ),
    (
        "S",
        "modules/attention_fn/triton_paged.py",
        1054,
        'w = tl.where(m_s == -float("inf"), 0.0, tl.exp(m_s - m_safe))',
    ),
    ("S", "modules/attention_fn/triton_paged.py", 1057, "acc += o_s * w[:, None]"),
    ("S", "modules/attention_fn/triton_paged.py", 1058, "l_sum += l_s * w"),
    (
        "S",
        "modules/attention_fn/triton_paged.py",
        1062,
        "out_tile = acc / tl.where(l_sum[:, None] == 0.0, 1.0, l_sum[:, None])",
    ),
    (
        "S",
        "modules/attention_fn/triton_paged.py",
        1064,
        "out_tile = _rot_h32(out_tile, h32, BLOCK_ROWS, HD_PAD)",
    ),
    (
        "S",
        "modules/attention_fn/bc_attn.py",
        42,
        'bc_attn_enable = os.environ.get("EXL3_BC_ATTN", "1") != "0"',
    ),
    ("S", "modules/attention_fn/bc_attn.py", 278, "block_n = max(16, 8192 // hd_pad)"),
    (
        "S",
        "modules/attention_fn/bc_attn.py",
        288,
        "splits_cap = max(1, min(target // programs, 128))",
    ),
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
        952,
        "max_seq_len = max(max_seq_len, job.get_max_seq_len() + self.num_draft_tokens)",
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
        "exllamav3_ext/activation_kernels.cuh",
        313,
        "x2 = __hmul2(x2, _sigmoid(y2));",
    ),
    # ---- stock rope_kernel ----
    ("S", "exllamav3_ext/rope.cu", 76, "sin = __sinf(fr * pf) * attn_factor;"),
    ("S", "exllamav3_ext/rope.cu", 166, "float r1 = v1 * cos - v2 * sin;"),
    ("S", "exllamav3_ext/rope.cu", 167, "float r2 = v2 * cos + v1 * sin;"),
    ("S", "exllamav3_ext/rope.cu", 199, "float sum = v1 * v1 + v2 * v2;"),
    ("S", "exllamav3_ext/rope.cu", 200, "sum = warp_reduce_sum_f(sum);"),
    (
        "S",
        "exllamav3_ext/rope.cu",
        208,
        "float rmf = rsqrtf(sum / (float) head_dim + norm_eps);",
    ),
    (
        "S",
        "exllamav3_ext/rope.cu",
        230,
        "half2 w = __hadd2(*wptr, norm_constant_bias_h2);",
    ),
    ("S", "exllamav3_ext/rope.cu", 232, "v = __hmul2(w, v);"),
]

MUTATIONS = {
    # elpis back-rotation over every other dim: fragment E:attn_verify.cu:637 fails
    "rot_line": (
        "E",
        "exllamav3_ext/attn_verify.cu",
        637,
        "i < 32; ++i",
        "i < 32; i += 2",
    ),
    # stock P.V without the alpha rescale: fragment S:triton_paged.py:973 fails
    "pv_line": (
        "S",
        "modules/attention_fn/triton_paged.py",
        973,
        "acc * alpha[:, None] + ",
        "acc + ",
    ),
    # elpis split width doubled: fragment E:bc_attn.py:440 fails
    "splits": (
        "E",
        "modules/attention_fn/bc_attn.py",
        440,
        "max(1, _get_sm_count(dev)",
        "max(1, 2 * _get_sm_count(dev)",
    ),
}


# The first ext patch NOT applied: the pre-3030 kernel this script documents
STOP_BEFORE = "3030-attn-verify-dominate.patch"


def build_elpis(stock: Path, dst: Path, stop_before: str | None = STOP_BEFORE) -> Path:
    tree = dst / "exllamav3"
    files = sorted(
        p.relative_to(stock).as_posix()
        for p in stock.rglob("*")
        if p.is_file()
        and not p.is_symlink()
        and "__pycache__" not in p.relative_to(stock).parts
    )
    for f in files:
        (tree / f).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(stock / f, tree / f)
    for series in ("exl3", "exl3-ext"):
        pdir = REPO / "patches" / series
        for line in (pdir / "series").read_text().splitlines():
            digest, name = line.split()
            if series == "exl3-ext" and name == stop_before:
                break
            check(
                sha(pdir / name) == digest,
                f"{series}/{name}: sha256 differs from the series",
            )
            r = subprocess.run(
                [
                    "patch",
                    "-p1",
                    "-s",
                    "-F0",
                    "--no-backup-if-mismatch",
                    "-i",
                    str(pdir / name),
                ],
                cwd=tree,
                capture_output=True,
                text=True,
            )
            check(
                r.returncode == 0,
                f"{series}/{name} does not apply: {r.stdout}{r.stderr}",
            )
    return tree


def check_frags(trees: dict):
    for side, rel, line, text in FRAGS:
        lines = (trees[side] / rel).read_text().splitlines()
        check(
            line <= len(lines) and text in lines[line - 1],
            f"{side}:{rel}:{line} does not hold {text!r} (holds {lines[line - 1].strip() if line <= len(lines) else 'EOF'!r})",
        )
    print(f"fragments: {len(FRAGS)} quoted lines hold their text")


# ---------------------------------------------------------------------------------------------
# 2. Pre stage and sigmoid: textual identity of the floating-point lines

FP_TOKENS = re.compile(
    r"(__sinf|__cosf|\* cos|\* sin|v1 \* v1|warp_reduce_sum_f|rsqrtf|\*= rmf|\*= w\.|__hadd2|__hmul2|"
    r"__floats2half2_rn|__float2half_rn|__half2float|__low2float|__high2float|\+= sums|"
    r"__bfloat1622float2|\+= norm_constant_bias|__float2half2_rn|__logf)"
)


def fp_lines(src: str) -> list:
    return [
        re.sub(r"\s+", " ", l.strip())
        for l in src.splitlines()
        if FP_TOKENS.search(l) and not l.strip().startswith("//")
    ]


def body(src: str, start: str, end: str) -> str:
    i = src.index(start)
    return src[i : src.index(end, i)]


def check_pre(trees: dict):
    rope = (trees["S"] / "exllamav3_ext/rope.cu").read_text()
    small = (trees["E"] / "exllamav3_ext/attn_small.cu").read_text()
    s = fp_lines(body(rope, "void rope_kernel", "store_head();"))
    e = fp_lines(body(small, "void attn_pre_kernel", "store_head();"))
    check(len(s) >= 25, f"rope_kernel: only {len(s)} floating-point lines found")
    check(
        s == e,
        "attn_pre_kernel's floating-point lines differ from rope_kernel's:\n"
        + "\n".join(f"  S {a}\n  E {b}" for a, b in zip(s, e) if a != b),
    )
    print(
        f"pre stage: {len(s)} floating-point lines of attn_pre_kernel = rope_kernel's, in order"
    )
    act = (trees["S"] / "exllamav3_ext/activation_kernels.cuh").read_text()
    av = (trees["E"] / "exllamav3_ext/attn_verify.cu").read_text()
    sg = [
        l.strip()
        for l in body(
            act, "__device__ __forceinline__ half2 _sigmoid(half2 x)", "}"
        ).splitlines()[2:]
    ]
    ag = [
        l.strip()
        for l in body(
            av, "__device__ __forceinline__ half2 av_gate_sigmoid(half2 x)", "}"
        ).splitlines()[2:]
    ]
    check(sg == ag and len(sg) == 5, f"gate sigmoid differs: {sg} vs {ag}")
    print("gate: av_gate_sigmoid body = _sigmoid body")


# ---------------------------------------------------------------------------------------------
# 3. Compiled code


def by_loc_ptx(ptx: str) -> list:
    cur, out = None, []
    for l in ptx.splitlines():
        m = re.search(r"\.loc\s+1 (\d+) \d+", l)
        if m:
            cur = int(m.group(1))
            continue
        if re.match(r"\s+[a-z@%]", l):
            out.append((cur, l.strip()))
    return out


def sass_by_line(sass: str, fname: str) -> list:
    """(source line, instruction) pairs from nvdisasm -g / -gi output: the first `//##` line of a header
    group names the innermost line; an instruction of the mma16816 / ex2 wrappers is credited to the
    line it is inlined at (its call site)"""
    cur, out, head = None, [], True
    for l in sass.splitlines():
        if "//##" in l:
            if head:
                m = re.search(
                    rf'{re.escape(fname)}", line (\d+)(?: inlined at "[^"]*{re.escape(fname)}", line (\d+))?',
                    l,
                )
                cur = None
                if m:
                    a, b = int(m.group(1)), m.group(2)
                    cur = int(b) if (b and a in WRAPPERS) else a
            head = False
            continue
        head = True
        m = re.search(r"/\*[0-9a-f]{4}\*/\s+(.*?)\s*;", l)
        if m:
            out.append((cur, m.group(1)))
    return out


WRAPPERS = set(range(103, 110)) | set(
    range(129, 135)
)  # mma16816 (E:attn_verify.cu:103-109), ex2 (129-134)


def ops_at(rows: list, line: int, op: str) -> list:
    return [
        i for ln, i in rows if ln == line and re.search(rf"(^|\s){re.escape(op)}", i)
    ]


def check_stock_compiled(stock: Path, triton: Path):
    for rel, digest in PINS.items():
        check(sha(triton / rel) == digest, f"triton cache {rel}: sha256 differs")
    check(
        sha(stock / "modules/attention_fn/triton_paged.py") == STOCK_TRITON_PAGED,
        "stock triton_paged.py sha256 differs",
    )
    src = (triton / SPLIT_DIR / "_paged_attn_decode_split_kernel.source").read_text()
    check(
        'triton_paged.py":852:0' in src
        and 'triton_paged.py":715:0' in src
        and 'triton_paged.py":763:0' in src,
        "cached split kernel: not compiled from the stock line layout (852 / 715 / 763)",
    )
    ttgir = (triton / SPLIT_DIR / "_paged_attn_decode_split_kernel.ttgir").read_text()
    check(
        re.search(r"%scores = tt\.dot .*tensor<16x256xf16.*tensor<256x32xf16", ttgir)
        is not None,
        "QK^T dot shape",
    )
    pv = re.search(r"%acc_\d+ = tt\.dot %acc_\d+, %v_tile_\d+, %acc_\d+", ttgir)
    check(pv is not None, "P.V dot does not accumulate into acc * alpha")
    ptx = by_loc_ptx(
        (triton / SPLIT_DIR / "_paged_attn_decode_split_kernel.ptx").read_text()
    )
    ex = [i for ln, i in ptx if ln in (959, 961, 1054)]
    lg = [i for i in ex if re.match(r"mul\.f32 .*0f3FB8AA3B", i)]
    check(
        len(lg) == sum(1 for i in ex if i.startswith("ex2.approx.f32")) > 0,
        "tl.exp is not FMUL log2e + ex2.approx",
    )
    check(
        any(re.match(r"mul\.f32 .*0f3D800000", i) for ln, i in ptx if ln == 943),
        "scores * 0.0625 (exact) missing",
    )
    check(
        sum(1 for ln, i in ptx if ln == 962 and i.startswith("fma.rn.f32")) == 2,
        "l * alpha + sum is not one FFMA per row",
    )
    ss = sass_by_line(
        subprocess.run(
            [
                "nvdisasm",
                "-g",
                "-c",
                str(triton / SPLIT_DIR / "_paged_attn_decode_split_kernel.cubin"),
            ],
            capture_output=True,
            text=True,
            check=True,
        ).stdout,
        "triton_paged.py",
    )
    qk = ops_at(ss, 943, "HMMA.16816.F32")
    check(
        len(qk) == 16
        and qk[0].endswith(", RZ")
        and all(not i.endswith("RZ") for i in qk[1:]),
        "QK^T is not a 16-HMMA chain",
    )
    check(len(ops_at(ss, 718, "HMMA.16816.F32")) == 16, "q rotation HMMA count")
    check(
        len(ops_at(ss, 973, "HMMA.16816.F32")) == 16
        and len(ops_at(ss, 973, "FMUL")) == 32,
        "P.V: 2 k16 HMMA per 8-col tile, acc * alpha FMUL",
    )
    cptx = by_loc_ptx(
        (triton / COMB_DIR / "_paged_attn_decode_combine_kernel.ptx").read_text()
    )
    check(
        all(
            i.startswith("div.full.f32")
            for ln, i in cptx
            if ln == 1062 and i.startswith("div")
        ),
        "acc / l_sum is not div.full",
    )
    check(
        sum(1 for ln, i in cptx if ln in (1057, 1058) and i.startswith("fma.rn.f32"))
        == 33,
        "combine FFMAs",
    )
    cs = sass_by_line(
        subprocess.run(
            [
                "nvdisasm",
                "-g",
                "-c",
                str(triton / COMB_DIR / "_paged_attn_decode_combine_kernel.cubin"),
            ],
            capture_output=True,
            text=True,
            check=True,
        ).stdout,
        "triton_paged.py",
    )
    check(
        len(ops_at(cs, 1062, "MUFU.RCP")) == 16
        and len(ops_at(cs, 718, "HMMA.16816.F32")) == 16,
        "combine: div.full = MUFU.RCP + FMUL; output rotation HMMA",
    )
    print(
        "stock compiled: Triton 3.6.0 cache pinned; dot chains, exp lowering, exact scale, FFMA fusion, div.full = RCP + FMUL"
    )


def nvcc(includes: list) -> list:
    """Return the nvcc on PATH and one -I flag for each include directory. Fail if one is absent."""
    exe = shutil.which("nvcc")
    check(exe is not None, "nvcc is not on PATH (the compiled checks need it)")
    inc = []
    for d in includes:
        check(Path(d).is_dir(), f"--cuda-include {d} is not a directory")
        inc += ["-I", str(d)]
    return [exe, *inc]


def check_elpis_compiled(elpis: Path, td: Path, includes: list):
    cub = td / "av.cubin"
    r = subprocess.run(
        source_link.locked(
            [
                *nvcc(includes),
                "-arch=sm_86",
                "-O3",
                "--use_fast_math",
                "-lineinfo",
                "-cubin",
                "-o",
                str(cub),
                str(elpis / "exllamav3_ext/attn_verify.cu"),
            ]
        ),
        capture_output=True,
        text=True,
    )
    check(r.returncode == 0, f"nvcc failed: {r.stderr[-2000:]}")
    sass = subprocess.run(
        ["nvdisasm", "-gi", "-c", str(cub)], capture_output=True, text=True, check=True
    ).stdout
    fns = re.split(r"\n\s*\.section\s+\.text\.", sass)
    fn = {f.split(",", 1)[0]: f for f in fns[1:]}
    sp = sass_by_line(fn["attn_verify_split_k3v3_tree"], "attn_verify.cu")
    cg = sass_by_line(fn["attn_verify_combine_gate"], "attn_verify.cu")
    check(
        len(ops_at(sp, 300, "HMMA.16816.F32")) + len(ops_at(sp, 301, "HMMA.16816.F32"))
        == 8,
        "q rotation: two k16 HMMA per n-tile (4 n-tiles)",
    )
    check(
        len(ops_at(sp, 414, "HMMA.16816.F32")) == 48,
        "QK^T: 16 k16 HMMA per m-tile x 3 m-tiles",
    )
    check(
        len(ops_at(sp, 513, "HMMA.16816.F32")) == 48,
        "P.V: 4 k16 groups x 4 n-tiles x 3 m-tiles",
    )
    check(
        len(ops_at(sp, 458, "MUFU.EX2")) == 6 and len(ops_at(sp, 458, "FADD")) == 6,
        "p = MUFU.EX2 of one FADD",
    )
    check(
        len(ops_at(sp, 433, "FMUL")) == 12 and len(ops_at(sp, 476, "FFMA")) == 6,
        "x = FMUL by scale_log2; l = FFMA",
    )
    check(len(ops_at(sp, 475, "FADD")) == 42, "cross-warp tsum: 7 FADD per row slot")
    rot = ops_at(cg, 637, "FFMA")
    check(
        len(rot) == 32 and rot[0].endswith(", RZ"),
        "back-rotation is not a 32-FFMA chain from RZ",
    )
    check(
        len(ops_at(cg, 631, "MUFU.RCP")) == 1 and len(ops_at(cg, 631, "FMUL")) == 1,
        "acc / lsum is not RCP + FMUL",
    )
    check(
        len(ops_at(cg, 628, "FFMA")) >= 4 and len(ops_at(cg, 629, "FFMA")) >= 4,
        "combine fmaf -> FFMA",
    )
    print(
        "elpis compiled (nvcc sm_86 -O3 --use_fast_math): QK^T HMMA chain, FMUL / FFMA as modelled, back-rotation 32 FFMA from RZ"
    )
    # pre stage (H_sass): the sum of squares and the NEOX rotation, compiled as the kernels' own lines
    small = (elpis / "exllamav3_ext/attn_small.cu").read_text().splitlines()
    probe = td / "probe.cu"
    probe.write_text(
        "#include <cuda_fp16.h>\n"
        'extern "C" __global__ void probe(const half2* x, half2* y, float* s, const float* cs)\n{\n'
        "    int t = threadIdx.x;\n    half2 v = x[t];\n"
        "    float v1 = __low2float(v);\n    float v2 = __high2float(v);\n"
        f"    {small[207].strip()}\n    s[t] = sum;\n    float cos = cs[0], sin = cs[1];\n"
        f"    {small[176].strip()}\n    {small[177].strip()}\n    y[t] = __floats2half2_rn(r1, r2);\n}}\n"
    )
    pc = td / "probe.cubin"
    r = subprocess.run(
        source_link.locked(
            [
                *nvcc(includes),
                "-arch=sm_86",
                "-O3",
                "--use_fast_math",
                "-cubin",
                "-o",
                str(pc),
                str(probe),
            ]
        ),
        capture_output=True,
        text=True,
    )
    check(r.returncode == 0, f"nvcc (probe) failed: {r.stderr[-2000:]}")
    ps = subprocess.run(
        ["nvdisasm", "-c", str(pc)], capture_output=True, text=True, check=True
    ).stdout
    ops = [
        m.group(1)
        for m in re.finditer(r"/\*[0-9a-f]{4}\*/\s+(FMUL|FFMA)\S*\s+([^;]*);", ps)
    ]
    check(
        ops == ["FMUL", "FFMA", "FMUL", "FMUL", "FFMA", "FFMA"],
        f"pre-stage probe: {ops} (expected sum FMUL + FFMA, rope 2 FMUL + 2 FFMA)",
    )
    print(
        "pre-stage probe: sum of squares = FMUL + FFMA; each RoPE output = FMUL (partner) + FFMA (self)"
    )


# ---------------------------------------------------------------------------------------------
# 4. Geometry and paths (H_zero, H_route)

K = ["r32", "t32", "r16", "t16", "q8", "ex2", "rcp", "rsq"]
S_E = 20  # 82 SMs // 4 kv heads (E:bc_attn.py:440)


def P(**kw):
    return tuple(kw.get(k, 0) for k in K)


def add(*ps):
    return tuple(sum(x) for x in zip(*ps))


def cdiv(a, b):
    return -(-a // b)


def dom(x, e, s):
    ea, eb, ec, ed, eh, ee, ef, eg = e
    sa, sb, sc, sd, sh, se, sf, sg = s
    capc = x * max(0, sh - eh)
    spare = max(0, (sd + sc + capc) - (ed + ec))
    return (
        eh <= sh
        and ed <= sd + capc
        and ed + ec <= sd + sc + capc
        and eb <= sb + x * spare
        and eb + ea <= sb + sa + x * spare
        and ee <= se
        and ef <= sf
        and eg <= sg
    )


def stock_geo(L):
    bound = (
        4096 * cdiv(L, 4096) + 1
    )  # bt_width * 256 + q_len, bt_width = 16 * ceil(ceil(L / 256) / 16)
    ns = max(1, min(41, cdiv(bound, 4 * 32)))
    return ns, cdiv(cdiv(bound, ns), 32) * 32


def live_groups(start, n, L, g):
    return 0 if L <= start else cdiv(min(n, L - start), g)


def anylive(a, b, L):
    return a < L and a < b


def elpis_tsum(j, own, L):
    """adds a p takes in the tile sum: p0 + p1, two lane xors, then red_sum warps 0..7 in order"""
    u, c = j - own, 0
    for size in (1, 2, 4):
        partner = ((u // size) * size) ^ size
        c += anylive(own + partner, own + partner + size, L)
    w, run, other = u // 8, u // 8 == 0, False
    for wp in range(1, 8):
        wl = anylive(own + 8 * wp, own + 8 * wp + 8, L)
        if wp == w:
            c += bool(anylive(own, own + 8, L) and w != 0)
            run = True
        elif run and wl:
            c += 1
    return c


def stock_tsum(j, own, L):
    """tl.sum over the 32-key tile: in-thread pair, lane xor 2 / 1, warp xor 2 / 1 (H_ptx)"""
    cur, c = {j - own}, 0
    for off in (1, 4, 2, 16, 8):
        partner = {x ^ off for x in cur}
        c += any(own + x < L for x in partner)
        cur |= partner
    return c


def side(L, s):
    if s == "e":
        T = cdiv(L, 64)
        return dict(
            nlive=min(S_E, T),
            slot=lambda j: (j // 64) % S_E,
            tiles=lambda x: [64 * t for t in range(x, T, S_E)],
            ts=64,
            ar=1,
            wr=1,
            tsum=elpis_tsum,
        )
    ns, sl = stock_geo(L)
    return dict(
        nlive=cdiv(L, sl),
        slot=lambda j: j // sl,
        tiles=lambda x: list(range(x * sl, min(x * sl + sl, L), 32)),
        ts=32,
        ar=2,
        wr=2,
        tsum=stock_tsum,
    )


def key_geo(L, j, G):
    s = G["slot"](j)
    tiles = G["tiles"](s)
    own = [t for t in tiles if t <= j < t + G["ts"]][0]
    idx, kk = tiles.index(own), (j - own) // 16
    others = min(16, L - (own + 16 * kk)) - 1
    o = int(idx > 0 or others > 0) + max(0, live_groups(own, G["ts"], L, 16) - (kk + 1))
    return dict(
        own=o,
        later=len(tiles) - idx - 1,
        laterk=sum(live_groups(t, G["ts"], L, 16) for t in tiles[idx + 1 :]),
        after=G["nlive"] - 1 - s,
        idx=idx,
        own_t=own,
        slot=s,
    )


def den_env(L, G, js):
    dr = 0
    for j in js:
        k = key_geo(L, j, G)
        dr = max(
            dr,
            2
            + G["tsum"](j, k["own_t"], L)
            + int(k["idx"] > 0)
            + k["later"]
            + 1
            + k["after"],
        )
    for s in range(G["nlive"]):
        dr = max(dr, G["wr"] + 1 + (G["nlive"] - 1 - s))
        n = len(G["tiles"](s))
        for t in range(1, n):
            dr = max(dr, G["ar"] + 1 + (n - 1 - t) + 1 + (G["nlive"] - 1 - s))
    return dict(dr32=dr, dt32=16, dex2=1)


def routes(L, s, js, srot=False):
    G = side(L, s)
    D = den_env(L, G, js)
    den = add(P(t32=2, r16=1), P(r32=D["dr32"], t32=D["dt32"], ex2=D["dex2"]))
    tail = add(
        den,
        P(rcp=1, r32=1),
        P(r16=3, r32=31) if (s == "e" and not srot) else P(r16=3, t32=2),
    )
    xs, w, a = P(r32=2, ex2=1), P(r32=G["wr"], ex2=1), P(r32=G["ar"], ex2=1)
    out = {}
    for j in js:
        k = key_geo(L, j, G)
        ch = add(P(t32=k["own"] + k["laterk"], r32=k["later"]), P(r32=1 + k["after"]))
        out[("AQ", j)] = add(P(t32=18, r16=1), xs, P(r16=1), ch, tail)
        out[("AK", j)] = add(P(r32=1, r16=1), P(t32=16), xs, P(r16=1), ch, tail)
        out[("AV", j)] = add(P(r32=1, r16=1), ch, tail)
    for x in range(G["nlive"]):
        out[("AW", x)] = add(P(t32=18, r16=1), w, P(r32=G["nlive"] - x), tail)
        tiles = G["tiles"](x)
        for ti in range(1, len(tiles)):
            later = tiles[ti + 1 :]
            out[("AA", x, ti)] = add(
                P(t32=18, r16=1),
                a,
                P(
                    r32=1 + len(later),
                    t32=sum(live_groups(t, G["ts"], L, 16) for t in later),
                ),
                P(r32=G["nlive"] - x),
                tail,
            )
    out[("AG",)] = P(r32=1, ex2=1, r16=4, rcp=1)
    return out, G, D


def keys(L):
    return sorted(set(list(range(min(L, 320))) + [L - 1] + list(range(0, L, 64))[:400]))


def bend_nats(text: str, name: str) -> tuple:
    m = re.search(rf"def {name}\(\) -> \S+:\n\s+\S*\{{([^}}]*)\}}", text)
    check(m is not None, f"{name} not found")
    return tuple(int(x.strip().rstrip("n")) for x in m.group(1).split(","))


def law_path(text: str, law: str) -> tuple:
    m = re.search(rf"law {law}:\n.*?Eb\.Path\{{([^}}]*)\}}", text, re.S)
    check(m is not None, f"law {law} not found")
    return tuple(int(x.strip().rstrip("n")) for x in m.group(1).split(","))


def check_geometry():
    model = (HERE / "err_attn.bend").read_text()
    laws = (HERE / "err_attn_finding_laws.bend").read_text()
    for s, name in (("e", "geo_e2"), ("s", "geo_s2")):
        G = side(2, s)
        D = den_env(2, G, [0, 1])
        for j in (0, 1):
            k = key_geo(2, j, G)
            got = (
                k["own"],
                k["later"],
                k["laterk"],
                k["after"],
                D["dr32"],
                D["dt32"],
                D["dex2"],
            )
            check(
                got == bend_nats(model, name),
                f"{name}: key {j} geometry {got} != Bend {bend_nats(model, name)}",
            )
    E, _, _ = routes(2, "e", [0, 1])
    S, _, _ = routes(2, "s", [0, 1])
    check(
        E[("AQ", 0)] == law_path(laws, "elpis_worst2_path"),
        f"elpis AQ path {E[('AQ', 0)]} != law",
    )
    check(
        S[("AQ", 0)] == law_path(laws, "stock_worst2_path"),
        f"stock AQ path {S[('AQ', 0)]} != law",
    )
    check(
        not any(dom(128, E[("AQ", 0)], p) for p in S.values()),
        "L = 2: some stock route dominates elpis AQ{0,0,0}",
    )
    print(
        f"geometry L = 2: geo_e2 = geo_s2 = {bend_nats(model, 'geo_e2')}; AQ paths elpis {E[('AQ', 0)]}, stock {S[('AQ', 0)]}"
    )


def scan():
    Ls = [
        1,
        2,
        3,
        16,
        17,
        32,
        33,
        64,
        65,
        128,
        129,
        256,
        500,
        1000,
        1280,
        1281,
        2000,
        2560,
        2561,
        4096,
        4097,
        8192,
        16384,
        65536,
        262144,
    ]
    print(
        "scan (routes not dominated by any stock route of the element; srot = elpis with stock's output stage):"
    )
    for L in Ls:
        js = keys(L)
        S, _, _ = routes(L, "s", js)
        cand = set(S.values())
        row = []
        for srot in (False, True):
            E, _, _ = routes(L, "e", js, srot)
            bad = sorted({
                k[0] for k, e in E.items() if not any(dom(128, e, p) for p in cand)
            })
            row.append(",".join(bad) or "-")
        check(
            row[0] != "-",
            f"L = {L}: the elpis routes are all dominated (the model's FALSE claim does not hold here)",
        )
        e0, s0 = routes(L, "e", [0])[0][("AQ", 0)], S[("AQ", 0)]
        print(
            f"  L={L:6d}  elpis: {row[0]:12s} srot: {row[1]:12s}  AQ(0) elpis r32/t32/ex2 {e0[0]}/{e0[1]}/{e0[5]}"
            f"  stock {s0[0]}/{s0[1]}/{s0[5]}"
        )


# ---------------------------------------------------------------------------------------------


def main(argv: list) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--stock", type=Path, required=True)
    ap.add_argument("--elpis", type=Path)
    ap.add_argument("--no-compiled", action="store_true")
    ap.add_argument("--triton", type=Path)
    ap.add_argument("--cuda-include", type=Path, action="append", default=[])
    ap.add_argument("--mutate", choices=sorted(MUTATIONS))
    a = ap.parse_args(argv[1:])
    if not a.no_compiled and a.triton is None:
        ap.error("--triton is required unless --no-compiled is given")
    with tempfile.TemporaryDirectory() as td:
        tdp = Path(td)
        elpis = a.elpis or build_elpis(a.stock, tdp)
        trees = {"S": a.stock, "E": elpis}
        if a.mutate:
            sd, rel, line, old, new = MUTATIONS[a.mutate]
            src = trees[sd]
            if sd == "S" or a.elpis:
                dst = tdp / f"mut{sd}"
                shutil.copytree(src, dst, symlinks=True)
                src = trees[sd] = dst
            lines = (src / rel).read_text().split("\n")
            check(
                lines[line - 1].count(old) == 1,
                f"mutation {a.mutate}: anchor not on line {line}",
            )
            lines[line - 1] = lines[line - 1].replace(old, new)
            (src / rel).write_text("\n".join(lines))
        check_frags(trees)
        check_pre(trees)
        if not a.no_compiled:
            check_stock_compiled(a.stock, a.triton)
            check_elpis_compiled(elpis, tdp, a.cuda_include)
        check_geometry()
        scan()
    print("err_attn_diff: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
