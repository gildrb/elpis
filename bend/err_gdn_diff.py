#!/usr/bin/env python3
# Copyright (c) 2026 Gil Rodrigues
"""Source link of bend/err_gdn.bend / bend/err_gdn_laws.bend.

The model holds the decode Gated DeltaNet rounding-error paths: elpis verify
gdn_conv_rule_norm_kernel against stock ExLlamaV3 355c6ee M=1 decode.

Builds the patched engine tree (the stock package directory + patches/exl3/series +
patches/exl3-ext/series, each patch checked against its series SHA-256) in a temporary
directory, then:
  1. citations: every `S <file>:<line> | <text>` (stock tree) and `E <file>:<line> |
     <text>` (patched tree) comment line of bend/err_gdn.bend, and the dispatch
     citations of H_dispatch below, must be the source line at that position
     (whitespace-trimmed equality);
  2. same arithmetic: each (stock line, elpis line) pair below must have the same
     arithmetic skeleton: operands (identifiers, literals, array elements, dereferences)
     are abstracted to `v`, loop / if headers, declarations, casts, exact bf16 -> fp32
     widenings and stock's CHANNELWISE = false ternary arms are removed; operators and
     function names (fmaf, __expf, rsqrtf, __shfl_xor_sync, __float2bfloat16_rz, ...)
     must match in order. Every edge of err_gdn.bend except the b/a GEMV order rests on
     these pairs; the b/a pairs show the same per-term operations (fmaf, shfl tree, bias
     add), whose different association the model counts;
  3. same helpers: the elpis copies of norm.cu's element helpers (gdn_norm_*) are the
     stock bodies.

Differential evidence on the source text, not a proof. `--mutate NAME` applies a
deliberate source mutation to the patched tree that the check must reject.

Usage: python3 bend/err_gdn_diff.py [--mutate NAME] STOCK_PACKAGE_DIR
       (STOCK_PACKAGE_DIR = the exllamav3 package directory of a clean 355c6ee checkout)
"""

from __future__ import annotations

import hashlib
import re
import shutil
import sys
import tempfile
from pathlib import Path
from typing import NoReturn

sys.path.insert(0, str(Path(__file__).resolve().parent))
import source_link

REPO = Path(__file__).resolve().parent.parent
MUTATE_ARGC = 3
PLAIN_ARGC = 2
MIN_MODEL_CITES = 80
MODEL = REPO / "bend" / "err_gdn.bend"
SERIES = [REPO / "patches" / "exl3", REPO / "patches" / "exl3-ext"]
FILES = {
    "gdn.cu": "exllamav3_ext/gdn.cu",
    "norm.cu": "exllamav3_ext/norm.cu",
    "gdn.cpp": "exllamav3_ext/libtorch/gated_delta_net.cpp",
    "gdn.py": "modules/gated_delta_net.py",
}

# H_dispatch (err_gdn_laws.bend): the served launches
DISPATCH = [
    ("S", "gdn.py", 1035, "self.bc_split and save_state and"),
    (
        "S",
        "gdn.py",
        1045,
        (
            "self.bc.run_bszN(x, y, conv_state, recurrent_state, recurrent_slots, "
            "save_history)"
        ),
    ),
    ("S", "gdn.cpp", 278, "gdn_ba_gemv_gr(x, ba_weight_t, ba_bias, s.ba, graph);"),
    ("S", "gdn.cpp", 280, "gated_delta_net_fused_op_3_gr"),
    ("S", "gdn.cpp", 290, "cuda_causal_conv1d_update_gr"),
    ("S", "gdn.cpp", 298, "true,"),
    ("S", "gdn.cpp", 303, "cuda_recurrent_gated_delta_rule_gr"),
    (
        "S",
        "gdn.cpp",
        319,
        "norm->run_gr(s.core_attn_out, s.core_attn_out_f, s.z, graph);",
    ),
    (
        "S",
        "gdn.cu",
        928,
        (
            "int v_split = (bsz == 1 && k_head_dim <= 128 && v_head_dim == "
            "128 && num_v_heads <= 64) ? 4 : 1;"
        ),
    ),
    (
        "S",
        "gdn.cu",
        983,
        (
            "if (v_split == 4) "
            "LAUNCH_RULE(cuda_recurrent_gated_delta_rule_kernel_128<false, "
            "4>)"
        ),
    ),
    (
        "S",
        "gdn.cu",
        1485,
        "else         LAUNCH_CONV(conv1d_update_kernel<true, false>)",
    ),
    ("S", "norm.cu", 641, "bool small = (dim <= 256);"),
    ("S", "norm.cu", 643, "dim3 blockDim(small ? 32 : NUM_THREADS, 1, 1);"),
    ("E", "gdn.cpp", 366, "fused_all = conv_sync.defined() && gdn_conv_rule_norm_gr"),
    (
        "E",
        "gdn.cpp",
        365,
        (
            "conv_sync = torch::zeros({MAX_BSZ * num_k_heads}, "
            "x.options().dtype(torch::kInt));"
        ),
    ),
    (
        "E",
        "gdn.cu",
        2993,
        (
            "#define GR_KS_DEFAULT 2                         // production "
            "b/a GEMV variant (EXL3_GDN_BA_KSPLIT unset)"
        ),
    ),
    ("E", "gdn.cu", 3553, "return env && env[0] ? std::atoi(env) : GR_KS_DEFAULT;"),
    ("E", "gdn.cu", 3707, "float scale = 1.0f / sqrtf(k_head_dim);"),
    ("S", "gdn.cu", 935, "float scale = 1.0f / sqrtf(k_head_dim);"),
    ("E", "gdn.cu", 3712, "int ks = ksplit < 0 ? gdn_ba_ksplit(-1) : ksplit;"),
    ("E", "gdn.cu", 3714, "if (S > GR_KS_ROWS || k / 2 > 512 * GR_KS_ITERS) ks = 0;"),
    (
        "E",
        "gdn.cu",
        3439,
        "else                gdn_rule_tokens<RULE_VERIFY, 4>(state, m, S, th, scale);",
    ),
    (
        "E",
        "gdn.cu",
        3444,
        (
            "gdn_rule_norm_row(m.out + warp_id * HD, w4, g4, y + row_off, epsilon, "
            "constant_bias, gate_act, dim, lane_id);"
        ),
    ),
]

# (stock file:line, elpis file:line): same arithmetic skeleton
SAME = [
    (("gdn.cu", 24), ("gdn.cu", 42)),  # _sigmoid_fast_exp
    (("gdn.cu", 49), ("gdn.cu", 67)),  # softplus
    (("gdn.cu", 50), ("gdn.cu", 68)),
    (("gdn.cu", 1543), ("gdn.cu", 3195)),  # qkv -> bf16
    (("gdn.cu", 1365), ("gdn.cu", 3218)),  # conv
    (("gdn.cu", 1368), ("gdn.cu", 3221)),
    (("gdn.cu", 1371), ("gdn.cu", 3223)),
    (("gdn.cu", 1373), ("gdn.cu", 3225)),
    (("gdn.cu", 747), ("gdn.cu", 2755)),  # l2 norm: squares, first xor tree
    (("gdn.cu", 752), ("gdn.cu", 2762)),
    (("gdn.cu", 797), ("gdn.cu", 2779)),  # rule: dot1 chain
    (("gdn.cu", 811), ("gdn.cu", 2799)),  # SUBK sum of dot1
    (("gdn.cu", 812), ("gdn.cu", 2800)),  # v
    (("gdn.cu", 827), ("gdn.cu", 2805)),  # state update
    (("gdn.cu", 829), ("gdn.cu", 2807)),  # v_out chain
    (("gdn.cu", 840), ("gdn.cu", 2857)),  # SUBK sum of v_out
    (("gdn.cu", 841), ("gdn.cu", 2858)),  # * scale, bf16 RZ
    (("gdn.cu", 806), ("gdn.cu", 2719)),  # exp(g)
    (("gdn.cu", 1554), ("gdn.cu", 3420)),  # beta
    (("gdn.cu", 1556), ("gdn.cu", 3422)),  # g
    (("gdn.cu", 1558), ("gdn.cu", 3425)),  # beta -> bf16
    (("norm.cu", 547), ("gdn.cu", 2954)),  # gated norm
    (("norm.cu", 19), ("gdn.cu", 2956)),
    (("norm.cu", 552), ("gdn.cu", 2958)),
    (("norm.cu", 569), ("gdn.cu", 2965)),
    (("norm.cu", 586), ("gdn.cu", 2971)),
    (("norm.cu", 588), ("gdn.cu", 2974)),
    (("gdn.cu", 1657), ("gdn.cu", 3330)),  # b/a: per-term fmaf, tree add, bias add
    (("gdn.cu", 1658), ("gdn.cu", 3331)),
    (("gdn.cu", 1662), ("gdn.cu", 3352)),
    (("gdn.cu", 1666), ("gdn.cu", 3413)),
]

# Stock l2 norm: the second tree's lanes >= 4 hold 0.0f (exact adds); elpis adds the
# four partials as (p0 + p2) + (p1 + p3), what the 2-level xor tree over lanes 0..3
# adds
L2_STOCK = [
    ("gdn.cu", 762, "sumq = lane < HEAD_DIM / 32 ? sh_red[0][lane] : 0.0f;"),
    ("gdn.cu", 771, "q = q * rsqrtf(sumq + 1e-6f);"),
]
L2_ELPIS = [
    ("gdn.cu", 2767, "float rs = rsqrtf(((p0 + p2) + (p1 + p3)) + 1e-6f);"),
    ("gdn.cu", 2768, "vec[lane] = x0 * rs;"),
]

# norm.cu element helpers and their elpis copies (gdn.cu, prefix gdn_norm_)
HELPERS = [
    ("read_bfloat164", "gdn_norm_read_bfloat164"),
    ("read_float4", "gdn_norm_read_float4"),
    ("write_half4", "gdn_norm_write_half4"),
    ("sum_sq4", "gdn_norm_sum_sq4"),
    ("apply4", "gdn_norm_apply4"),
    ("_silu", "gdn_norm_silu"),
    ("_sigmoid_f", "gdn_norm_sigmoid_f"),
]

# Mutations by name: the file, its original text and the replacement.
MUTATIONS = {
    "dot1_order": (
        "gdn.cu",
        "sum = sum + k_rd[j] * state[j];",
        "sum = k_rd[j] * state[j] + sum * 1.0f;",
    ),
    "l2_order": (
        "gdn.cu",
        "float rs = rsqrtf(((p0 + p2) + (p1 + p3)) + 1e-6f);",
        "float rs = rsqrtf(((p0 + p1) + (p2 + p3)) + 1e-6f);",
    ),
    "silu_div": (
        "gdn.cu",
        (
            "float recip = __fdividef(1.0f, 1.0f + e);\n    return x * recip;\n}\n\n"
            "__device__ __forceinline__ float gdn_norm_sigmoid_f"
        ),
        (
            "float recip = 1.0f / (1.0f + e);\n    return x * recip;\n}\n\n__device__ "
            "__forceinline__ float gdn_norm_sigmoid_f"
        ),
    ),
    "ba_bias": (
        "gdn.cu",
        "bv += __half2float(ba_bias[h]);",
        "bv += 2.0f * __half2float(ba_bias[h]);",
    ),
}


def fail(msg: str) -> NoReturn:
    """Stop with an error.

    Args:
        msg: The failure description.

    Raises:
        SystemExit: Always.

    """
    text = f"err_gdn_diff: {msg}"
    raise SystemExit(text)


def patch_tool() -> str:
    """Resolve `patch` on PATH.

    Returns:
        The executable path.

    """
    found = shutil.which("patch")
    if found is None:
        fail("patch is not on PATH")
    return found


def build_patched(stock: Path, out: Path) -> None:
    """Copy the stock package to out and apply both series, hash-checked.

    Args:
        stock: The stock package directory.
        out: The new patched tree.

    """
    patch_exe = patch_tool()
    shutil.copytree(
        stock, out, ignore=shutil.ignore_patterns("__pycache__", "*.so", "build")
    )
    for d in SERIES:
        for line in (d / "series").read_text().splitlines():
            if not line.strip():
                continue
            sha, name = line.split()
            patch = d / name
            if hashlib.sha256(patch.read_bytes()).hexdigest() != sha:
                fail(f"{patch}: sha256 differs from the series")
            r = source_link.run(
                [
                    patch_exe,
                    "-p1",
                    "-s",
                    "--no-backup-if-mismatch",
                    "-d",
                    str(out),
                    "-i",
                    str(patch),
                ],
                capture_output=True,
                text=True,
                check=False,
                cpu_heavy=False,
            )
            if r.returncode:
                fail(f"{name} does not apply: {r.stdout}{r.stderr}")


def line_of(root: Path, short: str, n: int) -> str:
    """Return line n of a tracked file, whitespace-trimmed.

    Args:
        root: The tree.
        short: The FILES key.
        n: The 1-based line number.

    Returns:
        The trimmed line.

    """
    lines = (root / FILES[short]).read_text().split("\n")
    if not 1 <= n <= len(lines):
        fail(f"{short}:{n} out of range")
    return lines[n - 1].strip()


def strip_wrapper(s: str, name: str) -> str:
    """Remove every name(X) wrapper, keeping X (balanced).

    Args:
        s: The source line.
        name: The wrapper function name.

    Returns:
        The line without the wrappers.

    """
    while True:
        i = s.find(name + "(")
        if i < 0:
            return s
        j = i + len(name) + 1
        depth = 1
        k = j
        while depth:
            if k >= len(s):
                fail(f"unbalanced {name}( in {s!r}")
            depth += {"(": 1, ")": -1}.get(s[k], 0)
            k += 1
        s = s[:i] + s[j : k - 1] + s[k:]


def strip_header(s: str) -> str:
    """Drop a leading `for (...)` / `if (...)` header.

    Args:
        s: The source line.

    Returns:
        The line without the header.

    """
    m = re.match(r"(for|if)\s*\(", s)
    if not m:
        return s
    k = m.end()
    depth = 1
    while depth:
        depth += {"(": 1, ")": -1}.get(s[k], 0)
        k += 1
    return s[k:].strip()


TOKEN = re.compile(
    r"\s*(\d+(?:\.\d*)?(?:e[-+]?\d+)?f?|[A-Za-z_]\w*(?:\.\w+)*|\+=|\*=|-="
    r"|[-+*/=(),?:;\[\]])"
)
TYPES = {"float", "bfloat16", "half", "const", "int", "size_t", "float4", "float2"}
OPERAND_BEFORE = {None, "=", "(", ",", "+", "-", "*", "/", "?", ":", "+=", "*=", "-="}


def skeleton(src: str) -> str:
    """Abstract a source line to its arithmetic skeleton.

    Args:
        src: The source line.

    Returns:
        Operators and function names, with operands replaced by `v`.

    """
    s = strip_header(src.strip())
    s = re.sub(r"\((?:float|size_t|int)\)\s*", "", s)
    s = re.sub(r"\(CHANNELWISE \? [^:]+ : ([^)]+)\)", r"\1", s)
    s = s.replace("CHANNELWISE ? 1.0f : ", "")
    s = strip_wrapper(s, "__bfloat162float")
    toks: list[str] = []
    pos = 0
    while pos < len(s):
        m = TOKEN.match(s, pos)
        if not m:
            fail(f"cannot tokenize {src!r} at {s[pos:]!r}")
        toks.append(str(m[1]))
        pos = m.end()
    out: list[str] = []
    depth = 0
    prev: str | None = None
    for i, tok in enumerate(toks):
        if tok == "[":
            depth += 1
            continue
        if tok == "]":
            depth -= 1
            continue
        if depth or tok in TYPES:
            continue
        if tok == "*" and prev in OPERAND_BEFORE:
            continue  # dereference
        nxt = toks[i + 1] if i + 1 < len(toks) else None
        t = "v" if re.match(r"[A-Za-z_\d]", tok) and nxt != "(" else tok
        if t == "v" and prev == "v":
            out.pop()  # `type name` leftovers
        out.append(t)
        prev = t
    return "".join(out)


def helper_body(text: str, name: str) -> str:
    """Return a __device__ helper's body, whitespace-normalized.

    Args:
        text: The source file text.
        name: The helper name.

    Returns:
        The body from its opening brace to its closing brace.

    """
    m = re.search(r"__device__[^\n]*\b" + re.escape(name) + r"\(", text)
    if not m:
        fail(f"helper {name} not found")
    i = text.index("{", m.end())
    j = text.index("\n}", i)
    return re.sub(r"\s+", " ", text[i : j + 2])


def parse_args(argv: list[str]) -> tuple[str | None, Path]:
    """Parse [--mutate NAME] STOCK_PACKAGE_DIR.

    Args:
        argv: The command line.

    Returns:
        (mutation name or None, resolved stock directory).

    """
    mutate = None
    if len(argv) >= MUTATE_ARGC and argv[1] == "--mutate":
        mutate = argv[2]
        argv = [argv[0], *argv[3:]]
        if mutate not in MUTATIONS:
            fail(f"unknown mutation {mutate}; known: {', '.join(MUTATIONS)}")
    if len(argv) != PLAIN_ARGC:
        fail("usage: err_gdn_diff.py [--mutate NAME] STOCK_PACKAGE_DIR")
    return mutate, Path(argv[1]).resolve()


type Cite = tuple[str, str, int, str, str]


def check_cites(roots: dict[str, Path]) -> list[Cite]:
    """Check every citation (check 1).

    Args:
        roots: The stock (S) and patched (E) trees.

    Returns:
        The checked citations.

    """
    cites: list[Cite] = []
    for k, line in enumerate(MODEL.read_text().split("\n"), 1):
        m = re.match(r"#\s*([SE]) (\S+):(\d+) \| (.*)$", line)
        if m:
            cites.append((
                str(m[1]),
                str(m[2]),
                int(m[3]),
                str(m[4]),
                f"err_gdn.bend:{k}",
            ))
    cites += [(s, f, ln, t, "H_dispatch") for s, f, ln, t in DISPATCH]
    cites += [("S", f, ln, t, "l2") for f, ln, t in L2_STOCK] + [
        ("E", f, ln, t, "l2") for f, ln, t in L2_ELPIS
    ]
    for side, short, ln, text, where in cites:
        got = line_of(roots[side], short, ln)
        if got != text.strip():
            fail(f"{where}: {side} {short}:{ln} is {got!r}, cited {text.strip()!r}")
    if len([c for c in cites if c[4].startswith("err_gdn")]) < MIN_MODEL_CITES:
        fail("too few model citations parsed")
    return cites


def check_same(stock: Path, elpis: Path) -> None:
    """Check the same arithmetic skeleton of every pair (check 2).

    Args:
        stock: The stock tree.
        elpis: The patched tree.

    """
    for (sf, sl), (ef, el) in SAME:
        a = skeleton(line_of(stock, sf, sl))
        eline = line_of(elpis, ef, el)
        for s2, e2 in HELPERS:
            eline = re.sub(r"\b" + re.escape(e2) + r"\b", s2, eline)
        b = skeleton(eline)
        if a != b:
            fail(f"arithmetic differs: S {sf}:{sl} {a!r} vs E {ef}:{el} {b!r}")


def check_helpers(stock: Path, elpis: Path) -> None:
    """Check the elpis helper copies (check 3).

    Args:
        stock: The stock tree.
        elpis: The patched tree.

    """
    stext = (stock / FILES["norm.cu"]).read_text()
    etext = (elpis / FILES["gdn.cu"]).read_text()
    for sname, ename in HELPERS:
        a = helper_body(stext, sname)
        b = helper_body(etext, ename)
        for s2, e2 in HELPERS:
            b = re.sub(r"\b" + re.escape(e2) + r"\b", s2, b)
        if a != b:
            fail(f"helper {ename} is not norm.cu's {sname}: {a!r} vs {b!r}")


def main(argv: list[str]) -> None:
    """Run every check on a patched copy of the stock tree.

    Args:
        argv: The command line.

    """
    mutate, stock = parse_args(argv)
    with tempfile.TemporaryDirectory(prefix="err_gdn_diff.") as tmp:
        elpis = Path(tmp) / "exllamav3"
        build_patched(stock, elpis)
        if mutate:
            short, a, b = MUTATIONS[mutate]
            f = elpis / FILES[short]
            text = f.read_text()
            if text.count(a) != 1:
                fail(f"mutation {mutate}: {text.count(a)} matches")
            f.write_text(text.replace(a, b))
        cites = check_cites({"S": stock, "E": elpis})
        check_same(stock, elpis)
        check_helpers(stock, elpis)
        n = len(cites) + len(SAME) + len(HELPERS)
        sys.stdout.write(
            f"err_gdn_diff: OK ({n} checks: {len(cites)} citations, {len(SAME)} "
            f"arithmetic pairs, {len(HELPERS)} helpers)\n"
        )


if __name__ == "__main__":
    main(sys.argv)
