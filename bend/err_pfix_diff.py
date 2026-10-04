#!/usr/bin/env python3
"""
Finite source link of bend/err_pfix.bend (ext 3031 prefill attention rounding-error paths) to the full-series
patched tree and to stock 355c6ee's Triton prefill.

Builds the patched engine tree (stock package directory + patches/exl3/series + patches/exl3-ext/series, each patch
checked against its series SHA-256) in a temporary directory, then checks, failing closed:
  b. model text: err_pfix.bend holds the expressions below (chain length, body size, segment literals);
  c. combine: chain_step / pattn_chain_combine as written (asserted verbatim; the per-row B formula and the pair
     condition parsed from the text) give, for a row with K = 2 .. 10 own chains in a warp combine of nch = K ..
     PA_MAXCH chains, every own chain's term the model's chain_c(k, K) roundings (chain_c computed here mirroring
     err_pfix.bend's body_b / body_c / chain_c) and fold the row's all-masked chains K .. nch - 1 (w = 0, x = 0)
     exactly; a row with K = 1 gets only x_0 * w_0 with w_0 = ex2(0) = 1 (exact: the model's no-combine case);
     the thread's 8 p tile sum, parsed from the text, is a balanced f_add tree of depth 3 over sc[0..3][2r, 2r+1],
     followed by the two quad f_add levels (den_in = 5);
  a. kernel text: the 3031 lines occur verbatim (once each) in pattn_kernel.cuh, the per-warp ones identically in
     pattn8_kernel.cuh (its park line the first statement of `if (act)`), the helpers only in pattn_kernel.cuh
     (included by pattn8), pattn.cu passes the scratch to both launches and checks one CTA per SM;
  d. chain plan replay: for every block start q64 in 0 .. 4096 and samples up to 262144, every warp (rows q_abs0 ..
     q_abs0 + 15, q_abs0 = q64 + 16 j) and every key bound total, the C formulas (ch_tiles, n_hi, ntiles, nch,
     evaluated from the extracted text) give E = cdiv(q64 + 1, 256) = e_len(q64), nch <= PA_MAXCH, and every row's
     kr (the call site's row_chains, evaluated from the text) is the model's K = n_chains(n_tiles(p), E); the
     combine of the row (c's transcription with that kr and nch) passes chain_c(k, K) roundings per own chain;
  e. stock citations (TP = stock modules/attention_fn/triton_paged.py): split span / bounds, interior bound, partial
     store, combine, split-count candidates (1, 2, 3, 4, 5, 6, 8).
Text evidence and a finite replay, not a proof. `--mutate NAME` applies a deliberate mutation (patched source or
model text) that the check must reject.

Usage: python3 bend/err_pfix_diff.py [--mutate NAME] STOCK_PACKAGE_DIR
  STOCK_PACKAGE_DIR: the stock exllamav3 package directory at 355c6ee (OUT/stock of bend/engine_trees.py).
"""

from __future__ import annotations

import hashlib
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

WT = Path(__file__).resolve().parent.parent
MODEL_FILE = WT / "bend/err_pfix.bend"
SERIES = [WT / "patches/exl3", WT / "patches/exl3-ext"]
FILES = {
    "K": "exllamav3_ext/pattn_kernel.cuh",
    "K8": "exllamav3_ext/pattn8_kernel.cuh",
    "CU": "exllamav3_ext/pattn.cu",
}

# per-warp kernel lines: exactly once in pattn_kernel.cuh and exactly once in pattn8_kernel.cuh
WARP_LINES = [
    "const int ch_tiles = (q_abs64 + 256) / 256;",
    "if (it > 0 && it % ch_tiles == 0) park_chain(park, slot, it / ch_tiles - 1, warp, lane, acc, m, l);",
    "const float sum = f_add(f_add(f_add(sc[0][2 * r], sc[0][2 * r + 1]), f_add(sc[1][2 * r], sc[1][2 * r + 1])), "
    "f_add(f_add(sc[2][2 * r], sc[2][2 * r + 1]), f_add(sc[3][2 * r], sc[3][2 * r + 1])));",
    "l[r] = f_fma(l[r], alpha[r], sum);",
    "const int nch = (ntiles + ch_tiles - 1) / ch_tiles;",
    "if (nch > 1) { const int kr[2] = {row_chains(q_abs_r0, ch_tiles, nch), row_chains(q_abs_r1, ch_tiles, nch)}; "
    "pattn_chain_combine(park, slot, nch, kr, warp, lane, acc, m, l); }",
    "const int q_abs_r0 = q_abs0 + gid, q_abs_r1 = q_abs0 + gid + 8;",
    "l[r] = f_add(l[r], __shfl_xor_sync(0xffffffffu, l[r], 1));",
    "l[r] = f_add(l[r], __shfl_xor_sync(0xffffffffu, l[r], 2));",
    "const int q_abs64 = total - q_len + (p0 & ~63);",
    "const int n_hi = min(q_abs0 + PA_BQ, total);",
]

# helpers: exactly once in pattn_kernel.cuh, absent from pattn8_kernel.cuh (it includes pattn_kernel.cuh)
HELPER_LINES = [
    "#define PA_MAXCH 10",
    "#define PA_PARK_Q 33",
    "#define PA_SLOT_F4 (PA_MAXCH * PA_PARK_W * PA_PARK_Q * 32)",
    "*park_at(park, slot, c, warp, lane, j) = make_float4(acc[j][0], acc[j][1], acc[j][2], acc[j][3]);",
    "*park_at(park, slot, c, warp, lane, 32) = make_float4(m[0], m[1], l[0], l[1]);",
    "m[0] = -INFINITY; m[1] = -INFINITY; l[0] = 0.f; l[1] = 0.f;",
    "w[0] = is_ninf(ml.x) ? 0.f : ex2(f_sub(ml.x, ms[0]));",
    "w[1] = is_ninf(ml.y) ? 0.f : ex2(f_sub(ml.y, ms[1]));",
    "ms[0] = is_ninf(ms[0]) ? 0.f : ms[0];",
    "ms[1] = is_ninf(ms[1]) ? 0.f : ms[1];",
    "const int B0 = kr[0] > 4 ? kr[0] - 3 : 1, B1 = kr[1] > 4 ? kr[1] - 3 : 1;",
    "return min((q_abs / PA_BN + ch_tiles) / ch_tiles, nch);",
]

# chain_step and the combine loop as written; the transcription in combine_counts() follows this text
CHAIN_STEP = (
    "{ if (c >= B) { v = f_fma(x0, w0, v); if (c + 1 < K) v = f_fma(x1, w1, v); return; } "
    "if (c + 1 < B) { const float pr = f_fma(x0, w0, f_mul(x1, w1)); v = c == 0 ? pr : f_add(v, pr); return; } "
    "const float pr = f_mul(x0, w0); v = c == 0 ? pr : f_add(v, pr); if (c + 1 < K) v = f_fma(x1, w1, v); }"
)
COMBINE_LOOP = [
    "park_chain(park, slot, nch - 1, warp, lane, acc, m, l);",
    "for (int c = 0; c < nch; c += 2)",
    "const bool two = c + 1 < nch;",
    "const float4 ml0 = *park_at(park, slot, c, warp, lane, 32);",
    "const float4 ml1 = two ? *park_at(park, slot, c + 1, warp, lane, 32) : zero;",
    "chain_w(ml0, ms, w0);",
    "chain_w(ml1, ms, w1);",
    "chain_step(c, B0, kr[0], l[0], ml0.z, w0[0], ml1.z, w1[0]);",
    "chain_step(c, B1, kr[1], l[1], ml0.w, w0[1], ml1.w, w1[1]);",
    "const float4 x0 = *park_at(park, slot, c, warp, lane, j);",
    "const float4 x1 = two ? *park_at(park, slot, c + 1, warp, lane, j) : zero;",
    "chain_step(c, B0, kr[0], acc[j][0], x0.x, w0[0], x1.x, w1[0]);",
    "chain_step(c, B0, kr[0], acc[j][1], x0.y, w0[0], x1.y, w1[0]);",
    "chain_step(c, B1, kr[1], acc[j][2], x0.z, w0[1], x1.z, w1[1]);",
    "chain_step(c, B1, kr[1], acc[j][3], x0.w, w0[1], x1.w, w1[1]);",
]

CU_LINES = [
    'TORCH_CHECK(b6 == 1 && b8 == 1, "pattn: the chain scratch needs one CTA per SM");',
    "cuda_check(cudaOccupancyMaxActiveBlocksPerMultiprocessor(&b6, pattn_detail::pattn_kernel<false>, PA_THREADS, PA_SMEM));",
    "cuda_check(cudaOccupancyMaxActiveBlocksPerMultiprocessor(&b8, pattn_detail::pattn8_kernel<false>, P8_THREADS, P8_SMEM));",
    "float4* pk = reinterpret_cast<float4*>(scratch.data_ptr());",
    'TORCH_CHECK(mode == 0, "pattn: mode must be 0 (fp32 accumulation; the f16-accumulating mode was removed by ext 3022)");',
]

# model expressions err_pfix.bend must contain
MODEL = [
    "def e_len(+q64: Nat) -> Nat:\n  Nat.div(Nat.add(q64, 256n), 256n)",
    "def body_b(+K: Nat) -> Nat:\n  pick(Nat.is_lt(4n, K), Nat.sub(K, 3n), 1n)",
    "def body_c(+k: Nat, +B: Nat) -> Nat:\n  +j = Nat.div(k, 2n)\n  +steps = Nat.div(Nat.add(B, 1n), 2n)\n"
    "  +base = pick(Nat.is_eq(Nat.mod(k, 2n), 1n), 2n, 1n)\n"
    "  +adds = pick(Nat.is_eq(j, 0n), Nat.sub(steps, 1n), Nat.sub(steps, j))\n  Nat.add(base, adds)",
    "def chain_c(+k: Nat, +K: Nat) -> Nat:\n  +B = body_b(K)\n"
    "  pick(Nat.is_lt(k, B), Nat.add(body_c(k, B), Nat.sub(K, B)), Nat.sub(K, k))",
    "def den_in() -> Eb.Path:\n  Eb.Path{5n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}",
    "def e_later() -> Eb.Path:\n  Eb.Path{2n, 0n, 0n, 0n, 0n, 1n, 0n, 0n}",
    "def den_later() -> Eb.Path:\n  Eb.Path{2n, 0n, 0n, 0n, 0n, 1n, 0n, 0n}",
    "def s_later() -> Eb.Path:\n  Eb.Path{2n, 2n, 0n, 0n, 0n, 1n, 0n, 0n}",
    "def fold() -> Eb.Path:\n  Eb.Path{1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}",
    "def comb(c: Nat) -> Eb.Path:\n  Eb.Path{1n+c, 0n, 0n, 0n, 0n, 1n, 0n, 0n}",
    "def fixed() -> Eb.Path:\n  Eb.Path{0n, 0n, 2n, 0n, 0n, 0n, 1n, 0n}",
    "def n_tiles(+p: Nat) -> Nat:\n  1n+Nat.div(p, 32n)",
    "def n_chains(+n: Nat, +E: Nat) -> Nat:\n  cdiv(n, E)",
    "def interior_tiles(+q64: Nat) -> Nat:\n  Nat.div(Nat.add(q64, 1n), 32n)",
    "Eb.add(when(Nat.is_lt(1n, K), comb(chain_c(k, K))), score(Nat.is_lt(Nat.add(Nat.mul(k, E), t), I), s)))))",
]

# the model's chain_c table, K = 2 .. 10 (err_pfix.bend comment / err_pfix_laws.bend)
CHAIN_TABLE = {
    2: [2, 1],
    3: [3, 2, 1],
    4: [4, 3, 2, 1],
    5: [4, 5, 3, 2, 1],
    6: [5, 6, 5, 3, 2, 1],
    7: [5, 6, 5, 6, 3, 2, 1],
    8: [6, 7, 6, 7, 5, 3, 2, 1],
    9: [6, 7, 6, 7, 5, 6, 3, 2, 1],
    10: [7, 8, 7, 8, 6, 7, 5, 3, 2, 1],
}

# stock citations (TP line, expected substring); line numbers as in bend/err_prefill_diff.py CITES
TP_CITES = [
    (1476, "span = tl.cdiv(tl.cdiv(n_hi - n_lo, num_splits), BLOCK_N) * BLOCK_N"),
    (1477, "s_lo = n_lo + split * span"),
    (1478, "s_hi = tl.minimum(s_lo + span, n_hi)"),
    (1533, "n_full = tl.maximum(((q_abs_min + 1) // BLOCK_N) * BLOCK_N, 0)"),
    (1554, "if IS_SPLIT:"),
    (1564, "tl.store(partial_ml + ml_base + tl.arange(0, BLOCK_M) * 2 + 1, l)"),
    (1620, 'm_safe = tl.where(m_max == -float("inf"), 0.0, m_max)'),
    (1624, "for sp in range(num_splits):"),
    (1628, 'w = tl.where(m_s == -float("inf"), 0.0, tl.exp2(m_s - m_safe))'),
    (1630, "acc += o_s * w[:, None]"),
    (1631, "l_sum += l_s * w"),
    (1635, "out_tile = acc / tl.where(l_sum[:, None] == 0.0, 1.0, l_sum[:, None])"),
    (1849, "if num_splits is None:"),
    (1857, "num_splits = 1"),
    (1858, "if bound_kv >= 8192 and programs:"),
    (1860, "for cand in (1, 2, 3, 4, 5, 6, 8):"),
    (1871, "num_splits = min(num_splits, max_splits)"),
]

# name: (target, old, new); target "MODEL" mutates the model text, else a FILES key of the patched tree
MUTATIONS = {
    "ch_tiles_512": (
        "K",
        "const int ch_tiles = (q_abs64 + 256) / 256;",
        "const int ch_tiles = (q_abs64 + 512) / 512;",
    ),
    "tail_2": (
        "K",
        "const int B0 = kr[0] > 4 ? kr[0] - 3 : 1, B1 = kr[1] > 4 ? kr[1] - 3 : 1;",
        "const int B0 = kr[0] > 3 ? kr[0] - 2 : 1, B1 = kr[1] > 3 ? kr[1] - 2 : 1;",
    ),
    # the pre-fix plan: every row combines with the warp's chain count
    "warp_k": (
        "K",
        "return min((q_abs / PA_BN + ch_tiles) / ch_tiles, nch);",
        "return nch;",
    ),
    "seq_lane_sum": (
        "K",
        "const float sum = f_add(f_add(f_add(sc[0][2 * r], sc[0][2 * r + 1]), f_add(sc[1][2 * r], sc[1][2 * r + 1])),\n"
        "                                    f_add(f_add(sc[2][2 * r], sc[2][2 * r + 1]), f_add(sc[3][2 * r], sc[3][2 * r + 1])));",
        "const float sum = f_add(f_add(f_add(f_add(f_add(f_add(f_add(sc[0][2 * r], sc[0][2 * r + 1]), sc[1][2 * r]), "
        "sc[1][2 * r + 1]),\n                                    sc[2][2 * r]), sc[2][2 * r + 1]), sc[3][2 * r]), sc[3][2 * r + 1]);",
    ),
    "pair_fold": (
        "K",
        "const float pr = f_fma(x0, w0, f_mul(x1, w1));",
        "const float pr = f_add(f_mul(x0, w0), f_mul(x1, w1));",
    ),
    "park8_outside_act": (
        "K8",
        "        if (act)\n        {\n            if (it > 0 && it % ch_tiles == 0) park_chain(park, slot, it / ch_tiles - 1, warp, lane, acc, m, l);\n",
        "        if (it > 0 && it % ch_tiles == 0) park_chain(park, slot, it / ch_tiles - 1, warp, lane, acc, m, l);\n"
        "        if (act)\n        {\n",
    ),
    "one_cta_check": (
        "CU",
        "TORCH_CHECK(b6 == 1 && b8 == 1,",
        "TORCH_CHECK(b6 >= 1 && b8 >= 1,",
    ),
    "model_e_len": (
        "MODEL",
        "Nat.div(Nat.add(q64, 256n), 256n)",
        "Nat.div(Nat.add(q64, 512n), 512n)",
    ),
    "model_tail": (
        "MODEL",
        "pick(Nat.is_lt(4n, K), Nat.sub(K, 3n), 1n)",
        "pick(Nat.is_lt(3n, K), Nat.sub(K, 2n), 1n)",
    ),
}


def fail(msg: str) -> None:
    raise SystemExit(f"err_pfix_diff: FAIL: {msg}")


def build_patched(stock: Path, out: Path) -> None:
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
            r = subprocess.run(
                [
                    "patch",
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
            )
            if r.returncode:
                fail(f"{name} does not apply: {r.stdout}{r.stderr}")


def norm(s: str) -> str:
    """whitespace-normalized text (statements may wrap)"""
    return re.sub(r"\s+", " ", s).strip()


def count(text: str, needle: str) -> int:
    return norm(text).count(norm(needle))


def func_body(text: str, name: str) -> str:
    m = re.search(r"__device__[^{;]*\b" + re.escape(name) + r"\(", text)
    if not m:
        fail(f"function {name} not found")
    i = text.index("{", m.end())
    depth, k = 0, i
    while True:
        depth += {"{": 1, "}": -1}.get(text[k], 0)
        k += 1
        if depth == 0:
            return text[i:k]


# ---- (c) the model's chain_c, mirroring err_pfix.bend ----
def body_b(K: int) -> int:
    return K - 3 if 4 < K else 1


def body_c(k: int, B: int) -> int:
    j = k // 2
    steps = (B + 1) // 2
    base = 2 if k % 2 == 1 else 1
    adds = steps - 1 if j == 0 else steps - j
    return base + adds


def chain_c(k: int, K: int) -> int:
    B = body_b(K)
    return body_c(k, B) + (K - B) if k < B else K - k


def combine_counts(nch: int, K: int, b_of, pa: int) -> dict[int, int]:
    """Roundings each own chain's term passes in pattn_chain_combine's loop for a row with K own chains in a warp
    combine of nch chains (text: COMBINE_LOOP, CHAIN_STEP). The loop steps c = 0, 2, 4, .. < nch with
    chain_step(c, B, K, v, x0, w0, x1, w1), B = b_of(K):
      c >= B:      v = fma(x0, w0, v) (one rounding of everything; exact when chain c is all-masked for the row,
                   c >= K: w = 0, x = 0), then if c + 1 < K: v = fma(x1, w1, v);
      c + pa < B:  pr = fma(x0, w0, x1 * w1) (chain c: 1, chain c + 1: 2), v = c == 0 ? pr : v + pr (one more of all);
      else:        pr = x0 * w0 (1), v = c == 0 ? pr : v + pr, then if c + 1 < K: v = fma(x1, w1, v).
    b_of / pa are the per-row B formula and pair condition parsed from the text."""
    B = b_of(K)
    v: dict[int, int] = {}

    def fold(ch: int) -> None:
        nonlocal v
        v = {k: n + 1 for k, n in v.items()}
        v[ch] = 1

    for c in range(0, nch, 2):
        if c >= B:
            if c < K:
                fold(c)
            if c + 1 < K:
                fold(c + 1)
            continue
        pr = {c: 1, c + 1: 2} if c + pa < B else {c: 1}
        v = (
            pr
            if c == 0
            else {k: n + 1 for k, n in v.items()} | {k: n + 1 for k, n in pr.items()}
        )
        if c + pa >= B and c + 1 < K:
            fold(c + 1)
    if sorted(v) != list(range(K)):
        fail(
            f"combine of a row with {K} own chains (nch = {nch}) covers chains {sorted(v)}"
        )
    return v


def add_depth(expr: str) -> tuple[int, list[str]]:
    """depth and leaves of a nested f_add(a, b) expression"""
    expr = expr.strip()
    if not expr.startswith("f_add("):
        return 0, [expr]
    inner = expr[len("f_add(") :]
    depth, k = 0, 0
    while True:
        ch = inner[k]
        if ch == "(" or ch == "[":
            depth += 1
        elif ch == ")" or ch == "]":
            if depth == 0:
                break
            depth -= 1
        elif ch == "," and depth == 0:
            split = k
        k += 1
    if inner[k + 1 :].strip():
        fail(f"trailing text after f_add: {inner[k + 1 :]!r}")
    da, la = add_depth(inner[:split])
    db, lb = add_depth(inner[split + 1 : k])
    return 1 + max(da, db), la + lb


C_EXPR = re.compile(r"^[\w\s+\-*/()&~,]+$")


def c_expr(text: str, name: str) -> str:
    """right-hand side of the unique `const int name = ...;` of text"""
    found = re.findall(r"const int " + re.escape(name) + r" = ([^;]+);", text)
    if len(found) != 1:
        fail(f"`const int {name}` occurs {len(found)} times")
    return norm(found[0])


_COMPILED: dict[str, object] = {}


def c_eval(expr: str, env: dict[str, object]) -> int:
    """evaluate C int arithmetic on non-negative operands (/ is floor division there)"""
    code = _COMPILED.get(expr)
    if code is None:
        if not C_EXPR.match(expr):
            fail(f"cannot evaluate C expression {expr!r}")
        code = _COMPILED[expr] = compile(expr.replace("/", "//"), "<c>", "eval")
    return eval(code, {"__builtins__": {}, "min": min, "max": max}, env)


def main(argv: list[str]) -> None:
    args = argv[1:]
    mutate = None
    if len(args) >= 2 and args[0] == "--mutate":
        mutate, args = args[1], args[2:]
        if mutate not in MUTATIONS:
            fail(f"unknown mutation {mutate!r}; known: {', '.join(MUTATIONS)}")
    if len(args) != 1:
        fail("usage: err_pfix_diff.py [--mutate NAME] STOCK_PACKAGE_DIR")
    stock = Path(args[0]).resolve()
    model = MODEL_FILE.read_text()
    with tempfile.TemporaryDirectory(prefix="err_pfix_diff.") as tmp:
        tree = Path(tmp) / "exllamav3"
        build_patched(stock, tree)
        src = {k: (tree / f).read_text() for k, f in FILES.items()}
        if mutate is not None:
            key, old, new = MUTATIONS[mutate]
            target = model if key == "MODEL" else src[key]
            if target.count(old) != 1:
                fail(f"mutation {mutate}: {target.count(old)} matches of its anchor")
            if key == "MODEL":
                model = model.replace(old, new)
            else:
                src[key] = src[key].replace(old, new)
            print(f"err_pfix_diff: applied mutation {mutate}")
        tp = (stock / "modules/attention_fn/triton_paged.py").read_text().split("\n")
        kt, k8, cu = src["K"], src["K8"], src["CU"]

        # (b) model text
        for e in MODEL:
            if e not in model:
                fail(f"err_pfix.bend: model expression missing: {e!r}")
        print(
            f"err_pfix_diff: (b) {len(MODEL)} model expressions present in err_pfix.bend"
        )

        # (c) combine: transcription asserted against the text, B and the pair condition parsed from it
        if norm(func_body(kt, "chain_step")) != CHAIN_STEP:
            fail(
                f"chain_step is not the transcribed text: {norm(func_body(kt, 'chain_step'))!r}"
            )
        comb = func_body(kt, "pattn_chain_combine")
        for ln in COMBINE_LOOP:
            if count(comb, ln) != 1:
                fail(f"pattn_chain_combine: {count(comb, ln)} occurrences of {ln!r}")
        mb = re.search(
            r"const int B0 = kr\[0\] > (\d+) \? kr\[0\] - (\d+) : (\d+), "
            r"B1 = kr\[1\] > (\d+) \? kr\[1\] - (\d+) : (\d+);",
            norm(comb),
        )
        if not mb or mb.groups()[:3] != mb.groups()[3:]:
            fail(
                "pattn_chain_combine: per-row B not of the form B_r = kr[r] > a ? kr[r] - b : c (same a, b, c)"
            )
        ba, bb, bc = (int(x) for x in mb.groups()[:3])
        mp = re.search(
            r"if \(c \+ (\d+) < B\) \{ const float pr = f_fma",
            norm(func_body(kt, "chain_step")),
        )
        if not mp:
            fail("chain_step: pair condition not of the form c + a < B")
        pa = int(mp.group(1))
        b_of = lambda n: n - bb if n > ba else bc
        maxch = int(re.findall(r"#define PA_MAXCH (\d+)", kt)[0])
        for K, want in CHAIN_TABLE.items():
            model_row = [chain_c(k, K) for k in range(K)]
            if model_row != want:
                fail(f"chain_c(., {K}) = {model_row}, table {want}")
        for K in range(1, maxch + 1):
            for nch in range(max(K, 2), maxch + 1):
                kern = combine_counts(nch, K, b_of, pa)
                got = [kern[k] for k in range(K)]
                want = [1] if K == 1 else [chain_c(k, K) for k in range(K)]
                if got != want:
                    fail(
                        f"combine of a row with K = {K} own chains in nch = {nch}: kernel roundings {got}, "
                        f"model chain_c {want}"
                    )
        sm = re.search(r"const float sum = (f_add\(.*?\));", kt, re.S)
        if not sm:
            fail(
                "tile sum `const float sum = f_add(...)` not found in pattn_kernel.cuh"
            )
        depth, leaves = add_depth(norm(sm.group(1)))
        want_leaves = [
            f"sc[{nt}][2 * r{' + 1' if e else ''}]" for nt in range(4) for e in range(2)
        ]
        if sorted(leaves) != sorted(want_leaves) or depth != 3:
            fail(
                f"tile sum: depth {depth} over {leaves} (want a depth-3 tree over the thread's 8 p, den_in = 3 + 2)"
            )
        print(
            f"err_pfix_diff: (c) a row with K = 2 .. {maxch} own chains in a combine of nch = K .. {maxch} chains: "
            f"chain k passes chain_c(k, K) roundings, chains K .. nch - 1 exact (B_r = kr[r] > {ba} ? kr[r] - {bb} "
            f": {bc}); K = 1: x_0 * w_0 only, w_0 = ex2(0) = 1 (exact); tile sum depth 3 + 2 quad levels = den_in 5"
        )

        # (e) stock citations
        for n, e in TP_CITES:
            if not 1 <= n <= len(tp) or e not in tp[n - 1]:
                got = tp[n - 1].strip() if 1 <= n <= len(tp) else "<none>"
                fail(f"TP:{n}: expected {e!r}, found {got!r}")
        print(
            f"err_pfix_diff: (e) {len(TP_CITES)} stock triton_paged.py citations hold"
        )

        # (d) chain plan replay over the extracted C formulas
        defs = {
            k: int(v)
            for k, v in re.findall(r"#define (PA_BQ|PA_BN|PA_MAXCH) (\d+)\b", kt)
        }
        if sorted(defs) != ["PA_BN", "PA_BQ", "PA_MAXCH"]:
            fail(f"defines not found: {defs}")
        e_ch, e_nhi, e_nt, e_nch = (
            c_expr(kt, n) for n in ("ch_tiles", "n_hi", "ntiles", "nch")
        )
        e_nt8 = c_expr(k8, "ntiles")
        if e_nt8 != f"p0 < q_len ? {e_nt} : 0":
            fail(f"pattn8 ntiles {e_nt8!r} is not pattn's {e_nt!r} for active warps")
        if (
            c_expr(k8, "ch_tiles") != e_ch
            or c_expr(k8, "nch") != e_nch
            or c_expr(k8, "n_hi") != e_nhi
        ):
            fail("pattn8 chain formulas differ from pattn's")
        ret = norm(func_body(kt, "row_chains"))
        mr = re.fullmatch(r"\{ return (.+); \}", ret)
        if not mr:
            fail(f"row_chains body {ret!r}")
        e_rc = mr.group(1)
        mk = re.search(r"const int kr\[2\] = \{(.+?)\};", norm(kt))
        if not mk:
            fail("call site: `const int kr[2] = {..}` not found")
        depth, parts, cur = 0, [], ""
        for ch in mk.group(1):
            depth += {"(": 1, ")": -1}.get(ch, 0)
            if ch == "," and depth == 0:
                parts.append(cur.strip())
                cur = ""
            else:
                cur += ch
        parts.append(cur.strip())
        if (
            len(parts) != 2
            or parts[1] != parts[0].replace("q_abs_r0", "q_abs_r1")
            or "q_abs_r0" not in parts[0]
        ):
            fail(
                f"call site: kr = {{{mk.group(1)}}} is not {{f(q_abs_r0), f(q_abs_r1)}} of the thread's two rows"
            )
        e_kr0, e_kr1 = parts
        if (
            norm(kt).count(
                "const int q_abs_r0 = q_abs0 + gid, q_abs_r1 = q_abs0 + gid + 8;"
            )
            != 1
        ):
            fail("rows of the thread are not q_abs0 + gid, q_abs0 + gid + 8")

        def row_chains(q_abs: int, ch_tiles: int, nch: int) -> int:
            return c_eval(
                e_rc, {"q_abs": q_abs, "ch_tiles": ch_tiles, "nch": nch, **defs}
            )

        q64s = (
            list(range(4097))
            + list(range(4097, 262145, 251))
            + [x + d for x in range(8192, 262145, 8192) for d in (-1, 0, 1)]
        )
        rows = straddle = 0
        counts: dict[tuple[int, int], list[int]] = {}
        witness = None
        for q64 in q64s:
            E = c_eval(e_ch, {"q_abs64": q64})
            if E != -(-(q64 + 1) // 256) or E != (q64 + 256) // 256:
                fail(
                    f"q64 = {q64}: ch_tiles = {E}, want cdiv(q64 + 1, 256) = e_len(q64)"
                )
            for j in range(4):
                qa = q64 + 16 * j
                for total in range(qa + 1, qa + defs["PA_BQ"] + 1):
                    env = {"q_abs0": qa, "total": total, **defs}
                    nhi = c_eval(e_nhi, env)
                    nt = c_eval(e_nt, {"n_hi": nhi, **defs})
                    nch = c_eval(e_nch, {"ntiles": nt, "ch_tiles": E})
                    if nch > defs["PA_MAXCH"]:
                        fail(
                            f"q64 = {q64}, warp {j}, total {total}: nch = {nch} > PA_MAXCH"
                        )
                    for p in range(qa, nhi):
                        rows += 1
                        n = p // 32 + 1
                        K = -(-n // E)
                        renv = {
                            "q_abs_r0": p,
                            "q_abs_r1": p,
                            "ch_tiles": E,
                            "nch": nch,
                            "row_chains": row_chains,
                        }
                        kr = c_eval(e_kr0 if p - qa < 8 else e_kr1, renv)
                        if n > nt or kr != K:
                            fail(
                                f"q64 = {q64}, warp {j}, total {total}, row {p}: {n} tiles, model K = {K}, "
                                f"kernel kr = {kr} (warp: {nt} tiles, nch = {nch})"
                            )
                        if nch < 2:
                            continue
                        if K < nch:
                            straddle += 1
                        if (nch, K) not in counts:
                            kern = combine_counts(nch, K, b_of, pa)
                            counts[(nch, K)] = [kern[k] for k in range(K)]
                            want = [1] if K == 1 else [chain_c(k, K) for k in range(K)]
                            if counts[(nch, K)] != want:
                                fail(
                                    f"q64 = {q64}, warp {j}, total {total}, row {p}: K = {K}, nch = {nch}: kernel "
                                    f"roundings {counts[(nch, K)]}, model chain_c {want}"
                                )
                        if (q64, total, p) == (65, 129, 113):
                            witness = (j, n, K, nch, counts[(nch, K)])
        if witness is None:
            fail("witness row q64 = 65, total = 129, p = 113 not replayed")
        j, n, K, nch, got = witness
        print(
            f"err_pfix_diff: (d) {len(q64s)} block starts, {rows} rows: E = cdiv(q64 + 1, 256), nch <= "
            f"{defs['PA_MAXCH']}, every row's kr = model K, combine roundings = chain_c(k, K) "
            f"({straddle} rows with K < nch, {len(counts)} (nch, K) pairs); witness q64 = 65, total = 129, row 113 "
            f"(warp {j}): n = {n}, K = {K}, nch = {nch}, roundings {got}"
        )

        # (a) kernel text
        for ln in WARP_LINES:
            for name, t in (("pattn_kernel.cuh", kt), ("pattn8_kernel.cuh", k8)):
                if count(t, ln) != 1:
                    fail(f"{name}: {count(t, ln)} occurrences of {ln!r} (want 1)")
        for ln in HELPER_LINES:
            if count(kt, ln) != 1:
                fail(
                    f"pattn_kernel.cuh: {count(kt, ln)} occurrences of {ln!r} (want 1)"
                )
            if count(k8, ln):
                fail(f"pattn8_kernel.cuh redefines {ln!r}")
        for fn in ("park_chain", "chain_w", "chain_step", "pattn_chain_combine"):
            if re.search(r"\b" + fn + r"\(\s*(float4|const|int)", k8):
                fail(f"pattn8_kernel.cuh defines its own {fn}")
        if count(k8, '#include "pattn_kernel.cuh"') != 1:
            fail("pattn8_kernel.cuh does not include pattn_kernel.cuh")
        park = norm(WARP_LINES[1])
        if norm(k8).count("if (act) { " + park) != 1:
            fail(
                "pattn8_kernel.cuh: the park line is not the first statement of `if (act)`"
            )
        body = func_body(kt, "park_chain")
        if count(body, "for (int j = 0; j < 32; ++j)") != 1:
            fail("park_chain does not store acc[0 .. 31]")
        for ln in CU_LINES:
            if count(cu, ln) != 1:
                fail(f"pattn.cu: {count(cu, ln)} occurrences of {ln!r}")
        if count(cu, "n_q_heads, n_kv_heads, scale_log2, pk);") != 2:
            fail("pattn.cu: the scratch is not passed to both launches")
        print(
            f"err_pfix_diff: (a) {len(WARP_LINES)} per-warp lines once in pattn and pattn8, {len(HELPER_LINES)} helper "
            f"lines once in pattn_kernel.cuh, pattn8 parks inside `if (act)`, pattn.cu passes park and checks "
            f"one CTA per SM"
        )
    print("err_pfix_diff: OK")


if __name__ == "__main__":
    main(sys.argv)
