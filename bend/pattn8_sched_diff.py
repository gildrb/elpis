#!/usr/bin/env python3
"""
Finite source link of bend/pattn8_sched.bend (ext 3020 8-warp prefill attention) to the patched engine text.

Argument: the patched exllamav3 package directory (the one holding exllamav3_ext/pattn8_kernel.cuh,
exllamav3_ext/pattn_kernel.cuh and exllamav3_ext/pattn.cu). Checks, failing closed:
  1. every index expression the Bend model transcribes occurs verbatim exactly once in pattn8_kernel.cuh (or
     pattn.cu for the host grid), and the 3010 constants the model uses are the ones in pattn_kernel.cuh;
  2. the per-warp arithmetic is 3010's text: after dropping comments, blank lines and indentation, and the
     structural differences the Bend laws cover (3020's `if (act) { ... }` wrappers, and `uint32_t pa[2][4];` /
     `const int hq = ...;` / `float alpha[2]` declared at a different place: 3010 declares alpha per tile inside the
     QK segment, 3020 once before the tile loop as `float alpha[2] = {1.f, 1.f};`; both assign alpha[r] for both
     rows in the compared QK segment before the P V of the same tile reads it), these segments are token-for-token
     equal in both kernels: QK^T + mask + online softmax + P packing (one tile), P V (one tile), the epilogue (ext
     3031 chain combine, l reduction, 1 / l, store), the q staging store of the prologue (ext 3022: q is staged
     unscaled, the scale is applied to the fp32 scores inside the QK segment), the accumulator / m / l
     initialisation and the per-thread row bounds;
  3. the tile issue lambda is 3010's with PA_THREADS -> P8_THREADS;
  4. ext 3031 chain parking: 3010 parks as the first statement of a tile, 3020 as the first statement of the tile's
     `if (act)` (a warp parks only at its own tiles), with the same text;
  5. the host runs mode 0 only (ext 3022 removed the f16-accumulating mode 1): it rejects mode != 0 before any
     launch, and launches pattn8_kernel<false> (EXL3_PATTN8 on) or pattn_kernel<false>, never an F16 = true kernel.
Text evidence, not a proof: it ties the Bend model to one source revision. `--mutate NAME` applies a deliberate
source mutation that must be rejected.

Usage: python3 bend/pattn8_sched_diff.py [--mutate NAME] ENGINE_PACKAGE_DIR
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

MODEL_EXPRS_K8 = [
    "#define P8_NW 8",
    "#define P8_NB 4",
    "#define P8_NH 2",
    "#define P8_PAIRS (PA_G / P8_NH)",
    "#define P8_THREADS (P8_NW * 32)",
    "const int kvh = blockIdx.x / P8_PAIRS, pair = blockIdx.x % P8_PAIRS;",
    "const int qc = gridDim.y - 1 - blockIdx.y;",
    "const int wb = warp % P8_NB, wh = warp / P8_NB;",
    "const int c0 = qc * P8_NB * PA_BQ;",
    "const int n_hi_cta = min(total - q_len + c0 + P8_NB * PA_BQ, total);",
    "const int ntiles_cta = (n_hi_cta + PA_BN - 1) / PA_BN;",
    "const int p0 = c0 + wb * PA_BQ;",
    "const int hq = kvh * PA_G + pair * P8_NH + wh;",
    "const int q_abs0 = total - q_len + p0;",
    "const int n_hi = min(q_abs0 + PA_BQ, total);",
    "const int ntiles = p0 < q_len ? (n_hi + PA_BN - 1) / PA_BN : 0;",
    "for (int it = 0; it < ntiles_cta; ++it)",
    "const bool act = it < ntiles;",
    "if (n0 + PA_BN - 1 > q_abs0)",
    "for (int c = tid; c < P8_NW * PA_BQ * 32; c += P8_THREADS)",
    "int row = c >> 5, ch = c & 31, w = row / PA_BQ, pos = row - w * PA_BQ;",
    "int p = c0 + (w % P8_NB) * PA_BQ + pos, h = kvh * PA_G + pair * P8_NH + w / P8_NB;",
    "const int qrow = warp * PA_BQ;",
    "if (ntiles == 0) return;",
    "int pos = p0 + gid + 8 * r;",
    "for (int i = 0; i < (PA_BN * 32 + P8_THREADS - 1) / P8_THREADS; ++i)",
    "int c = tid + i * P8_THREADS;",
]
MODEL_EXPRS_K6 = ["#define PA_G 6", "#define PA_BQ 16", "#define PA_BN 32", "#define PA_PAGE 256", "#define PA_NW 6"]
MODEL_EXPRS_HOST = [
    "const int nqc = (q_len + P8_NB * PA_BQ - 1) / (P8_NB * PA_BQ);",
    "dim3 grid(n_kv_heads * P8_PAIRS, nqc, bsz);",
]

MUTATIONS = {
    # act admits one iteration past the warp's own tiles
    "act_le": ("const bool act = it < ntiles;", "const bool act = it <= ntiles;"),
    # PV MMA k-halves in the opposite order (different fp32 accumulation order)
    "pv_order": ("mma_f32(tp, pa[0], bv[0][2 * hn], bv[0][2 * hn + 1]);\n                        mma_f32(tp, pa[1], bv[1][2 * hn], bv[1][2 * hn + 1]);",
                 "mma_f32(tp, pa[1], bv[1][2 * hn], bv[1][2 * hn + 1]);\n                        mma_f32(tp, pa[0], bv[0][2 * hn], bv[0][2 * hn + 1]);"),
    # softmax tile sum (ext 3031 tree) with the first pair's operands swapped
    "sum_order": ("f_add(f_add(f_add(sc[0][2 * r], sc[0][2 * r + 1]),", "f_add(f_add(f_add(sc[0][2 * r + 1], sc[0][2 * r]),"),
    # ext 3031: park every tile boundary, also for tiles past the warp's own (outside `if (act)`)
    "park_outside_act": ("        if (act)\n        {\n            if (it > 0 && it % ch_tiles == 0) park_chain(",
                         "        if (it > 0 && it % ch_tiles == 0) park_chain(park, slot, 0, warp, lane, acc, m, l);\n"
                         "        if (act)\n        {\n            if (it > 0 && it % ch_tiles == 0) park_chain("),
    # q head pair stride 3 instead of 2
    "head_map": ("const int hq = kvh * PA_G + pair * P8_NH + wh;", "const int hq = kvh * PA_G + pair * 3 + wh;"),
}


def fail(msg: str) -> None:
    raise SystemExit(f"pattn8_sched_diff: FAIL: {msg}")


def norm(text: str) -> list[str]:
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
    j = text.find(end, i)
    if j < 0:
        fail(f"{what}: end anchor {end!r} not found after start")
    return text[i:j]


def once(text: str, expr: str, where: str) -> None:
    n = text.count(expr)
    if n != 1:
        fail(f"{where}: {expr!r} occurs {n} times (want 1)")


def drop(lines: list[str], unwanted: list[str]) -> list[str]:
    return [line for line in lines if line not in unwanted]


def unwrap_act(lines: list[str], what: str) -> list[str]:
    # 3020 wraps the segment in `if (act) { ... }`: exactly one leading `if (act)`, `{` and one trailing `}`
    if lines[:2] != ["if (act)", "{"] or lines[-1] != "}":
        fail(f"{what}: 3020 segment is not wrapped in if (act) {{ ... }}")
    return lines[2:-1]


def compare(a: list[str], b: list[str], what: str) -> None:
    if a != b:
        for k, (x, y) in enumerate(zip(a, b)):
            if x != y:
                fail(f"{what}: line {k}: 3010 {x!r} != 3020 {y!r}")
        fail(f"{what}: lengths differ ({len(a)} vs {len(b)})")
    print(f"pattn8_sched_diff: {what}: {len(a)} normalized lines equal")


def main(argv: list[str]) -> None:
    mutate = None
    args = argv[1:]
    if len(args) == 3 and args[0] == "--mutate":
        mutate = args[1]
        args = args[2:]
    if len(args) != 1:
        fail(__doc__.strip().split("\n")[-1])
    root = Path(args[0])
    k6 = (root / "exllamav3_ext/pattn_kernel.cuh").read_text()
    k8 = (root / "exllamav3_ext/pattn8_kernel.cuh").read_text()
    host = (root / "exllamav3_ext/pattn.cu").read_text()
    if mutate is not None:
        if mutate not in MUTATIONS:
            fail(f"unknown mutation {mutate!r}")
        old, new = MUTATIONS[mutate]
        once(k8, old, "mutation anchor")
        k8 = k8.replace(old, new, 1)
        print(f"pattn8_sched_diff: applied mutation {mutate}")

    # 1. transcribed expressions
    for e in MODEL_EXPRS_K8:
        once(k8, e, "pattn8_kernel.cuh")
    for e in MODEL_EXPRS_K6:
        once(k6, e, "pattn_kernel.cuh")
    for e in MODEL_EXPRS_HOST:
        once(host, e, "pattn.cu")
    print(f"pattn8_sched_diff: {len(MODEL_EXPRS_K8) + len(MODEL_EXPRS_K6) + len(MODEL_EXPRS_HOST)} transcribed expressions found once each")

    # 2. per-warp arithmetic
    qk6 = drop(norm(seg(k6, "// S = Q K^T (raw fp32 sums)", "cp_wait0();", "3010 QK")), ["uint32_t pa[2][4];", "float alpha[2];"])
    qk8 = unwrap_act(["if (act)", "{"] + norm(seg(k8, "// S = Q K^T (raw fp32 sums)", "cp_wait0();", "3020 QK")), "QK")
    compare(qk6, qk8, "QK^T + mask + online softmax + P pack")
    if qk8.count("alpha[r] = is_ninf(m[r]) ? 0.f : ex2(f_sub(m[r], m_use));") != 1 or "for (int r = 0; r < 2; ++r)" not in qk8:
        fail("QK: alpha[r] is not assigned for both rows in the compared segment")
    pv6 = norm(seg(k6, "// O += P V", 'asm volatile("cp.async.wait_group 1;\\n" ::);   // K(it + 1)', "3010 PV"))
    pv8 = unwrap_act(["if (act)", "{"] + norm(seg(k8, "// O += P V", 'asm volatile("cp.async.wait_group 1;\\n" ::);   // K(it + 1)', "3020 PV")), "PV")
    compare(pv6, pv8, "P V")
    comb = "// Ext 3031: more than one chain: stock's split combine of the parked chains and the live one"
    ep6 = drop(norm(seg(k6, comb, "} // namespace pattn_detail", "3010 epilogue")), ["const int hq = kvh * PA_G + warp;"])
    ep8 = norm(seg(k8, comb, "} // namespace pattn_detail", "3020 epilogue"))
    compare(ep6, ep8, "epilogue (chain combine, l reduction, 1 / l, store)")
    st = "*reinterpret_cast<uint4*>(qs + swz(row, ch * 8)) = u;"
    sc6 = norm(seg(k6, st, "float acc[32][4];", "3010 q store"))
    sc8 = norm(seg(k8, st, "float acc[32][4];", "3020 q store"))
    compare(sc6, sc8, "q staging store (unscaled)")
    in6 = norm(seg(k6, "float acc[32][4];", "#pragma unroll 1", "3010 init"))
    in8 = drop(norm(seg(k8, "float acc[32][4];", "#pragma unroll 1", "3020 init")), ["uint32_t pa[2][4];", "float alpha[2] = {1.f, 1.f};"])
    compare(in6, in8, "accumulator / m / l init, qrow, row bounds")

    # 3. tile issue
    is6 = norm(seg(k6, "auto issue = [&]", "if (ntiles > 0) issue(k16, ks, 0);", "3010 issue").replace("PA_THREADS", "P8_THREADS"))
    is8 = norm(seg(k8, "auto issue = [&]", "if (ntiles_cta > 0) issue(k16, ks, 0);", "3020 issue"))
    compare(is6, is8, "tile issue (PA_THREADS -> P8_THREADS)")

    # 4. chain parking: first statement of the tile (3010) / of the tile's `if (act)` (3020)
    park = "if (it > 0 && it % ch_tiles == 0) park_chain(park, slot, it / ch_tiles - 1, warp, lane, acc, m, l);"
    n6, n8 = norm(k6), norm(k8)
    if n6.count(park) != 1 or n8.count(park) != 1 or k8.count("park_chain(") != 1:
        fail("park: the park line does not occur once in each kernel, or pattn8 calls park_chain elsewhere")
    i6, i8 = n6.index(park), n8.index(park)
    if n6[i6 - 1] != "const int n0 = it * PA_BN;" or n8[i8 - 2:i8] != ["if (act)", "{"] \
            or n6[i6 + 1] != "float sc[4][4];" or n8[i8 + 1] != "float sc[4][4];":
        fail("park: not the first statement of the tile (3010) / of the tile's if (act) (3020), right before QK")
    print("pattn8_sched_diff: park: 3010 parks first in the tile, 3020 first in the tile's if (act)")

    # 5. host dispatch: mode 0 only, F16 = false launches only
    pre = host[: host.find("if (pattn8_enabled())")]
    once(pre, 'TORCH_CHECK(mode == 0, "pattn: mode must be 0', "pattn.cu before the launches")
    d8 = norm(seg(host, "if (pattn8_enabled())", "cuda_check(cudaPeekAtLastError());\n}", "3020 host"))
    l8 = [x for x in d8 if "<<<" in x]
    if l8 != ["pattn_detail::pattn8_kernel<false><<<grid, P8_THREADS, P8_SMEM, stream>>>(",
              "pattn_detail::pattn_kernel<false><<<grid, PA_THREADS, PA_SMEM, stream>>>("]:
        fail(f"host: launches are {l8}, want pattn8_kernel<false> then pattn_kernel<false>")
    if "<true>" in host or "if (mode" in host:
        fail("host: an F16 = true instantiation or a mode branch is present")
    print("pattn8_sched_diff: host dispatch mode 0 only -> pattn8_kernel<false> (EXL3_PATTN8) else pattn_kernel<false>")
    print("pattn8_sched_diff: OK")


if __name__ == "__main__":
    main(sys.argv)
