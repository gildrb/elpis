#!/usr/bin/env python3
"""
Finite source link of bend/kv_compact.bend (ext 3013 tree-verify KV commit) to the patched engine text: the move
derivation (cache/kv_compact.py kv_moves), the kernel's read-all-then-write loops and the extension's host checks
(exllamav3_ext/kv_compact.cu) occur verbatim, the read loop precedes the write loop, and the path validation kv_moves
applies (P[0] == 0, strictly increasing, rows < 8) is the domain the Bend law enumerates. Text evidence, not a proof.
`--mutate NAME` applies a deliberate source mutation that must be rejected.

Usage: python3 bend/kv_compact_diff.py [--mutate NAME] ENGINE_PACKAGE_DIR
"""
from __future__ import annotations

import sys
from pathlib import Path

CU = [
    "if (i < batch.num_moves) row[i] = set.base[batch.src[i] * set.units + u];",
    "if (i < batch.num_moves) set.base[batch.dst[i] * set.units + u] = row[i];",
    'TORCH_CHECK(s != d, "kv_compact_rows: move ", i, " copies token ", s, " onto itself");',
    'TORCH_CHECK(batch.dst[k] != d, "kv_compact_rows: moves ", k, " and ", i, " share destination ", d);',
    'TORCH_CHECK(batch.dst[k] != s, "kv_compact_rows: move ", i, " reads token ", s, ", the destination of earlier move ", k);',
    "for (int k = 0; k < i; ++k)",
]
PY = [
    "return [(phys(base + rows[j]), phys(base + j)) for j in range(1, count) if rows[j] != j]",
    "if rows[0] != 0:",
    "if any(rows[j] <= rows[j - 1] for j in range(1, count)):",
    "if rows[-1] >= KV_COMPACT_ROWS:",
    "if len(set(pages)) != len(pages):",
    "KV_COMPACT_ROWS = 8",
]
MUTATIONS = {
    "swap": ("return [(phys(base + rows[j]), phys(base + j))", "return [(phys(base + j), phys(base + rows[j]))"),
    "write_first": ("if (i < batch.num_moves) row[i] = set.base[batch.src[i] * set.units + u];",
                    "if (i < batch.num_moves) row[i] = set.base[batch.src[i] * set.units + u]; set.base[batch.dst[i] * set.units + u] = row[i];"),
}


def fail(msg: str) -> None:
    raise SystemExit(f"kv_compact_diff: FAIL: {msg}")


def main(argv: list[str]) -> None:
    args = argv[1:]
    mutate = None
    if len(args) == 3 and args[0] == "--mutate":
        mutate, args = args[1], args[2:]
    if len(args) != 1:
        fail("usage: kv_compact_diff.py [--mutate NAME] ENGINE_PACKAGE_DIR")
    root = Path(args[0])
    cu = (root / "exllamav3_ext/kv_compact.cu").read_text()
    py = (root / "cache/kv_compact.py").read_text()
    if mutate is not None:
        old, new = MUTATIONS[mutate]
        if old in py:
            py = py.replace(old, new)
        elif old in cu:
            cu = cu.replace(old, new)
        else:
            fail(f"mutation anchor {old!r}")
        print(f"kv_compact_diff: applied mutation {mutate}")
    lines = [x.strip() for x in cu.split("\n")]
    for e in CU:
        if lines.count(e) != 1:
            fail(f"kv_compact.cu: {e!r} is a whole line {lines.count(e)} times (want 1)")
    between = [x for x in lines[lines.index(CU[0]) + 1:lines.index(CU[1])] if x]
    if between != ["#pragma unroll", "for (int i = 0; i < KV_COMPACT_MAX_MOVES; ++i)"]:
        fail(f"kv_compact.cu: between the read and the write loop: {between!r}")
    for e in PY:
        if py.count(e) != 1:
            fail(f"kv_compact.py: {e!r} occurs {py.count(e)} times (want 1)")
    if not cu.index(CU[0]) < cu.index(CU[1]):
        fail("kv_compact.cu: the read loop must precede the write loop")
    print(f"kv_compact_diff: {len(CU) + len(PY)} expressions found once each; reads precede writes")
    print("kv_compact_diff: OK")


if __name__ == "__main__":
    main(sys.argv)
