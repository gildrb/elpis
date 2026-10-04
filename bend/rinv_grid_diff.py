#!/usr/bin/env python3
"""
Source link of bend/rowinv_served.bend grid_S (the 3006 split grid, H_grid of rowinv_served_laws.bend) to the
patch series: replaying every patch of patches/exl3-ext/series (sha256-checked) on modules/attention_fn/bc_attn.py,
the live `av_splits = ...` assignments of the patched file are exactly `av_splits = 0` (the ineligible default) and
`av_splits = max(1, _get_sm_count(dev) // kvh)`, the latter added by 3006-attn-verify-stride.patch at patch line 738
and not touched by any later patch; the Bend transcription is `Nat.max(1n, Nat.div(sms, kvh))` and agrees with the
Python expression (evaluated from the patch text) on a grid of SM / kv-head counts. Text and sample evidence, not a
proof. `--mutate NAME` applies a deliberate mutation that must be rejected.

Usage: python3 bend/rinv_grid_diff.py [--mutate NAME]
"""

from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
PATCHES = REPO / "patches" / "exl3-ext"
MODEL = REPO / "bend" / "rowinv_served.bend"
TARGET = "modules/attention_fn/bc_attn.py"
SRC_PATCH = "3006-attn-verify-stride.patch"
SRC_LINE = 738
EXPR = "av_splits = max(1, _get_sm_count(dev) // kvh)"
DEFAULT = "av_splits = 0"
BEND_DEF = (
    "def grid_S(+sms: Nat, +kvh: Nat) -> Nat:\n  Nat.max(1n, Nat.div(sms, kvh))\n"
)
BEND_CITE = "3006-attn-verify-stride.patch:738"
ASSIGN = re.compile(r"^\s*av_splits\s*=")

# name: (file kind, original, replacement)
MUTATIONS = {
    "bsz": (
        "patch",
        "+            av_splits = max(1, _get_sm_count(dev) // kvh)",
        "+            av_splits = max(1, _get_sm_count(dev) // (bsz * kvh))",
    ),
    "floor0": (
        "patch",
        "+            av_splits = max(1, _get_sm_count(dev) // kvh)",
        "+            av_splits = max(0, _get_sm_count(dev) // kvh)",
    ),
    "bend_div": (
        "bend",
        "  Nat.max(1n, Nat.div(sms, kvh))",
        "  Nat.max(1n, Nat.div(sms, 1n))",
    ),
}


def fail(msg: str) -> None:
    raise SystemExit(f"rinv_grid_diff: FAIL: {msg}")


def bend_grid(sms: int, kvh: int) -> int:
    # Base Nat.div(a, 0) is 0 (divmod by 0); Nat.max(1n, x)
    return max(1, sms // kvh if kvh else 0)


def main(argv: list[str]) -> None:
    args = argv[1:]
    mutate = None
    if len(args) == 2 and args[0] == "--mutate":
        mutate = args[1]
    elif args:
        fail("usage: rinv_grid_diff.py [--mutate NAME]")
    if mutate is not None and mutate not in MUTATIONS:
        fail(f"unknown mutation {mutate!r}")
    series = []
    for line in (PATCHES / "series").read_text().splitlines():
        if not line.strip():
            continue
        digest, name = line.split()
        text = (PATCHES / name).read_bytes()
        if hashlib.sha256(text).hexdigest() != digest:
            fail(f"{name}: sha256 differs from series")
        series.append((name, text.decode()))
    model = MODEL.read_text()
    if mutate is not None:
        kind, old, new = MUTATIONS[mutate]
        if kind == "patch":
            series = [
                (n, t.replace(old, new) if n == SRC_PATCH else t) for n, t in series
            ]
            if not any(new in t for _, t in series):
                fail(f"mutation anchor {old!r}")
        else:
            if old not in model:
                fail(f"mutation anchor {old!r}")
            model = model.replace(old, new)
        print(f"rinv_grid_diff: applied mutation {mutate}")
    live: dict[str, tuple[str, int]] = {}
    for name, text in series:
        cur = None
        for no, line in enumerate(text.split("\n"), 1):
            if line.startswith("+++ "):
                cur = line[4:].strip()
                cur = cur[2:] if cur.startswith("b/") else cur
                continue
            if (
                line.startswith("--- ")
                or cur != TARGET
                or not line[:1] in "+-"
                or not ASSIGN.match(line[1:])
            ):
                continue
            stmt = line[1:].strip()
            if line[0] == "-":
                if stmt not in live:
                    fail(f"{name}:{no} removes {stmt!r}, which is not live")
                del live[stmt]
            else:
                if stmt in live:
                    fail(f"{name}:{no} re-adds live {stmt!r}")
                live[stmt] = (name, no)
    if set(live) != {EXPR, DEFAULT}:
        fail(f"live av_splits assignments after the series: {sorted(live)}")
    if live[EXPR] != (SRC_PATCH, SRC_LINE):
        fail(f"{EXPR!r} comes from {live[EXPR]}, not {SRC_PATCH}:{SRC_LINE}")
    if model.count(BEND_DEF) != 1:
        fail("rowinv_served.bend: grid_S is not `Nat.max(1n, Nat.div(sms, kvh))`")
    if BEND_CITE not in model:
        fail(f"rowinv_served.bend does not cite {BEND_CITE}")
    rhs = EXPR.split("=", 1)[1].strip()
    for sms in range(0, 257):
        for kvh in range(1, 33):
            got = eval(
                rhs,
                {"max": max, "_get_sm_count": lambda _dev, s=sms: s},
                {"dev": 0, "kvh": kvh},
            )
            if got != bend_grid(sms, kvh):
                fail(f"sms {sms} kvh {kvh}: python {got}, bend {bend_grid(sms, kvh)}")
    print(
        f"rinv_grid_diff: {len(series)} patches replayed on {TARGET}; {EXPR!r} from {SRC_PATCH}:{SRC_LINE} is live and final"
    )
    print("rinv_grid_diff: grid_S transcription agrees on sms 0..256, kvh 1..32")
    print("rinv_grid_diff: OK")


if __name__ == "__main__":
    main(sys.argv)
