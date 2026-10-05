#!/usr/bin/env python3
# Copyright (c) 2026 Gil Rodrigues
"""Source link of bend/rowinv_served.bend grid_S to the patch series.

grid_S is the 3006 split grid, H_grid of rowinv_served_laws.bend. Replaying every
patch of patches/exl3-ext/series (sha256-checked) on modules/attention_fn/bc_attn.py,
the live `av_splits = ...` assignments of the patched file are exactly
`av_splits = 0` (the ineligible default) and
`av_splits = max(1, _get_sm_count(dev) // kvh)`, the latter added by
3006-attn-verify-stride.patch at patch line 738 and not touched by any later patch;
the Bend transcription is `Nat.max(1n, Nat.div(sms, kvh))` and agrees with the
Python expression (evaluated from the patch text) on a grid of SM / kv-head counts.
Text and sample evidence, not a proof. `--mutate NAME` applies a deliberate mutation
that must be rejected.

Usage: python3 bend/rinv_grid_diff.py [--mutate NAME]
"""

from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path
from typing import TYPE_CHECKING, NoReturn

sys.path.insert(0, str(Path(__file__).resolve().parent))
import pysubset

if TYPE_CHECKING:
    from collections.abc import Callable

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
MUTATE_ARGC = 2
SMS_END = 257
KVH_END = 33

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


def fail(msg: str) -> NoReturn:
    """Stop with a FAIL message.

    Args:
        msg: The failure description.

    Raises:
        SystemExit: Always.

    """
    text = f"rinv_grid_diff: FAIL: {msg}"
    raise SystemExit(text)


def bend_grid(sms: int, kvh: int) -> int:
    """Return grid_S as Bend computes it.

    Base Nat.div(a, 0) is 0 (divmod by 0); Nat.max(1n, x).

    Args:
        sms: The SM count.
        kvh: The kv-head count.

    Returns:
        The split count.

    """
    return max(1, sms // kvh if kvh else 0)


def sm_count_of(sms: int) -> Callable[[object], int]:
    """Return a `_get_sm_count` stand-in that reports `sms` SMs.

    Args:
        sms: The SM count to report.

    Returns:
        The stand-in function.

    """

    def get_sm_count(_dev: object) -> int:
        return sms

    return get_sm_count


def parse_mutation(args: list[str]) -> str | None:
    """Return the `--mutate` name of the arguments, if any.

    Args:
        args: The command-line arguments after the program name.

    Returns:
        The mutation name, or None.

    """
    mutate = None
    if len(args) == MUTATE_ARGC and args[0] == "--mutate":
        mutate = args[1]
    elif args:
        fail("usage: rinv_grid_diff.py [--mutate NAME]")
    if mutate is not None and mutate not in MUTATIONS:
        fail(f"unknown mutation {mutate!r}")
    return mutate


def read_series() -> list[tuple[str, str]]:
    """Return the sha256-checked patches of the series, in order.

    Returns:
        (name, text) pairs.

    """
    series: list[tuple[str, str]] = []
    for line in (PATCHES / "series").read_text().splitlines():
        if not line.strip():
            continue
        digest, name = line.split()
        text = (PATCHES / name).read_bytes()
        if hashlib.sha256(text).hexdigest() != digest:
            fail(f"{name}: sha256 differs from series")
        series.append((name, text.decode()))
    return series


def apply_mutation(
    mutate: str, series: list[tuple[str, str]], model: str
) -> tuple[list[tuple[str, str]], str]:
    """Apply a mutation to the series or the model.

    Args:
        mutate: The mutation name.
        series: (name, text) pairs of the patch series.
        model: The Bend model text.

    Returns:
        The mutated series and model.

    """
    kind, old, new = MUTATIONS[mutate]
    if kind == "patch":
        series = [(n, t.replace(old, new) if n == SRC_PATCH else t) for n, t in series]
        if not any(new in t for _, t in series):
            fail(f"mutation anchor {old!r}")
    else:
        if old not in model:
            fail(f"mutation anchor {old!r}")
        model = model.replace(old, new)
    sys.stdout.write(f"rinv_grid_diff: applied mutation {mutate}\n")
    return series, model


def live_assignments(series: list[tuple[str, str]]) -> dict[str, tuple[str, int]]:
    """Replay the series' `av_splits = ...` lines on TARGET.

    Args:
        series: (name, text) pairs of the patch series.

    Returns:
        The live assignments, each with the patch and line that added it.

    """
    live: dict[str, tuple[str, int]] = {}
    for name, text in series:
        cur = None
        for no, line in enumerate(text.split("\n"), 1):
            if line.startswith("+++ "):
                cur = line[4:].strip()
                cur = cur.removeprefix("b/")
                continue
            if (
                line.startswith("--- ")
                or cur != TARGET
                or line[:1] not in "+-"
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
    return live


def check_grid() -> None:
    """Compare the patch expression with bend_grid on the sample grid."""
    rhs = EXPR.split("=", 1)[1].strip()
    grid = pysubset.compile_expr(rhs)
    for sms in range(SMS_END):
        get_sm_count = sm_count_of(sms)
        for kvh in range(1, KVH_END):
            got = grid({
                "max": max,
                "_get_sm_count": get_sm_count,
                "dev": 0,
                "kvh": kvh,
            })
            if got != bend_grid(sms, kvh):
                fail(f"sms {sms} kvh {kvh}: python {got}, bend {bend_grid(sms, kvh)}")


def main(argv: list[str]) -> None:
    """Run the source link.

    Args:
        argv: The command line, program name first.

    """
    mutate = parse_mutation(argv[1:])
    series = read_series()
    model = MODEL.read_text()
    if mutate is not None:
        series, model = apply_mutation(mutate, series, model)
    live = live_assignments(series)
    if set(live) != {EXPR, DEFAULT}:
        fail(f"live av_splits assignments after the series: {sorted(live)}")
    if live[EXPR] != (SRC_PATCH, SRC_LINE):
        fail(f"{EXPR!r} comes from {live[EXPR]}, not {SRC_PATCH}:{SRC_LINE}")
    if model.count(BEND_DEF) != 1:
        fail("rowinv_served.bend: grid_S is not `Nat.max(1n, Nat.div(sms, kvh))`")
    if BEND_CITE not in model:
        fail(f"rowinv_served.bend does not cite {BEND_CITE}")
    check_grid()
    sys.stdout.write(
        f"rinv_grid_diff: {len(series)} patches replayed on {TARGET}; {EXPR!r} "
        f"from {SRC_PATCH}:{SRC_LINE} is live and final\n"
    )
    sys.stdout.write(
        "rinv_grid_diff: grid_S transcription agrees on sms 0..256, kvh 1..32\n"
    )
    sys.stdout.write("rinv_grid_diff: OK\n")


if __name__ == "__main__":
    main(sys.argv)
