#!/usr/bin/env python3
# Copyright (c) 2026 Gil Rodrigues
"""Cross-check the Bend precision table against the CPU-computed decode table.

The Bend table is bend/PRECISION_TABLE.bend; the decode table is partA.md (analyze_a.py
over the stock sources and the persisted autotune cache): per (op, m), the stock run
range / int8, and the elpis run range / "= stock".

    python3 bend/precision_diff.py [--parta PATH]

PATH: the partA.md decode table; the default is bend/gen/precision_parta.txt. The script
runs the `bend` on PATH (exactly bend 2.0.35, bend/source_link.py).

Prints one line per disagreement and exits 1 if any; lm_head's stock class is not
normalized by Bend (unary Nat), so only its elpis route (= stock) is compared.
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import source_link

HERE = Path(__file__).resolve().parent

PARTA_CELLS = 7
BEND_CELLS = 5

type Key = tuple[str, int]
type Row = tuple[str, str, str]


def parta_rows(path: str) -> dict[Key, Row]:
    """Parse the partA.md decode table.

    Args:
        path: The table file.

    Returns:
        (stock run, elpis kernel, elpis run) per (op, m).

    """
    rows: dict[Key, Row] = {}
    for line in Path(path).read_text(encoding="utf-8").splitlines():
        cells = [
            c.strip()
            for c in line.replace("(q|gate)", "(q/gate)").strip().strip("|").split("|")
        ]
        if len(cells) != PARTA_CELLS or not cells[1].isdigit():
            continue
        op, m, _kern, _cfg, stock_run, elpis_kern, elpis_run = cells
        rows[op, int(m)] = (stock_run, elpis_kern, elpis_run)
    return rows


def bend_rows(bend: str) -> dict[Key, Row]:
    """Evaluate bend/PRECISION_TABLE.bend and parse its rows.

    Args:
        bend: The `bend` executable.

    Returns:
        (stock class, elpis route, elpis class) per (op, m).

    """
    out = subprocess.run(  # ruff: ignore[subprocess-without-shell-equals-true]  argv: pinned bend + repo PRECISION_TABLE.bend, no shell
        [bend, str(HERE / "PRECISION_TABLE.bend")],
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    text = out.strip()
    if text.startswith('"'):
        text = bytes(text[1:-1], "utf-8").decode("unicode_escape")
    rows: dict[Key, Row] = {}
    for line in text.splitlines():
        cells = [c.strip() for c in line.replace("(q|gate)", "(q/gate)").split("|")]
        if len(cells) == BEND_CELLS:
            rows[cells[0], int(cells[1])] = (cells[2], cells[3], cells[4])
    return rows


def run_range(cls: str) -> str | None:
    """Normalize a class to its run range.

    'fp16 runs 112..2128 k-values, ...' -> '112..2128' (or '64' when lo == hi);
    'int8 activations' -> 'int8'.

    Args:
        cls: The class text.

    Returns:
        The normalized range, or None if the class has no known form.

    """
    if cls.startswith("int8"):
        return "int8"
    m = re.match(r"fp16 runs (\d+)\.\.(\d+) k-values", cls)
    if not m:
        return None
    lo, hi = str(m[1]), str(m[2])
    return lo if lo == hi else f"{lo}..{hi}"


def compare(key: Key, p: Row, b: Row, elpis_run: str, parta_run: str) -> list[str]:
    """Compare one partA row with its Bend row.

    Args:
        key: The (op, m) of the rows.
        p: The partA row.
        b: The Bend row.
        elpis_run: The expected elpis longest run.
        parta_run: The partA elpis longest run (pre-3023).

    Returns:
        The disagreement lines.

    """
    p_stock, p_ekern, p_erun = p
    b_stock, b_route, b_elpis = b
    lines: list[str] = []
    p_stock_n = "int8" if p_stock.startswith("int8") else p_stock
    if key[0] != "lm_head" and run_range(b_stock) != p_stock_n:
        lines.append(f"{key}: stock {b_stock!r} vs partA {p_stock!r}")
    p_same = p_ekern.startswith("= stock")
    b_same = b_elpis == "= stock kernel"
    if p_same != b_same:
        lines.append(
            f"{key}: elpis route {b_route!r} / {b_elpis!r} vs partA {p_ekern!r}"
        )
    elif not b_same and (
        (run_range(b_elpis) or "").split("..")[-1] != elpis_run or p_erun != parta_run
    ):
        lines.append(
            f"{key}: elpis longest run {b_elpis!r} vs expected {elpis_run} "
            f"(partA, pre-3023: {p_erun!r})"
        )
    return lines


def str_arg(ns: argparse.Namespace, name: str) -> str:
    """Return a string option of the parsed arguments.

    Args:
        ns: The parsed arguments.
        name: The option's destination name.

    Returns:
        The option value.

    Raises:
        TypeError: The value is not a string.

    """
    value = getattr(ns, name)
    if not isinstance(value, str):
        msg = f"--{name}: expected a string"
        raise TypeError(msg)
    return value


def main() -> None:
    """Run the cross-check and exit 1 on any disagreement."""
    ap = argparse.ArgumentParser()
    ap.add_argument("--parta", default=str(HERE / "gen/precision_parta.txt"))
    # partA.md predates ext 3023 (m16 fold-32): its elpis longest run is the FOLD = 4
    # instance's 64 k-values; the served EXL3_M16_FOLD32 = 1 instance folds every 2
    # k16 tiles = 32 k-values (bend/m16_diet.bend cfg_fold).
    ap.add_argument("--elpis-run", default="32")
    ap.add_argument("--parta-run", default="64")
    a = ap.parse_args()
    parta, elpis_run, parta_run = (
        str_arg(a, "parta"),
        str_arg(a, "elpis_run"),
        str_arg(a, "parta_run"),
    )
    pa, bd = parta_rows(parta), bend_rows(source_link.bend())
    bad = 0
    for key in sorted(pa):
        if key not in bd:
            sys.stdout.write(f"missing in Bend table: {key}\n")
            bad += 1
            continue
        for line in compare(key, pa[key], bd[key], elpis_run, parta_run):
            sys.stdout.write(f"{line}\n")
            bad += 1
    sys.stdout.write(
        f"{len(pa)} partA rows, {len(bd)} Bend rows, {bad} disagreement(s)\n"
    )
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
