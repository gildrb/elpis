#!/usr/bin/env python3
"""Cross-check the Bend precision table (bend/PRECISION_TABLE.bend) against the CPU-computed decode table
partA.md (analyze_a.py over the stock sources and the persisted autotune cache): per (op, m), the stock run
range / int8, and the elpis run range / "= stock".

    python3 bend/precision_diff.py [--parta PATH]

PATH: the partA.md decode table; the default is bend/gen/precision_parta.txt. The script runs the `bend` on
PATH (exactly bend 2.0.35, bend/source_link.py).

Prints one line per disagreement and exits 1 if any; lm_head's stock class is not normalized by Bend
(unary Nat), so only its elpis route (= stock) is compared.
"""
import argparse
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import source_link  # noqa: E402


def parta_rows(path):
    rows = {}
    for line in Path(path).read_text().splitlines():
        cells = [c.strip() for c in line.replace("(q|gate)", "(q/gate)").strip().strip("|").split("|")]
        if len(cells) != 7 or not cells[1].isdigit():
            continue
        op, m, _kern, _cfg, stock_run, elpis_kern, elpis_run = cells
        rows[(op, int(m))] = (stock_run, elpis_kern, elpis_run)
    return rows


def bend_rows(bend):
    out = subprocess.run([bend, str(HERE / "PRECISION_TABLE.bend")], capture_output=True, text=True, check=True).stdout
    text = out.strip()
    if text.startswith('"'):
        text = bytes(text[1:-1], "utf-8").decode("unicode_escape")
    rows = {}
    for line in text.splitlines():
        cells = [c.strip() for c in line.replace("(q|gate)", "(q/gate)").split("|")]
        if len(cells) == 5:
            rows[(cells[0], int(cells[1]))] = (cells[2], cells[3], cells[4])
    return rows


def run_range(cls):
    """'fp16 runs 112..2128 k-values, ...' -> '112..2128' (or '64' when lo == hi); 'int8 activations' -> 'int8'."""
    if cls.startswith("int8"):
        return "int8"
    m = re.match(r"fp16 runs (\d+)\.\.(\d+) k-values", cls)
    if not m:
        return None
    lo, hi = m.groups()
    return lo if lo == hi else f"{lo}..{hi}"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--parta", default=str(HERE / "gen/precision_parta.txt"))
    # partA.md predates ext 3023 (m16 fold-32): its elpis longest run is the FOLD = 4 instance's 64 k-values;
    # the served EXL3_M16_FOLD32 = 1 instance folds every 2 k16 tiles = 32 k-values (bend/m16_diet.bend cfg_fold).
    ap.add_argument("--elpis-run", default="32")
    ap.add_argument("--parta-run", default="64")
    a = ap.parse_args()
    pa, bd = parta_rows(a.parta), bend_rows(source_link.bend())
    bad = 0
    for key in sorted(pa):
        if key not in bd:
            print(f"missing in Bend table: {key}")
            bad += 1
            continue
        p_stock, p_ekern, p_erun = pa[key]
        b_stock, b_route, b_elpis = bd[key]
        p_stock_n = "int8" if p_stock.startswith("int8") else p_stock
        if key[0] != "lm_head" and run_range(b_stock) != p_stock_n:
            print(f"{key}: stock {b_stock!r} vs partA {p_stock!r}")
            bad += 1
        p_same = p_ekern.startswith("= stock")
        b_same = b_elpis == "= stock kernel"
        if p_same != b_same:
            print(f"{key}: elpis route {b_route!r} / {b_elpis!r} vs partA {p_ekern!r}")
            bad += 1
        elif not b_same and ((run_range(b_elpis) or "").split("..")[-1] != a.elpis_run or p_erun != a.parta_run):
            print(f"{key}: elpis longest run {b_elpis!r} vs expected {a.elpis_run} (partA, pre-3023: {p_erun!r})")
            bad += 1
    print(f"{len(pa)} partA rows, {len(bd)} Bend rows, {bad} disagreement(s)")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
