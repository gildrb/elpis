#!/usr/bin/env python3
"""Compare the normal-arm target token ids of two invariance.py run outputs, case by case.

usage: inv-compare.py A/result.json B/result.json
Exit 0 only if both runs PASS their own draft-arm invariance and every case's normal ids are equal.
"""
import json
import sys


def load(path: str) -> dict:
    with open(path) as f:
        return json.load(f)


def main() -> None:
    a, b = load(sys.argv[1]), load(sys.argv[2])
    ok = a["pass"] is True and b["pass"] is True
    print(f"A pass={a['pass']} errors={len(a['errors'])}; B pass={b['pass']} errors={len(b['errors'])}")
    if a["cases"].keys() != b["cases"].keys():
        print(f"case sets differ: {sorted(a['cases'].keys() ^ b['cases'].keys())}")
        ok = False
    for name in sorted(a["cases"].keys() & b["cases"].keys()):
        ia = a["cases"][name]["arms"]["normal"]["ids"]
        ib = b["cases"][name]["arms"]["normal"]["ids"]
        first = next((i for i, (x, y) in enumerate(zip(ia, ib)) if x != y), None)
        if first is None and len(ia) != len(ib):
            first = min(len(ia), len(ib))
        ra = len(a["cases"][name]["arms"]["normal"]["rounds"])
        rb = len(b["cases"][name]["arms"]["normal"]["rounds"])
        print(f"{name:28s} {len(ia):6d} {len(ib):6d} rounds {ra:5d} {rb:5d} "
              + ("EQUAL" if first is None else f"DIFF@{first}"))
        ok = ok and first is None
    print("IDENTICAL" if ok else "NOT IDENTICAL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
