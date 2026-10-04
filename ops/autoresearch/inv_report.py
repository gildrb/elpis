#!/usr/bin/env python3
"""Draft-invariance gate report (host side): the served-policy (tree) run and a second run of invariance.py over
the 15 parity cases (parity-1/parity.py cases(False)): the forced chain (EXL3_TREE=1 EXL3_TREE_FORCE_CHAIN=1, arms
normal / cap / wrong0) or the non-tree engine (EXL3_TREE=0, arms normal / cap / wrong0 / m1, m1 = no draft).

Pass only if both runs PASS their own arm invariance, each runs at least normal / cap / wrong0, and, for every case,
every gating arm of both runs has ids identical to the tree run's normal arm. The m1 arm (no draft: the generator's
own M=1 kernels) is reported, not gated: its first divergence and the top-2 logit margin of both arms there (from the
run's probe). Per prompt and arm it records the ids sha256, length, rounds, accepted draft tokens (sum of count - 1)
and rejected draft tokens (sum of 7 - (count - 1): the 7-token window), and the first divergence vs the tree normal arm.

    python3 inv_report.py TREE/result.json SECOND/result.json OUT.json
"""

import hashlib
import json
import sys

BASE_ARMS = ("normal", "cap", "wrong0")
REPORTED = ("m1",)
WINDOW = 7


def main(tree_path, chain_path, out_path):
    runs = {"tree": json.load(open(tree_path)), "second": json.load(open(chain_path))}
    ok = all(r["pass"] is True and not r["errors"] for r in runs.values())
    report = {
        "pass": False,
        "runs_pass": {k: r["pass"] for k, r in runs.items()},
        "run_errors": {k: len(r["errors"]) for k, r in runs.items()},
        "cases": {},
    }
    names = list(runs["tree"]["cases"])
    if set(names) != set(runs["second"]["cases"]) or len(names) != 15:
        ok = False
        report["case_set_error"] = [
            sorted(runs["tree"]["cases"]),
            sorted(runs["second"]["cases"]),
        ]
    report["arms"] = {k: r["arms"] for k, r in runs.items()}
    if any(not set(BASE_ARMS) <= set(r["arms"]) for r in runs.values()):
        ok = False
    n_equal = n_total = 0
    margins = {}
    for pol, r in runs.items():
        for p in r.get("probes", []):
            if p.get("arms", [None, None])[1] in REPORTED:
                lg = p.get("logits_at_t_minus_1") or {}
                margins[(pol, p["case"], p["arms"][1])] = {
                    k: v.get("margin") for k, v in lg.items()
                }
    for name in names:
        ref = runs["tree"]["cases"][name]["arms"].get("normal", {}).get("ids")
        rows = {}
        for pol, r in runs.items():
            arms = r["cases"].get(name, {}).get("arms", {})
            for arm in r["arms"]:
                a = arms.get(arm)
                if a is None or ref is None:
                    ok = ok and arm in REPORTED
                    rows[f"{pol}/{arm}"] = {"missing": True}
                    continue
                ids = a["ids"]
                first = next(
                    (i for i, (x, y) in enumerate(zip(ref, ids)) if x != y), None
                )
                if first is None and len(ids) != len(ref):
                    first = min(len(ids), len(ref))
                acc = sum(c - 1 for _, c in a["rounds"])
                rows[f"{pol}/{arm}"] = {
                    "ids_sha256": hashlib.sha256(json.dumps(ids).encode()).hexdigest(),
                    "tokens": len(ids),
                    "rounds": len(a["rounds"]),
                    "accepted_draft": acc,
                    "rejected_draft": WINDOW * len(a["rounds"]) - acc,
                    "first_divergence_vs_tree_normal": first,
                }
                if arm in REPORTED:
                    rows[f"{pol}/{arm}"]["reported_only"] = True
                    rows[f"{pol}/{arm}"]["logit_margin_at_divergence"] = margins.get((
                        pol,
                        name,
                        arm,
                    ))
                    continue
                n_total += 1
                if first is None:
                    n_equal += 1
                else:
                    ok = False
        report["cases"][name] = rows
        line = "  ".join(
            f"{k}:{'==' if v.get('first_divergence_vs_tree_normal') is None and not v.get('missing') else 'DIFF@' + str(v.get('first_divergence_vs_tree_normal'))}"
            for k, v in rows.items()
        )
        print(f"{name:24s} {len(ref or []):6d}  {line}")
    report["identical"] = f"{n_equal}/{n_total}"
    report["pass"] = ok
    with open(out_path, "w") as f:
        json.dump(report, f, indent=1)
    print(
        f"{n_equal}/{n_total} identical; runs pass {report['runs_pass']}; {'PASS' if ok else 'FAIL'}"
    )
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:4]))
