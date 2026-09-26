"""Per-call latency of the served EXL3 greedy acceptance vs a Python reference.

Run inside the served image (its python 3.13 + torch; CPU only), one core:
  docker run --rm --network none -v ART:/art/a:ro -v OUT:/out \\
    --entrypoint /usr/bin/taskset qwen-inference:exl3 -c 6 \\
    /opt/venv/bin/python -I -B /out/exl3_accept_latency.py /out/r.json /art/a [...]
Each artifact directory is fully admitted through its own loader, and both
implementations must reproduce the pinned table and agree on every timed
input. Batches of 20000 calls alternate order every round (3 warmup + 40).
Cases: *_server = the engine's GreedyAccept.__call__ (tensor rows, tolist,
sorted stop tuple, loader, ctypes); *_loader = Acceptor.accept on lists;
*_ctypes_floor = the exported function on a prefilled buffer; py_server /
py_list = the serial generator decision in Python with the same inputs.
"""

from __future__ import annotations

import gc
import importlib.util
import json
import random
import statistics
import sys
import time
from pathlib import Path

import torch
from exllamav3.generator.greedy_accept import GreedyAccept


def load(directory: str):
    spec = importlib.util.spec_from_file_location(
        f"loader_{abs(hash(directory))}", Path(directory) / "exl3_bend_accept.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def ref_accept(verify_ids, proposals, stops, budget, checkpoint):
    """Serial generator decision: stop token, budget, final, mismatch/checkpoint."""
    k = len(proposals)
    for i in range(k):
        t = verify_ids[i]
        n = i + 1
        if t in stops or n >= budget:
            return n, True
        if proposals[i] != t or n == checkpoint:
            return n, False
    return k + 1, (verify_ids[k] in stops or k + 1 >= budget)


def ref_server(verify_ids, proposals, stop_tokens, budget, checkpoint):
    """Same call shape as GreedyAccept.__call__, Python decision."""
    return ref_accept(verify_ids.tolist(), proposals.tolist(), stop_tokens, budget, checkpoint)


def served(acceptor):
    """The engine's own GreedyAccept.__call__ bound to an admitted acceptor."""
    g = GreedyAccept.__new__(GreedyAccept)
    g.acceptor = acceptor
    return g


def inputs_table_k7(rng: random.Random, n: int):
    """k = 7 inputs of the admission table section A (binary alphabet)."""
    out = []
    for _ in range(n):
        x = rng.randrange(1 << 15)
        v = [(17, 248046)[(x >> (2 * i)) & 1] for i in range(8)]
        p = [(17, 248046)[(x >> (2 * i + 1)) & 1] for i in range(7)]
        budget = rng.choice([*range(1, 10), 262144])
        cp = rng.randrange(8)
        out.append((v, p, {248046}, budget, cp))
    return out


def inputs_served(rng: random.Random, n: int):
    """k = 7 rounds shaped like serving: random vocab ids, accepted prefix
    geometric (mean ~3.5 of 7), stop set of two ids, large budget, rare
    checkpoint and rare stop hit."""
    stops = {248044, 248046}
    out = []
    for _ in range(n):
        v = [rng.randrange(248000) for _ in range(8)]
        acc = min(7, int(rng.expovariate(1 / 3.5)))
        p = [v[i] if i < acc else (v[i] + 1) % 248000 for i in range(7)]
        if rng.random() < 0.02:
            v[rng.randrange(8)] = 248046
        budget = rng.randrange(1, 64) if rng.random() < 0.05 else 4096
        cp = rng.randrange(1, 8) if rng.random() < 0.1 else 0
        out.append((v, p, stops, budget, cp))
    return out


def as_tensors(items):
    v = torch.tensor([it[0] for it in items], dtype=torch.long)
    p = torch.tensor([it[1] for it in items], dtype=torch.long)
    return [(v[i], p[i], it[2], it[3], it[4]) for i, it in enumerate(items)]


def run_batch(fn, items, sink):
    t0 = time.perf_counter_ns()
    for a, b, c, d, e in items:
        sink.append(fn(a, b, c, d, e))
    return time.perf_counter_ns() - t0


def bench(cases, items_by_case, rounds=40, warm=3):
    raw = {name: [] for name in cases}
    names = list(cases)
    for r in range(warm + rounds):
        order = names if r % 2 == 0 else names[::-1]
        for name in order:
            fn, kind = cases[name]
            items = items_by_case[kind]
            sink = []
            gc.disable()
            dt = run_batch(fn, items, sink)
            gc.enable()
            if r >= warm:
                raw[name].append(dt / len(items))
    return raw


def summarize(raw):
    return {
        k: {
            "median_ns": statistics.median(v),
            "min_ns": min(v),
            "max_ns": max(v),
            "n": len(v),
        }
        for k, v in raw.items()
    }


def main(argv):
    out_path = argv[0]
    dirs = argv[1:]
    rng = random.Random(20260926)
    table = inputs_table_k7(rng, 20000)
    real = inputs_served(rng, 20000)
    stop_tuple = lambda items: [(v, p, tuple(sorted(s)), b, c) for v, p, s, b, c in items]
    items = {
        "table_list": stop_tuple(table),
        "served_list": stop_tuple(real),
        "table_tensor": as_tensors(table),
        "served_tensor": as_tensors(real),
    }
    report = {"python": sys.version, "torch": torch.__version__, "dirs": dirs}
    cases = {}
    for idx, d in enumerate(dirs):
        mod = load(d)
        acc = mod.admit(d)  # full admission: hashes + complete table differential
        # Full-output equality over the complete admission input set (3.26M
        # cells) for both implementations against the pinned Bend table.
        table_bytes = (Path(d) / mod.TABLE_NAME).read_bytes()
        assert mod.render(acc.accept).encode() == table_bytes
        if idx == 0:
            assert mod.render(ref_accept).encode() == table_bytes, "python reference differs"
            report["python_reference_table_equal"] = True
        report[f"bend{idx}_table_equal"] = True
        g = served(acc)
        # Equality on the timing inputs too (lists and tensors, server path).
        for kind in ("table", "served"):
            got_b = [g(*it) for it in items[f"{kind}_tensor"]]
            got_l = [acc.accept(*it) for it in items[f"{kind}_list"]]
            want = [ref_server(*it) for it in items[f"{kind}_tensor"]]
            assert got_b == want == got_l, kind
        for kind in ("table", "served"):
            cases[f"bend{idx}_server_{kind}"] = (g, f"{kind}_tensor")
            cases[f"bend{idx}_loader_{kind}"] = (acc.accept, f"{kind}_list")
        # ctypes floor: the exported function on a prefilled cell buffer.
        fn, cells = acc._function, acc._cells
        acc.accept(*items["served_list"][0])
        cases[f"bend{idx}_ctypes_floor"] = ((lambda a, b, c, d, e, fn=fn, cells=cells: fn(cells)), "served_list")
    for kind in ("table", "served"):
        cases[f"py_server_{kind}"] = (ref_server, f"{kind}_tensor")
        cases[f"py_list_{kind}"] = (ref_accept, f"{kind}_list")
    raw = bench(cases, items)
    report["summary"] = summarize(raw)
    report["raw_ns_per_call"] = raw
    Path(out_path).write_text(json.dumps(report, indent=1))
    for k, v in report["summary"].items():
        print(f"{k:28s} median {v['median_ns']:8.1f} ns  min {v['min_ns']:8.1f}  max {v['max_ns']:8.1f}")


if __name__ == "__main__":
    main(sys.argv[1:])
