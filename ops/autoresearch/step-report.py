#!/usr/bin/env python3
"""Step (verify round) time vs the proven DRAM floor, per kernel trace.

Floor bytes per round from bend/roofline.bend's round form (ROOFLINE_TABLE output):
  bytes(d, c, w) = c0 + kd*d + kc*c + kw*w, c = committed tokens/round, w = min(d + 8, 2056)
minus the draft head saving for images with ext 9002 (int4 draft head: 656 MB instead of the 954 MB
6-bit target head). Bandwidth 875.6 GB/s (the ledger's calibrated DRAM read rate).
"""
import re
import sys

C0, KD, KC, KW = 15656770816, 14336, 1052544, 4480
HEAD_FULL, HEAD_Q4 = 954055680, 656e6
BW = 875.6e9
E = "/mnt/ssd/storage/ai/qwen3.8-27b/exl3-serving-2/evidence"
TRACES = [  # dir, image, power W, has 9002
    ("kernel-trace-1", "g3", 280, False),
    ("kernel-trace-2", "g5m", 280, False),
    ("kernel-trace-3", "g7n", 280, False),
    ("kernel-trace-4", "g7j", 350, True),
    ("kernel-trace-5", "g7kafq", 350, True),
    ("kernel-trace-6", "g7kafqt", 350, True),
]
DEPTH = {"aime-think": 107, "ctx-8192": 8190, "ctx-32768": 32728}


def parse(path):
    txt = open(path).read()
    dec = {m.group(1): float(m.group(2)) for m in re.finditer(r"^(\S+): prompt=\d+ gen=\d+ decode=([\d.]+) tok/s", txt, re.M)}
    wall = {}
    for m in re.finditer(r"^== (\S+)\s+prompt=\d+.*?\n.*?\nround wall ms profiled=\[[^\]]*\] unprofiled median=([\d.]+)", txt, re.M | re.S):
        wall[m.group(1)] = float(m.group(2))
    buckets = {}
    for m in re.finditer(r"^== (\S+)\s+prompt=.*?\nbucket\s+n/round\s+ms/round\n(.*?)\nweight GEMM", txt, re.M | re.S):
        buckets[m.group(1)] = {l.split()[0]: float(l.split()[-1]) for l in m.group(2).splitlines() if l.strip()}
    return dec, wall, buckets


rows = []
for d, img, watts, q4 in TRACES:
    try:
        dec, wall, buckets = parse(f"{E}/{d}/trace.log")
    except FileNotFoundError:
        continue
    for case, depth in DEPTH.items():
        if case not in wall:
            continue
        w_ms = wall[case]
        tpr = dec[case] * w_ms / 1000.0          # committed tokens per round in the trace case
        byts = C0 + KD * depth + KC * tpr + KW * min(depth + 8, 2056) - ((HEAD_FULL - HEAD_Q4) if q4 else 0)
        floor = byts / BW * 1000.0
        rows.append((img, watts, case, depth, w_ms, floor, floor / w_ms, tpr))
print(f"{'image':8s} {'W':>4s} {'depth':>6s} {'step ms':>8s} {'floor ms':>9s} {'eff':>6s} {'tok/step':>8s}")
for img, watts, case, depth, w_ms, floor, eff, tpr in rows:
    print(f"{img:8s} {watts:4d} {depth:6d} {w_ms:8.2f} {floor:9.2f} {eff*100:5.1f}% {tpr:8.2f}")
if len(sys.argv) > 1:
    dec, wall, buckets = parse(f"{E}/{sys.argv[1]}/trace.log")
    for case, b in buckets.items():
        print(f"== {case} buckets (ms/round), wall {wall.get(case)}")
        for k, v in sorted(b.items(), key=lambda kv: -kv[1]):
            print(f"   {k:22s} {v:7.3f}")
