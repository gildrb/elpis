#!/usr/bin/env python3
"""Per-call tok/s and energy for an autoresearch output dir, from the 250 ms nvidia-smi sampler."""
import csv, datetime, glob, json, sys
samples = []
for row in csv.reader(open('/tmp/gpu-power.csv')):
    try:
        t = datetime.datetime.strptime(row[0].strip(), '%Y/%m/%d %H:%M:%S.%f').timestamp()
        samples.append((t, float(row[1].split()[0]), int(row[2].split()[0])))
    except (ValueError, IndexError):
        continue
def find(o):
    if isinstance(o, dict):
        if 'usage' in o and 'time' in o:
            yield o
        for v in o.values():
            yield from find(v)
    elif isinstance(o, list):
        for v in o:
            yield from find(v)
tt = tj = ts = 0.0
for f in sorted(glob.glob(sys.argv[1] + '/tiny-math/**/traces.jsonl', recursive=True)):
    for line in open(f):
        for u in find(json.loads(line)):
            ct = (u['usage'] or {}).get('completion_tokens')
            t0, t1 = u['time']['start'], u['time']['end']
            if not ct:
                continue
            w = [s for s in samples if t0 <= s[0] <= t1]
            if len(w) < 4:
                sys.exit(f'too few power samples for a {ct}-token call')
            p = sum(s[1] for s in w) / len(w)
            sm = sum(s[2] for s in w) / len(w)
            j = p * (t1 - t0)
            tt += ct; tj += j; ts += t1 - t0
            print(f"tokens={ct:6d} secs={t1-t0:7.2f} tok/s={ct/(t1-t0):7.2f} mean {p:6.1f} W  SM {sm:5.0f} MHz  {ct/j:.3f} tok/J")
print(f"tiny-math: {tt:.0f} tok, {ts:.1f} s, {tt/ts:.2f} tok/s, mean {tj/ts:.1f} W, {tt/tj:.3f} tok/J")
