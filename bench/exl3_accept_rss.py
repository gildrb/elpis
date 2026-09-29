"""RSS delta of loading libexl3_accept.so (fresh process): exl3_accept_rss.py LIB."""

import ctypes
import json
import sys


def status():
    out = {}
    for line in open("/proc/self/status"):
        key, _, rest = line.partition(":")
        if key in ("VmRSS", "RssAnon", "RssFile", "VmSize"):
            out[key] = int(rest.split()[0])
    return out


lib = sys.argv[1]
cells = (ctypes.c_int64 * 23)(7, 4096, 0, 1, 248046, 0, 0, 0, *range(8), *range(7))
# Warm the ctypes load/call machinery on an already-mapped library so the
# delta below is the library itself, not first-touch of ctypes code paths.
for kind in (ctypes.CDLL, ctypes.PyDLL):
    warm = kind("libc.so.6", mode=ctypes.RTLD_LOCAL).labs
    warm.argtypes = [ctypes.POINTER(ctypes.c_int64)]
    warm.restype = ctypes.c_int32
    warm(cells)
before = status()
handle = ctypes.CDLL(lib, mode=ctypes.RTLD_LOCAL)
fn = handle.elpis_exl3_accept
fn.argtypes = [ctypes.POINTER(ctypes.c_int64)]
fn.restype = ctypes.c_int32
loaded = status()
result = fn(cells)
called = status()
print(json.dumps({
    "result": result,
    "load_kib": {k: loaded[k] - before[k] for k in before},
    "first_call_kib": {k: called[k] - loaded[k] for k in before},
}))
