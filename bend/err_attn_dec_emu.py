#!/usr/bin/env python3
"""
CPU emulation of one decode-attention row (Qwen3.8-27B full-attention layer: 6 q heads of one kv head,
head_dim 256, CQ3 K / V cache, row at absolute position L - 1) through three kernels, against an fp64
reference of the same inputs:

  stock    355c6ee M = 1: Triton _paged_attn_decode_split_kernel (32-key tiles, num_splits / split_len
           from the block-table bound, acc * alpha + tl.dot) + _paged_attn_decode_combine_kernel
           (sequential fma over splits, div, _rot_h32)
  current  elpis ext 3006 / 3007 / 3012 attn_verify_split_k3v3 + attn_verify_combine_gate (64-key tiles,
           CTA x of 20 takes tiles x, x + 20, ...; MMA into the running acc; 8 warp partials summed in
           sequence; fma combine in slot order; 32-FFMA back-rotation)
  fixed    elpis ext 3030 (integer running max: exact power-of-two alpha and weights; 64-key tile tree
           sum; fresh-C P V folded by one fma; pairwise-tree combine; two-k16-MMA back-rotation)

Arithmetic: fp16 / fp32 roundings emulated exactly (numpy casts, fma through fp64); ex2 = exp2 in fp64
rounded to fp32; div.full / acc / lsum = fp32(rcp) then fp32 product; tensor-core mma.m16n8k16 .f32 =
the project's calibrated model (Fasi, Higham, Mikaitis, Pranesh 2021; Int8Attn/split/emu_split.py):
TC=al{K}e{E} (default al8e1): every K products (exact) plus the accumulator are aligned to the largest
exponent keeping 24 + E bits (lower bits truncated), summed exactly, result rounded toward zero;
TC=rz{K}: exact sum of K products into the accumulator, rounded toward zero.

The pre stage (q norm / RoPE) and the output gate are common to all three (bend/err_attn_laws.bend
pre_eq) and left out: the inputs are the fp16 q head and the cache codes / scales, the output is the
fp16 attention output before the gate.

Inputs per case: random (N(0, 1) q, uniform codes, log-normal scales) and adversarial:
  flat    q = 0: every score 0, every p equal: the longest sums (denominator, P V, combine)
  ramp    scores rising with the key index: the running max moves at every tile (rescale chains)
  peak    one key 30 log2-units above a random background: p spans the fp16 range
  offset  V codes all 7 but one bit of noise: large common value, small differences

Usage: python3 err_attn_dec_emu.py [--L 2,64,500,1281,4097,8192,32768] [--cases random,flat,ramp,peak,offset]
       [--seed 1] [--fp32out | --quot] [--v1] [--json OUT]
Needs numpy (any CPython 3.10+).
"""

from __future__ import annotations

import argparse
import json
import os
import sys

import numpy as np

f16, f32, f64 = np.float16, np.float32, np.float64
HD, G, PAGE = 256, 6, 256
S_E = 20  # 82 SMs // 4 kv heads (E:bc_attn.py av_splits)
SPLITS_CAP = 41  # stock: min(2 * 82 // 4, 128)
L2E = f32(np.log2(np.e))  # fp32(log2 e) = 0f3FB8AA3B
SCALE = 1.0 / 16.0  # 1 / sqrt(256)
SCALE_LOG2 = f32(
    SCALE * float(L2E)
)  # elpis scale_log2 = fp32(2^-4 log2 e) = 2^-4 fp32(log2 e)
TC = os.environ.get("TC", "al8e1")
CASES = ["random", "flat", "ramp", "peak", "offset"]
OUT32 = (
    False  # --fp32out: compare the fp32 rotation result, before the final fp16 store
)
QUOT = False  # --quot: compare the fp32 quotient acc / lsum (rotated domain), before any output rounding


def out16(y):
    return y.astype(f32) if OUT32 else y.astype(f16)


def cdiv(a, b):
    return -(-a // b)


def h32_f16():
    h = np.ones((1, 1))
    while h.shape[0] < 32:
        h = np.block([[h, h], [h, -h]])
    return (h / np.sqrt(32.0)).astype(f32).astype(f16)


H32 = h32_f16()
H32_64 = H32.astype(f64)


# ---- rounding primitives ----


def rz32(x):
    r = x.astype(f32)
    over = np.abs(r.astype(f64)) > np.abs(x)
    return np.where(over, np.nextafter(r, f32(0)), r).astype(f32)


def fma32(a, b, c):
    return (a.astype(f64) * b.astype(f64) + c.astype(f64)).astype(f32)


def add32(a, b):
    return (a.astype(f64) + b.astype(f64)).astype(f32)


def ex2(x):
    with np.errstate(over="ignore"):
        return np.exp2(x.astype(f64)).astype(f32)


def div32(a, l):
    r = (1.0 / l.astype(f64)).astype(f32)
    return (a.astype(f64) * r.astype(f64)).astype(f32)


def tc_steps(C, A, B):
    """mma.m16n8k16 chain: C (R, D) fp32 += A (R, k) fp16 @ B (k, D) fp16, one k16 step at a time in k order."""
    A64, B64 = A.astype(f64), B.astype(f64)
    k = A.shape[1]
    if TC.startswith("rz"):
        g = int(TC[2:])
        for j in range(0, k, g):
            C = rz32(C.astype(f64) + A64[:, j : j + g] @ B64[j : j + g])
        return C
    g, e = (int(x) for x in TC[2:].split("e"))
    for j in range(0, k, g):
        prods = A64[:, j : j + g, None] * B64[None, j : j + g, :]
        terms = np.concatenate([C.astype(f64)[:, None, :], prods], 1)
        mx = np.abs(terms).max(1)
        _, ex = np.frexp(mx)
        q = np.ldexp(1.0, ex - 24 - e)
        s = (np.trunc(terms / q[:, None, :]) * q[:, None, :]).sum(1)
        C = np.where(mx > 0, rz32(s), f32(0)).astype(f32)
    return C


def rot_mma(x16):
    """(R, 256) fp16 -> H32-rotated per 32-group by two k16 MMA steps from zero, fp32"""
    R = x16.shape[0]
    xg = x16.reshape(R * 8, 32)
    y = tc_steps(np.zeros((R * 8, 32), f32), xg, H32)
    return y.reshape(R, HD)


def scores_tc(q16, k16):
    """(R, 256) x (N, 256) -> (R, N) fp32 by the 16-step k16 chain over dims, in chunks of keys"""
    out = np.empty((q16.shape[0], k16.shape[0]), f32)
    for c0 in range(0, k16.shape[0], 4096):
        kc = k16[c0 : c0 + 4096]
        out[:, c0 : c0 + 4096] = tc_steps(
            np.zeros((q16.shape[0], kc.shape[0]), f32), q16, kc.T
        )
    return out


# ---- inputs ----


def make_case(kind, L, rng):
    q = rng.standard_normal((G, HD)).astype(f16)
    kc = rng.integers(0, 8, (L, HD)).astype(np.int64)
    vc = rng.integers(0, 8, (L, HD)).astype(np.int64)
    ks = np.exp(rng.normal(-1.0, 0.4, (L, 8))).astype(f16)
    vs = np.exp(rng.normal(-1.0, 0.4, (L, 8))).astype(f16)
    if kind == "flat":
        q = np.zeros((G, HD), f16)
    elif kind == "ramp":
        # q = H32 column 0 on dims 0..31 (its H32 rotation is ~e_0), key j's dim-0 value grows with j: the
        # scores rise across the row, so the running max moves at every tile
        q = np.zeros((G, HD), f16)
        q[:, :32] = H32[:, 0]
        kc[:, 0] = 7
        ks[:, 0] = (8.0 + 56.0 * np.arange(L) / max(L, 1)).astype(f16)
    elif kind == "peak":
        # one key aligned with the rotated q (codes 7 / 0 by its sign, scale 2): ~30 log2 units above the rest
        j = int(rng.integers(0, L))
        q = (rng.standard_normal((G, HD)) * 0.5).astype(f16)
        qr0 = (q[0].astype(f64).reshape(8, 32) @ H32_64).reshape(HD)
        kc[j] = np.where(qr0 > 0, 7, 0)
        ks[j] = f16(2.0)
    elif kind == "offset":
        vc = np.where(rng.random((L, HD)) < 0.5, 7, 6).astype(np.int64)
    return q, kc, ks, vc, vs


def deq16(codes, scales):
    s = (scales.astype(f32) * f32(0.25)).astype(f32)
    v = ((codes.astype(f32) - f32(3.5)) * np.repeat(s, 32, axis=1)).astype(f32)
    return v.astype(f16)


def reference(q, K16, V16, L):
    """fp64: q exact (fp16 input), K / V the cache values (fp16 dequant is exact for 3-bit codes x fp16 scale / 4
    whenever representable; we take the fp16 cache values as the leaves), exact rotations and softmax"""
    q64 = q.astype(f64).reshape(G * 8, 32) @ H32_64
    q64 = q64.reshape(G, HD)
    s = (q64 @ K16.astype(f64).T) * SCALE
    s -= s.max(1, keepdims=True)
    p = np.exp(s)
    o = (p @ V16.astype(f64)) / p.sum(1, keepdims=True)
    if QUOT:
        return o
    return (o.reshape(G * 8, 32) @ H32_64).reshape(G, HD)


# ---- stock ----


def stock_geo(L):
    bound = 4096 * cdiv(L, 4096) + 1
    ns = max(1, min(SPLITS_CAP, cdiv(bound, 4 * 32)))
    return ns, cdiv(cdiv(bound, ns), 32) * 32


def tree_sum(p, offs):
    s = p.astype(f32)
    idx = np.arange(p.shape[1])
    for off in offs:
        s = add32(s, s[:, idx ^ off])
    return s[:, 0]


def run_stock(qr16, sc, V16, L):
    ns, sl = stock_geo(L)
    s = (sc * f32(SCALE)).astype(f32)  # exact (power of two)
    parts = []
    for sp in range(ns):
        n0, n1 = sp * sl, min(sp * sl + sl, L)
        if n0 >= L:
            break
        m = np.full(G, -np.inf, f32)
        l = np.zeros(G, f32)
        acc = np.zeros((G, HD), f32)
        for t0 in range(n0, n1, 32):
            t1 = min(t0 + 32, n1)
            st = np.full((G, 32), -np.inf, f32)
            st[:, : t1 - t0] = s[:, t0:t1]
            m_new = np.maximum(m, st.max(1))
            m_exp = np.where(np.isinf(m_new), f32(0), m_new).astype(f32)
            with np.errstate(invalid="ignore"):
                p = ex2(((st - m_exp[:, None]).astype(f32) * L2E).astype(f32))
                p = np.where(np.isinf(st), f32(0), p)
                alpha = np.where(
                    np.isinf(m),
                    f32(0),
                    ex2(((m - m_exp).astype(f32) * L2E).astype(f32)),
                ).astype(f32)
            l = fma32(l, alpha, tree_sum(p, (1, 4, 2, 16, 8)))
            Vt = np.zeros((32, HD), f16)
            Vt[: t1 - t0] = V16[t0:t1]
            acc = tc_steps((acc * alpha[:, None]).astype(f32), p.astype(f16), Vt)
            m = m_new
        parts.append((m, l, acc))
    m_max = np.max([p[0] for p in parts], axis=0)
    m_safe = np.where(np.isinf(m_max), f32(0), m_max).astype(f32)
    acc = np.zeros((G, HD), f32)
    lsum = np.zeros(G, f32)
    for m_s, l_s, o_s in parts:
        w = np.where(
            np.isinf(m_s), f32(0), ex2(((m_s - m_safe).astype(f32) * L2E).astype(f32))
        ).astype(f32)
        acc = fma32(o_s, w[:, None], acc)
        lsum = fma32(l_s, w, lsum)
    o = div32(acc, np.where(lsum == 0, f32(1), lsum)[:, None])
    if QUOT:
        return o
    return out16(rot_mma(o.astype(f16)))


# ---- elpis (current and fixed) ----


def run_elpis(qr16, sc, V16, L, mode):
    """mode: 'current' (ext 3006 / 3007 / 3012), 'fixed' (ext 3030), 'v1' (rejected 3030 draft: p taken
    against the integer running max, so the row's top key has p in [1, 2) and pays an fp16 rounding)"""
    fixed = mode != "current"
    x = (sc * SCALE_LOG2).astype(f32)  # FMUL by scale_log2
    T = cdiv(L, 64)
    parts = []
    for cta in range(min(S_E, T)):
        m = np.full(G, -np.inf, f32)
        l = np.zeros(G, f32)
        acc = np.zeros((G, HD), f32)
        for i in range(cta, T, S_E):
            t0, t1 = 64 * i, min(64 * i + 64, L)
            xt = np.full((G, 64), -np.inf, f32)
            xt[:, : t1 - t0] = x[:, t0:t1]
            tmax = xt.max(1)
            m_new = np.maximum(m, np.floor(tmax) if fixed else tmax).astype(f32)
            m_use = np.where(np.isinf(m_new), f32(0), m_new).astype(f32)
            with np.errstate(invalid="ignore"):
                if fixed:
                    alpha = np.where(
                        np.isinf(m),
                        f32(0),
                        np.where(
                            m_new == m,
                            f32(1),
                            np.exp2((m - m_use).astype(f64)).astype(f32),
                        ),
                    )
                else:
                    alpha = np.where(
                        np.isinf(m),
                        f32(0),
                        np.where(m_new == m, f32(1), ex2((m - m_use).astype(f32))),
                    )
                if mode == "fixed":
                    # p against the tile's own max (its top key exactly 1); the tile joins the integer-scaled
                    # state through c = ex2(tmax - m_new) < 2
                    t_use = np.where(np.isinf(tmax), f32(0), tmax).astype(f32)
                    p = np.where(
                        np.isinf(xt), f32(0), ex2((xt - t_use[:, None]).astype(f32))
                    )
                    c = np.where(
                        np.isinf(tmax), f32(0), ex2((t_use - m_use).astype(f32))
                    ).astype(f32)
                else:
                    p = np.where(
                        np.isinf(xt), f32(0), ex2((xt - m_use[:, None]).astype(f32))
                    )
            alpha = alpha.astype(f32)
            # tile-local token u = 8 warp + 2 t + e: in-thread pair, lane xors (offsets 1, 2, 4)
            if fixed:
                tsum = tree_sum(p, (1, 2, 4, 8, 16, 32))
            else:
                w8 = p.reshape(G, 8, 8)
                ws = np.stack([tree_sum(w8[:, w], (1, 2, 4)) for w in range(8)], 1)
                tsum = ws[:, 0]
                for w in range(1, 8):
                    tsum = add32(tsum, ws[:, w])
            Vt = np.zeros((64, HD), f16)
            Vt[: t1 - t0] = V16[t0:t1]
            P16 = p.astype(f16)
            if mode == "fixed":
                l = fma32(tsum, c, (l * alpha).astype(f32))
                pv = tc_steps(np.zeros((G, HD), f32), P16, Vt)
                acc = fma32(pv, c[:, None], (acc * alpha[:, None]).astype(f32))
            elif mode == "v1":
                l = fma32(l, alpha, tsum)
                pv = tc_steps(np.zeros((G, HD), f32), P16, Vt)
                acc = fma32(acc, alpha[:, None], pv)
            else:
                l = fma32(l, alpha, tsum)
                acc = tc_steps((acc * alpha[:, None]).astype(f32), P16, Vt)
            m = m_new
        parts.append((m, l, acc))
    mmax = np.max([p[0] for p in parts], axis=0)
    m_use = np.where(np.isinf(mmax), f32(0), mmax).astype(f32)
    if fixed:
        terms = []
        for m_s, l_s, o_s in parts:
            w = np.exp2((m_s - m_use).astype(f64)).astype(f32)  # exact power of two
            terms.append(((o_s * w[:, None]).astype(f32), (l_s * w).astype(f32)))
        st = {}
        n = 0
        for a, c in terms:  # binary counter = fixed aligned tree
            k = 0
            while (n >> k) & 1:
                pa, pc = st[k]
                a, c = add32(pa, a), add32(pc, c)
                k += 1
            st[k] = (a, c)
            n += 1
        acc = np.zeros((G, HD), f32)
        lsum = np.zeros(G, f32)
        for k in range(12):
            if (n >> k) & 1:
                acc, lsum = add32(st[k][0], acc), add32(st[k][1], lsum)
    else:
        acc = np.zeros((G, HD), f32)
        lsum = np.zeros(G, f32)
        for m_s, l_s, o_s in parts:
            w = np.where(np.isinf(m_s), f32(-1), ex2((m_s - m_use).astype(f32)))
            acc = fma32(o_s, w[:, None], acc)
            lsum = fma32(l_s, w, lsum)
    o32 = div32(acc, np.where(lsum == 0, f32(1), lsum)[:, None])
    if QUOT:
        return o32
    o = o32.astype(f16)
    if fixed:
        return out16(rot_mma(o))
    y = np.zeros((G * 8, 32), f32)
    og = o.reshape(G * 8, 32)
    for i in range(32):
        y = fma32(og[:, i : i + 1].astype(f32), H32[i : i + 1, :].astype(f32), y)
    return out16(y.reshape(G, HD))


def stats(o, ref):
    e = np.abs(o.astype(f64) - ref)
    return {
        "mean": float(e.mean()),
        "max": float(e.max()),
        "rms": float(np.sqrt((e * e).mean())),
    }


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("--L", default="2,64,500,1281,4097,8192,32768")
    ap.add_argument("--cases", default="random,flat,ramp,peak,offset")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument(
        "--v1",
        action="store_true",
        help="also run the rejected integer-max-for-p draft",
    )
    ap.add_argument(
        "--fp32out",
        action="store_true",
        help="measure before the final fp16 rounding of the output",
    )
    ap.add_argument(
        "--quot",
        action="store_true",
        help="measure the fp32 quotient acc / lsum (split + combine only)",
    )
    ap.add_argument("--json")
    a = ap.parse_args(argv[1:])
    global OUT32, QUOT
    OUT32 = a.fp32out
    QUOT = a.quot
    rows = []
    print(
        f"TC model {TC}; errors |out - fp64 ref| over 6 heads x 256 dims ({'fp32 quotient acc / lsum, rotated domain' if QUOT else ('fp32 rotation result' if OUT32 else 'fp16 attention output')}, before the gate)"
    )
    print(
        f"{'case':7s} {'L':>7s} | {'stock mean':>11s} {'max':>10s} | {'current mean':>12s} {'max':>10s} | {'fixed mean':>11s} {'max':>10s} | fixed/stock mean, max"
        + (" | v1/stock mean, max" if a.v1 else "")
    )
    for kind in a.cases.split(","):
        for L in (int(x) for x in a.L.split(",")):
            rng = np.random.default_rng([a.seed, L, CASES.index(kind)])
            q, kc, ks, vc, vs = make_case(kind, L, rng)
            K16, V16 = deq16(kc, ks), deq16(vc, vs)
            ref = reference(q, K16, V16, L)
            qr16 = rot_mma(q).astype(f16)
            sc = scores_tc(qr16, K16)
            res = {
                "case": kind,
                "L": L,
                "stock": stats(run_stock(qr16, sc, V16, L), ref),
                "current": stats(run_elpis(qr16, sc, V16, L, "current"), ref),
                "fixed": stats(run_elpis(qr16, sc, V16, L, "fixed"), ref),
            }
            if a.v1:
                res["v1"] = stats(run_elpis(qr16, sc, V16, L, "v1"), ref)
            rows.append(res)
            s, c, f = res["stock"], res["current"], res["fixed"]
            extra = (
                f" | {res['v1']['mean'] / s['mean']:.3f}, {res['v1']['max'] / s['max']:.3f}"
                if a.v1
                else ""
            )
            print(
                f"{kind:7s} {L:7d} | {s['mean']:11.4e} {s['max']:10.3e} | {c['mean']:12.4e} {c['max']:10.3e} | "
                f"{f['mean']:11.4e} {f['max']:10.3e} | {f['mean'] / s['mean']:.3f}, {f['max'] / s['max']:.3f}{extra}",
                flush=True,
            )
    if a.json:
        with open(a.json, "w") as fh:
            json.dump({"tc": TC, "rows": rows}, fh, indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
