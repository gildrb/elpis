#!/usr/bin/env python3
# Copyright (c) 2026 Gil Rodrigues
"""CPU emulation of one decode-attention row through three kernels.

The row: a Qwen3.8-27B full-attention layer (6 q heads of one kv head, head_dim 256,
CQ3 K / V cache, row at absolute position L - 1), against an fp64 reference of the
same inputs:

  stock    355c6ee M = 1: Triton _paged_attn_decode_split_kernel (32-key tiles,
           num_splits / split_len from the block-table bound, acc * alpha + tl.dot)
           + _paged_attn_decode_combine_kernel (sequential fma over splits, div,
           _rot_h32)
  current  elpis ext 3006 / 3007 / 3012 attn_verify_split_k3v3 +
           attn_verify_combine_gate (64-key tiles, CTA x of 20 takes tiles x, x + 20,
           ...; MMA into the running acc; 8 warp partials summed in sequence; fma
           combine in slot order; 32-FFMA back-rotation)
  fixed    elpis ext 3030 (integer running max: exact power-of-two alpha and weights;
           64-key tile tree sum; fresh-C P V folded by one fma; pairwise-tree
           combine; two-k16-MMA back-rotation)

Arithmetic: fp16 / fp32 roundings emulated exactly (numpy casts, fma through fp64);
ex2 = exp2 in fp64 rounded to fp32; div.full / acc / lsum = fp32(rcp) then fp32
product; tensor-core mma.m16n8k16 .f32 = the project's calibrated model (Fasi,
Higham, Mikaitis, Pranesh 2021; Int8Attn/split/emu_split.py): TC=al{K}e{E} (default
al8e1): every K products (exact) plus the accumulator are aligned to the largest
exponent keeping 24 + E bits (lower bits truncated), summed exactly, result rounded
toward zero; TC=rz{K}: exact sum of K products into the accumulator, rounded toward
zero.

The pre stage (q norm / RoPE) and the output gate are common to all three
(bend/err_attn_laws.bend pre_eq) and left out: the inputs are the fp16 q head and the
cache codes / scales, the output is the fp16 attention output before the gate.

Inputs per case: random (N(0, 1) q, uniform codes, log-normal scales) and
adversarial:
  flat    q = 0: every score 0, every p equal: the longest sums (denominator, P V,
          combine)
  ramp    scores rising with the key index: the running max moves at every tile
          (rescale chains)
  peak    one key 30 log2-units above a random background: p spans the fp16 range
  offset  V codes all 7 but one bit of noise: large common value, small differences

Usage: python3 err_attn_dec_emu.py [--L 2,64,500,1281,4097,8192,32768]
       [--cases random,flat,ramp,peak,offset]
       [--seed 1] [--fp32out | --quot] [--v1] [--json OUT]
Needs numpy (any CPython 3.10+).
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING

import numpy as np

if TYPE_CHECKING:
    import numpy.typing as npt

    F16 = npt.NDArray[np.float16]
    F32 = npt.NDArray[np.float32]
    F64 = npt.NDArray[np.float64]
    I64 = npt.NDArray[np.int64]
    Fl = npt.NDArray[np.float16] | npt.NDArray[np.float32] | npt.NDArray[np.float64]

f16, f32, f64 = np.float16, np.float32, np.float64
HD, G, PAGE = 256, 6, 256
H_DIM = 32  # the Hadamard rotation size
S_E = 20  # 82 SMs // 4 kv heads (E:bc_attn.py av_splits)
SPLITS_CAP = 41  # stock: min(2 * 82 // 4, 128)
L2E = f32(np.log2(np.e))  # fp32(log2 e) = 0f3FB8AA3B
SCALE = 1.0 / 16.0  # 1 / sqrt(256)
SCALE_LOG2 = f32(
    SCALE * float(L2E)
)  # elpis scale_log2 = fp32(2^-4 log2 e) = 2^-4 fp32(log2 e)
TC = os.environ.get("TC", "al8e1")
CASES = ["random", "flat", "ramp", "peak", "offset"]
OFFSET_P = 0.5  # offset case: probability of code 7 (else 6)
COMBINE_LEVELS = 12  # binary-counter levels of the fixed combine tree


@dataclass(frozen=True)
class Out:
    """The measured output.

    fp32out: compare the fp32 rotation result, before the final fp16 store.
    quot: compare the fp32 quotient acc / lsum (rotated domain), before any output
    rounding.
    """

    fp32out: bool = False
    quot: bool = False


def out16(y: F32, out: Out) -> F16 | F32:
    """Round the output as measured.

    Args:
        y: the fp32 output.
        out: the measured output.

    Returns:
        y in fp32 under --fp32out, else in fp16.

    """
    return y.astype(f32) if out.fp32out else y.astype(f16)


def cdiv(a: int, b: int) -> int:
    """Divide rounding up.

    Args:
        a: the dividend.
        b: the divisor.

    Returns:
        ceil(a / b).

    """
    return -(-a // b)


def h32_f16() -> F16:
    """Build the fp16 normalized 32 x 32 Hadamard matrix.

    Returns:
        H32 / sqrt(32) rounded through fp32 to fp16.

    """
    h = np.ones((1, 1))
    while h.shape[0] < H_DIM:
        h = np.block([[h, h], [h, -h]])
    return (h / np.sqrt(32.0)).astype(f32).astype(f16)


H32 = h32_f16()
H32_64 = H32.astype(f64)


# ---- rounding primitives ----


def rz32(x: Fl) -> F32:
    """Round to fp32 toward zero.

    Args:
        x: the values.

    Returns:
        x rounded toward zero to fp32.

    """
    r = x.astype(f32)
    over = np.abs(r.astype(f64)) > np.abs(x)
    return np.where(over, np.nextafter(r, f32(0)), r).astype(f32)


def fma32(a: Fl, b: Fl, c: Fl) -> F32:
    """Fuse multiply-add in fp32.

    Args:
        a: the first factor.
        b: the second factor.
        c: the addend.

    Returns:
        fp32(a * b + c), one rounding.

    """
    return (a.astype(f64) * b.astype(f64) + c.astype(f64)).astype(f32)


def add32(a: Fl, b: Fl) -> F32:
    """Add in fp32.

    Args:
        a: the first addend.
        b: the second addend.

    Returns:
        fp32(a + b).

    """
    return (a.astype(f64) + b.astype(f64)).astype(f32)


def ex2(x: Fl) -> F32:
    """Raise two to x, rounded to fp32.

    Args:
        x: the exponents.

    Returns:
        fp32(2^x).

    """
    with np.errstate(over="ignore"):
        return np.exp2(x.astype(f64)).astype(f32)


def div32(a: Fl, den: Fl) -> F32:
    """Divide as div.full: fp32(rcp) then the fp32 product.

    Args:
        a: the dividend.
        den: the divisor.

    Returns:
        fp32(a * fp32(1 / den)).

    """
    r = (1.0 / den.astype(f64)).astype(f32)
    return (a.astype(f64) * r.astype(f64)).astype(f32)


def tc_steps(c: F32, a: F16, b: F16) -> F32:
    """Run the mma.m16n8k16 chain, one k16 step at a time in k order.

    C (R, D) fp32 += A (R, k) fp16 @ B (k, D) fp16.

    Args:
        c: the accumulator C.
        a: the A operand.
        b: the B operand.

    Returns:
        The accumulated C.

    """
    a64, b64 = a.astype(f64), b.astype(f64)
    k = a.shape[1]
    if TC.startswith("rz"):
        g = int(TC[2:])
        for j in range(0, k, g):
            c = rz32(c.astype(f64) + a64[:, j : j + g] @ b64[j : j + g])
        return c
    g, e = (int(x) for x in TC[2:].split("e"))
    for j in range(0, k, g):
        prods = a64[:, j : j + g, None] * b64[None, j : j + g, :]
        terms = np.concatenate([c.astype(f64)[:, None, :], prods], 1)
        mx = np.abs(terms).max(1)
        _, ex = np.frexp(mx)
        q = np.ldexp(1.0, ex - 24 - e)
        s = (np.trunc(terms / q[:, None, :]) * q[:, None, :]).sum(1)
        c = np.where(mx > 0, rz32(s), f32(0)).astype(f32)
    return c


def rot_mma(x16: F16) -> F32:
    """Rotate (R, 256) fp16 by H32 per 32-group with two k16 MMA steps from zero.

    Args:
        x16: the (R, 256) fp16 rows.

    Returns:
        The (R, 256) fp32 rotation.

    """
    rows = x16.shape[0]
    xg = x16.reshape(rows * 8, 32)
    y = tc_steps(np.zeros((rows * 8, 32), f32), xg, H32)
    return y.reshape(rows, HD)


def scores_tc(q16: F16, k16: F16) -> F32:
    """Score (R, 256) x (N, 256) by the 16-step k16 chain over dims, in key chunks.

    Args:
        q16: the (R, 256) fp16 queries.
        k16: the (N, 256) fp16 keys.

    Returns:
        The (R, N) fp32 scores.

    """
    out = np.empty((q16.shape[0], k16.shape[0]), f32)
    for c0 in range(0, k16.shape[0], 4096):
        kc = k16[c0 : c0 + 4096]
        out[:, c0 : c0 + 4096] = tc_steps(
            np.zeros((q16.shape[0], kc.shape[0]), f32), q16, kc.T
        )
    return out


# ---- inputs ----


def make_case(
    kind: str, n_keys: int, rng: np.random.Generator
) -> tuple[F16, I64, F16, I64, F16]:
    """Draw the inputs of one case.

    Args:
        kind: the case name (CASES).
        n_keys: the row length L.
        rng: the generator.

    Returns:
        q, K codes, K scales, V codes, V scales.

    """
    q = rng.standard_normal((G, HD)).astype(f16)
    kc = rng.integers(0, 8, (n_keys, HD)).astype(np.int64)
    vc = rng.integers(0, 8, (n_keys, HD)).astype(np.int64)
    ks = np.exp(rng.normal(-1.0, 0.4, (n_keys, 8))).astype(f16)
    vs = np.exp(rng.normal(-1.0, 0.4, (n_keys, 8))).astype(f16)
    if kind == "flat":
        q = np.zeros((G, HD), f16)
    elif kind == "ramp":
        # q = H32 column 0 on dims 0..31 (its H32 rotation is ~e_0), key j's dim-0
        # value grows with j: the scores rise across the row, so the running max
        # moves at every tile
        q = np.zeros((G, HD), f16)
        q[:, :32] = H32[:, 0]
        kc[:, 0] = 7
        ks[:, 0] = (8.0 + 56.0 * np.arange(n_keys) / max(n_keys, 1)).astype(f16)
    elif kind == "peak":
        # one key aligned with the rotated q (codes 7 / 0 by its sign, scale 2): ~30
        # log2 units above the rest
        j = int(rng.integers(0, n_keys))
        q = (rng.standard_normal((G, HD)) * 0.5).astype(f16)
        qr0 = (q[0].astype(f64).reshape(8, 32) @ H32_64).reshape(HD)
        kc[j] = np.where(qr0 > 0, 7, 0)
        ks[j] = f16(2.0)
    elif kind == "offset":
        vc = np.where(rng.random((n_keys, HD)) < OFFSET_P, 7, 6).astype(np.int64)
    return q, kc, ks, vc, vs


def deq16(codes: I64, scales: F16) -> F16:
    """Dequantize 3-bit codes to fp16 cache values.

    Args:
        codes: the (N, 256) codes.
        scales: the (N, 8) fp16 scales.

    Returns:
        The (N, 256) fp16 values.

    """
    s = (scales.astype(f32) * f32(0.25)).astype(f32)
    v = ((codes.astype(f32) - f32(3.5)) * np.repeat(s, 32, axis=1)).astype(f32)
    return v.astype(f16)


def reference(q: F16, k16: F16, v16: F16, out: Out) -> F64:
    """Compute the fp64 reference.

    q exact (fp16 input), K / V the cache values (fp16 dequant is exact for 3-bit
    codes x fp16 scale / 4 whenever representable; we take the fp16 cache values as
    the leaves), exact rotations and softmax.

    Args:
        q: the fp16 q head.
        k16: the fp16 keys.
        v16: the fp16 values.
        out: the measured output.

    Returns:
        The (G, 256) fp64 output.

    """
    q64 = q.astype(f64).reshape(G * 8, 32) @ H32_64
    q64 = q64.reshape(G, HD)
    s = (q64 @ k16.astype(f64).T) * SCALE
    s -= s.max(1, keepdims=True)
    p = np.exp(s)
    o = (p @ v16.astype(f64)) / p.sum(1, keepdims=True)
    if out.quot:
        return o
    return (o.reshape(G * 8, 32) @ H32_64).reshape(G, HD)


# ---- stock ----


def stock_geo(n_keys: int) -> tuple[int, int]:
    """Compute the stock split geometry.

    Args:
        n_keys: the row length L.

    Returns:
        num_splits, split_len.

    """
    bound = 4096 * cdiv(n_keys, 4096) + 1
    ns = max(1, min(SPLITS_CAP, cdiv(bound, 4 * 32)))
    return ns, cdiv(cdiv(bound, ns), 32) * 32


def tree_sum(p: Fl, offs: tuple[int, ...]) -> F32:
    """Sum rows by xor-shuffle steps in fp32.

    Args:
        p: the (R, N) values.
        offs: the xor offsets in order.

    Returns:
        The (R,) fp32 sums (lane 0).

    """
    s = p.astype(f32)
    idx = np.arange(p.shape[1])
    for off in offs:
        s = add32(s, s[:, idx ^ off])
    return s[:, 0]


Part = tuple["F32", "F32", "F32"]  # (m, l, acc) of one split / CTA


def stock_split(s: F32, v16: F16, n0: int, n1: int) -> Part:
    """Run one stock split over keys n0..n1.

    Args:
        s: the scaled scores.
        v16: the fp16 values.
        n0: the first key.
        n1: the key bound.

    Returns:
        The split's (m, l, acc).

    """
    m = np.full(G, -np.inf, f32)
    lsum = np.zeros(G, f32)
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
        lsum = fma32(lsum, alpha, tree_sum(p, (1, 4, 2, 16, 8)))
        vt = np.zeros((32, HD), f16)
        vt[: t1 - t0] = v16[t0:t1]
        acc = tc_steps((acc * alpha[:, None]).astype(f32), p.astype(f16), vt)
        m = m_new
    return m, lsum, acc


def run_stock(sc: F32, v16: F16, n_keys: int, out: Out) -> F16 | F32:
    """Run the stock split + combine kernels.

    Args:
        sc: the fp32 scores.
        v16: the fp16 values.
        n_keys: the row length L.
        out: the measured output.

    Returns:
        The measured output.

    """
    ns, sl = stock_geo(n_keys)
    s = (sc * f32(SCALE)).astype(f32)  # exact (power of two)
    parts: list[Part] = []
    for sp in range(ns):
        n0, n1 = sp * sl, min(sp * sl + sl, n_keys)
        if n0 >= n_keys:
            break
        parts.append(stock_split(s, v16, n0, n1))
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
    if out.quot:
        return o
    return out16(rot_mma(o.astype(f16)), out)


# ---- elpis (current and fixed) ----


def elpis_alpha(m: F32, m_new: F32, m_use: F32, *, fixed: bool) -> F32:
    """Compute the running-state rescale factor of one tile.

    Args:
        m: the running max before the tile.
        m_new: the running max after the tile.
        m_use: m_new with -inf replaced by 0.
        fixed: ext 3030 (exact power of two) rather than the current kernel.

    Returns:
        The fp32 alpha.

    """
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
    return alpha.astype(f32)


def elpis_weights(xt: F32, tmax: F32, m_use: F32, mode: str) -> tuple[F32, F32 | None]:
    """Compute the tile's weights p and, in mode fixed, the join factor c.

    Args:
        xt: the tile's log2-scaled scores.
        tmax: the tile's max.
        m_use: the running max with -inf replaced by 0.
        mode: the kernel (run_elpis).

    Returns:
        p, and c (mode fixed) or None.

    """
    with np.errstate(invalid="ignore"):
        if mode == "fixed":
            # p against the tile's own max (its top key exactly 1); the tile joins
            # the integer-scaled state through c = ex2(tmax - m_new) < 2
            t_use = np.where(np.isinf(tmax), f32(0), tmax).astype(f32)
            p = np.where(np.isinf(xt), f32(0), ex2((xt - t_use[:, None]).astype(f32)))
            c = np.where(
                np.isinf(tmax), f32(0), ex2((t_use - m_use).astype(f32))
            ).astype(f32)
            return p, c
        p = np.where(np.isinf(xt), f32(0), ex2((xt - m_use[:, None]).astype(f32)))
    return p, None


def elpis_tile_sum(p: F32, *, fixed: bool) -> F32:
    """Sum the tile's weights per row.

    Tile-local token u = 8 warp + 2 t + e: in-thread pair, lane xors (offsets 1, 2,
    4).

    Args:
        p: the (G, 64) weights.
        fixed: ext 3030 (one tile tree) rather than warp partials in sequence.

    Returns:
        The (G,) fp32 sums.

    """
    if fixed:
        return tree_sum(p, (1, 2, 4, 8, 16, 32))
    w8 = p.reshape(G, 8, 8)
    ws = np.stack([tree_sum(w8[:, w], (1, 2, 4)) for w in range(8)], 1)
    tsum = ws[:, 0]
    for w in range(1, 8):
        tsum = add32(tsum, ws[:, w])
    return tsum


def elpis_cta(x: F32, v16: F16, cta: int, n_keys: int, mode: str) -> Part:
    """Run one elpis split CTA over tiles cta, cta + S_E, ...

    Args:
        x: the log2-scaled scores.
        v16: the fp16 values.
        cta: the CTA index.
        n_keys: the row length L.
        mode: the kernel (run_elpis).

    Returns:
        The CTA's (m, l, acc).

    """
    fixed = mode != "current"
    m = np.full(G, -np.inf, f32)
    lsum = np.zeros(G, f32)
    acc = np.zeros((G, HD), f32)
    for i in range(cta, cdiv(n_keys, 64), S_E):
        t0, t1 = 64 * i, min(64 * i + 64, n_keys)
        xt = np.full((G, 64), -np.inf, f32)
        xt[:, : t1 - t0] = x[:, t0:t1]
        tmax = xt.max(1)
        m_new = np.maximum(m, np.floor(tmax) if fixed else tmax).astype(f32)
        m_use = np.where(np.isinf(m_new), f32(0), m_new).astype(f32)
        p, c = elpis_weights(xt, tmax, m_use, mode)
        vt = np.zeros((64, HD), f16)
        vt[: t1 - t0] = v16[t0:t1]
        tile = Tile(
            alpha=elpis_alpha(m, m_new, m_use, fixed=fixed),
            tsum=elpis_tile_sum(p, fixed=fixed),
            c=c,
            p16=p.astype(f16),
            vt=vt,
        )
        lsum, acc = elpis_fold(lsum, acc, tile, mode)
        m = m_new
    return m, lsum, acc


@dataclass(frozen=True)
class Tile:
    """One tile's contribution to the running state."""

    alpha: F32
    tsum: F32
    c: F32 | None
    p16: F16
    vt: F16


def elpis_fold(lsum: F32, acc: F32, t: Tile, mode: str) -> tuple[F32, F32]:
    """Fold one tile into the running denominator and accumulator.

    Args:
        lsum: the running denominator.
        acc: the running accumulator.
        t: the tile.
        mode: the kernel (run_elpis).

    Returns:
        The new lsum, acc.

    """
    if t.c is not None:
        pv = tc_steps(np.zeros((G, HD), f32), t.p16, t.vt)
        return (
            fma32(t.tsum, t.c, (lsum * t.alpha).astype(f32)),
            fma32(pv, t.c[:, None], (acc * t.alpha[:, None]).astype(f32)),
        )
    if mode == "v1":
        pv = tc_steps(np.zeros((G, HD), f32), t.p16, t.vt)
        return fma32(lsum, t.alpha, t.tsum), fma32(acc, t.alpha[:, None], pv)
    return (
        fma32(lsum, t.alpha, t.tsum),
        tc_steps((acc * t.alpha[:, None]).astype(f32), t.p16, t.vt),
    )


def combine_fixed(parts: list[Part], m_use: F32) -> tuple[F32, F32]:
    """Combine the CTAs by the ext 3030 pairwise tree.

    Args:
        parts: the CTAs' (m, l, acc).
        m_use: the max of the CTA maxima, -inf replaced by 0.

    Returns:
        acc, lsum.

    """
    terms: list[tuple[F32, F32]] = []
    for m_s, l_s, o_s in parts:
        w = np.exp2((m_s - m_use).astype(f64)).astype(f32)  # exact power of two
        terms.append(((o_s * w[:, None]).astype(f32), (l_s * w).astype(f32)))
    st: dict[int, tuple[F32, F32]] = {}
    n = 0
    for term in terms:  # binary counter = fixed aligned tree
        ta, tc = term
        k = 0
        while (n >> k) & 1:
            pa, pc = st[k]
            ta, tc = add32(pa, ta), add32(pc, tc)
            k += 1
        st[k] = (ta, tc)
        n += 1
    acc = np.zeros((G, HD), f32)
    lsum = np.zeros(G, f32)
    for k in range(COMBINE_LEVELS):
        if (n >> k) & 1:
            acc, lsum = add32(st[k][0], acc), add32(st[k][1], lsum)
    return acc, lsum


def combine_current(parts: list[Part], m_use: F32) -> tuple[F32, F32]:
    """Combine the CTAs by fma in slot order.

    Args:
        parts: the CTAs' (m, l, acc).
        m_use: the max of the CTA maxima, -inf replaced by 0.

    Returns:
        acc, lsum.

    """
    acc = np.zeros((G, HD), f32)
    lsum = np.zeros(G, f32)
    for m_s, l_s, o_s in parts:
        w = np.where(np.isinf(m_s), f32(-1), ex2((m_s - m_use).astype(f32)))
        acc = fma32(o_s, w[:, None], acc)
        lsum = fma32(l_s, w, lsum)
    return acc, lsum


def run_elpis(sc: F32, v16: F16, n_keys: int, mode: str, out: Out) -> F16 | F32:
    """Run the elpis split + combine kernels.

    mode: 'current' (ext 3006 / 3007 / 3012), 'fixed' (ext 3030), 'v1' (rejected 3030
    draft: p taken against the integer running max, so the row's top key has p in
    [1, 2) and pays an fp16 rounding).

    Args:
        sc: the fp32 scores.
        v16: the fp16 values.
        n_keys: the row length L.
        mode: the kernel.
        out: the measured output.

    Returns:
        The measured output.

    """
    fixed = mode != "current"
    x = (sc * SCALE_LOG2).astype(f32)  # FMUL by scale_log2
    parts = [
        elpis_cta(x, v16, cta, n_keys, mode)
        for cta in range(min(S_E, cdiv(n_keys, 64)))
    ]
    mmax = np.max([p[0] for p in parts], axis=0)
    m_use = np.where(np.isinf(mmax), f32(0), mmax).astype(f32)
    acc, lsum = (combine_fixed if fixed else combine_current)(parts, m_use)
    o32 = div32(acc, np.where(lsum == 0, f32(1), lsum)[:, None])
    if out.quot:
        return o32
    o = o32.astype(f16)
    if fixed:
        return out16(rot_mma(o), out)
    y = np.zeros((G * 8, 32), f32)
    og = o.reshape(G * 8, 32)
    for i in range(32):
        y = fma32(og[:, i : i + 1].astype(f32), H32[i : i + 1, :].astype(f32), y)
    return out16(y.reshape(G, HD), out)


def stats(o: F16 | F32, ref: F64) -> dict[str, float]:
    """Summarize the absolute error against the reference.

    Args:
        o: the output.
        ref: the fp64 reference.

    Returns:
        mean, max and rms of |o - ref|.

    """
    e = np.abs(o.astype(f64) - ref)
    return {
        "mean": float(e.mean()),
        "max": float(e.max()),
        "rms": float(np.sqrt((e * e).mean())),
    }


def case_stats(
    kind: str, n_keys: int, seed: int, out: Out, *, v1: bool
) -> dict[str, dict[str, float]]:
    """Run one case through every kernel.

    Args:
        kind: the case name.
        n_keys: the row length L.
        seed: the seed.
        out: the measured output.
        v1: also run the rejected draft.

    Returns:
        The error stats per kernel.

    """
    rng = np.random.default_rng([seed, n_keys, CASES.index(kind)])
    q, kc, ks, vc, vs = make_case(kind, n_keys, rng)
    k16, v16 = deq16(kc, ks), deq16(vc, vs)
    ref = reference(q, k16, v16, out)
    sc = scores_tc(rot_mma(q).astype(f16), k16)
    res = {
        "stock": stats(run_stock(sc, v16, n_keys, out), ref),
        "current": stats(run_elpis(sc, v16, n_keys, "current", out), ref),
        "fixed": stats(run_elpis(sc, v16, n_keys, "fixed", out), ref),
    }
    if v1:
        res["v1"] = stats(run_elpis(sc, v16, n_keys, "v1", out), ref)
    return res


def run_case(
    kind: str, n_keys: int, seed: int, out: Out, *, v1: bool
) -> dict[str, object]:
    """Run one case through every kernel and print its row.

    Args:
        kind: the case name.
        n_keys: the row length L.
        seed: the seed.
        out: the measured output.
        v1: also run the rejected draft.

    Returns:
        The case's JSON row.

    """
    r = case_stats(kind, n_keys, seed, out, v1=v1)
    s, c, f = r["stock"], r["current"], r["fixed"]
    extra = ""
    if v1:
        r1 = r["v1"]
        extra = f" | {r1['mean'] / s['mean']:.3f}, {r1['max'] / s['max']:.3f}"
    sys.stdout.write(
        f"{kind:7s} {n_keys:7d} | {s['mean']:11.4e} {s['max']:10.3e} | "
        f"{c['mean']:12.4e} {c['max']:10.3e} | "
        f"{f['mean']:11.4e} {f['max']:10.3e} | "
        f"{f['mean'] / s['mean']:.3f}, {f['max'] / s['max']:.3f}{extra}\n"
    )
    sys.stdout.flush()
    return {"case": kind, "L": n_keys, **r}


def main(argv: list[str]) -> int:
    """Run the emulation.

    Args:
        argv: the command line.

    Returns:
        The exit status.

    """
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
    out = Out(fp32out=a.fp32out, quot=a.quot)
    if out.quot:
        what = "fp32 quotient acc / lsum, rotated domain"
    elif out.fp32out:
        what = "fp32 rotation result"
    else:
        what = "fp16 attention output"
    sys.stdout.write(
        f"TC model {TC}; errors |out - fp64 ref| over 6 heads x 256 dims "
        f"({what}, before the gate)\n"
    )
    sys.stdout.write(
        f"{'case':7s} {'L':>7s} | {'stock mean':>11s} {'max':>10s} | "
        f"{'current mean':>12s} {'max':>10s} | {'fixed mean':>11s} {'max':>10s} | "
        "fixed/stock mean, max" + (" | v1/stock mean, max" if a.v1 else "") + "\n"
    )
    rows = [
        run_case(kind, int(x), a.seed, out, v1=a.v1)
        for kind in a.cases.split(",")
        for x in a.L.split(",")
    ]
    if a.json:
        with Path(a.json).open("w", encoding="utf-8") as fh:
            json.dump({"tc": TC, "rows": rows}, fh, indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
