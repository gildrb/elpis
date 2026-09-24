# Laws of the DRAM roofline model of one verify round (roofline.bend, generated
# from the safetensors headers) against its independent config-shape
# enumeration (roofline_spec.bend), plus the bandwidth-ceiling algebra over Nat
# (roofline_bin.bend). What is proven is the Bend model: byte counts under the
# stated counting rule, and arithmetic consequences for ANY bandwidth, time and
# rate. Bandwidth, kernel times and tok/s are measured inputs, not proven.
import Base
import ./roofline_bin.bend as N
import ./roofline.bend as Impl
import ./roofline_spec.bend as Spec

# (a) floor_exact: the header-constant closed form equals the per-tensor,
# per-layer enumeration from the config, as a linear form, hence at every
# depth d, committed count c and draft window read w.
law floor_form:
  {Impl.round() == Spec.round() : N.Form}

law floor_exact:
  for +d: N.Bin
  for +c: N.Bin
  for +w: N.Bin
  {N.Form.at(Impl.round(), d, c, w) == N.Form.at(Spec.round(), d, c, w) : N.Bin}

# The 18 kernel-trace-3 bucket phases partition the round's bytes exactly
# (no byte counted twice or dropped), at every (d, c, w).
law phases_partition:
  for +d: N.Bin
  for +c: N.Bin
  for +w: N.Bin
  {N.Form.at(N.Form.sum(Impl.phases()), d, c, w) == N.Form.at(Impl.round(), d, c, w) : N.Bin}

# (b) ceiling: for any bandwidth bw and unit u, a schedule whose phases each
# move their bytes no faster than bw (bytes * u <= time * bw) and whose byte
# counts sum to the round's total takes total time >= total / bw.
law ceiling:
  for +ps: List<&2, N.Phase>
  for +bw: Nat
  for +u: Nat
  for +total: Nat
  for +fits: {N.Sched.fits(ps, bw, u) == True{} : Bool}
  for part: {N.Sched.bytes(ps) == total : Nat}
  {Nat.is_le(Nat.mul(total, u), Nat.mul(N.Sched.time(ps), bw)) == True{} : Bool}

# (c) toks_ceiling: a round moving B bytes in time T within bandwidth bw
# (B * u <= T * bw) that sustains rate r for tm tokens per round (r * T <=
# tm * s, s: time units per rate unit) satisfies tokens * BW >= tok_s * bytes:
#   r * B * u <= tm * s * bw.
law toks_ceiling:
  for +B: Nat
  for +bw: Nat
  for +u: Nat
  for +T: Nat
  for +tm: Nat
  for +r: Nat
  for +s: Nat
  for fits: {Nat.is_le(Nat.mul(B, u), Nat.mul(T, bw)) == True{} : Bool}
  for rate: {Nat.is_le(Nat.mul(r, T), Nat.mul(tm, s)) == True{} : Bool}
  {Nat.is_le(Nat.mul(Nat.mul(r, B), u), Nat.mul(Nat.mul(tm, s), bw)) == True{} : Bool}

# A claimed rate above the ceiling is refuted: no round time T admits it.
law toks_refuted:
  for +B: Nat
  for +bw: Nat
  for +u: Nat
  for +T: Nat
  for +tm: Nat
  for +r: Nat
  for +s: Nat
  for above: {Nat.is_lt(Nat.mul(Nat.mul(tm, s), bw), Nat.mul(Nat.mul(r, B), u)) == True{} : Bool}
  for fits: {Nat.is_le(Nat.mul(B, u), Nat.mul(T, bw)) == True{} : Bool}
  for rate: {Nat.is_le(Nat.mul(r, T), Nat.mul(tm, s)) == True{} : Bool}
  Empty

# The printed ceiling is sound: every sustainable rate is at most
# Ceil.rate (floor division), so a claim above the printed value is refuted.
law ceiling_rate:
  for +B: Nat
  for +bw: Nat
  for +u: Nat
  for +T: Nat
  for +tm: Nat
  for +r: Nat
  for +s: Nat
  for pos: {Nat.is_lt(0n, Nat.mul(B, u)) == True{} : Bool}
  for fits: {Nat.is_le(Nat.mul(B, u), Nat.mul(T, bw)) == True{} : Bool}
  for rate: {Nat.is_le(Nat.mul(r, T), Nat.mul(tm, s)) == True{} : Bool}
  {Nat.is_le(r, N.Ceil.rate(tm, s, bw, B, u)) == True{} : Bool}

# (d) monotone in depth: every byte form with Nat coefficients (the round's
# included) moves no fewer bytes at a deeper context, at a fixed committed count.
law monotone_depth:
  for +l: N.Lin
  for +d: Nat
  for +e: Nat
  for +c: Nat
  {Nat.is_le(N.Lin.eval(l, d, c), N.Lin.eval(l, Nat.add(d, e), c)) == True{} : Bool}

# (e) ledger: when every phase's floor is within its measurement, the losses
# (measured - floor) of the phases sum to measured - floor of the round.
law ledger:
  for +rs: List<&2, N.Row>
  for +ok: {N.Ledger.valid(rs) == True{} : Bool}
  {N.Ledger.loss(rs) == Nat.sub(N.Ledger.meas(rs), N.Ledger.floor(rs)) : Nat}
