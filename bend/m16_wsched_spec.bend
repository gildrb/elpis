# Independent reference vocabulary for ext 8205's slot-weighted schedule tables (bend/m16_wsched.bend):
# half-open ranges and the byte extent of a partial slot of the m16 workspace. Ownership, contributors
# and counter events use the shared specs (gemm_m16_wpart_spec's owns / owners / touches /
# touch_count, mlp_m16_sched_spec's counter events, tail_m16_sched_spec's event projections bars /
# works / syncs); nothing here uses the partition formulas (start, owner, max_contrib) that the laws
# compare against.
import Base

# x lies in the half-open range [lo, lo + len).
def in_range(+x: Nat, +lo: Nat, +len: Nat) -> Bool:
  Bool.and(Nat.is_le(lo, x), Nat.is_lt(x, Nat.add(lo, len)))

# One past the last byte of partial slot i, slots of `floats` fp32 values laid out from byte 0.
def slot_end(+i: Nat, +floats: Nat) -> Nat:
  Nat.mul(Nat.mul(1n+i, floats), 4n)
