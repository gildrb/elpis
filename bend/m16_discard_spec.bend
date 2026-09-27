# Independent reference for ext 2113's split-K slot discard (m16_discard.bend): the workspace as nested arrays of
# 128-byte lines, without the kernels' address expressions, and what a load of a line must observe.
#   - a float at offset x (floats from the 128-byte-aligned workspace base) lies in line x / 32 (128 B = 32 floats);
#   - the partial-slot workspace is slot s (16 token rows) x row r (512 columns = 4 chunks of 128) x chunk ch (4 lines
#     of 32 floats) x line q: line ((s * 16 + r) * 4 + ch) * 4 + q, cell (s * 16 + r) * 512 + col;
#   - contributor c < mc of group g owns slot g * mc + c of its workspace (m16g: one workspace; 8201 / tail: gate+up
#     then down (then o_proj), laid out one after the other);
#   - a load in launch n at a step between the launch's stores and its end must observe launch n's stored value, or
#     for slot 0 after the finish's sum store (step 3), that sum: never an earlier launch's value and never a
#     discarded (undefined) line, whether the switch is on or off.
import Base
import ./m16_discard.bend as Impl

def line_of(+x: Nat) -> Nat:
  Nat.div(x, 32n)

def jline(+s: Nat, +r: Nat, +ch: Nat, +q: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(s, 16n), r), 4n), ch), 4n), q)

def cell(+s: Nat, +r: Nat, +col: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.add(Nat.mul(s, 16n), r), 512n), col)

def slot_of(+g: Nat, +mc: Nat, +c: Nat) -> Nat:
  Nat.add(Nat.mul(g, mc), c)

def want_pick(early: Bool, zero: Bool, +n: Nat) -> Impl.Ev:
  match early:
    case True{}:
      Impl.Wr{n}
    case False{}:
      match zero:
        case True{}:
          Impl.Sum0{n}
        case False{}:
          Impl.Wr{n}

# the value a load at step st (1..7) of launch n observes: the launch's store before the sum store (steps 1..3),
# after it the sum on slot 0 and the store elsewhere
def want(zero: Bool, +n: Nat, +st: Nat) -> Impl.Ev:
  want_pick(Nat.is_lt(st, 4n), zero, n)

# an accepted EXL3_SPLITK_DISCARD value is 0 or 1
def knob_ok(k: Impl.Knob) -> Bool:
  match k:
    case Impl.Ok{v}:
      Nat.is_le(v, 1n)
    case Impl.Refused{}:
      True{}
