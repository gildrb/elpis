# Precision classes of the decode GEMMs and their order (shared vocabulary of
# bend/precision_stock.bend, bend/precision_elpis.bend and bend/precision_laws.bend).
#
# The model is a Nat model of ACCUMULATION SCHEDULES, not of floating-point values: a class
# records how one output element's dot product is accumulated (activation precision, the length
# of every fp16 accumulation run before it is folded into fp32, and the precision of the partial
# sums that cross thread blocks). It never computes a float, a rounding error or an error bound.
#
# The order encoded here (the contract, stated by the user for elpis):
#   int8 activations  <  fp16 accumulation in runs of n k-values folded into fp32
#                        (a smaller n is more precise)  <  fp32 accumulation throughout.
# Two refinements inside the fp16-run class, both monotone in the same direction:
#   - a schedule whose LONGEST run is shorter is more precise (worst case, `ge`);
#   - partials that cross thread blocks kept in fp32 are at least as precise as partials rounded to
#     fp16 between blocks (exl3_gemm_inner.cuh:692-705 read_sum_gl / 724-735 write_sum_gl in fp16 when
#     the output is fp16).
import Base

# One output element's accumulation schedule.
#   Int8{}            the activations are quantized to int8 before the dot product (exl3_gemv_int8).
#   Runs{lo, hi, p32} fp16 activations, fp16 MMA accumulation in runs of lo .. hi k-values (every run
#                     of every output element has a length in [lo, hi]), each run folded into fp32;
#                     p32: partial sums handed between thread blocks stay fp32 (True) or are stored as
#                     fp16 (False).
#   Fp32{}            fp32 accumulation throughout (no fp16 run).
type Acc is Data:
  Int8{}
  Runs{lo: Nat, hi: Nat, p32: Bool}
  Fp32{}

# p32 order: fp32 partials (True) >= fp16 partials (False).
def p32_ge(a: Bool, b: Bool) -> Bool:
  Bool.or(a, Bool.not(b))

# Worst-case order: a is at least as precise as b.
#   anything >= Int8; Fp32 >= anything; Int8 >= only Int8; Runs >= Fp32 never;
#   Runs{_, h1, p1} >= Runs{_, h2, p2} iff h1 <= h2 (a's longest fp16 run is no longer) and p1 >= p2.
def ge(a: Acc, b: Acc) -> Bool:
  match a b:
    case Int8{} Int8{}:
      True{}
    case Int8{} Runs{l2, h2, p2}:
      False{}
    case Int8{} Fp32{}:
      False{}
    case Runs{l1, h1, p1} Int8{}:
      True{}
    case Runs{l1, h1, p1} Runs{l2, h2, p2}:
      Bool.and(Nat.is_le(h1, h2), p32_ge(p1, p2))
    case Runs{l1, h1, p1} Fp32{}:
      False{}
    case Fp32{} _:
      True{}

# Element-wise order: every fp16 run of a is no longer than every fp16 run of b (a's longest run
# <= b's shortest run), so for EVERY output element a's schedule is at least as precise as b's.
# Implies ge (law dom_implies_ge). Not reflexive on Runs with lo < hi: identical kernels are
# compared by identity instead (Same in bend/precision_laws.bend).
def dom(a: Acc, b: Acc) -> Bool:
  match a b:
    case Int8{} Int8{}:
      True{}
    case Int8{} Runs{l2, h2, p2}:
      False{}
    case Int8{} Fp32{}:
      False{}
    case Runs{l1, h1, p1} Int8{}:
      True{}
    case Runs{l1, h1, p1} Runs{l2, h2, p2}:
      Bool.and(Nat.is_le(h1, l2), p32_ge(p1, p2))
    case Runs{l1, h1, p1} Fp32{}:
      False{}
    case Fp32{} _:
      True{}

# Rank of the three coarse classes (int8 < fp16 runs < fp32), for the order statement.
def rank(a: Acc) -> Nat:
  match a:
    case Int8{}:
      0n
    case Runs{l, h, p}:
      1n
    case Fp32{}:
      2n

def show_bool(b: Bool) -> String:
  match b:
    case True{}:
      "fp32"
    case False{}:
      "fp16"

def show(a: Acc) -> String:
  match a:
    case Int8{}:
      "int8 activations"
    case Runs{lo, hi, p}:
      "fp16 runs " ++ Nat.show(lo) ++ ".." ++ Nat.show(hi) ++ " k-values, fp32 fold, " ++ show_bool(p) ++ " block partials"
    case Fp32{}:
      "fp32 accumulation"

# Well-formed class: lo <= hi for runs.
def wf(a: Acc) -> Bool:
  match a:
    case Int8{}:
      True{}
    case Runs{lo, hi, p}:
      Nat.is_le(lo, hi)
    case Fp32{}:
      True{}
