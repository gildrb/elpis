# Independent reference for the ext 3010 prefill attention schedule (pattn_sched.bend): causal
# attention of a prefill chunk. Row j < q_len of a chunk of q_len rows whose keys are 0 .. L - 1 sits
# at absolute position L - q_len + j and must see every key p <= that position exactly once, and no
# other key.
import Base
import ./attn_stride_spec.bend as SS

def sees(+L: Nat, +q: Nat, +j: Nat, +p: Nat) -> Bool:
  Nat.is_le(p, Nat.add(Nat.sub(L, q), j))

def once(b: Bool) -> Nat:
  SS.once(b)

# Every c < n occurs exactly once in xs
def all_once(+n: Nat, +xs: List<&2, Nat>) -> Bool:
  SS.all_once(n, xs)
