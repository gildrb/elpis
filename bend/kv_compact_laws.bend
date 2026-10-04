# Obligations for ext 3013 (kv_compact.bend: kv_moves, the read-all-then-write kernel and the host checks) against the
# chain-verify result and the sequential ascending copy (kv_compact_spec.bend). Domain: every legal accepted path of the
# 8-row window (0 followed by an ascending subset of rows 1 .. 7, enumerated by m < 128 through Spec.path_of), logical
# window slots (phys is injective by the distinct-page check). Values are opaque row identities.
import Base
import ./kv_compact.bend as Impl
import ./kv_compact_spec.bend as Spec

# For every legal path: the moves kv_moves derives pass the extension's checks (src != dst, distinct destinations, no
# source an earlier destination); the kernel (every source read before any destination is written) leaves the window
# exactly as the sequential ascending copy does; and slots 0 .. count - 1 then hold the path rows P[0] .. P[count - 1],
# which is what a chain verify of the path writes there.
law commit_moves:
  for +m: Nat
  for mb: {Nat.is_lt(m, 128n) == True{} : Bool}
  {Impl.checks(Impl.kv_moves(Spec.path_of(m))) == True{} : Bool} &
  {Impl.kernel(Spec.window(), Impl.kv_moves(Spec.path_of(m))) == Spec.seq_copy(Impl.kv_moves(Spec.path_of(m)), Spec.window()) : List<&2, Nat>} &
  {List.take(&2, Nat, Impl.kernel(Spec.window(), Impl.kv_moves(Spec.path_of(m))), List.length(&2, Nat, Spec.path_of(m))) == Spec.path_of(m) : List<&2, Nat>}
