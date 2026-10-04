# Proof of kv_compact_laws.bend (ext 3013 commit moves): the 128 legal paths are checked by evaluation (kc_all), and a
# per-path boolean check is turned into the three stated facts (kc_beq_ok: boolean list equality is equality).
import Base
import ./kv_compact.bend as Impl
import ./kv_compact_spec.bend as Spec
import ./kv_compact_laws.bend as Laws
import ./gemm_m16_partition_proof.bend as Ar

def kc_beq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, ys2}:
      False{}
    case Con{x, xs2} Nil{}:
      False{}
    case Con{x, xs2} Con{y, ys2}:
      Bool.and(Nat.is_eq(x, y), kc_beq(xs2, ys2))

def kc_beq_ok(xs: List<&2, Nat>, ys: List<&2, Nat>, h: {kc_beq(xs, ys) == True{} : Bool}) -> {xs == ys : List<&2, Nat>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys2}:
      Empty.absurd({Nil{} == Con{y, ys2} : List<&2, Nat>}, Ar.ar_false_true(h))
    case Con{x, xs2} Nil{}:
      Empty.absurd({Con{x, xs2} == Nil{} : List<&2, Nat>}, Ar.ar_false_true(h))
    case Con{+x, +xs2} Con{+y, +ys2}:
      +hh = h
      +ex = Ar.ar_eq_true(x, y, Ar.ar_and_l(Nat.is_eq(x, y), kc_beq(xs2, ys2), hh))
      +et = kc_beq_ok(xs2, ys2, Ar.ar_and_r(Nat.is_eq(x, y), kc_beq(xs2, ys2), hh))
      Equal.trans(List<&2, Nat>, Con{x, xs2}, Con{y, xs2}, Con{y, ys2},
        Equal.cong(Nat, List<&2, Nat>, z => Con{z, xs2}, x, y, ex),
        Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Con{y, z}, xs2, ys2, et))

def kc_ck(+m: Nat) -> Bool:
  Bool.and(Impl.checks(Impl.kv_moves(Spec.path_of(m))),
    Bool.and(kc_beq(Impl.kernel(Spec.window(), Impl.kv_moves(Spec.path_of(m))), Spec.seq_copy(Impl.kv_moves(Spec.path_of(m)), Spec.window())),
      kc_beq(List.take(&2, Nat, Impl.kernel(Spec.window(), Impl.kv_moves(Spec.path_of(m))), List.length(&2, Nat, Spec.path_of(m))), Spec.path_of(m))))

def kc_all(+n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+k:
      Bool.and(kc_ck(k), kc_all(k))

# all 128 legal paths, by evaluation
def kc_all128() -> {kc_all(128n) == True{} : Bool}:
  {==}

def kc_from(+d: Nat, +m: Nat, h: {kc_all(Nat.add(d, 1n+m)) == True{} : Bool}) -> {kc_ck(m) == True{} : Bool}:
  match d:
    case 0n:
      Ar.ar_and_l(kc_ck(m), kc_all(m), h)
    case 1n+e:
      kc_from(e, m, Ar.ar_and_r(kc_ck(Nat.add(e, 1n+m)), kc_all(Nat.add(e, 1n+m)), h))

def Laws.commit_moves(m, mb):
  +d = Nat.sub(128n, 1n+m)
  +le = Ar.ard_rt(Nat.is_lt(m, 128n), Nat.is_le(1n+m, 128n), Ar.ar_lt_succ_le(m, 128n), mb)
  +e128 = Equal.trans(Nat, Nat.add(d, 1n+m), Nat.add(1n+m, d), 128n, Ar.ar_add_comm(d, 1n+m), Ar.ar_sub_add(128n, 1n+m, le))
  +all = Equal.trans(Bool, kc_all(Nat.add(d, 1n+m)), kc_all(128n), True{}, Equal.cong(Nat, Bool, z => kc_all(z), Nat.add(d, 1n+m), 128n, e128), kc_all128())
  +ck = kc_from(d, m, all)
  +A = Impl.checks(Impl.kv_moves(Spec.path_of(m)))
  +K = Impl.kernel(Spec.window(), Impl.kv_moves(Spec.path_of(m)))
  +B = kc_beq(K, Spec.seq_copy(Impl.kv_moves(Spec.path_of(m)), Spec.window()))
  +C = kc_beq(List.take(&2, Nat, K, List.length(&2, Nat, Spec.path_of(m))), Spec.path_of(m))
  +bc = Ar.ar_and_r(A, Bool.and(B, C), ck)
  (Ar.ar_and_l(A, Bool.and(B, C), ck),
   kc_beq_ok(K, Spec.seq_copy(Impl.kv_moves(Spec.path_of(m)), Spec.window()), Ar.ar_and_l(B, C, bc)),
   kc_beq_ok(List.take(&2, Nat, K, List.length(&2, Nat, Spec.path_of(m))), Spec.path_of(m), Ar.ar_and_r(B, C, bc)))
