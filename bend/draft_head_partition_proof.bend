# Proof of the draft-head tile partition law (draft_head_partition_laws.bend) about the Bend model
# draft_head_partition.bend. Structural evidence only: no unsafe definitions, axioms, holes, foreign
# proof code or answer tables. Every def precedes its uses.
#
# Idea: a 16-warp block b of a G-block grid walks exactly the tiles that two 8-warp finisher blocks
# 2 b (warps 0..7) and 2 b + 1 (warps 8..15) of a 2 G-block grid walk in the m16 finisher loop
# (gemm_m16_partition.bend, jobloop): start warp + 16 b = w' + 8 (2 b + h) and stride 16 G =
# 8 (2 G). Hit counts therefore agree block pair by block pair, and the proven m16 law
# finish_jobs_once (every job < J visited exactly once, none past the end) gives the result.
import Base
import ./draft_head_partition.bend as Impl
import ./draft_head_partition_spec.bend as Spec
import ./draft_head_partition_laws.bend as Laws
import ./gemm_m16_partition.bend as M16
import ./gemm_m16_partition_spec.bend as MS
import ./gemm_m16_partition_laws.bend as ML
import ./gemm_m16_partition_proof.bend as MP

# ==== arithmetic ====

# c * 16 == (c + c) * 8
def dh_q(+c: Nat) -> {Nat.mul(c, 16n) == Nat.mul(Nat.add(c, c), 8n) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), MP.ar_add_succ_r(p, p)) : {Nat.mul(1n+p, 16n) == Nat.mul(1n+_, 8n) : Nat}
      %dh_q(p) : {Nat.add(16n, Nat.mul(p, 16n)) == Nat.add(16n, _) : Nat}
      {==}

# 16 * c == 8 * (c + c)
def dh_m16(+c: Nat) -> {Nat.mul(16n, c) == Nat.mul(8n, Nat.add(c, c)) : Nat}:
  Equal.trans(Nat, Nat.mul(16n, c), Nat.mul(c, 16n), Nat.mul(8n, Nat.add(c, c)),
    MP.ar_mul_comm(16n, c),
    Equal.trans(Nat, Nat.mul(c, 16n), Nat.mul(Nat.add(c, c), 8n), Nat.mul(8n, Nat.add(c, c)),
      dh_q(c), MP.ar_mul_comm(Nat.add(c, c), 8n)))

# w + (8 + z) == (8 + w) + z
def dh_s8(+w: Nat, +z: Nat) -> {Nat.add(w, Nat.add(8n, z)) == Nat.add(Nat.add(8n, w), z) : Nat}:
  match w:
    case 0n:
      {==}
    case 1n+p:
      %dh_s8(p, z) : {1n+Nat.add(p, Nat.add(8n, z)) == 1n+_ : Nat}
      {==}

# (b + b) > 0 for b > 0
def dh_grid2(G: Nat, grid: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.add(G, G)) == True{} : Bool}:
  match G:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.add(0n, 0n)) == True{} : Bool}, MP.ar_false_true(grid))
    case 1n+p:
      {==}

# ==== the two specs' bit / member agree ====

def dh_bit_v(v: Bool) -> {MS.bit(v) == Spec.bit(v) : Nat}:
  match v:
    case True{}:
      {==}
    case False{}:
      {==}

def dh_bit_or(e: Bool, -xs: List<&2, Nat>, -x: Nat,
    ih: {Spec.bit(Spec.member(xs, x)) == MS.bit(MS.member(xs, x)) : Nat})
  -> {Spec.bit(Bool.or(e, Spec.member(xs, x))) == MS.bit(Bool.or(e, MS.member(xs, x))) : Nat}:
  match e:
    case True{}:
      {==}
    case False{}:
      ih

def dh_bit(+xs: List<&2, Nat>, +x: Nat) -> {Spec.bit(Spec.member(xs, x)) == MS.bit(MS.member(xs, x)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +y <> rest:
      dh_bit_or(Nat.is_eq(y, x), rest, x, dh_bit(rest, x))

# ==== a 16-warp block is an 8-warp block pair ====

# Warp w < 8 of block c walks the finisher tiles of warp w of block 2 c (grid 2 G).
def dh_tiles_lo(+c: Nat, +w: Nat, +G: Nat, +n: Nat)
  -> {Impl.tiles(c, w, G, n) == M16.jobloop(Nat.add(c, c), w, Nat.add(G, G), n) : List<&2, Nat>}:
  %dh_m16(c) : {Impl.tiles(c, w, G, n) == M16.jobloop.go(1n+n, Nat.is_lt(Nat.add(w, _), n), Nat.add(w, _), Nat.mul(8n, Nat.add(G, G)), n) : List<&2, Nat>}
  %dh_m16(G) : {Impl.tiles(c, w, G, n) == M16.jobloop.go(1n+n, Nat.is_lt(Nat.add(w, Nat.mul(16n, c)), n), Nat.add(w, Nat.mul(16n, c)), _, n) : List<&2, Nat>}
  {==}

# Warp 8 + w of block c walks the finisher tiles of warp w of block 2 c + 1 (grid 2 G).
def dh_tiles_hi(+c: Nat, +w: Nat, +G: Nat, +n: Nat)
  -> {Impl.tiles(c, Nat.add(8n, w), G, n) == M16.jobloop(1n+Nat.add(c, c), w, Nat.add(G, G), n) : List<&2, Nat>}:
  %Equal.sym(Nat, Nat.mul(8n, 1n+Nat.add(c, c)), Nat.add(8n, Nat.mul(8n, Nat.add(c, c))), MP.ar_mul_succ_r(8n, Nat.add(c, c))) : {Impl.tiles(c, Nat.add(8n, w), G, n) == M16.jobloop.go(1n+n, Nat.is_lt(Nat.add(w, _), n), Nat.add(w, _), Nat.mul(8n, Nat.add(G, G)), n) : List<&2, Nat>}
  %dh_m16(c) : {Impl.tiles(c, Nat.add(8n, w), G, n) == M16.jobloop.go(1n+n, Nat.is_lt(Nat.add(w, Nat.add(8n, _)), n), Nat.add(w, Nat.add(8n, _)), Nat.mul(8n, Nat.add(G, G)), n) : List<&2, Nat>}
  %Equal.sym(Nat, Nat.add(w, Nat.add(8n, Nat.mul(16n, c))), Nat.add(Nat.add(8n, w), Nat.mul(16n, c)), dh_s8(w, Nat.mul(16n, c))) : {Impl.tiles(c, Nat.add(8n, w), G, n) == M16.jobloop.go(1n+n, Nat.is_lt(_, n), _, Nat.mul(8n, Nat.add(G, G)), n) : List<&2, Nat>}
  %dh_m16(G) : {Impl.tiles(c, Nat.add(8n, w), G, n) == M16.jobloop.go(1n+n, Nat.is_lt(Nat.add(Nat.add(8n, w), Nat.mul(16n, c)), n), Nat.add(Nat.add(8n, w), Nat.mul(16n, c)), _, n) : List<&2, Nat>}
  {==}

def dh_hit_lo(+c: Nat, +w: Nat, +x: Nat, +G: Nat, +n: Nat)
  -> {Spec.bit(Spec.member(Impl.tiles(c, w, G, n), x)) ==
      MS.bit(MS.member(M16.jobloop(Nat.add(c, c), w, Nat.add(G, G), n), x)) : Nat}:
  %dh_tiles_lo(c, w, G, n) : {Spec.bit(Spec.member(Impl.tiles(c, w, G, n), x)) == MS.bit(MS.member(_, x)) : Nat}
  dh_bit(Impl.tiles(c, w, G, n), x)

def dh_hit_hi(+c: Nat, +w: Nat, +x: Nat, +G: Nat, +n: Nat)
  -> {Spec.bit(Spec.member(Impl.tiles(c, Nat.add(8n, w), G, n), x)) ==
      MS.bit(MS.member(M16.jobloop(1n+Nat.add(c, c), w, Nat.add(G, G), n), x)) : Nat}:
  %dh_tiles_hi(c, w, G, n) : {Spec.bit(Spec.member(Impl.tiles(c, Nat.add(8n, w), G, n), x)) == MS.bit(MS.member(_, x)) : Nat}
  dh_bit(Impl.tiles(c, Nat.add(8n, w), G, n), x)

# Warps w < k of block c == finisher warps w < k of block 2 c.
def dh_warp_lo(+k: Nat, +c: Nat, +x: Nat, +G: Nat, +n: Nat)
  -> {Impl.warp_hits(k, c, x, G, n) == M16.warp_hits(k, Nat.add(c, c), x, Nat.add(G, G), n) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+w:
      +w1 = w
      MP.p8_add_cong(Impl.warp_hits(w1, c, x, G, n), M16.warp_hits(w1, Nat.add(c, c), x, Nat.add(G, G), n),
        Spec.bit(Spec.member(Impl.tiles(c, w1, G, n), x)),
        MS.bit(MS.member(M16.jobloop(Nat.add(c, c), w1, Nat.add(G, G), n), x)),
        dh_warp_lo(w1, c, x, G, n), dh_hit_lo(c, w1, x, G, n))

# Hits of the warps 8 .. 8 + k - 1 of block c.
def dh_hi_sum(+k: Nat, +c: Nat, +x: Nat, +G: Nat, +n: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+w:
      Nat.add(dh_hi_sum(w, c, x, G, n), Spec.bit(Spec.member(Impl.tiles(c, Nat.add(8n, w), G, n), x)))

def dh_hi_eq(+k: Nat, +c: Nat, +x: Nat, +G: Nat, +n: Nat)
  -> {dh_hi_sum(k, c, x, G, n) == M16.warp_hits(k, 1n+Nat.add(c, c), x, Nat.add(G, G), n) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+w:
      +w1 = w
      MP.p8_add_cong(dh_hi_sum(w1, c, x, G, n), M16.warp_hits(w1, 1n+Nat.add(c, c), x, Nat.add(G, G), n),
        Spec.bit(Spec.member(Impl.tiles(c, Nat.add(8n, w1), G, n), x)),
        MS.bit(MS.member(M16.jobloop(1n+Nat.add(c, c), w1, Nat.add(G, G), n), x)),
        dh_hi_eq(w1, c, x, G, n), dh_hit_hi(c, w1, x, G, n))

# warps < 8 + k == warps < 8, then warps 8 .. 8 + k - 1
def dh_split(+k: Nat, +c: Nat, +x: Nat, +G: Nat, +n: Nat)
  -> {Impl.warp_hits(Nat.add(8n, k), c, x, G, n) ==
      Nat.add(Impl.warp_hits(8n, c, x, G, n), dh_hi_sum(k, c, x, G, n)) : Nat}:
  match k:
    case 0n:
      Equal.sym(Nat, Nat.add(Impl.warp_hits(8n, c, x, G, n), 0n), Impl.warp_hits(8n, c, x, G, n),
        MP.ar_add_zero_r(Impl.warp_hits(8n, c, x, G, n)))
    case 1n+w:
      +w1 = w
      +a = Impl.warp_hits(8n, c, x, G, n)
      +b = dh_hi_sum(w1, c, x, G, n)
      +h = Spec.bit(Spec.member(Impl.tiles(c, Nat.add(8n, w1), G, n), x))
      Equal.trans(Nat, Nat.add(Impl.warp_hits(Nat.add(8n, w1), c, x, G, n), h), Nat.add(Nat.add(a, b), h),
        Nat.add(a, Nat.add(b, h)),
        MP.p8_add_cong(Impl.warp_hits(Nat.add(8n, w1), c, x, G, n), Nat.add(a, b), h, h,
          dh_split(w1, c, x, G, n), {==}),
        MP.ar_add_assoc(a, b, h))

# All 16 warps of block c == the finisher block pair 2 c, 2 c + 1.
def dh_block(+c: Nat, +x: Nat, +G: Nat, +n: Nat)
  -> {Impl.warp_hits(16n, c, x, G, n) ==
      Nat.add(M16.warp_hits(8n, Nat.add(c, c), x, Nat.add(G, G), n),
        M16.warp_hits(8n, 1n+Nat.add(c, c), x, Nat.add(G, G), n)) : Nat}:
  Equal.trans(Nat, Impl.warp_hits(Nat.add(8n, 8n), c, x, G, n),
    Nat.add(Impl.warp_hits(8n, c, x, G, n), dh_hi_sum(8n, c, x, G, n)),
    Nat.add(M16.warp_hits(8n, Nat.add(c, c), x, Nat.add(G, G), n),
      M16.warp_hits(8n, 1n+Nat.add(c, c), x, Nat.add(G, G), n)),
    dh_split(8n, c, x, G, n),
    MP.p8_add_cong(Impl.warp_hits(8n, c, x, G, n), M16.warp_hits(8n, Nat.add(c, c), x, Nat.add(G, G), n),
      dh_hi_sum(8n, c, x, G, n), M16.warp_hits(8n, 1n+Nat.add(c, c), x, Nat.add(G, G), n),
      dh_warp_lo(8n, c, x, G, n), dh_hi_eq(8n, c, x, G, n)))

# Blocks b < c of the 16-warp grid G == finisher blocks < 2 c of the grid 2 G.
def dh_grid(+c: Nat, +x: Nat, +G: Nat, +n: Nat)
  -> {Impl.tile_hits(c, x, G, n) == M16.job_hits(Nat.add(c, c), x, Nat.add(G, G), n) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      +p1 = p
      +j = M16.job_hits(Nat.add(p1, p1), x, Nat.add(G, G), n)
      +a = M16.warp_hits(8n, Nat.add(p1, p1), x, Nat.add(G, G), n)
      +b = M16.warp_hits(8n, 1n+Nat.add(p1, p1), x, Nat.add(G, G), n)
      %Equal.sym(Nat, Nat.add(p1, 1n+p1), 1n+Nat.add(p1, p1), MP.ar_add_succ_r(p1, p1)) : {Impl.tile_hits(1n+p1, x, G, n) == M16.job_hits(1n+_, x, Nat.add(G, G), n) : Nat}
      Equal.trans(Nat, Impl.tile_hits(1n+p1, x, G, n), Nat.add(j, Nat.add(a, b)), Nat.add(Nat.add(j, a), b),
        MP.p8_add_cong(Impl.tile_hits(p1, x, G, n), j, Impl.warp_hits(16n, p1, x, G, n), Nat.add(a, b),
          dh_grid(p1, x, G, n), dh_block(p1, x, G, n)),
        Equal.sym(Nat, Nat.add(Nat.add(j, a), b), Nat.add(j, Nat.add(a, b)), MP.ar_add_assoc(j, a, b)))

# ==== Law tiles_exactly_once ====

def Laws.tiles_exactly_once(x, G, n, grid):
  +g2 = dh_grid2(G, grid)
  Equal.trans(Nat, Impl.tile_hits(G, x, G, n), M16.job_hits(Nat.add(G, G), x, Nat.add(G, G), n),
    Spec.covered(x, n),
    dh_grid(G, x, G, n),
    Equal.trans(Nat, M16.job_hits(Nat.add(G, G), x, Nat.add(G, G), n), MS.bit(Nat.is_lt(x, n)),
      Spec.covered(x, n),
      ML.finish_jobs_once(x, Nat.add(G, G), n, g2),
      dh_bit_v(Nat.is_lt(x, n))))

# ==== Law tile_order ====

# x + 2 == 2 + x
def dh_add2(+x: Nat) -> {Nat.add(x, 2n) == 1n+1n+x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %dh_add2(p) : {1n+Nat.add(p, 2n) == 1n+_ : Nat}
      {==}

# (2 + x) / 2 == 1 + x / 2
def dh_div2(+x: Nat) -> {Nat.div(1n+1n+x, 2n) == 1n+Nat.div(x, 2n) : Nat}:
  %dh_add2(x) : {Nat.div(_, 2n) == 1n+Nat.div(x, 2n) : Nat}
  MP.ar_div_add_self(x, 2n, {==})

# x / 2 == g  gives  (2 + x) / 2 == 1 + g
def dh_st(+x: Nat, -g: Nat, h: {Nat.div(x, 2n) == g : Nat}) -> {Nat.div(1n+1n+x, 2n) == 1n+g : Nat}:
  %h : {Nat.div(1n+1n+x, 2n) == 1n+_ : Nat}
  dh_div2(x)

# a < a + (1 + y)
def dh_lt(+a: Nat, +y: Nat) -> {Nat.is_lt(a, Nat.add(a, 1n+y)) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      dh_lt(p, y)

# With base / 2 folded groups g (hg: (1 + base) / 2 == g) and r base iterations left before CH
# (hc: CH == base + 8 r), the loop from base emits the spec trace of 4 r groups from (g, base).
def dh_loop(+r: Nat, +e: Nat, +base: Nat, +g: Nat, +CH: Nat,
    +hg: {Nat.div(1n+base, 2n) == g : Nat}, +hc: {CH == Nat.add(base, Nat.mul(8n, r)) : Nat})
  -> {Impl.loop(Nat.add(1n+r, e), Nat.is_lt(base, CH), base, CH) == Spec.groups_trace(Nat.mul(4n, r), g, base) : List<&2, Spec.Ev>}:
  match r:
    case 0n:
      %Equal.sym(Nat, CH, Nat.add(base, 0n), hc) : {Impl.loop(1n+e, Nat.is_lt(base, _), base, CH) == Nil{} : List<&2, Spec.Ev>}
      %Equal.sym(Nat, Nat.add(base, 0n), base, MP.ar_add_zero_r(base)) : {Impl.loop(1n+e, Nat.is_lt(base, _), base, CH) == Nil{} : List<&2, Spec.Ev>}
      %Equal.sym(Bool, Nat.is_lt(base, base), False{}, MP.ar_lt_irrefl(base)) : {Impl.loop(1n+e, _, base, CH) == Nil{} : List<&2, Spec.Ev>}
      {==}
    case 1n+q:
      +q1 = q
      +h1 = dh_st(1n+base, g, hg)
      +h2 = dh_st(1n+1n+1n+base, 1n+g, h1)
      +h3 = dh_st(1n+1n+1n+1n+1n+base, 1n+1n+g, h2)
      +h4 = dh_st(1n+1n+1n+1n+1n+1n+1n+base, 1n+1n+1n+g, h3)
      +hc2 = Equal.trans(Nat, CH, Nat.add(base, Nat.add(8n, Nat.mul(8n, q1))), Nat.add(Nat.add(8n, base), Nat.mul(8n, q1)),
        Equal.trans(Nat, CH, Nat.add(base, Nat.mul(8n, 1n+q1)), Nat.add(base, Nat.add(8n, Nat.mul(8n, q1))),
          hc, Equal.cong(Nat, Nat, z => Nat.add(base, z), Nat.mul(8n, 1n+q1), Nat.add(8n, Nat.mul(8n, q1)),
            MP.ar_mul_succ_r(8n, q1))),
        dh_s8(base, Nat.mul(8n, q1)))
      +ih = dh_loop(q1, e, Nat.add(8n, base), 1n+1n+1n+1n+g, CH, h4, hc2)
      %Equal.sym(Nat, CH, Nat.add(base, Nat.mul(8n, 1n+q1)), hc) : {Impl.loop(1n+1n+Nat.add(q1, e), Nat.is_lt(base, _), base, CH) == Spec.groups_trace(Nat.mul(4n, 1n+q1), g, base) : List<&2, Spec.Ev>}
      %Equal.sym(Bool, Nat.is_lt(base, Nat.add(base, Nat.mul(8n, 1n+q1))), True{}, dh_lt(base, Nat.add(q1, Nat.mul(7n, 1n+q1)))) : {Impl.loop(1n+1n+Nat.add(q1, e), _, base, CH) == Spec.groups_trace(Nat.mul(4n, 1n+q1), g, base) : List<&2, Spec.Ev>}
      %Equal.sym(Nat, Nat.mul(4n, 1n+q1), Nat.add(4n, Nat.mul(4n, q1)), MP.ar_mul_succ_r(4n, q1)) : {Impl.loop(1n+1n+Nat.add(q1, e), True{}, base, CH) == Spec.groups_trace(_, g, base) : List<&2, Spec.Ev>}
      %Equal.sym(List<&2, Spec.Ev>, Impl.loop(Nat.add(1n+q1, e), Nat.is_lt(Nat.add(8n, base), CH), Nat.add(8n, base), CH), Spec.groups_trace(Nat.mul(4n, q1), 1n+1n+1n+1n+g, Nat.add(8n, base)), ih) : {Impl.body(base, _) == Spec.groups_trace(Nat.add(4n, Nat.mul(4n, q1)), g, base) : List<&2, Spec.Ev>}
      %Equal.sym(Nat, Nat.div(1n+base, 2n), g, hg) : {Spec.Chunk{base} <> Spec.Chunk{1n+base} <> Spec.Fold{_} <> Spec.Chunk{1n+1n+base} <> Spec.Chunk{1n+1n+1n+base} <> Spec.Fold{Nat.div(1n+1n+1n+base, 2n)} <> Spec.Chunk{1n+1n+1n+1n+base} <> Spec.Chunk{1n+1n+1n+1n+1n+base} <> Spec.Fold{Nat.div(1n+1n+1n+1n+1n+base, 2n)} <> Spec.Chunk{1n+1n+1n+1n+1n+1n+base} <> Spec.Chunk{1n+1n+1n+1n+1n+1n+1n+base} <> Spec.Fold{Nat.div(1n+1n+1n+1n+1n+1n+1n+base, 2n)} <> Spec.groups_trace(Nat.mul(4n, q1), 1n+1n+1n+1n+g, Nat.add(8n, base)) == Spec.groups_trace(Nat.add(4n, Nat.mul(4n, q1)), g, base) : List<&2, Spec.Ev>}
      %Equal.sym(Nat, Nat.div(1n+1n+1n+base, 2n), 1n+g, h1) : {Spec.Chunk{base} <> Spec.Chunk{1n+base} <> Spec.Fold{g} <> Spec.Chunk{1n+1n+base} <> Spec.Chunk{1n+1n+1n+base} <> Spec.Fold{_} <> Spec.Chunk{1n+1n+1n+1n+base} <> Spec.Chunk{1n+1n+1n+1n+1n+base} <> Spec.Fold{Nat.div(1n+1n+1n+1n+1n+base, 2n)} <> Spec.Chunk{1n+1n+1n+1n+1n+1n+base} <> Spec.Chunk{1n+1n+1n+1n+1n+1n+1n+base} <> Spec.Fold{Nat.div(1n+1n+1n+1n+1n+1n+1n+base, 2n)} <> Spec.groups_trace(Nat.mul(4n, q1), 1n+1n+1n+1n+g, Nat.add(8n, base)) == Spec.groups_trace(Nat.add(4n, Nat.mul(4n, q1)), g, base) : List<&2, Spec.Ev>}
      %Equal.sym(Nat, Nat.div(1n+1n+1n+1n+1n+base, 2n), 1n+1n+g, h2) : {Spec.Chunk{base} <> Spec.Chunk{1n+base} <> Spec.Fold{g} <> Spec.Chunk{1n+1n+base} <> Spec.Chunk{1n+1n+1n+base} <> Spec.Fold{1n+g} <> Spec.Chunk{1n+1n+1n+1n+base} <> Spec.Chunk{1n+1n+1n+1n+1n+base} <> Spec.Fold{_} <> Spec.Chunk{1n+1n+1n+1n+1n+1n+base} <> Spec.Chunk{1n+1n+1n+1n+1n+1n+1n+base} <> Spec.Fold{Nat.div(1n+1n+1n+1n+1n+1n+1n+base, 2n)} <> Spec.groups_trace(Nat.mul(4n, q1), 1n+1n+1n+1n+g, Nat.add(8n, base)) == Spec.groups_trace(Nat.add(4n, Nat.mul(4n, q1)), g, base) : List<&2, Spec.Ev>}
      %Equal.sym(Nat, Nat.div(1n+1n+1n+1n+1n+1n+1n+base, 2n), 1n+1n+1n+g, h3) : {Spec.Chunk{base} <> Spec.Chunk{1n+base} <> Spec.Fold{g} <> Spec.Chunk{1n+1n+base} <> Spec.Chunk{1n+1n+1n+base} <> Spec.Fold{1n+g} <> Spec.Chunk{1n+1n+1n+1n+base} <> Spec.Chunk{1n+1n+1n+1n+1n+base} <> Spec.Fold{1n+1n+g} <> Spec.Chunk{1n+1n+1n+1n+1n+1n+base} <> Spec.Chunk{1n+1n+1n+1n+1n+1n+1n+base} <> Spec.Fold{_} <> Spec.groups_trace(Nat.mul(4n, q1), 1n+1n+1n+1n+g, Nat.add(8n, base)) == Spec.groups_trace(Nat.add(4n, Nat.mul(4n, q1)), g, base) : List<&2, Spec.Ev>}
      {==}

def Laws.tile_order(L):
  dh_loop(L, Nat.mul(7n, L), 0n, 0n, Nat.mul(8n, L), {==}, {==})
