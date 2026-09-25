# Finite differential table of the ext 3007 fused pre-attention model (bend/attn_pre.bend) and its
# unfused reference (bend/attn_pre_spec.bend), compared byte for byte by bend/attn_pre_diff.py
# against the index expressions quoted from exllamav3_ext/attn_small.cu (fused) and
# activation.cu / rope.cu / cache/q_cache_kernels.cuh / cache/q_cache.cu (unfused), compiled for the
# CPU. Address lists are summarized as FNV-1a over U32 (order and value sensitive) plus a count.
# H = head loops of every (block z, thread row y) of the launch grid, per (heads J, heads_per_block P).
# Q = per q head job (in grid order): the qg halves read, the q halves written, the gate halves read
# and written; the deinterleave sources of the q / g halves written; rope_kernel's q halves.
# K = per k head job: the k halves read / written, rope_kernel's k halves, then per warp its
# (c, cc, is_v, g0, base, source span, words, scales) quantization chunks.
# U = per token: the unfused quant_cache_paged_kernel warps (bx, w): g0, base, source, words, scales.
# R = RoPE pairs (fused offset vs rope_kernel's with rotate_offset 0), NEOX and GPT-J.
import Base
import ./attn_pre.bend as Impl
import ./attn_pre_spec.bend as Spec

def fnv(xs: List<&2, Nat>, h: U32, +n: Nat) -> String:
  match xs:
    case Nil{}:
      U32.show(h) ++ ":" ++ Nat.show(n)
    case x <> rest:
      fnv(rest, U32.mul(U32.xor(h, U32.from_nat(x)), 16777619), 1n+n)

def summ(xs: List<&2, Nat>) -> String:
  fnv(xs, 2166136261, 0n)

def nums(+xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      "-"
    case x <> rest:
      match rest:
        case Nil{}:
          Nat.show(x)
        case y <> more:
          Nat.show(x) ++ "," ++ nums(rest)

# ---- H ----
def h_rows(k: Nat, +y: Nat, +z: Nat, +Pb: Nat, +Z: Nat, +J: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+m:
      " " ++ Nat.show(z) ++ ":" ++ Nat.show(y) ++ "=" ++ nums(Impl.heads(z, y, Pb, Z, J)) ++
        h_rows(m, 1n+y, z, Pb, Z, J)

def h_blocks(k: Nat, +z: Nat, +Pb: Nat, +Z: Nat, +J: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+m:
      h_rows(Pb, 0n, z, Pb, Z, J) ++ h_blocks(m, 1n+z, Pb, Z, J)

def line_h(+J: Nat, +P: Nat) -> String:
  +Pb = Impl.par(P, J)
  +Z = Impl.zgrid(J, P)
  "H J=" ++ Nat.show(J) ++ " P=" ++ Nat.show(P) ++ " par=" ++ Nat.show(Pb) ++ " Z=" ++ Nat.show(Z) ++
    h_blocks(Z, 0n, Pb, Z, J)

# ---- address lists ----
def l2(k: Nat, +t: Nat, +base: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+m:
      Impl.lane2(base, t, 0n) <> Impl.lane2(base, t, 1n) <> l2(m, 1n+t, base)

def s2(k: Nat, +t: Nat, +base: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+m:
      Spec.lane2(base, t, 0n) <> Spec.lane2(base, t, 1n) <> s2(m, 1n+t, base)

def g8.pick(inp: Bool, +r: Nat, +nq: Nat, +h: Nat, +hd: Nat, +i: Nat, +j: Nat) -> Nat:
  match inp:
    case True{}:
      Impl.g_in(r, nq, h, hd, i, j)
    case False{}:
      Impl.g_out(r, nq, h, hd, i, j)

def j8(k: Nat, +j: Nat, +r: Nat, +nq: Nat, +h: Nat, +hd: Nat, +i: Nat, +inp: Bool) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+m:
      g8.pick(inp, r, nq, h, hd, i, j) <> j8(m, 1n+j, r, nq, h, hd, i, inp)

def g_all(k: Nat, +i: Nat, +r: Nat, +nq: Nat, +h: Nat, +hd: Nat, +inp: Bool) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+m:
      List.append(&2, Nat, j8(8n, 0n, r, nq, h, hd, i, inp), g_all(m, 1n+i, r, nq, h, hd, inp))

def map_dq(xs: List<&2, Nat>, +hd8: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      Spec.deint_q_elem(x, hd8) <> map_dq(rest, hd8)

def map_dg(xs: List<&2, Nat>, +hd8: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      Spec.deint_g_elem(x, hd8) <> map_dg(rest, hd8)

# instance: nq, nk, hd, bsz, S, P, bits, bps, seqlens of batch 0 / 1 (bt: bt_fn below)
type Inst is Data:
  Inst{nq: Nat, nk: Nat, hd: Nat, bsz: Nat, S: Nat, P: Nat, bits: Nat, bps: Nat, sl0: Nat, sl1: Nat}

# block_table[i] of every instance: a closed map with distinct entries
def bt_fn(i: Nat) -> Nat:
  Nat.add(Nat.mul(i, 5n), 3n)

def seqlen(+b: Nat, +sl0: Nat, +sl1: Nat) -> Nat:
  match b:
    case 0n:
      sl0
    case 1n+p:
      sl1

def line_q(+b: Nat, +tok: Nat, +h: Nat, +nq: Nat, +hd: Nat, +S: Nat) -> String:
  +r = Impl.row(b, S, tok)
  +T = Nat.div(hd, 2n)
  +hd8 = Nat.div(hd, 8n)
  "Q b=" ++ Nat.show(b) ++ " tok=" ++ Nat.show(tok) ++ " h=" ++ Nat.show(h) ++
    " qin=" ++ summ(l2(T, 0n, Impl.qg_head(r, nq, h, hd))) ++
    " qout=" ++ summ(l2(T, 0n, Impl.q_head(r, nq, h, hd))) ++
    " gin=" ++ summ(g_all(hd8, 0n, r, nq, h, hd, True{})) ++
    " gout=" ++ summ(g_all(hd8, 0n, r, nq, h, hd, False{})) ++
    " dq=" ++ summ(map_dq(l2(T, 0n, Impl.q_head(r, nq, h, hd)), hd8)) ++
    " dg=" ++ summ(map_dg(g_all(hd8, 0n, r, nq, h, hd, False{}), hd8)) ++
    " rq=" ++ summ(s2(T, 0n, Spec.rope_head(b, S, tok, nq, h, hd)))

# quant_block_x4 spans: l < 32, v < 4
def v4(k: Nat, +v: Nat, +l: Nat, +start: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+m:
      Nat.add(start, Nat.add(Nat.mul(l, 4n), v)) <> v4(m, 1n+v, l, start)

def span(k: Nat, +l: Nat, +start: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+m:
      List.append(&2, Nat, v4(4n, 0n, l, start), span(m, 1n+l, start))

def fsrc(k: Nat, +v: Nat, +l: Nat, +r: Nat, +nk: Nat, +kvh: Nat, +hd: Nat, +cc: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+m:
      Impl.kv_src(r, nk, kvh, hd, cc, l, v) <> fsrc(m, 1n+v, l, r, nk, kvh, hd, cc)

def fspan(k: Nat, +l: Nat, +r: Nat, +nk: Nat, +kvh: Nat, +hd: Nat, +cc: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+m:
      List.append(&2, Nat, fsrc(4n, 0n, l, r, nk, kvh, hd, cc), fspan(m, 1n+l, r, nk, kvh, hd, cc))

def bsw(isv: Bool) -> String:
  match isv:
    case True{}:
      "1"
    case False{}:
      "0"

def rng(+a: Nat, +n: Nat) -> String:
  Nat.show(a) ++ "-" ++ Nat.show(Nat.sub(Nat.add(a, n), 1n))

def active(+gpt: Nat, +g0: Nat) -> Nat:
  Nat.min(4n, Nat.sub(gpt, g0))

def chunk(+c: Nat, +r: Nat, +b: Nat, +tok: Nat, +kvh: Nat, +I: Inst) -> String:
  match I:
    case Inst{+nq, +nk, +hd, +bsz, +S, +P, +bits, +bps, +sl0, +sl1}:
      +cc = Impl.cc_of(c, hd)
      +gpt = Nat.div(Nat.mul(nk, hd), 32n)
      +g = Impl.g0(kvh, hd, cc)
      +phys = Impl.token_phys(~bt_fn, bps, b, Impl.token_idx(tok, seqlen(b, sl0, sl1)))
      +bs = Impl.base(phys, gpt, g)
      +act = active(gpt, g)
      " " ++ Nat.show(c) ++ "/" ++ Nat.show(cc) ++ "/" ++ bsw(Impl.is_v(c, hd)) ++ "/" ++ Nat.show(g) ++
        "/" ++ Nat.show(bs) ++ "/src=" ++ summ(fspan(32n, 0n, r, nk, kvh, hd, cc)) ++ "/words=" ++
        rng(Impl.word(bs, bits, 0n), Nat.mul(act, bits)) ++ "/scales=" ++ rng(Impl.scale(bs, 0n), act)

def chunks_of(cs: List<&2, Nat>, +r: Nat, +b: Nat, +tok: Nat, +kvh: Nat, +I: Inst) -> String:
  match cs:
    case Nil{}:
      ""
    case c <> rest:
      chunk(c, r, b, tok, kvh, I) ++ chunks_of(rest, r, b, tok, kvh, I)

def warps_k(k: Nat, +w: Nat, +r: Nat, +b: Nat, +tok: Nat, +kvh: Nat, +I: Inst) -> String:
  match k:
    case 0n:
      ""
    case 1n+m:
      match I:
        case Inst{+nq, +nk, +hd, +bsz, +S, +P, +bits, +bps, +sl0, +sl1}:
          " w" ++ Nat.show(w) ++ ":" ++ chunks_of(Impl.warp_chunks(w, hd), r, b, tok, kvh, I) ++
            warps_k(m, 1n+w, r, b, tok, kvh, I)

def line_k(+b: Nat, +tok: Nat, +kvh: Nat, +I: Inst) -> String:
  match I:
    case Inst{+nq, +nk, +hd, +bsz, +S, +P, +bits, +bps, +sl0, +sl1}:
      +r = Impl.row(b, S, tok)
      +T = Nat.div(hd, 2n)
      "K b=" ++ Nat.show(b) ++ " tok=" ++ Nat.show(tok) ++ " kvh=" ++ Nat.show(kvh) ++
        " k=" ++ summ(l2(T, 0n, Impl.k_head(r, nk, kvh, hd))) ++
        " rk=" ++ summ(s2(T, 0n, Spec.rope_head(b, S, tok, nk, kvh, hd))) ++
        warps_k(Impl.warps(hd), 0n, r, b, tok, kvh, I)

def job.pick(isq: Bool, +h: Nat, +b: Nat, +tok: Nat, +I: Inst) -> String:
  match isq:
    case True{}:
      match I:
        case Inst{+nq, +nk, +hd, +bsz, +S, +P, +bits, +bps, +sl0, +sl1}:
          line_q(b, tok, h, nq, hd, S)
    case False{}:
      match I:
        case Inst{+nq, +nk, +hd, +bsz, +S, +P, +bits, +bps, +sl0, +sl1}:
          line_k(b, tok, Nat.sub(h, nq), I)

def job(+h: Nat, +b: Nat, +tok: Nat, +I: Inst) -> String:
  match I:
    case Inst{+nq, +nk, +hd, +bsz, +S, +P, +bits, +bps, +sl0, +sl1}:
      job.pick(Nat.is_lt(h, nq), h, b, tok, I)

def jobs(hs: List<&2, Nat>, +b: Nat, +tok: Nat, +I: Inst) -> IO(Unit):
  match hs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case h <> rest:
      do IO<Unit>:
        IO.print(job(h, b, tok, I))
        jobs(rest, b, tok, I)

def rows_y(k: Nat, +y: Nat, +z: Nat, +b: Nat, +tok: Nat, +Pb: Nat, +Z: Nat, +J: Nat, +I: Inst) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        jobs(Impl.heads(z, y, Pb, Z, J), b, tok, I)
        rows_y(m, 1n+y, z, b, tok, Pb, Z, J, I)

def blocks_z(k: Nat, +z: Nat, +b: Nat, +tok: Nat, +Pb: Nat, +Z: Nat, +J: Nat, +I: Inst) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        rows_y(Pb, 0n, z, b, tok, Pb, Z, J, I)
        blocks_z(m, 1n+z, b, tok, Pb, Z, J, I)

# ---- U: unfused quant_cache_paged_kernel, block (bx, tok, b), warp w ----
def u_warp.pick(ret: Bool, +bx: Nat, +w: Nat, +g: Nat, +gpt: Nat, +b: Nat, +tok: Nat, +I: Inst) -> String:
  match ret:
    case True{}:
      " " ++ Nat.show(bx) ++ ":" ++ Nat.show(w) ++ "/-"
    case False{}:
      match I:
        case Inst{+nq, +nk, +hd, +bsz, +S, +P, +bits, +bps, +sl0, +sl1}:
          +pos = Spec.q_token_pos(~bt_fn, bps, b, Spec.q_token_idx(tok, seqlen(b, sl0, sl1)))
          +bs = Spec.q_base(pos, gpt, g)
          +inb = Spec.q_base(Spec.q_in_pos(b, S, tok), gpt, g)
          +act = active(gpt, g)
          " " ++ Nat.show(bx) ++ ":" ++ Nat.show(w) ++ "/" ++ Nat.show(g) ++ "/" ++ Nat.show(bs) ++
            "/src=" ++ summ(span(32n, 0n, Nat.mul(inb, 32n))) ++ "/words=" ++
            rng(Spec.q_word(bs, bits, 0n), Nat.mul(act, bits)) ++ "/scales=" ++ rng(Spec.q_scale(bs, 0n), act)

def u_warp(+bx: Nat, +w: Nat, +b: Nat, +tok: Nat, +I: Inst) -> String:
  match I:
    case Inst{+nq, +nk, +hd, +bsz, +S, +P, +bits, +bps, +sl0, +sl1}:
      +gpt = Nat.div(Nat.mul(nk, hd), 32n)
      +g = Spec.q_g0(bx, Spec.q_usage(gpt), w)
      u_warp.pick(Nat.is_ge(g, gpt), bx, w, g, gpt, b, tok, I)

def u_ws(k: Nat, +w: Nat, +bx: Nat, +b: Nat, +tok: Nat, +I: Inst) -> String:
  match k:
    case 0n:
      ""
    case 1n+m:
      u_warp(bx, w, b, tok, I) ++ u_ws(m, 1n+w, bx, b, tok, I)

def u_bx(k: Nat, +bx: Nat, +usage: Nat, +b: Nat, +tok: Nat, +I: Inst) -> String:
  match k:
    case 0n:
      ""
    case 1n+m:
      u_ws(usage, 0n, bx, b, tok, I) ++ u_bx(m, 1n+bx, usage, b, tok, I)

def line_u(+b: Nat, +tok: Nat, +I: Inst) -> String:
  match I:
    case Inst{+nq, +nk, +hd, +bsz, +S, +P, +bits, +bps, +sl0, +sl1}:
      +gpt = Nat.div(Nat.mul(nk, hd), 32n)
      "U b=" ++ Nat.show(b) ++ " tok=" ++ Nat.show(tok) ++ " tb=" ++ Nat.show(Spec.q_tb(gpt)) ++
        " usage=" ++ Nat.show(Spec.q_usage(gpt)) ++ u_bx(Spec.q_tb(gpt), 0n, Spec.q_usage(gpt), b, tok, I)

def per_tok(k: Nat, +tok: Nat, +b: Nat, +I: Inst) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      match I:
        case Inst{+nq, +nk, +hd, +bsz, +S, +P, +bits, +bps, +sl0, +sl1}:
          +J = Nat.add(nq, nk)
          do IO<Unit>:
            blocks_z(Impl.zgrid(J, P), 0n, b, tok, Impl.par(P, J), Impl.zgrid(J, P), J, I)
            IO.print(line_u(b, tok, I))
            per_tok(m, 1n+tok, b, I)

def per_b(k: Nat, +b: Nat, +I: Inst) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      match I:
        case Inst{+nq, +nk, +hd, +bsz, +S, +P, +bits, +bps, +sl0, +sl1}:
          do IO<Unit>:
            per_tok(S, 0n, b, I)
            per_b(m, 1n+b, I)

def inst(+I: Inst) -> IO(Unit):
  match I:
    case Inst{+nq, +nk, +hd, +bsz, +S, +P, +bits, +bps, +sl0, +sl1}:
      do IO<Unit>:
        IO.print("I nq=" ++ Nat.show(nq) ++ " nk=" ++ Nat.show(nk) ++ " hd=" ++ Nat.show(hd) ++
          " bsz=" ++ Nat.show(bsz) ++ " S=" ++ Nat.show(S) ++ " P=" ++ Nat.show(P) ++ " bits=" ++
          Nat.show(bits) ++ " bps=" ++ Nat.show(bps) ++ " sl=" ++ Nat.show(sl0) ++ "," ++ Nat.show(sl1))
        per_b(bsz, 0n, I)

# ---- R ----
def pair_s(p: Nat & Nat) -> String:
  (a, b) = p
  Nat.show(a) ++ "/" ++ Nat.show(b)

def r_t.pick(neox: Bool, +t: Nat, +rdim: Nat, +pd: Nat) -> String:
  match neox:
    case True{}:
      " " ++ pair_s(Impl.neox_pair(Impl.offset(pd, rdim), t, pd)) ++ "=" ++
        pair_s(Spec.neox_pair(Spec.rope_offset(0n, pd, rdim), t, pd))
    case False{}:
      " " ++ pair_s(Impl.gptj_pair(Impl.offset(pd, rdim), t)) ++ "=" ++
        pair_s(Spec.gptj_pair(Spec.rope_offset(0n, pd, rdim), t))

def r_t(k: Nat, +t: Nat, +rdim: Nat, +pd: Nat, +neox: Bool) -> String:
  match k:
    case 0n:
      ""
    case 1n+m:
      r_t.pick(neox, t, rdim, pd) ++ r_t(m, 1n+t, rdim, pd, neox)

def r_rd(k: Nat, +rdim: Nat, +pd: Nat, +neox: Bool) -> String:
  match k:
    case 0n:
      ""
    case 1n+m:
      " |" ++ r_t(Nat.div(pd, 2n), 0n, rdim, pd, neox) ++ r_rd(m, 1n+rdim, pd, neox)

def line_r(+pd: Nat, +rd: Nat, +neox: Bool) -> String:
  "R pd=" ++ Nat.show(pd) ++ " rd=" ++ Nat.show(rd) ++ " neox=" ++ bsw(neox) ++ r_rd(rd, 0n, pd, neox)

# Must match HS / INSTS / RS of attn_pre_diff.py
def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(line_h(28n, 1n))
    IO.print(line_h(28n, 2n))
    IO.print(line_h(28n, 3n))
    IO.print(line_h(28n, 4n))
    IO.print(line_h(28n, 8n))
    IO.print(line_h(5n, 2n))
    IO.print(line_h(4n, 8n))
    IO.print(line_h(1n, 1n))
    inst(Inst{24n, 4n, 256n, 1n, 8n, 4n, 3n, 150n, 1000n, 0n})
    inst(Inst{6n, 2n, 128n, 2n, 3n, 3n, 4n, 4n, 254n, 511n})
    inst(Inst{3n, 1n, 256n, 1n, 1n, 8n, 3n, 2n, 0n, 0n})
    inst(Inst{8n, 8n, 256n, 1n, 2n, 2n, 3n, 3n, 300n, 0n})
    IO.print(line_r(64n, 1n, True{}))
    IO.print(line_r(64n, 1n, False{}))
    IO.print(line_r(8n, 3n, True{}))
    IO.print(line_r(8n, 3n, False{}))
    IO.print(line_r(256n, 1n, True{}))
