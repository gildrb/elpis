# Finite differential table of the ext patch 3003 verify-attention models (bend/attn_chunk.bend,
# bend/attn_chunk_bounds.bend), compared byte for byte by bend/attn_chunk_diff.py against the
# expressions quoted from exllamav3_ext/attn_verify.cuh / attn_verify.cu / attn_verify_gr.cu /
# libtorch/attention.cpp (compiled for the CPU) and modules/attention_fn/bc_attn.py (evaluated).
# Per (L, chunk): A = stores of each chunk s < live + 2 over a grid of S CTAs; T = chunk geometry
# n_start:n_end:ntiles; B = the combine's merged chunk list of each row of a q_len 8 round. C =
# checked sizes and partial / output indices at the corners; H = host sizing.
import Base
import ./attn_chunk.bend as Impl
import ./attn_chunk_bounds.bend as Bd

def nums(+xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> rest:
      match rest:
        case Nil{}:
          Nat.show(x)
        case y <> more:
          Nat.show(x) ++ "," ++ nums(rest)

def ws(k: Nat, +s: Nat, +S: Nat, +L: Nat, +ch: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+m:
      Nat.show(Impl.writes(S, S, s, L, ch)) ++ ws(m, 1n+s, S, L, ch)

def line_a(+L: Nat, +ch: Nat, +S: Nat) -> String:
  "A L=" ++ Nat.show(L) ++ " chunk=" ++ Nat.show(ch) ++ " S=" ++ Nat.show(S) ++ " live=" ++
    Nat.show(Impl.live(L, ch)) ++ " w=" ++ ws(Nat.add(Impl.live(L, ch), 2n), 0n, S, L, ch)

def geo(k: Nat, +c: Nat, +L: Nat, +ch: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+m:
      " " ++ Nat.show(Impl.n_start(c, ch)) ++ ":" ++ Nat.show(Impl.n_end(c, L, ch)) ++ ":" ++
        Nat.show(Impl.ntiles(c, L, ch)) ++ geo(m, 1n+c, L, ch)

def line_t(+L: Nat, +ch: Nat) -> String:
  "T L=" ++ Nat.show(L) ++ " chunk=" ++ Nat.show(ch) ++ geo(Impl.live(L, ch), 0n, L, ch)

def line_b(+L: Nat, +ch: Nat, +q: Nat) -> String:
  "B L=" ++ Nat.show(L) ++ " chunk=" ++ Nat.show(ch) ++ " q=" ++ Nat.show(q) ++ " m=" ++
    nums(Impl.merged(L, ch, 8n, q))

def rows_b(k: Nat, +q: Nat, +L: Nat, +ch: Nat) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        IO.print(line_b(L, ch, q))
        rows_b(m, 1n+q, L, ch)

def per_s(ss: List<&2, Nat>, +L: Nat, +ch: Nat) -> IO(Unit):
  match ss:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case s <> rest:
      do IO<Unit>:
        IO.print(line_a(L, ch, s))
        per_s(rest, L, ch)

def rows_if(short: Bool, +L: Nat, +ch: Nat) -> IO(Unit):
  match short:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      rows_b(8n, 0n, L, ch)

def per_lc(+L: Nat, +ch: Nat) -> IO(Unit):
  do IO<Unit>:
    per_s([1n, 3n, 20n, 82n], L, ch)
    IO.print(line_t(L, ch))
    rows_if(Nat.is_lt(L, 8n), L, ch)

def per_ch(chs: List<&2, Nat>, +L: Nat) -> IO(Unit):
  match chs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case ch <> rest:
      do IO<Unit>:
        per_lc(L, ch)
        per_ch(rest, L)

def per_l(ls: List<&2, Nat>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case l <> rest:
      do IO<Unit>:
        per_ch([64n, 96n, 512n, 1024n], l)
        per_l(rest)

# C corners: for b in [0, bsz - 1], kvh in [0, nkv - 1], c in [0, mc - 1]: partial_o at (row 0, col
# 0) and (row 47, col 255), partial_ml at (row 0, k 0) and (row 47, k 1)
def corner(+b: Nat, +kvh: Nat, +c: Nat, +nkv: Nat, +mc: Nat) -> String:
  " " ++ Nat.show(Bd.po_index(b, kvh, c, 0n, 0n, nkv, mc)) ++ ":" ++
    Nat.show(Bd.po_index(b, kvh, c, 47n, 255n, nkv, mc)) ++ ":" ++
    Nat.show(Bd.pml_index(b, kvh, c, 0n, 0n, nkv, mc)) ++ ":" ++
    Nat.show(Bd.pml_index(b, kvh, c, 47n, 1n, nkv, mc))

def corners_c(cs: List<&2, Nat>, +b: Nat, +kvh: Nat, +nkv: Nat, +mc: Nat) -> String:
  match cs:
    case Nil{}:
      ""
    case c <> rest:
      corner(b, kvh, c, nkv, mc) ++ corners_c(rest, b, kvh, nkv, mc)

def corners_k(ks: List<&2, Nat>, +b: Nat, +nkv: Nat, +mc: Nat) -> String:
  match ks:
    case Nil{}:
      ""
    case k <> rest:
      corners_c([0n, Nat.sub(mc, 1n)], b, k, nkv, mc) ++ corners_k(rest, b, nkv, mc)

def corners_b(bs: List<&2, Nat>, +nkv: Nat, +mc: Nat) -> String:
  match bs:
    case Nil{}:
      ""
    case b <> rest:
      corners_k([0n, Nat.sub(nkv, 1n)], b, nkv, mc) ++ corners_b(rest, nkv, mc)

def outs_d(ds: List<&2, Nat>, +b: Nat, +nkv: Nat, +nq: Nat, +ql: Nat) -> String:
  match ds:
    case Nil{}:
      ""
    case d <> rest:
      " " ++ Nat.show(Bd.out_index(b, Nat.sub(ql, 1n), Nat.sub(nkv, 1n), Nat.sub(Nat.div(nq, nkv), 1n), d, ql, nq, nkv)) ++
        outs_d(rest, b, nkv, nq, ql)

def outs_b(bs: List<&2, Nat>, +nkv: Nat, +nq: Nat, +ql: Nat) -> String:
  match bs:
    case Nil{}:
      ""
    case b <> rest:
      outs_d([0n, 255n], b, nkv, nq, ql) ++ outs_b(rest, nkv, nq, ql)

def line_c(+bsz: Nat, +nkv: Nat, +mc: Nat, +nq: Nat, +ql: Nat) -> String:
  "C bsz=" ++ Nat.show(bsz) ++ " nkv=" ++ Nat.show(nkv) ++ " mc=" ++ Nat.show(mc) ++ " nq=" ++
    Nat.show(nq) ++ " ql=" ++ Nat.show(ql) ++ " o=" ++ Nat.show(Bd.check_o(bsz, nkv, mc)) ++
    " ml=" ++ Nat.show(Bd.check_ml(bsz, nkv, mc)) ++ " out=" ++ Nat.show(Bd.check_out(bsz, ql, nq)) ++
    corners_b([0n, Nat.sub(bsz, 1n)], nkv, mc) ++ outs_b([0n, Nat.sub(bsz, 1n)], nkv, nq, ql)

def line_h(+sms: Nat, +bsz: Nat, +kvh: Nat, +pages: Nat, +ch: Nat, +splits: Nat, +nsub: Nat,
    +rows: Nat, +hd: Nat) -> String:
  "H sms=" ++ Nat.show(sms) ++ " bsz=" ++ Nat.show(bsz) ++ " kvh=" ++ Nat.show(kvh) ++ " pages=" ++
    Nat.show(pages) ++ " chunk=" ++ Nat.show(ch) ++ " S=" ++ Nat.show(Bd.host_splits(sms, bsz, kvh)) ++
    " mc=" ++ Nat.show(Bd.host_max_chunks(pages, ch)) ++ " pn_o=" ++
    Nat.show(Bd.host_pn_o(bsz, kvh, splits, nsub, rows, hd, pages, ch)) ++ " pn_ml=" ++
    Nat.show(Bd.host_pn_ml(bsz, kvh, splits, nsub, rows, pages, ch))

# Must match LS / CHUNKS / SS / BIG / IDX / HOST of attn_chunk_diff.py
def main() -> IO(Unit):
  do IO<Unit>:
    per_l([1n, 8n, 63n, 64n, 65n, 511n, 512n, 513n, 1000n, 1032n, 2056n, 4104n])
    per_lc(18608n, 512n)
    per_lc(18608n, 1024n)
    per_lc(32776n, 512n)
    per_lc(32776n, 1024n)
    IO.print(line_c(1n, 4n, 528n, 24n, 8n))
    IO.print(line_c(2n, 4n, 17n, 24n, 3n))
    IO.print(line_c(1n, 8n, 3n, 32n, 1n))
    IO.print(line_c(3n, 2n, 5n, 12n, 8n))
    IO.print(line_h(82n, 1n, 4n, 1056n, 512n, 39n, 3n, 16n, 256n))
    IO.print(line_h(82n, 1n, 4n, 1057n, 512n, 39n, 3n, 16n, 256n))
    IO.print(line_h(82n, 1n, 4n, 1n, 1024n, 39n, 3n, 16n, 256n))
    IO.print(line_h(82n, 2n, 4n, 33n, 192n, 10n, 1n, 16n, 256n))
    IO.print(line_h(46n, 1n, 8n, 5n, 64n, 2n, 4n, 16n, 256n))
    IO.print(line_h(82n, 1n, 4n, 1056n, 1024n, 39n, 3n, 16n, 256n))
