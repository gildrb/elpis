# Finite differential table of the ext patch 3006 verify-attention models (bend/attn_stride.bend,
# bend/attn_stride_bounds.bend), compared byte for byte by bend/attn_stride_diff.py against the
# expressions quoted from exllamav3_ext/attn_verify.cuh / attn_verify.cu / attn_verify_gr.cu /
# libtorch/attention.cpp (compiled for the CPU) and modules/attention_fn/bc_attn.py (evaluated).
# Per (L, S): A = stores of each partial slot s < live + 2 by the S split CTAs, live tiles and live
# slots; T = block-table trap outcome for ceil(L / 256) and ceil(L / 256) - 1 pages, then per CTA
# x < S its tile count, first / last tile start and the last tile's block-table page; B = the
# combine's merged slot list of each row of a q_len 8 round. C = checked sizes and partial / output
# indices at the corners; G = attn_verify_gr's splits check and the combine's live trap outcome per
# (S, L); H = host sizing.
import Base
import ./attn_stride.bend as Impl
import ./attn_stride_bounds.bend as Bd

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

def ws(k: Nat, +s: Nat, +S: Nat, +L: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+m:
      Nat.show(Impl.writes(S, s, L)) ++ ws(m, 1n+s, S, L)

def line_a(+L: Nat, +S: Nat) -> String:
  "A L=" ++ Nat.show(L) ++ " S=" ++ Nat.show(S) ++ " tiles=" ++ Nat.show(Impl.live_tiles(L)) ++
    " live=" ++ Nat.show(Impl.live_slots(Impl.live_tiles(L), S)) ++ " w=" ++
    ws(Nat.add(Impl.live_slots(Impl.live_tiles(L), S), 2n), 0n, S, L)

# Tile count k of CTA x: first / last tile start and the last tile's block-table page
def last(+m: Nat, +x: Nat, +S: Nat) -> String:
  ":" ++ Nat.show(Impl.tile_n0(x, 0n, S)) ++ ":" ++ Nat.show(Impl.tile_n0(x, m, S)) ++ ":" ++
    Nat.show(Bd.tile_page(Impl.tile_n0(x, m, S)))

def ends(k: Nat, +x: Nat, +S: Nat) -> String:
  match k:
    case 0n:
      ":-"
    case 1n+m:
      last(m, x, S)

def ctas(k: Nat, +x: Nat, +L: Nat, +S: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+m:
      " " ++ Nat.show(Impl.cta_tiles(Impl.live_tiles(L), x, S)) ++
        ends(Impl.cta_tiles(Impl.live_tiles(L), x, S), x, S) ++ ctas(m, 1n+x, L, S)

def line_t(+L: Nat, +S: Nat) -> String:
  "T L=" ++ Nat.show(L) ++ " S=" ++ Nat.show(S) ++ " runs=" ++
    Nat.show(Impl.bit(Bd.runs(L, Impl.cdiv(L, 256n)))) ++
    Nat.show(Impl.bit(Bd.runs(L, Nat.sub(Impl.cdiv(L, 256n), 1n)))) ++ ctas(S, 0n, L, S)

def line_b(+L: Nat, +S: Nat, +q: Nat) -> String:
  "B L=" ++ Nat.show(L) ++ " S=" ++ Nat.show(S) ++ " q=" ++ Nat.show(q) ++ " m=" ++
    nums(Impl.merged(L, S, 8n, q))

def rows_b(k: Nat, +q: Nat, +L: Nat, +S: Nat) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        IO.print(line_b(L, S, q))
        rows_b(m, 1n+q, L, S)

def rows_if(short: Bool, +L: Nat, +S: Nat) -> IO(Unit):
  match short:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      rows_b(8n, 0n, L, S)

def per_ls(+L: Nat, +S: Nat) -> IO(Unit):
  do IO<Unit>:
    IO.print(line_a(L, S))
    IO.print(line_t(L, S))
    rows_if(Nat.is_lt(L, 8n), L, S)

def per_s(ss: List<&2, Nat>, +L: Nat) -> IO(Unit):
  match ss:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case s <> rest:
      do IO<Unit>:
        per_ls(L, s)
        per_s(rest, L)

def per_l(ls: List<&2, Nat>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case l <> rest:
      do IO<Unit>:
        per_s([1n, 3n, 20n, 82n], l)
        per_l(rest)

# C corners: for b in [0, bsz - 1], kvh in [0, nkv - 1], x in [0, S - 1]: the split's partial_o at
# (row 0, col 0) / (row 47, col 255) and partial_ml at (row 0, k 0) / (row 47, k 1) of CTA x, then
# the combine's reads of slot s = x at the same corners
def corner(+b: Nat, +kvh: Nat, +x: Nat, +nkv: Nat, +S: Nat) -> String:
  " " ++ Nat.show(Bd.po_index(b, kvh, x, 0n, 0n, nkv, S)) ++ ":" ++
    Nat.show(Bd.po_index(b, kvh, x, 47n, 255n, nkv, S)) ++ ":" ++
    Nat.show(Bd.pml_index(b, kvh, x, 0n, 0n, nkv, S)) ++ ":" ++
    Nat.show(Bd.pml_index(b, kvh, x, 47n, 1n, nkv, S)) ++ "/" ++
    Nat.show(Bd.co_index(b, kvh, 0n, x, 0n, nkv, S)) ++ ":" ++
    Nat.show(Bd.co_index(b, kvh, 47n, x, 255n, nkv, S)) ++ ":" ++
    Nat.show(Bd.cml_index(b, kvh, 0n, x, 0n, nkv, S)) ++ ":" ++
    Nat.show(Bd.cml_index(b, kvh, 47n, x, 1n, nkv, S))

def corners_x(xs: List<&2, Nat>, +b: Nat, +kvh: Nat, +nkv: Nat, +S: Nat) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> rest:
      corner(b, kvh, x, nkv, S) ++ corners_x(rest, b, kvh, nkv, S)

def corners_k(ks: List<&2, Nat>, +b: Nat, +nkv: Nat, +S: Nat) -> String:
  match ks:
    case Nil{}:
      ""
    case k <> rest:
      corners_x([0n, Nat.sub(S, 1n)], b, k, nkv, S) ++ corners_k(rest, b, nkv, S)

def corners_b(bs: List<&2, Nat>, +nkv: Nat, +S: Nat) -> String:
  match bs:
    case Nil{}:
      ""
    case b <> rest:
      corners_k([0n, Nat.sub(nkv, 1n)], b, nkv, S) ++ corners_b(rest, nkv, S)

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

def line_c(+bsz: Nat, +nkv: Nat, +S: Nat, +nq: Nat, +ql: Nat) -> String:
  "C bsz=" ++ Nat.show(bsz) ++ " nkv=" ++ Nat.show(nkv) ++ " S=" ++ Nat.show(S) ++ " nq=" ++
    Nat.show(nq) ++ " ql=" ++ Nat.show(ql) ++ " o=" ++ Nat.show(Bd.check_o(bsz, nkv, S)) ++
    " ml=" ++ Nat.show(Bd.check_ml(bsz, nkv, S)) ++ " out=" ++ Nat.show(Bd.check_out(bsz, ql, nq)) ++
    corners_b([0n, Nat.sub(bsz, 1n)], nkv, S) ++ outs_b([0n, Nat.sub(bsz, 1n)], nkv, nq, ql)

def line_h(+sms: Nat, +bsz: Nat, +kvh: Nat, +splits: Nat, +nsub: Nat, +rows: Nat, +hd: Nat) -> String:
  "H sms=" ++ Nat.show(sms) ++ " bsz=" ++ Nat.show(bsz) ++ " kvh=" ++ Nat.show(kvh) ++ " S=" ++
    Nat.show(Bd.host_splits(sms, kvh)) ++ " pn_o=" ++
    Nat.show(Bd.host_pn_o(bsz, kvh, splits, nsub, rows, hd, sms)) ++ " pn_ml=" ++
    Nat.show(Bd.host_pn_ml(bsz, kvh, splits, nsub, rows, sms))

# G: attn_verify_gr's splits check and whether the combine runs past its `live > AV_HD` trap
def line_g(+S: Nat, +L: Nat) -> String:
  "G S=" ++ Nat.show(S) ++ " L=" ++ Nat.show(L) ++ " gr=" ++ Nat.show(Impl.bit(Bd.gr_ok(S))) ++
    " live=" ++ Nat.show(Impl.live_slots(Impl.live_tiles(L), S)) ++ " runs=" ++
    Nat.show(Impl.bit(Bd.combine_runs(Impl.live_slots(Impl.live_tiles(L), S))))

def per_g(ls: List<&2, Nat>, +S: Nat) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case l <> rest:
      do IO<Unit>:
        IO.print(line_g(S, l))
        per_g(rest, S)

def per_gs(ss: List<&2, Nat>) -> IO(Unit):
  match ss:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case s <> rest:
      do IO<Unit>:
        per_g([1n, 16384n, 16385n, 16448n, 16449n, 38400n], s)
        per_gs(rest)

# Must match LS / SS / BIG / IDX / HOST / GS / GL of attn_stride_diff.py
def main() -> IO(Unit):
  do IO<Unit>:
    per_l([1n, 8n, 63n, 64n, 65n, 127n, 128n, 129n, 511n, 512n, 513n, 1000n, 1279n, 1280n, 1281n, 1343n, 2560n, 4104n])
    per_ls(18608n, 20n)
    per_ls(32776n, 20n)
    per_ls(262152n, 20n)
    IO.print(line_c(1n, 4n, 20n, 24n, 8n))
    IO.print(line_c(2n, 4n, 3n, 24n, 3n))
    IO.print(line_c(1n, 8n, 1n, 32n, 1n))
    IO.print(line_c(2n, 2n, 82n, 12n, 8n))
    IO.print(line_c(3n, 1n, 5n, 6n, 5n))
    per_gs([0n, 1n, 82n, 255n, 256n, 257n, 512n, 513n])
    IO.print(line_h(82n, 1n, 4n, 39n, 3n, 16n, 256n))
    IO.print(line_h(82n, 1n, 4n, 10n, 1n, 16n, 256n))
    IO.print(line_h(46n, 1n, 8n, 2n, 4n, 16n, 256n))
    IO.print(line_h(82n, 2n, 1n, 4n, 1n, 16n, 256n))
    IO.print(line_h(4n, 1n, 8n, 1n, 1n, 16n, 256n))
    IO.print(line_h(82n, 4n, 4n, 20n, 2n, 16n, 128n))
