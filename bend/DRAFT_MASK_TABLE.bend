# Finite differential table of the DFlash2 draft mask model (bend/draft_mask.bend), compared byte
# for byte by bend/draft_mask_diff.py against the engine's own code: dflash2_kernel_window and
# _normalize_window executed from the patched sources, and the GQA split kernel's window-start,
# split, tile and mask lines (triton_paged.py, ext patch 3002) transcribed verbatim to scalars.
# One line per (is_causal, W, S, L, r, BLOCK_N): the bit of key n for n = 0 .. S + L + 1.
# Domain: is_causal absent/true/false, W 1..9, cache length S 0..20, q_len L 1..8, row r < L,
# BLOCK_N 16 and 64.
import Base
import ./draft_mask.bend as Impl

def cfg_name(cfg: Maybe<&2, Bool>) -> String:
  match cfg:
    case None{}:
      "none"
    case Some{c}:
      match c:
        case True{}:
          "true"
        case False{}:
          "false"

def bit(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def bits(k: Nat, +cfg: Maybe<&2, Bool>, +w: Nat, +S: Nat, +L: Nat, +r: Nat, +BN: Nat, +n: Nat)
    -> String:
  match k:
    case 0n:
      ""
    case 1n+m:
      bit(Impl.draft_keep(cfg, w, S, L, r, n, BN)) ++ bits(m, cfg, w, S, L, r, BN, 1n+n)

def line(+cfg: Maybe<&2, Bool>, +w: Nat, +S: Nat, +L: Nat, +r: Nat, +BN: Nat) -> String:
  "cfg=" ++ cfg_name(cfg) ++ " W=" ++ Nat.show(1n+w) ++ " S=" ++ Nat.show(S) ++ " L=" ++
    Nat.show(L) ++ " r=" ++ Nat.show(r) ++ " BN=" ++ Nat.show(BN) ++ " " ++
    bits(2n+Nat.add(S, L), cfg, w, S, L, r, BN, 0n)

def rows_r(k: Nat, +cfg: Maybe<&2, Bool>, +w: Nat, +S: Nat, +L: Nat, +r: Nat, +BN: Nat)
    -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        IO.print(line(cfg, w, S, L, r, BN))
        rows_r(m, cfg, w, S, L, 1n+r, BN)

def rows_l(k: Nat, +cfg: Maybe<&2, Bool>, +w: Nat, +S: Nat, +L: Nat, +BN: Nat) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        rows_r(L, cfg, w, S, L, 0n, BN)
        rows_l(m, cfg, w, S, 1n+L, BN)

def rows_s(k: Nat, +cfg: Maybe<&2, Bool>, +w: Nat, +S: Nat, +BN: Nat) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        rows_l(8n, cfg, w, S, 1n, BN)
        rows_s(m, cfg, w, 1n+S, BN)

def rows_w(k: Nat, +cfg: Maybe<&2, Bool>, +w: Nat, +BN: Nat) -> IO(Unit):
  match k:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+m:
      do IO<Unit>:
        rows_s(21n, cfg, w, 0n, BN)
        rows_w(m, cfg, 1n+w, BN)

def rows_bn(+cfg: Maybe<&2, Bool>) -> IO(Unit):
  do IO<Unit>:
    rows_w(9n, cfg, 0n, 16n)
    rows_w(9n, cfg, 0n, 64n)

def main() -> IO(Unit):
  do IO<Unit>:
    rows_bn(None{})
    rows_bn(Some{True{}})
    rows_bn(Some{False{}})
