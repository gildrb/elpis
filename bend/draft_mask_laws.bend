# Laws of the DFlash2 draft attention mask (exl3 patch 0005-draft-block-mask) over the Bend model
# bend/draft_mask.bend (config -> _normalize_window -> GQA split kernel window start and mask)
# against the independent z-lab reference bend/draft_mask_spec.bend.
# Domains: any config is_causal (absent, true, false), any admitted window W = 1 + w, any cache
# length S, any q_len L, any query row r, any key n, any BLOCK_N (BLOCK_N = 0 included: Nat.div
# by 0 is 0, so lo = 0). The served drafter is is_causal false, W = 2048, L = 8, BLOCK_N = 64
# (bc_attn.py:283, head_dim 128).
import Base
import ./draft_mask.bend as Impl
import ./draft_mask_spec.bend as Spec

# The window start never skips a key the left window keeps: with WINDOW_LEFT = l (or none), every
# key n passing the left test q_abs <= n + l lies at or after lo, for every S, r and BLOCK_N.
law start_keeps_left:
  for l: Impl.Side
  for +S: Nat
  for +r: Nat
  for +n: Nat
  for +BN: Nat
  for left: {Impl.left_ok(l, Nat.add(S, r), n) == True{} : Bool}
  {Nat.is_le(Impl.start(l, S, BN), n) == True{} : Bool}

# Refinement: post-0005 the draft kernel keeps exactly the keys the reference shows, for every
# admitted window, every is_causal setting, every cache length, block size, row, key and BLOCK_N.
law mask_refines:
  for cfg: Maybe<&2, Bool>
  for +w: Nat
  for +S: Nat
  for +L: Nat
  for +r: Nat
  for +n: Nat
  for +BN: Nat
  {Impl.draft_keep(cfg, w, S, L, r, n, BN) ==
    Spec.visible(Spec.layer_causal(cfg), 1n+w, Nat.add(S, L), Nat.add(S, r), n) : Bool}

# Fail closed: a zero window yields no kernel request; every W >= 1 yields the modeled one.
law window_admitted:
  for cfg: Maybe<&2, Bool>
  for +w: Nat
  {Impl.draft_req(cfg, 0n) == None{} : Maybe<&2, Impl.Req>} &
  {Impl.draft_req(cfg, 1n+w) == Some{Impl.req_of(cfg, w)} : Maybe<&2, Impl.Req>}

# The served drafter (is_causal false, sliding_window 2048) gets kernel window (2047, 2047).
law served_window:
  {Impl.normalize(Impl.req_of(Some{False{}}, 2047n)) == Impl.Win{Impl.At{2047n}, Impl.At{2047n}}
    : Impl.Win}

# Witness that g7n (pre-0005) differs from the reference: at cache length 0, q_len 8, query row
# 0 does not see block key 1 under g7n's (2048, 0), while the reference (is_causal false, W 2048)
# shows it.
law g7n_differs:
  {Impl.g7n_keep(2048n, 0n, 8n, 0n, 1n, 64n) == False{} : Bool} &
  {Spec.visible(Spec.layer_causal(Some{False{}}), 2048n, 8n, 0n, 1n) == True{} : Bool}
