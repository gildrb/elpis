# Independent reference for the DFlash2 draft attention mask: the z-lab drafter
# (github.com/z-lab/dflash dflash/model.py@07ebd93, the revision the vLLM speculators docs pin).
#   :365-367  Qwen3DFlashAttention.__init__: is_causal = config.is_causal when present, else
#             (layer_type == "sliding_attention"); sliding_window = config.sliding_window on a
#             sliding_attention layer.
#   :157-171  _attention_mask(query, key, is_causal, sliding_window):
#               query_position = key_len - q_len + i, key_position = j (j < key_len),
#               visible  = True
#               visible &= key_position <= query_position              if is_causal
#               visible &= query_position - key_position < sliding_window
#               visible &= key_position - query_position < sliding_window  if not is_causal
# Positions are integers in the reference; on Nat, q - k < W is q < k + W and k - q < W is
# k < q + W (no truncation). The draft cache holds a key for every position below key_len (the
# engine cache is full size; the reference's sliding cache only drops keys the window already
# hides), so the key domain is every k < key_len. Scope: sliding_attention layers (every layer of
# the served drafter, models/dflash2-exl3/config.json:31-37). Proof model (Nat, Bool), not a
# shipped artifact.
import Base

# :365-367 on a sliding_attention layer: config is_causal if set, else True.
def layer_causal(cfg: Maybe<&2, Bool>) -> Bool:
  match cfg:
    case None{}:
      True{}
    case Some{c}:
      c

# `visible &= key_position <= query_position` when causal.
def causal_part(causal: Bool, +q: Nat, +k: Nat) -> Bool:
  match causal:
    case True{}:
      Nat.is_le(k, q)
    case False{}:
      True{}

# `visible &= key_position - query_position < sliding_window` when not causal.
def ahead_part(causal: Bool, +W: Nat, +q: Nat, +k: Nat) -> Bool:
  match causal:
    case True{}:
      True{}
    case False{}:
      Nat.is_lt(k, Nat.add(q, W))

# Key k is visible to the query at position q, key_len = klen keys, window W, in the order the
# reference applies its conditions.
def visible(+causal: Bool, +W: Nat, +klen: Nat, +q: Nat, +k: Nat) -> Bool:
  Bool.and(Nat.is_lt(k, klen),
    Bool.and(causal_part(causal, q, k),
      Bool.and(Nat.is_lt(q, Nat.add(k, W)), ahead_part(causal, W, q, k))))
