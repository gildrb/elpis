# Model of the DFlash2 draft attention mask the engine serves with exl3 patch
# 0005-draft-block-mask (on patches/exl3 0001-0003 and the patches/exl3-ext series): config ->
# window request -> kernel window -> per-key predicate of the GQA split kernel.
#   architecture/dflash.py (post-0005) dflash2_kernel_window: window W >= 1 (config
#     sliding_window, or EXL3_DFLASH2_WINDOW parsed as a positive decimal), causal = config
#     is_causal, True when absent; returns (W - 1, W - 1), or (W - 1, 0) when causal. W = 0 and W >
#     2^30 raise (the upper cap keeps the int32 kernel arithmetic in range; outside this Nat model).
#   architecture/dflash2.py:125 passes that value as Attention.sliding_window; bc_attn.py:129
#     keeps it as BCAttn.window_size; bc_attn.py:294 turns it into (WINDOW_LEFT, WINDOW_RIGHT) by
#     triton_paged._normalize_window (:279-286). Before 0005 the int config value went through
#     the same path (g7n).
#   architecture/dflash2.py:309-311 (prepare_inputs): the draft forward runs with causal=False,
#     so the kernels' CAUSAL constexpr is False (bc_attn.py:312).
#   triton_paged.py _paged_attn_decode_gqa_split_kernel (ext patch 3002 :181-189): total_k_len =
#     cache_seqlens + q_len, window start lo = floor(max(0, total_k_len - q_len - WINDOW_LEFT) /
#     BLOCK_N) * BLOCK_N when WINDOW_LEFT >= 0, else 0; its splits cover [lo, total_k_len) (unchanged
#     by 0005, not modeled). Query row r has q_abs = total_k_len - q_len + r (_gqa_rows, :76).
#     _gqa_step (:89-95) keeps key n iff n < n_end (<= total_k_len), (CAUSAL: n <= q_abs),
#     (WINDOW_LEFT >= 0: n >= q_abs - WINDOW_LEFT), (WINDOW_RIGHT >= 0: n <= q_abs + WINDOW_RIGHT).
# With S = cache_seqlens and L = q_len: total_k_len = S + L, q_abs = S + r, and
# max(0, total_k_len - q_len - WINDOW_LEFT) = S - WINDOW_LEFT truncated (Nat.sub). Integer
# comparisons n >= q - l and n <= q + r are written q <= n + l and n <= q + r (no truncation).
# Proof model (Nat, Bool), not a shipped artifact.
import Base

# A Python int handed to _normalize_window: negative (the kernels test `>= 0`) or n >= 0.
type SInt is Data:
  Neg{}
  Nn{n: Nat}

# Attention.sliding_window as the kernels receive it: an int or a (left, right) tuple.
type Req is Data:
  ReqInt{w: SInt}
  ReqPair{l: SInt, r: SInt}

# One window side as the kernel constexpr: absent (< 0) or n.
type Side is Data:
  NoWin{}
  At{n: Nat}

type Win is Data:
  Win{l: Side, r: Side}

def side(x: SInt) -> Side:
  match x:
    case Neg{}:
      NoWin{}
    case Nn{n}:
      At{n}

# triton_paged._normalize_window (:279-286): int w < 0 -> (-1, -1); int w >= 0 -> (w, 0);
# (l, r) -> (int(l), int(r)).
def normalize(req: Req) -> Win:
  match req:
    case ReqInt{w}:
      match w:
        case Neg{}:
          Win{NoWin{}, NoWin{}}
        case Nn{n}:
          Win{At{n}, At{0n}}
    case ReqPair{l, r}:
      Win{side(l), side(r)}

# 0005 dflash2_kernel_window for W = 1 + w (the admitted domain; W = 0 raises, see draft_req).
def req_of(cfg: Maybe<&2, Bool>, +w: Nat) -> Req:
  match cfg:
    case None{}:
      ReqPair{Nn{w}, Nn{0n}}
    case Some{c}:
      match c:
        case True{}:
          ReqPair{Nn{w}, Nn{0n}}
        case False{}:
          ReqPair{Nn{w}, Nn{w}}

# 0005 dflash2_kernel_window over every window: W = 0 is refused (ValueError, no request).
def draft_req(cfg: Maybe<&2, Bool>, W: Nat) -> Maybe<&2, Req>:
  match W:
    case 0n:
      None{}
    case 1n+w:
      Some{req_of(cfg, w)}

# Pre-0005 (g7n): the config int reaches _normalize_window unchanged.
def g7n_req(W: Nat) -> Req:
  ReqInt{Nn{W}}

# Window start lo (3002 :182-184).
def start(l: Side, S: Nat, +BN: Nat) -> Nat:
  match l:
    case NoWin{}:
      0n
    case At{n}:
      Nat.mul(Nat.div(Nat.sub(S, n), BN), BN)

# `if CAUSAL: n <= q_abs` (3002 :90-91).
def causal_ok(flag: Bool, +q: Nat, +n: Nat) -> Bool:
  match flag:
    case True{}:
      Nat.is_le(n, q)
    case False{}:
      True{}

# `if WINDOW_LEFT >= 0: n >= q_abs - WINDOW_LEFT` (3002 :92-93).
def left_ok(l: Side, +q: Nat, +n: Nat) -> Bool:
  match l:
    case NoWin{}:
      True{}
    case At{v}:
      Nat.is_le(q, Nat.add(n, v))

# `if WINDOW_RIGHT >= 0: n <= q_abs + WINDOW_RIGHT` (3002 :94-95).
def right_ok(r: Side, +q: Nat, +n: Nat) -> Bool:
  match r:
    case NoWin{}:
      True{}
    case At{v}:
      Nat.is_le(n, Nat.add(q, v))

# Key n reaches query row r's softmax: inside the launched range [lo, S + L) and kept by the
# _gqa_step mask, for cache length S, q_len L, BLOCK_N = BN.
def keep(win: Win, +flag: Bool, +S: Nat, +L: Nat, +r: Nat, +n: Nat, +BN: Nat) -> Bool:
  match win:
    case Win{+l, rs}:
      +q = Nat.add(S, r)
      Bool.and(Nat.is_le(start(l, S, BN), n),
        Bool.and(Nat.is_lt(n, Nat.add(S, L)),
          Bool.and(causal_ok(flag, q, n),
            Bool.and(left_ok(l, q, n), right_ok(rs, q, n)))))

# The draft forward's CAUSAL flag (dflash2.py:311).
def draft_flag() -> Bool:
  False{}

# The served mask post-0005, window W = 1 + w.
def draft_keep(cfg: Maybe<&2, Bool>, +w: Nat, +S: Nat, +L: Nat, +r: Nat, +n: Nat, +BN: Nat)
    -> Bool:
  keep(normalize(req_of(cfg, w)), draft_flag(), S, L, r, n, BN)

# The g7n mask (pre-0005), config window W.
def g7n_keep(+W: Nat, +S: Nat, +L: Nat, +r: Nat, +n: Nat, +BN: Nat) -> Bool:
  keep(normalize(g7n_req(W)), draft_flag(), S, L, r, n, BN)
