# Unfused reference of ext 3007's fused pre-attention launch: the index maps of the three launches
# attn_pre_kernel replaces in BC_Attention::run_gr (tree = HEAD 585b810 series), transcribed over Nat
# from the kernels' own expressions:
#   D = activation.cu deinterleave_qg_kernel (uint4 = 8 halves),
#   R = rope.cu rope_kernel (head pointers, half2 lanes, apply_rope pairs),
#   Q = cache/q_cache_kernels.cuh quant_cache_paged_kernel + quant_block_x4, launched by
#       cache/q_cache.cu quant_cache_paged_gr (in_contiguous = true, the BC path).
# Element convention: a half2 lane t covers halves 2 t + j (j < 2) of its pointer; a uint4 lane i
# covers halves 8 i + j (j < 8); quant_block_x4's lane l reads halves 4 l + v (v < 4) of its span
# (half2 lanes 2 l and 2 l + 1). Independent of bend/attn_pre.bend (the fused model).
import Base

def bit(value: Bool) -> Nat:
  match value:
    case True{}:
      1n
    case False{}:
      0n

# util.h CEIL_DIVIDE(x, size) = (x + size - 1) / size
def cdiv(+a: Nat, +b: Nat) -> Nat:
  Nat.div(Nat.sub(Nat.add(a, b), 1n), b)

# ---- D: deinterleave_qg_kernel(qg, q, g, hd8, n8): thread i < n8
#   d = i % hd8; h = i / hd8; src = h * 2 * hd8 + d; q[i] = qg[src]; g[i] = qg[src + hd8]
def deint_src(+i: Nat, +hd8: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.mul(Nat.div(i, hd8), 2n), hd8), Nat.mod(i, hd8))

# Half e of q is half e % 8 of uint4 e / 8: it comes from half deint_q_elem(e) of qg
def deint_q_elem(+e: Nat, +hd8: Nat) -> Nat:
  Nat.add(Nat.mul(deint_src(Nat.div(e, 8n), hd8), 8n), Nat.mod(e, 8n))

# Half e of g comes from half deint_g_elem(e) of qg (uint4 src + hd8)
def deint_g_elem(+e: Nat, +hd8: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.add(deint_src(Nat.div(e, 8n), hd8), hd8), 8n), Nat.mod(e, 8n))

# ---- R: rope_kernel, grid (seq_len, bsz, head_groups) x (thr, parallel_heads)
# q head: q + ((batch * seq_len + token_pos) * num_heads_q + head_idx) * q_head_stride (in and out);
# k head: k + ((batch * seq_len + token_pos) * num_heads_k + head_idx - num_heads_q) * k_head_stride;
# BC_Attention passes the dense q4 / k4 statics, stride = head_dim.
def rope_head(+b: Nat, +S: Nat, +tok: Nat, +n: Nat, +head: Nat, +stride: Nat) -> Nat:
  Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(b, S), tok), n), head), stride)

# ((half2*) ptr)[t]: halves 2 t + j
def lane2(+base: Nat, +t: Nat, +j: Nat) -> Nat:
  Nat.add(base, Nat.add(Nat.mul(t, 2n), j))

# apply_rope: int offset = rotate_offset + partial_head_dim * rdim;
#   NEOX: (sh_head[offset + t], sh_head[offset + t + partial_head_dim / 2]), t < partial_head_dim / 2
#   GPTJ: half2 at sh_head + offset + t * 2 (low, high)
def rope_offset(+rotate_offset: Nat, +pd: Nat, +rdim: Nat) -> Nat:
  Nat.add(rotate_offset, Nat.mul(pd, rdim))

def neox_pair(+offset: Nat, +t: Nat, +pd: Nat) -> Nat & Nat:
  (Nat.add(offset, t), Nat.add(Nat.add(offset, t), Nat.div(pd, 2n)))

def gptj_pair(+offset: Nat, +t: Nat) -> Nat & Nat:
  (Nat.add(offset, Nat.mul(t, 2n)), Nat.add(Nat.add(offset, Nat.mul(t, 2n)), 1n))

# ---- Q: quant_cache_paged_gr launch geometry (q_cache.cu):
#   groups_per_token = dim / 32; chunks_per_token = CEIL_DIVIDE(groups_per_token, 4);
#   tb_per_token = CEIL_DIVIDE(chunks_per_token, MAX_WARPS = 8);
#   tb_usage = CEIL_DIVIDE(chunks_per_token, tb_per_token); grid (tb_per_token, seq_len, bsz) x 32 tb_usage
def q_chunks(+gpt: Nat) -> Nat:
  cdiv(gpt, 4n)

def q_tb(+gpt: Nat) -> Nat:
  cdiv(q_chunks(gpt), 8n)

def q_usage(+gpt: Nat) -> Nat:
  cdiv(q_chunks(gpt), q_tb(gpt))

# quant_cache_paged_kernel, block (bx, y, batch), warp w:
#   token_idx = blockIdx.y + cache_seqlens[batch_idx]; page_idx = token_idx / CQ_PAGE_SIZE;
#   token_pos = block_table[blocks_per_seq * batch_idx + page_idx] * CQ_PAGE_SIZE + token_idx % CQ_PAGE_SIZE;
#   in_pos = in_contiguous ? batch_idx * gridDim.y + blockIdx.y : token_pos;
#   g0 = (blockIdx.x * (blockDim.x >> 5) + warp) * 4 (the warp returns when g0 >= groups_per_token);
#   base = token_pos * groups_per_token + g0; in_base = in_pos * groups_per_token + g0
def q_token_idx(+y: Nat, +seqlen: Nat) -> Nat:
  Nat.add(y, seqlen)

# block_table entry index blocks_per_seq * batch_idx + page_idx; the table itself is ~bt
def q_bt_index(+bps: Nat, +b: Nat, +ti: Nat) -> Nat:
  Nat.add(Nat.mul(bps, b), Nat.div(ti, 256n))

def q_token_pos(~bt: Nat -> Nat, +bps: Nat, +b: Nat, +ti: Nat) -> Nat:
  Nat.add(Nat.mul(bt(q_bt_index(bps, b, ti)), 256n), Nat.mod(ti, 256n))

def q_in_pos(+b: Nat, +S: Nat, +y: Nat) -> Nat:
  Nat.add(Nat.mul(b, S), y)

def q_g0(+bx: Nat, +usage: Nat, +w: Nat) -> Nat:
  Nat.mul(Nat.add(Nat.mul(bx, usage), w), 4n)

def q_base(+pos: Nat, +gpt: Nat, +g0: Nat) -> Nat:
  Nat.add(Nat.mul(pos, gpt), g0)

# quant_block_x4(k_in + in_base * 32, k_out + base * bits, k_out_scales + base, ...): lane l reads
# halves 4 l + v of its span; lane < 4 bits stores word lane; lane < active stores scale lane
def q_src(+in_base: Nat, +l: Nat, +v: Nat) -> Nat:
  Nat.add(Nat.mul(in_base, 32n), Nat.add(Nat.mul(l, 4n), v))

def q_word(+base: Nat, +bits: Nat, +lane: Nat) -> Nat:
  Nat.add(Nat.mul(base, bits), lane)

def q_scale(+base: Nat, +lane: Nat) -> Nat:
  Nat.add(base, lane)

# ---- law vocabulary ----
# The list a loop yields when its first index is its only one
def opt(hit: Bool, +x: Nat) -> List<&2, Nat>:
  match hit:
    case True{}:
      x <> Nil{}
    case False{}:
      Nil{}

# x occurs in the list
def member(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), member(rest, x))

# Element `side` of a RoPE pair: 0 = the first operand, otherwise the second
def side_of(side: Nat, p: Nat & Nat) -> Nat:
  match side:
    case 0n:
      (a, b) = p
      a
    case 1n+s:
      (a, b) = p
      b
