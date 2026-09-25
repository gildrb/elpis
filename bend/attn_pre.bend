# Model of ext 3007's fused pre-attention kernel (exllamav3_ext/attn_small.cu: attn_pre_gr launcher
# + attn_pre_kernel), transcribed over Nat from the kernel's index expressions (lines quoted by
# bend/attn_pre_diff.py). One launch replaces deinterleave_qg + rope (head norm, RoPE) +
# quant_cache_paged (bend/attn_pre_spec.bend). Floating-point work is not modelled here: the
# per-element operations are the unfused kernels' own lines (REPORT.md section 2); this model is the
# addressing: which halves each thread reads and writes, and where each quantized group lands.
# Element convention as in the spec: half2 lane t = halves 2 t + j, uint4 lane i = halves 8 i + j,
# quant_block_x4 lane l = halves 4 l + v of its span.
# Modelling assumption (documented, not checked by the diff): after store_head, sh_head[x] holds the
# half the row just stored to k at the head's element x (x < head_dim); the K quantization reads the
# shared copy, so its source is modelled as the k element (attn_small.cu store_head / quant call).
import Base

def cdiv(+a: Nat, +b: Nat) -> Nat:
  Nat.div(Nat.sub(Nat.add(a, b), 1n), b)

# ---- launcher (attn_pre_gr) ----
# int warps = CEIL_DIVIDE(head_dim / 2, 32); int thr = warps * 32;
def warps(+hd: Nat) -> Nat:
  cdiv(Nat.div(hd, 2n), 32n)

# int parallel_heads = MIN(heads_per_block, heads);
def par(+P: Nat, +J: Nat) -> Nat:
  Nat.min(P, J)

# dim3 blocks(seq_len, bsz, CEIL_DIVIDE(heads, parallel_heads));
def zgrid(+J: Nat, +P: Nat) -> Nat:
  cdiv(J, par(P, J))

# ---- strided loops `for (x = x0; x < lim; x += step)`; `go` is the loop condition. `fuel`
# bounds the model's iterations only (callers pass lim + 1: each step adds step >= 1).
def loop.go(fuel: Nat, go: Bool, +x: Nat, +step: Nat, +lim: Nat) -> List<&2, Nat>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      match go:
        case True{}:
          x <> loop.go(f, Nat.is_lt(Nat.add(x, step), lim), Nat.add(x, step), step, lim)
        case False{}:
          Nil{}

def loop(+x0: Nat, +step: Nat, +lim: Nat) -> List<&2, Nat>:
  loop.go(1n+lim, Nat.is_lt(x0, lim), x0, step, lim)

# for (int head_idx = blockIdx.z * blockDim.y + threadIdx.y; head_idx < num_heads_q + num_heads_k;
#      head_idx += gridDim.z * blockDim.y): the head jobs of thread row y of block z
def heads(+z: Nat, +y: Nat, +Pb: Nat, +Z: Nat, +J: Nat) -> List<&2, Nat>:
  loop(Nat.add(Nat.mul(z, Pb), y), Nat.mul(Z, Pb), J)

# ---- per head job ----
# const int row = batch * seq_len + token_pos;  (batch = blockIdx.y, token_pos = blockIdx.x)
def row(+b: Nat, +S: Nat, +tok: Nat) -> Nat:
  Nat.add(Nat.mul(b, S), tok)

# q head: g_head_in_ptr = qg + ((size_t) row * num_heads_q + head_idx) * 2 * head_dim;
def qg_head(+r: Nat, +nq: Nat, +h: Nat, +hd: Nat) -> Nat:
  Nat.mul(Nat.mul(Nat.add(Nat.mul(r, nq), h), 2n), hd)

#         g_head_out_ptr = q_out + ((size_t) row * num_heads_q + head_idx) * head_dim;
def q_head(+r: Nat, +nq: Nat, +h: Nat, +hd: Nat) -> Nat:
  Nat.mul(Nat.add(Nat.mul(r, nq), h), hd)

# k head: g_head_out_ptr = k + ((size_t) row * num_heads_k + kv_head) * head_dim; in = out
def k_head(+r: Nat, +nk: Nat, +kvh: Nat, +hd: Nat) -> Nat:
  Nat.mul(Nat.add(Nat.mul(r, nk), kvh), hd)

# load_head / store_head: ((half2*) ptr)[t] for t < head_dim / 2
def lane2(+base: Nat, +t: Nat, +j: Nat) -> Nat:
  Nat.add(base, Nat.add(Nat.mul(t, 2n), j))

# gate copy: gs = (const uint4*) (g_head_in_ptr + head_dim); gd = (uint4*) (g_out + ((size_t) row *
# num_heads_q + head_idx) * head_dim); for (i = t; i < head_dim / 8; i += blockDim.x) gd[i] = gs[i]
def g_in(+r: Nat, +nq: Nat, +h: Nat, +hd: Nat, +i: Nat, +j: Nat) -> Nat:
  Nat.add(Nat.add(qg_head(r, nq, h, hd), hd), Nat.add(Nat.mul(i, 8n), j))

def g_out(+r: Nat, +nq: Nat, +h: Nat, +hd: Nat, +i: Nat, +j: Nat) -> Nat:
  Nat.add(q_head(r, nq, h, hd), Nat.add(Nat.mul(i, 8n), j))

# apply_rope: int offset = partial_head_dim * rdim; the NEOX / GPT-J pairs are rope_kernel's
def offset(+pd: Nat, +rdim: Nat) -> Nat:
  Nat.mul(pd, rdim)

def neox_pair(+offset: Nat, +t: Nat, +pd: Nat) -> Nat & Nat:
  (Nat.add(offset, t), Nat.add(Nat.add(offset, t), Nat.div(pd, 2n)))

def gptj_pair(+offset: Nat, +t: Nat) -> Nat & Nat:
  (Nat.add(offset, Nat.mul(t, 2n)), Nat.add(Nat.add(offset, Nat.mul(t, 2n)), 1n))

# ---- K / V quantization of a k head (kv_head = head_idx - num_heads_q) ----
# int chunks = head_dim / 128; for (int c = warp_id; c < 2 * chunks; c += warps)
def chunks(+hd: Nat) -> Nat:
  Nat.div(hd, 128n)

def warp_chunks(+w: Nat, +hd: Nat) -> List<&2, Nat>:
  loop(w, warps(hd), Nat.mul(2n, chunks(hd)))

# bool is_v = c >= chunks; int cc = is_v ? c - chunks : c;
def cc_of.pick(is_v: Bool, +c: Nat, +n: Nat) -> Nat:
  match is_v:
    case True{}:
      Nat.sub(c, n)
    case False{}:
      c

def cc_of(+c: Nat, +hd: Nat) -> Nat:
  cc_of.pick(Nat.is_ge(c, chunks(hd)), c, chunks(hd))

# the V half of the loop: is_v
def is_v(+c: Nat, +hd: Nat) -> Bool:
  Nat.is_ge(c, chunks(hd))

# int g0 = (kv_head * head_dim + cc * 128) / 32;
def g0(+kvh: Nat, +hd: Nat, +cc: Nat) -> Nat:
  Nat.div(Nat.add(Nat.mul(kvh, hd), Nat.mul(cc, 128n)), 32n)

# int token_idx = token_pos + cache_seqlens[batch]; int page_idx = token_idx / CQ_PAGE_SIZE;
# int token_phys = block_table[blocks_per_seq * batch + page_idx] * CQ_PAGE_SIZE + (token_idx % CQ_PAGE_SIZE);
def token_idx(+tok: Nat, +seqlen: Nat) -> Nat:
  Nat.add(tok, seqlen)

def bt_index(+bps: Nat, +b: Nat, +ti: Nat) -> Nat:
  Nat.add(Nat.mul(bps, b), Nat.div(ti, 256n))

def token_phys(~bt: Nat -> Nat, +bps: Nat, +b: Nat, +ti: Nat) -> Nat:
  Nat.add(Nat.mul(bt(bt_index(bps, b, ti)), 256n), Nat.mod(ti, 256n))

# int base = token_phys * groups_per_token + g0;
def base(+phys: Nat, +gpt: Nat, +g0: Nat) -> Nat:
  Nat.add(Nat.mul(phys, gpt), g0)

# K: quant_block_x4<BITS>(sh_head + cc * 128, ...) with sh_head = the stored k head (see header);
# V: quant_block_x4<BITS>(v + ((size_t) row * num_heads_k + kv_head) * head_dim + cc * 128, ...);
# lane l reads halves 4 l + v of the span
def kv_src(+r: Nat, +nk: Nat, +kvh: Nat, +hd: Nat, +cc: Nat, +l: Nat, +v: Nat) -> Nat:
  Nat.add(Nat.add(k_head(r, nk, kvh, hd), Nat.mul(cc, 128n)), Nat.add(Nat.mul(l, 4n), v))

# k_cache + (size_t) base * BITS: word `lane` (lane < 4 BITS); k_scales + base: scale `lane` (< 4)
def word(+base: Nat, +bits: Nat, +lane: Nat) -> Nat:
  Nat.add(Nat.mul(base, bits), lane)

def scale(+base: Nat, +lane: Nat) -> Nat:
  Nat.add(base, lane)
