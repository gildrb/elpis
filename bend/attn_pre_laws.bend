# Laws of ext 3007's fused pre-attention kernel (attn_small.cu attn_pre_kernel) over the Nat model
# bend/attn_pre.bend, against the unfused deinterleave_qg / rope / quant_cache_paged index maps of
# bend/attn_pre_spec.bend. Addressing only (which halves, groups and words each thread touches); the
# per-element float operations are the unfused kernels' own lines (REPORT.md section 2) and the
# numbers are checked on the GPU (bench_attn_small.py). Domains: head_dim = 8 hd8 for the q / gate
# laws, head_dim = 128 C for the quantization laws (attn_pre_gr requires head_dim % 128 == 0; the
# served shape is head_dim 256: hd8 = 32, C = 2). Rows r = batch * seq_len + token_pos are any Nat.
# The finite link to the CUDA source is bend/attn_pre_diff.py (quoted lines vs ATTN_PRE_TABLE.bend).
import Base
import ./attn_pre.bend as Impl
import ./attn_pre_spec.bend as Spec

# ---- (1) head jobs: every head of a token row is handled by exactly one thread row ----

# The launch grid covers every head: J <= Z * par and par >= 1 (P, J >= 1).
law grid_covers:
  for +J: Nat
  for +P: Nat
  for jpos: {Nat.is_lt(0n, J) == True{} : Bool}
  for ppos: {Nat.is_lt(0n, P) == True{} : Bool}
  {Nat.is_le(J, Nat.mul(Impl.zgrid(J, P), Impl.par(P, J))) == True{} : Bool} &
  {Nat.is_lt(0n, Impl.par(P, J)) == True{} : Bool}

# With a covering grid, the head loop of thread row y < Pb of block z runs at most once: its only
# head is z * Pb + y, when that is a head.
law heads_single:
  for +z: Nat
  for +y: Nat
  for +Pb: Nat
  for +Z: Nat
  for +J: Nat
  for fits: {Nat.is_le(J, Nat.mul(Z, Pb)) == True{} : Bool}
  {Impl.heads(z, y, Pb, Z, J) == Spec.opt(Nat.is_lt(Nat.add(Nat.mul(z, Pb), y), J),
    Nat.add(Nat.mul(z, Pb), y)) : List<&2, Nat>}

# Cover: head h < J is the job of thread row h % Pb of block h / Pb, a thread of the grid.
law heads_cover:
  for +h: Nat
  for +Pb: Nat
  for +Z: Nat
  for +J: Nat
  for pos: {Nat.is_lt(0n, Pb) == True{} : Bool}
  for fits: {Nat.is_le(J, Nat.mul(Z, Pb)) == True{} : Bool}
  for inside: {Nat.is_lt(h, J) == True{} : Bool}
  {Nat.is_lt(Nat.div(h, Pb), Z) == True{} : Bool} &
  {Nat.is_lt(Nat.mod(h, Pb), Pb) == True{} : Bool} &
  {Impl.heads(Nat.div(h, Pb), Nat.mod(h, Pb), Pb, Z, J) == h <> Nil{} : List<&2, Nat>}

# Exclusive: a thread row y < Pb whose loop visits head h is that row (with heads_single: once).
law heads_exclusive:
  for +z: Nat
  for +y: Nat
  for +h: Nat
  for +Pb: Nat
  for +Z: Nat
  for +J: Nat
  for row: {Nat.is_lt(y, Pb) == True{} : Bool}
  for fits: {Nat.is_le(J, Nat.mul(Z, Pb)) == True{} : Bool}
  for hit: {Spec.member(Impl.heads(z, y, Pb, Z, J), h) == True{} : Bool}
  {z == Nat.div(h, Pb) : Nat} & {y == Nat.mod(h, Pb) : Nat}

# ---- (2) q / gate / k halves: sources and destinations ----

# The q half a fused lane reads from the interleaved row is the qg half deinterleave_qg copies into
# the q half the lane writes (so the head's q values are the unfused ones).
law q_source:
  for +r: Nat
  for +nq: Nat
  for +h: Nat
  for +hd8: Nat
  for +t: Nat
  for +j: Nat
  for lane: {Nat.is_lt(t, Nat.mul(hd8, 4n)) == True{} : Bool}
  for half: {Nat.is_lt(j, 2n) == True{} : Bool}
  {Impl.lane2(Impl.qg_head(r, nq, h, Nat.mul(hd8, 8n)), t, j) ==
    Spec.deint_q_elem(Impl.lane2(Impl.q_head(r, nq, h, Nat.mul(hd8, 8n)), t, j), hd8) : Nat}

# The gate half a fused lane copies is the one deinterleave_qg copies to the same g half.
law g_source:
  for +r: Nat
  for +nq: Nat
  for +h: Nat
  for +hd8: Nat
  for +i: Nat
  for +j: Nat
  for vec: {Nat.is_lt(i, hd8) == True{} : Bool}
  for half: {Nat.is_lt(j, 8n) == True{} : Bool}
  {Impl.g_in(r, nq, h, Nat.mul(hd8, 8n), i, j) ==
    Spec.deint_g_elem(Impl.g_out(r, nq, h, Nat.mul(hd8, 8n), i, j), hd8) : Nat}

# The q and k halves a fused lane writes are rope_kernel's halves of the same (batch, token, head, lane).
law rope_dest:
  for +b: Nat
  for +S: Nat
  for +tok: Nat
  for +n: Nat
  for +h: Nat
  for +hd: Nat
  for +t: Nat
  for +j: Nat
  {Impl.lane2(Impl.q_head(Impl.row(b, S, tok), n, h, hd), t, j) ==
    Spec.lane2(Spec.rope_head(b, S, tok, n, h, hd), t, j) : Nat} &
  {Impl.lane2(Impl.k_head(Impl.row(b, S, tok), n, h, hd), t, j) ==
    Spec.lane2(Spec.rope_head(b, S, tok, n, h, hd), t, j) : Nat}

# Exactly once, q (and k, the same map over num_heads_k): two lanes of heads < n writing the same
# half are the same (row, head, lane, half) ...
law head_lanes_inj:
  for +r1: Nat
  for +h1: Nat
  for +t1: Nat
  for +j1: Nat
  for +r2: Nat
  for +h2: Nat
  for +t2: Nat
  for +j2: Nat
  for +n: Nat
  for +hd8: Nat
  for hh1: {Nat.is_lt(h1, n) == True{} : Bool}
  for hh2: {Nat.is_lt(h2, n) == True{} : Bool}
  for tt1: {Nat.is_lt(t1, Nat.mul(hd8, 4n)) == True{} : Bool}
  for tt2: {Nat.is_lt(t2, Nat.mul(hd8, 4n)) == True{} : Bool}
  for jj1: {Nat.is_lt(j1, 2n) == True{} : Bool}
  for jj2: {Nat.is_lt(j2, 2n) == True{} : Bool}
  for same: {Impl.lane2(Impl.q_head(r1, n, h1, Nat.mul(hd8, 8n)), t1, j1) ==
    Impl.lane2(Impl.q_head(r2, n, h2, Nat.mul(hd8, 8n)), t2, j2) : Nat}
  {r1 == r2 : Nat} & {h1 == h2 : Nat} & {t1 == t2 : Nat} & {j1 == j2 : Nat}

# ... and every half e of the buffer is written: by lane (e % hd) / 2, half e % 2, of head
# (e / hd) % n of row (e / hd) / n (a head job of the grid by heads_cover).
law head_lanes_cover:
  for +e: Nat
  for +n: Nat
  for +hd8: Nat
  for npos: {Nat.is_lt(0n, n) == True{} : Bool}
  for dpos: {Nat.is_lt(0n, hd8) == True{} : Bool}
  {Nat.is_lt(Nat.mod(Nat.div(e, Nat.mul(hd8, 8n)), n), n) == True{} : Bool} &
  {Nat.is_lt(Nat.div(Nat.mod(e, Nat.mul(hd8, 8n)), 2n), Nat.mul(hd8, 4n)) == True{} : Bool} &
  {Nat.is_lt(Nat.mod(Nat.mod(e, Nat.mul(hd8, 8n)), 2n), 2n) == True{} : Bool} &
  {Impl.lane2(Impl.q_head(Nat.div(Nat.div(e, Nat.mul(hd8, 8n)), n), n,
      Nat.mod(Nat.div(e, Nat.mul(hd8, 8n)), n), Nat.mul(hd8, 8n)),
    Nat.div(Nat.mod(e, Nat.mul(hd8, 8n)), 2n), Nat.mod(Nat.mod(e, Nat.mul(hd8, 8n)), 2n)) == e : Nat}

# k heads use the same map as q heads (so head_lanes_inj / head_lanes_cover cover k too).
law k_is_q_map:
  for +r: Nat
  for +n: Nat
  for +h: Nat
  for +hd: Nat
  {Impl.k_head(r, n, h, hd) == Impl.q_head(r, n, h, hd) : Nat}

# qg read once: a q lane's half and a gate lane's half never coincide, and each kind is injective
# (the q-lane reads are head_lanes_inj over the doubled row: qg_head(r, n, h, hd) = q_head(r, n, h,
# hd) * 2 ... stated directly).
law qg_reads_inj:
  for +r1: Nat
  for +h1: Nat
  for +t1: Nat
  for +j1: Nat
  for +r2: Nat
  for +h2: Nat
  for +t2: Nat
  for +j2: Nat
  for +n: Nat
  for +hd8: Nat
  for hh1: {Nat.is_lt(h1, n) == True{} : Bool}
  for hh2: {Nat.is_lt(h2, n) == True{} : Bool}
  for tt1: {Nat.is_lt(t1, Nat.mul(hd8, 4n)) == True{} : Bool}
  for tt2: {Nat.is_lt(t2, Nat.mul(hd8, 4n)) == True{} : Bool}
  for jj1: {Nat.is_lt(j1, 2n) == True{} : Bool}
  for jj2: {Nat.is_lt(j2, 2n) == True{} : Bool}
  for same: {Impl.lane2(Impl.qg_head(r1, n, h1, Nat.mul(hd8, 8n)), t1, j1) ==
    Impl.lane2(Impl.qg_head(r2, n, h2, Nat.mul(hd8, 8n)), t2, j2) : Nat}
  {r1 == r2 : Nat} & {h1 == h2 : Nat} & {t1 == t2 : Nat} & {j1 == j2 : Nat}

law qg_q_ne_g:
  for +r1: Nat
  for +h1: Nat
  for +t: Nat
  for +j: Nat
  for +r2: Nat
  for +h2: Nat
  for +i: Nat
  for +k: Nat
  for +n: Nat
  for +hd8: Nat
  for tt: {Nat.is_lt(t, Nat.mul(hd8, 4n)) == True{} : Bool}
  for jj: {Nat.is_lt(j, 2n) == True{} : Bool}
  for ii: {Nat.is_lt(i, hd8) == True{} : Bool}
  for kk: {Nat.is_lt(k, 8n) == True{} : Bool}
  for same: {Impl.lane2(Impl.qg_head(r1, n, h1, Nat.mul(hd8, 8n)), t, j) ==
    Impl.g_in(r2, n, h2, Nat.mul(hd8, 8n), i, k) : Nat}
  Empty

# ---- (3) RoPE pairs ----

# The fused pairs are rope_kernel's (BC_Attention passes rotate_offset 0).
law rope_pairs_match:
  for +pd: Nat
  for +rdim: Nat
  for +t: Nat
  {Impl.neox_pair(Impl.offset(pd, rdim), t, pd) ==
    Spec.neox_pair(Spec.rope_offset(0n, pd, rdim), t, pd) : Nat & Nat} &
  {Impl.gptj_pair(Impl.offset(pd, rdim), t) ==
    Spec.gptj_pair(Spec.rope_offset(0n, pd, rdim), t) : Nat & Nat}

# The pairs partition the rotated span [0, pd rd), pd = 2 ph: every element a is side
# (a % pd) / ph of NEOX pair t = (a % pd) % ph of block rdim = a / pd, and side (a % pd) % 2 of GPT-J
# pair (a % pd) / 2 ...
law rope_pairs_cover:
  for +a: Nat
  for +ph: Nat
  for pos: {Nat.is_lt(0n, ph) == True{} : Bool}
  {Nat.is_lt(Nat.mod(Nat.mod(a, Nat.mul(ph, 2n)), ph), ph) == True{} : Bool} &
  {Nat.is_lt(Nat.div(Nat.mod(a, Nat.mul(ph, 2n)), ph), 2n) == True{} : Bool} &
  {Spec.side_of(Nat.div(Nat.mod(a, Nat.mul(ph, 2n)), ph),
    Impl.neox_pair(Impl.offset(Nat.mul(ph, 2n), Nat.div(a, Nat.mul(ph, 2n))),
      Nat.mod(Nat.mod(a, Nat.mul(ph, 2n)), ph), Nat.mul(ph, 2n))) == a : Nat} &
  {Nat.is_lt(Nat.div(Nat.mod(a, Nat.mul(ph, 2n)), 2n), ph) == True{} : Bool} &
  {Spec.side_of(Nat.mod(Nat.mod(a, Nat.mul(ph, 2n)), 2n),
    Impl.gptj_pair(Impl.offset(Nat.mul(ph, 2n), Nat.div(a, Nat.mul(ph, 2n))),
      Nat.div(Nat.mod(a, Nat.mul(ph, 2n)), 2n))) == a : Nat}

# ... and no element is in two pairs (or twice in one): NEOX
law rope_neox_inj:
  for +r1: Nat
  for +t1: Nat
  for +s1: Nat
  for +r2: Nat
  for +t2: Nat
  for +s2: Nat
  for +ph: Nat
  for tt1: {Nat.is_lt(t1, ph) == True{} : Bool}
  for tt2: {Nat.is_lt(t2, ph) == True{} : Bool}
  for ss1: {Nat.is_lt(s1, 2n) == True{} : Bool}
  for ss2: {Nat.is_lt(s2, 2n) == True{} : Bool}
  for same: {Spec.side_of(s1, Impl.neox_pair(Impl.offset(Nat.mul(ph, 2n), r1), t1, Nat.mul(ph, 2n))) ==
    Spec.side_of(s2, Impl.neox_pair(Impl.offset(Nat.mul(ph, 2n), r2), t2, Nat.mul(ph, 2n))) : Nat}
  {r1 == r2 : Nat} & {t1 == t2 : Nat} & {s1 == s2 : Nat}

# ... GPT-J
law rope_gptj_inj:
  for +r1: Nat
  for +t1: Nat
  for +s1: Nat
  for +r2: Nat
  for +t2: Nat
  for +s2: Nat
  for +ph: Nat
  for tt1: {Nat.is_lt(t1, ph) == True{} : Bool}
  for tt2: {Nat.is_lt(t2, ph) == True{} : Bool}
  for ss1: {Nat.is_lt(s1, 2n) == True{} : Bool}
  for ss2: {Nat.is_lt(s2, 2n) == True{} : Bool}
  for same: {Spec.side_of(s1, Impl.gptj_pair(Impl.offset(Nat.mul(ph, 2n), r1), t1)) ==
    Spec.side_of(s2, Impl.gptj_pair(Impl.offset(Nat.mul(ph, 2n), r2), t2)) : Nat}
  {r1 == r2 : Nat} & {t1 == t2 : Nat} & {s1 == s2 : Nat}

# ---- (4) K / V quantization: chunks tile the heads, land where the unfused kernel writes ----

# Each warp w < warps of a k head row takes exactly chunk w, and there are 2 C of them (C K chunks,
# then C V chunks): head_dim = 128 C gives warps = 2 C.
law warp_chunks:
  for +C: Nat
  for +w: Nat
  for ww: {Nat.is_lt(w, Nat.mul(2n, C)) == True{} : Bool}
  {Impl.warps(Nat.mul(C, 128n)) == Nat.mul(2n, C) : Nat} &
  {Impl.chunks(Nat.mul(C, 128n)) == C : Nat} &
  {Impl.warp_chunks(w, Nat.mul(C, 128n)) == w <> Nil{} : List<&2, Nat>}

# Chunk c < 2 C is K chunk c or V chunk c - C, cc < C either way.
law chunk_cc:
  for +C: Nat
  for +c: Nat
  for cw: {Nat.is_lt(c, Nat.mul(2n, C)) == True{} : Bool}
  {Nat.is_lt(Impl.cc_of(c, Nat.mul(C, 128n)), C) == True{} : Bool}

# The group offset of chunk (kv_head, cc) is 4 (kv_head C + cc), exactly (no truncation).
law g0_exact:
  for +kvh: Nat
  for +C: Nat
  for +cc: Nat
  {Impl.g0(kvh, Nat.mul(C, 128n), cc) == Nat.mul(Nat.add(Nat.mul(kvh, C), cc), 4n) : Nat}

# The chunks tile the k / v buffers exactly once: lane l < 32, value v < 4 of chunk cc < C of head
# kvh < n is a distinct half ...
law chunk_tile_inj:
  for +r1: Nat
  for +k1: Nat
  for +c1: Nat
  for +l1: Nat
  for +v1: Nat
  for +r2: Nat
  for +k2: Nat
  for +c2: Nat
  for +l2: Nat
  for +v2: Nat
  for +n: Nat
  for +C: Nat
  for kk1: {Nat.is_lt(k1, n) == True{} : Bool}
  for kk2: {Nat.is_lt(k2, n) == True{} : Bool}
  for cc1: {Nat.is_lt(c1, C) == True{} : Bool}
  for cc2: {Nat.is_lt(c2, C) == True{} : Bool}
  for ll1: {Nat.is_lt(l1, 32n) == True{} : Bool}
  for ll2: {Nat.is_lt(l2, 32n) == True{} : Bool}
  for vv1: {Nat.is_lt(v1, 4n) == True{} : Bool}
  for vv2: {Nat.is_lt(v2, 4n) == True{} : Bool}
  for same: {Impl.kv_src(r1, n, k1, Nat.mul(C, 128n), c1, l1, v1) ==
    Impl.kv_src(r2, n, k2, Nat.mul(C, 128n), c2, l2, v2) : Nat}
  {r1 == r2 : Nat} & {k1 == k2 : Nat} & {c1 == c2 : Nat} & {l1 == l2 : Nat} & {v1 == v2 : Nat}

# ... and every half e is covered: head (e / hd) % n, chunk x / 128, lane (x % 128) / 4, value x % 4
# with x = e % hd, hd = 128 C.
law chunk_tile_cover:
  for +e: Nat
  for +n: Nat
  for +C: Nat
  for npos: {Nat.is_lt(0n, n) == True{} : Bool}
  for cpos: {Nat.is_lt(0n, C) == True{} : Bool}
  {Nat.is_lt(Nat.mod(Nat.div(e, Nat.mul(C, 128n)), n), n) == True{} : Bool} &
  {Nat.is_lt(Nat.div(Nat.mod(e, Nat.mul(C, 128n)), 128n), C) == True{} : Bool} &
  {Nat.is_lt(Nat.div(Nat.mod(Nat.mod(e, Nat.mul(C, 128n)), 128n), 4n), 32n) == True{} : Bool} &
  {Nat.is_lt(Nat.mod(Nat.mod(Nat.mod(e, Nat.mul(C, 128n)), 128n), 4n), 4n) == True{} : Bool} &
  {Impl.kv_src(Nat.div(Nat.div(e, Nat.mul(C, 128n)), n), n, Nat.mod(Nat.div(e, Nat.mul(C, 128n)), n),
    Nat.mul(C, 128n), Nat.div(Nat.mod(e, Nat.mul(C, 128n)), 128n),
    Nat.div(Nat.mod(Nat.mod(e, Nat.mul(C, 128n)), 128n), 4n),
    Nat.mod(Nat.mod(Nat.mod(e, Nat.mul(C, 128n)), 128n), 4n)) == e : Nat}

# Refinement against quant_cache_paged_kernel (in_contiguous): the unfused warp (bx, w) handling
# chunk bx usage + w = kv_head C + cc of token (b, tok) reads the same k / v halves (lane by lane)
# and writes the same base (hence the same words and scales, quant_block_x4 being shared), with
# groups_per_token = n C 4 = n head_dim / 32.
law quant_refines:
  for ~bt: Nat -> Nat
  for +b: Nat
  for +S: Nat
  for +tok: Nat
  for +seqlen: Nat
  for +bps: Nat
  for +n: Nat
  for +kvh: Nat
  for +C: Nat
  for +cc: Nat
  for +bx: Nat
  for +usage: Nat
  for +w: Nat
  for +l: Nat
  for +v: Nat
  for chunk: {Nat.add(Nat.mul(bx, usage), w) == Nat.add(Nat.mul(kvh, C), cc) : Nat}
  {Impl.kv_src(Impl.row(b, S, tok), n, kvh, Nat.mul(C, 128n), cc, l, v) ==
    Spec.q_src(Spec.q_base(Spec.q_in_pos(b, S, tok), Nat.mul(Nat.mul(n, C), 4n), Spec.q_g0(bx, usage, w)), l, v)
    : Nat} &
  {Impl.base(Impl.token_phys(~bt, bps, b, Impl.token_idx(tok, seqlen)), Nat.mul(Nat.mul(n, C), 4n),
      Impl.g0(kvh, Nat.mul(C, 128n), cc)) ==
    Spec.q_base(Spec.q_token_pos(~bt, bps, b, Spec.q_token_idx(tok, seqlen)), Nat.mul(Nat.mul(n, C), 4n),
      Spec.q_g0(bx, usage, w)) : Nat}

# groups_per_token = num_heads_k * head_dim / 32 is n C 4 exactly.
law gpt_exact:
  for +n: Nat
  for +C: Nat
  {Nat.div(Nat.mul(n, Nat.mul(C, 128n)), 32n) == Nat.mul(Nat.mul(n, C), 4n) : Nat}

# The cache row of token position ti of batch b is page block_table[bps b + ti / 256], slot ti % 256.
law cache_slot:
  for ~bt: Nat -> Nat
  for +bps: Nat
  for +b: Nat
  for +ti: Nat
  {Nat.div(Impl.token_phys(~bt, bps, b, ti), 256n) == bt(Impl.bt_index(bps, b, ti)) : Nat} &
  {Nat.mod(Impl.token_phys(~bt, bps, b, ti), 256n) == Nat.mod(ti, 256n) : Nat}

# Word `lane` of a chunk at base (phys, g0) is word lane % bits of group g0 + lane / bits of row
# phys; (row, group < gpt, word < bits) determine the word address uniquely.
law word_group:
  for +phys: Nat
  for +gpt: Nat
  for +g0: Nat
  for +bits: Nat
  for +lane: Nat
  for pos: {Nat.is_lt(0n, bits) == True{} : Bool}
  {Impl.word(Impl.base(phys, gpt, g0), bits, lane) ==
    Nat.add(Nat.mul(Nat.add(Nat.mul(phys, gpt), Nat.add(g0, Nat.div(lane, bits))), bits), Nat.mod(lane, bits)) : Nat}

law word_inj:
  for +p1: Nat
  for +g1: Nat
  for +i1: Nat
  for +p2: Nat
  for +g2: Nat
  for +i2: Nat
  for +gpt: Nat
  for +bits: Nat
  for gg1: {Nat.is_lt(g1, gpt) == True{} : Bool}
  for gg2: {Nat.is_lt(g2, gpt) == True{} : Bool}
  for ii1: {Nat.is_lt(i1, bits) == True{} : Bool}
  for ii2: {Nat.is_lt(i2, bits) == True{} : Bool}
  for same: {Nat.add(Nat.mul(Nat.add(Nat.mul(p1, gpt), g1), bits), i1) ==
    Nat.add(Nat.mul(Nat.add(Nat.mul(p2, gpt), g2), bits), i2) : Nat}
  {p1 == p2 : Nat} & {g1 == g2 : Nat} & {i1 == i2 : Nat}
