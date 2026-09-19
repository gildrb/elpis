# Bonsai PQ2_0 native serving — engineering status

Date: 2026-09-19 (bisect session ~11:00-13:30). Branch: perf/attention-correctness @ d4c0926.
Work is UNCOMMITTED in the working tree per the task rules; Git history untouched.

## Identity (pinned this session)

- Target: prism-ml/Ternary-Bonsai-2-27B-gguf — `Ternary-Bonsai-2-27B-PQ2_0.gguf`
  sha256 `3907dc1658db1f78a9826bf8d5bcb8dc65db0d466388937af57f2294fae62ec1`,
  7,206,168,928 bytes, arch `qwen35`, 851 tensors (402 PQ2_0 / 353 F32 / 96 BF16).
- Draft: syvai/Qwen3.8-27B-DFlash2-W4A16 @ 4d30ec7 (unchanged; 2 files verified).
- Reference engine: PrismML-Eng/llama.cpp release prism-b10683-d8f26ee (source
  mirrored at /tmp/prism-ref, ephemeral — re-fetchable from GitHub at commit
  d8f26eec76da6d09bb708bcba51ef64b8cd868a3; key ops: src/models/delta-net-base.cpp,
  ggml/src/ggml-cuda/gated_delta_net.cu, ggml_compute_forward_gated_delta_net in
  ggml-cpu/ops.cpp; built binary in image `bonsai-inference:local`).
- SGLang: 0bcd822377da7b5718e674eaf9c870d349424dd1 + 23-patch experimental
  series + 2 new patches (below). Image `qwen-inference:pq2-stage1`.
- State root: /mnt/ssd/storage/ai/qwen3.8-27b. Wrapper:
  models/bonsai-pq2-wrapper (config + tokenizer + MANIFEST.json + payload symlink).

## PQ2_0 format contract (verified against the real artifact AND the fork source)

- Block 34 B / 128 weights: fp16 scale d FIRST (bytes 0-1), then 32 code bytes.
  Weight j: byte 2 + j//4, bits (2*(j%4))..+1, value (q-1)*d, codes 0..2 only
  (code 3 = +2d defined but never emitted). Quantizer ref: d = amax.
- prism.hadamard v1: block 1024, normalized natural-order WHT
  H[i][j]=(-1)^popcount(i&j)/sqrt(n); explicit per-width signs
  [5120, 6144, 17408] (28672 values). Fold = T(w) = H(D*w) on every listed
  matmul weight's input dim; token_embd rows stored latent, restore = D*(H z).
- Fold coverage exact: 401 folded == all PQ2 matmul weights; token_embd the
  only inverse table. GDN ssm_out: ggml rep-major activation is permuted to
  k-group-major before ssm_out inside the fork; SGLang's native v order equals
  that post-perm order (no perm needed for ssm_out itself).
- Norm weights: attn_norm/post_attention_norm/output_norm/attn_q_norm/attn_k_norm
  stored as (1 + w_hf) (Gemma convention); **ssm_norm stored verbatim**.

## EMPIRICAL VERIFICATIONS DONE (all against real bytes)

1. token_embd restore D*(H z) vs the W4A16 original embed row0: corr 0.886
   (wrong order 0.024, latent -0.004) — fixes F4's transform semantics.
2. ffn_down / ssm_out / attn_qkv / attn_gate / attn_q / attn_k / attn_v /
   attn_output / ffn_gate / ffn_up: corr(dequant(PQ2), T(W4A16)) = 0.874-0.882
   (raw ≈ 0) — fixes F3's identity/dims and the fold direction per weight.
3. Triton PQ2 decode == numpy reference exactly (0.0 diff) on real rows.
4. Transform forward/inverse/round-trip == numpy within fp32 eps.
5. GDN per-head vectors + conv channels + z rows are in GGML rep-major tiling
   (head = rep*16 + k_group): permuted corr 0.99 vs 0.04 direct. Serving must
   permute them to SGLang k-group-major (implemented in the loader patch).
6. Gemma norm offset: gguf = 1 + hf verified for q_norm (attn_norm checked
   analytically); ssm_norm verbatim.
7. Fork oracle: "The capital of France is" -> top-1 " Paris" (11751, -0.182),
   top-8 saved at bench/results/bonsai-oracle/p1-prompt-logprobs.json.
8. FULL 64-LAYER NUMPY REFERENCE (/tmp/manual_full.py, rebuildable): running the
   oracle prompt [760, 6511, 314, 9338, 369] (no BOS) through all 64 layers +
   final norm + folded lm_head in fp32 reproduces the fork oracle top-8 SET
   exactly and in order; top-1 " Paris" -0.1837 vs oracle -0.1818, every
   logprob within ~0.02. This validates end-to-end: stored-as-is Gemma norms,
   fold direction on both sides, VPERM, conv orientation (kernel[0] = oldest),
   decay exp(a*softplus(alpha+dt)) BEFORE the delta update, beta=sigmoid,
   gate-OUTSIDE gated norm (HF "# Norm before gate", fork ggml_swiglu_split,
   SGLang RMSNormGated norm_before_gate=True all agree), neox rope (mrope
   sections [11,11,10,0] degenerate to standard rope for text), GQA 24/4 with
   q|gate split, and the folded output head. The earlier /tmp/manual_chain.py
   had TWO bugs that invalidated the old probe numbers: it ran a 6-token
   prompt ("The capital city of France is" - token 3177 is " city") instead of
   the oracle's 5-token prompt, and it applied an extra `1 +` on full-attn
   q/k norms (the GGUF stores the final weight; the fork applies it verbatim).
9. Serving kernel faithfulness: the SGLang fla chunk GDN kernel matches an
   fp32 sequential recurrence on ITS OWN bf16 inputs per-token to ~2e-4
   relative (t1 0.04531 vs 0.04548 ... t4 0.15088 vs 0.15095); the entire
   remaining gap vs the fp32 numpy reference is bf16 activation precision
   (conv + Hadamard transform run in bf16), compounding over 64 layers to
   ~0.06 rel at the final norm. Standard bf16-serving behavior, not a bug.

## ROOT CAUSES FIXED (2026-09-19 bisect, pq2-gguf-loader.patch)

The "garbage tokens" state had THREE defects, all in
`_apply_gguf_value_transform` (weight_utils hunk of pq2-gguf-loader.patch),
all proven by dump-vs-numpy rel_l2 on the live endpoint (SGLANG_PQ2_DEBUG +
SGLANG_PQ2_DEBUG_DUMP tensor dumps, oracle prompt, call 9):

1. BF16 early-return skipped every later transform: ssm_beta/ssm_alpha
   (BF16) loaded WITHOUT the v-head permutation (served ba vs VPERM rel 1.18,
   vs NOPERM rel 0.0018). Fix: bit-reinterpret in place, then fall through.
2. Quantized tensors are renamed `.weight` -> `.qweight` before the
   transform, so every endswith(".weight") check missed: the v halves of
   attn_qkv and attn_gate (PQ2) loaded unpermuted (served v vs VPERM rel
   1.39, vs NOPERM rel 0.0018). Fix: match on hf_name with ".qweight"
   stripped. q/k parts always matched (rel 0.0019) - only v/z were wrong.
3. Dead A_log branch: "linear_attn.A_log" was inside the perm-suffix list,
   so the perm branch shadowed log(-a); the backend then computed
   g = -exp(a_raw)*softplus ~ -3e-4, i.e. decay ~ 1 (state never forgets).
   Fix: A_log conversion first, removed from the perm list.

The conv1d/dt_bias permutes (F32, unchanged names) already fired; embed was
always value-exact. After the fix: served v/z vs VPERM rel 0.0021/0.0026,
ba vs VPERM rel 0.0021; GDN core exact (see verification 9).

END-TO-END RESULT on the live bring-up endpoint (target-only, bf16 KV, eager,
18021): greedy completion of the oracle prompt returns " Paris" with logprob
-0.1789 (oracle -0.1818, numpy fp32 -0.1837); top-8 set matches the oracle
7/8 with tail-order shuffles inside the -4.4..-4.5 band (bf16 drift). The
fork-oracle parity gate for step 3 below is PASSED.

## CURRENT STATE OF THE MODEL

The stack BOOTS end-to-end and is NUMERICALLY CORRECT: target (7.2 GB, load
~28 s) + DFlash2 draft + KVarN KV + CUDA-graph flags; engine reaches
"ready to roll" and serves oracle-parity greedy output in the
target-only/bf16/eager qualification mode. VRAM fits with margin (7.0-8.1 GB
free after pools at 245760 ctx).

Previously-suspected layer-0 leads are all CLOSED: permutation direction was
consistent manual==served (the real defect was that the served permute never
ran - defects 1/2 above); decay placement and beta sigmoid were always
correct; the 2.24x/"sqrt(5)" layer0-out norm gap was an artifact of the
wrong 6-token probe prompt and pre-perm measurements; the gated norm is
gate-outside in fork, HF, and SGLang alike.

## Built this session (2026-09-18/19)

- patches/gguf-package/pq2-type-registration.patch (+ docker/build-gguf-package.sh):
  gguf-py 0.19.0 gains PQ2_0 = 142 as a first-class type, geometry (128, 34).
  No TQ2_0 aliasing (F3 repair at the parsing layer; verified in-image).
- patches/pq2-gguf-loader.patch: qwen3_5 GGUF->HF name map (48 GDN + 16 full
  layers), value transforms (BF16 bit-reinterpret — F5's real defect —,
  A_log=log(-a) FIRST (previously shadowed by the perm list — bug), conv1d
  reshape, Gemma -1 on gemma-style norms, GDN v-head permutation now applied
  for BF16 tensors and .qweight rows alike — previously skipped for both),
  wrapper-dir support in GGUFModelLoader, contract init, tuple-
  shard GGUF splitting in linear.py, lm_head.qweight routing in qwen3_5_text.py,
  quant_config passed to embed_tokens, SGLANG_PQ2_DEBUG(_DUMP) hooks.
- patches/pq2-serving-ops.patch: pq2_ops.py (contract init + validation,
  Hadamard transforms, PQ2 linear/embedding forward), pq2_triton.py (decode +
  TF32 dot matmul kernels; weights stay packed on GPU — no dense reconstruction),
  gguf.py routing (linear + embedding + process-weights check), DFlash selector
  accepts GGUF heads (logits_processor.py).
- patches/experimental.series: += pq2-gguf-loader.patch, pq2-serving-ops.patch
  (sha256-pinned; apply.sh verified on a fresh checkout).
- serve/entrypoint.sh: KVarN qualification compliance + commit-graph hook.
  Every KVarN mode now emits --disable-overlap-schedule and
  --disable-flashinfer-autotune (kvarn_hook.py validates both in ALL modes,
  not just eager). QWEN_COMMIT_GRAPH=1 selects graph qualification mode
  (--kvarn-qualification-mode graph + --kvarn-commit-graph) with the
  validator-mandated graph geometry --cuda-graph-backend-decode full
  --cuda-graph-bs-decode 1 --cuda-graph-backend-prefill disabled; kvarn
  without commit-graph requires QWEN_QUALIFICATION_EXECUTION=eager (native
  mode forbids any captured graph). Commit-graph with non-kvarn KV refused.
- prepare/pq2/: independent package (strict GGUF reader, PQ2 decoder/encoder,
  Hadamard, artifact validation) + 12/12 passing tests incl. task Examples A-G.
- prepare/build-bonsai-wrapper.py: builds the serving wrapper (config/tokenizer/
  manifest/symlink) — run once; wrapper exists in the state root.
- prepare/verify-models.py: --representation gguf authenticates wrapper + payload
  + draft (passes on the real artifacts).
- serve/entrypoint.sh: ONE fixed path (Bonsai PQ2_0 + DFLASH + KVarN); legacy
  selectors (QWEN_MODEL_FAMILY/REPRESENTATION/SPEC_ALGORITHM/DSPARK) refused.
  F2: no python -c pre-pass — everything is build-time integrated.
- Deleted: serve/convert-bonsai-to-w4a16.py (F6), serve/adapt_dspark_draft.py (F9),
  bend/bonsai_patch.py. docker-compose.yml lost the representation selector.
- Dockerfile: the patch-apply RUN no longer swallows build-patches.sh failures
  with a trailing `|| true` (a failed apply used to export a silently broken
  image; the entrypoint's missing patch-series check was the only guard).

## NEXT STEPS (in order)

1. Re-enable DFLASH + KVarN on the numerically-correct stack — DONE 2026-09-19.
   - 1a eager (QWEN_QUALIFICATION=speculative, KV=kvarn, mode native,
     QWEN_QUALIFICATION_CONTEXT=131072, 18021): ready 161 s (load 29.2 s,
     pool 132096). Oracle-parity gate PASSED: top-1 11751 " Paris" -0.1792
     (oracle -0.1818, target-only run -0.1789), top-8 7/8 (served id 279
     replaces oracle 1076 in the -4.99 tail band — same bf16 shuffle class
     as before). spec_accept_length 4.0 on a 48-token probe; text coherent.
   - 1b CUDA graphs + commit-graph (execution=default, QWEN_COMMIT_GRAPH=1,
     QWEN_QUALIFICATION_CONTEXT=245760 — kvarn_budget.py pins capture to
     context245760/pool246784): target-verify + draft-verify graphs captured
     (backend=full, bs=[1], 8 tok/req; 2.27 s + 3.31 s), DFLASH selector
     folded into the draft graph. Decode batches run cuda graph: True;
     kvarn_commit_graph=True resolved, 0 capture-fallback warnings,
     0 exceptions across a 512-token decode (accept 3.9-4.5). Parity gate
     PASSED with a byte-identical distribution to 1a. Startup 90.8 s,
     8.96 GB free after pools.
   - 1c C1 ladder (bench/results/decode-c1-bonsai-pq2-step1.json, 5 reps x
     1024/8192/32768 on the 1b stack, greedy, streamed, corpus-pinned):
     committed tok/s median 34.17 / 22.65 / 21.11 at 1k/8k/32k (min-max
     20.11-57.16). TTFT median 4.92 / 37.38 / 153.50 s — prefill ~217 tok/s
     at all depths. Acceptance is the variance driver: per-request accept
     length 1.95-8.0 on the frozen corpus splits 1k/8k rows bimodally
     (accept ~2.3-3.5 slow reps vs ~6.7 fast reps; 32k converges to ~2.3-3.2).
     Power p50 279 W, max 282.1 W (280 W cap, nvidia-smi jitter as in prior
     runs). This is the correctness-first baseline for step 2 (>=170 tok/s
     target); the W4A16 stage22 stack's 115.5/91.7/66.6 is the other-model
     reference, not a regression.
2. Performance: PARTIALLY DELIVERED 2026-09-19 — 2.2-2.7x on the dominant
   kernel, targets not yet reached, next levers measured and pinned.
   - Profile (torch profiler via /start_profile, 40 steps + 384-token decode,
     18021): _pq2_matmul_kernel was 83% of ALL GPU time (3.675 s of 4.426 s,
     184.5 us avg) — ~95 GB/s effective against the 3090's 936 GB/s. The
     whitepaper's own 4090 row (~660 GB/s) proves the format is not the
     bound; the correctness-first Triton kernel was.
   - Microbench ladder (real shapes, M=8, synthetic packed data, old kernel
     as baseline): v1 95 GB/s -> blocked-layout+fp16-dot 159 -> v4 (64-weight
     halves + fp16 X + split-K) 209 GB/s aggregate. Plateau ~210 GB/s is
     STRUCTURAL for Triton on this pattern: independent of block sizes,
     num_warps/num_stages, split-K, decode formulation (code-only dots with
     per-group d/sx correction: same plateau), and layout (split-plane
     sector alignment: SLOWER, 177 GB/s — the 34-byte rows do not cost 2x).
     Split-K is deterministic (fixed-order fp32 partial reduce).
   - Serving integration (pq2-stage2 image): linear qweights consumed from
     a blocked layout ([n_blocks, k_blocks, 128, 34], repacked once per
     parameter and cached by data_ptr; +6.4 GiB VRAM, 2.61 GB still free),
     fp16 tensor-core dots with fp32 accumulation (bf16 activations convert
     exactly; products exact; only fp32 add order differs), BK=64 decode
     halves, split-K heuristic. Only pq2_ops.py/pq2_triton.py changed
     (both new-file hunks regenerated in the patch; series sha256 updated to
     647121d3...; gguf.py/logits hunks byte-identical). Old row-layout
     kernel deleted (clean cutover; embedding decode path untouched).
   - Parity gate on pq2-stage2: PASS — top-1 11751 " Paris" -0.1779
     (oracle -0.1818; v1 serving -0.1792), top-8 7/8 identical set. Gate
     PASSED again after the full C1 ladder (coherent streaming, finish
     length, accept 1.95-8.0).
   - C1 (bench/results/decode-c1-bonsai-pq2-step2.json, same protocol as
     step 1): median 60.64 / 45.89 / 36.00 tok/s at 1k/8k/32k (was
     34.17 / 22.65 / 21.11 — +77% / +103% / +71%); TTFT 2.67 / 20.20 /
     84.81 s (was 4.92 / 37.38 / 153.50 — prefill ~385 tok/s). Power p50
     278.6 W, max 281.4 W. Per-step GPU ~47 ms (profile 2: PQ2 path
     1466 ms/window, 67.6 us avg — the 210 GB/s Triton plateau confirmed
     in serving; Hadamard dense matmuls 323 ms; sign-mul + fp16-convert
     elementwise 112 ms; everything else ~220 ms) + ~25 ms serialized host.
   - Matched-conditions comparison vs the pinned Qwen W4A16 stack
     (decode-c1-stage22-on.json, same bench/protocol/GPU, "HyperQwen"
     per Section 11): Bonsai PQ2 = 0.53 / 0.50 / 0.54x of stage22-on at
     1k/8k/32k. Both stacks run DFlash2 + KVarN + graphs + commit-graph;
     context rungs differ (262144 vs 245760 — the kvarn capture pin).
   - Round 2 (pq2-stage3): CUDA mma kernel. A scalar-FMA CUDA kernel and a
     sector-aligned split-plane layout both measured WORSE than the Triton
     plateau (110 / 177 GB/s; E1 decode-only probe 242 GB/s = latency-bound
     streaming — ~83 KB in flight GPU-wide vs ~560 KB needed); the fix was
     tensor cores: mma.sync.m16n8k16 with fragment-direct decode (one warp =
     one 16x8 tile, lane decodes its own A-fragment positions from the
     blocked bytes, 2 ushort loads per row, fp16 products in fp32 acc,
     ~47 instr per k16 per lane vs ~274 scalar). Microbench: 197-365 GB/s
     per shape, 337 aggregate (1.6x Triton, 3.5x the serving v1 baseline);
     standalone nvcc 13.0, sm_86. Serving: compiled at import via
     torch.utils.cpp_extension (cached in /cache; SGLANG_PQ2_DISABLE_CUDA_
     GEMM=1 disables), explicit dispatch M<=16 and M%8==0 -> CUDA (decode/
     verify tiles), larger M stays Triton (its M-blocking covers prefill;
     grid-z M-tiling would re-read the weight stream per token tile — the
     prefill lever is a shared-staged A-fragment loop, documented below).
     Two integration bugs fixed loudly (fp32 part pointer dereferenced on
     the split_k==1 path; at::Half pointer cast).
   - Round-2 parity: PASS, distribution byte-identical to stage2 (-0.1779,
     7/8) — both paths are exact-product fp32-acc; bf16 output rounding
     dominates. C1 (bench/results/decode-c1-bonsai-pq2-step3.json): median
     70.94 / 51.41 / 42.30 tok/s at 1k/8k/32k (+17% / +12% / +17.5% over
     stage2; 2.08x / 2.27x / 2.0x over the round-1 baseline). TTFT
     unchanged (2.65 / 20.2 / 84.9 s — prefill untouched). Power p50
     278.5 W, max 284.4 W (transient sampling spike, cap band). Matched-
     conditions ratio vs stage22-on: 0.61 / 0.56 / 0.64.
   - REMAINING LEVERS to 170/140/100 (updated): (a) prefill: stage A-
     fragments in shared per k-group and loop M-tiles inside the block —
     eliminates the per-token-tile weight re-read (chunked 1024-token
     prefill currently pays ~64x weight traffic in the Triton M-blocking;
     measured projection: TTFT 32k 84.9 s -> ~10-15 s, prefill 385 ->
     ~10^5 tok/s class); (b) fused sign-flip + fast-WHT + fp16-convert
     kernel to replace the dense 1024x1024 bf16 Hadamard matmul per
     projection (~13 ms/step -> ~2 ms); (c) host path (~25 ms/step
     serialized scheduling; 22.8K tiny H2D copies per window); (d) decode
     GEMM to the fork-class ~660 GB/s via cp.async double-buffered weight
     staging (measured decode-only ceiling with the current load pattern:
     242 GB/s; mma serving: 273 GB/s at the 16k shape incl. reduce).
3. Bend (F7): DONE 2026-09-19 — Section-7 operators implemented as Bend
   qualification references (bend/pq2_refs.bend), CPU-qualified, CUDA
   codegen verified; the serving path stays Triton. Integration gap
   measured and reported below.
   - Operators: PQ2 block decode (code table (q-1)*d with code 3 = +2d,
     per-byte bit extraction), folded Hadamard (sign flip + normalized
     Sylvester WHT via the contiguous-half block recursion H_n x =
     [H_m a + H_m b ; H_m a - H_m b] — natural order with NO bit-reversal
     stage; 1/sqrt(n) applied once via Newton sqrt), ternary dot, GDN
     delta-channel step (u = v - k.s; s' = a*s + beta*k*u; decay before
     update, beta outside the norm). Parallelism: the fwht recursion
     branches on two independent halves inside one let pair; reductions
     are explicit match recursion (Bend's fold auto-recurses on the
     folded list's tail, so two-list locks step must be plain recursion).
   - Qualification: 7/7 pinned checks PASS on bend run-rs (HVM 2.0.22 /
     bend 0.2.37): decode of byte 0x19, two-byte block decode, the task's
     Example-A butterfly ([1,2] -> [3,-1]), H4 identity and signed-form
     transforms against the parity construction, dot, delta step.
   - Codegen: bend gen-cu emits 230,954 bytes of CUDA; standalone nvcc
     (CUDA 13.0, -arch=sm_86) compiles it in ~19 s inside the serving
     image.
   - DEVICE EXECUTION GAP (measured, first-hand): (a) `bend run-cu`
     fails to initialize CUDA on this NixOS host ("If you've installed
     CUDA and nvcc after HVM, please reinstall HVM"); (b) the standalone
     compiled gen-cu binary runs the interaction net but emits no result
     within 20 s and 60 s windows (0 bytes output) — the gen-cu runtime
     hosts arrays as interaction-net lists with host-staged injection,
     so per-cycle serving ops and even the small check harness cannot
     complete at this budget. The references therefore qualify semantics
     on the CPU interpreter; serving stays on the Triton kernels.
   - Toolchain findings (bend 0.2.37 / HVM 2.0.22, for the F10 gate
     rework): numeric `match` with literal cases is broken at runtime
     (case 0 matches every value; if/else chains required); `if` inside
     a `with IO:` block fails with "HVM output had no result"; tuple-
     returning recursive functions misbehave (use single-List or scalar
     returns); `bend PROOF.bend` itself fails with "attempt to clone a
     non-affine global reference" — the repo's proof harness needs a
     rework on this toolchain before it can gate anything.
4. F10 gates + docs: rewrite BONSAI-DEPLOY.md, qualification.md tie-ins, then
   capability/context qualification (Prime Envs per eval/README.md).

## Debug instrumentation (this session, kept in the patch)

pq2-gguf-loader.patch's SGLANG_PQ2_DEBUG block gains value dumps:
SGLANG_PQ2_DEBUG_DUMP=<dir> saves the first 64 forwards per tagged module
(embed, l0-inproj-qkvz/ba, l0-gdn in/out, l0-gdn-attn, l0-gdn-norm,
l0-outproj, l0-gateup, layer{0,1,2,3,63}-out, l3-qkv, final-norm) as
<dir>/<tag>.<call>.pt with {out, in} float tensors; every dump prints its
call index and input_ids so the oracle-prompt call is identifiable (the
server warmup consumes early calls: one 6-token prefill + decode steps).
Reference artifacts this session: /tmp/manual_full.py (full 64-layer numpy
chain), /tmp/ref-l0.npz + /tmp/ref-final.npz + /tmp/ref-logits.npy,
comparison scripts in /cache/pq2-debug/. /tmp is ephemeral; the numbers live
in this doc.

## Reproduce (current bring-up)

docker build -t qwen-inference:pq2-stage1 --build-arg QWEN_PATCH_SERIES=experimental .
docker run --rm --name bonsai-pq2-test --gpus all --shm-size 32gb \
  -v .../qwen-inference-launch.lock:/run/qwen-inference-launch.lock \
  -v .../models:/models:ro -v .../api-key:/app/api_key.txt:ro -v .../cache:/cache \
  -v .../overrides/draft_vocab_ids.json:/state/draft_vocab_ids.json:ro \
  -v <repo>/prepare:/model-preparation:ro \
  -v <repo>/serve/entrypoint.sh:/opt/qwen/serve/entrypoint.sh:ro \
  -e QWEN_ALLOW_UNQUALIFIED=1 -e QWEN_DRAFT_VOCAB_JSON=/state/draft_vocab_ids.json \
  -e QWEN_MEM_FRACTION_STATIC=0.94 -e QWEN_QUALIFICATION=target-only \
  -e QWEN_QUALIFICATION_CONTEXT=131072 -e QWEN_QUALIFICATION_EXECUTION=eager \
  -e QWEN_QUALIFICATION_KV=bf16 -p 18021:18020 qwen-inference:pq2-stage1

1a eager speculative+KVarN rung (verified above): same command with
  -e QWEN_QUALIFICATION=speculative -e QWEN_QUALIFICATION_KV=kvarn
  (QWEN_QUALIFICATION_CONTEXT=131072; the entrypoint adds mode native).

1b graphs+commit-graph rung (verified above): additionally
  -e QWEN_QUALIFICATION_CONTEXT=245760 -e QWEN_QUALIFICATION_EXECUTION=default \
  -e QWEN_COMMIT_GRAPH=1
  (the entrypoint then emits mode graph + --kvarn-commit-graph + decode FULL
  bs[1] / prefill-disabled graph geometry; capture is hard-pinned to
  context245760/pool246784 by kvarn_budget.py).

Round-2/3 images: same command, tag qwen-inference:pq2-stage2 (blocked+fp16
Triton kernel) or qwen-inference:pq2-stage3 (CUDA mma decode kernel). The
mma extension compiles once at import (~30 s, cached under
/cache/.cache/torch_extensions); delete that directory to force a rebuild.

Add `-e SGLANG_PQ2_DEBUG=1 -e SGLANG_PQ2_DEBUG_DUMP=/cache/pq2-debug` for the
value-dump instrumentation described above.

(For production builds the prepare/ copy is baked into the image; the mount is
only needed while prepare/ has uncommitted changes.)
