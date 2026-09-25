# Measurement protocol

**Status:** the serving stack is EXL3 with native DFlash2 speculative decoding
(greedy, one sequence, native context 262144, CQ3 cache) on one RTX 3090. The
frozen lane below is protocol `exl3-native-broad-c1-request-v2`, a **new
comparison segment that needs a fresh baseline**. Its primary pools four native
tasksets, so it is not comparable with `exl3-native-math3-c1-request-v1`
(math-only primary) or any earlier segment. Only its `aime25_*` metrics keep the
v1 math definition (same producer, tasks, config and budget); they are a
whole-stack comparison only. No lane here is full quality, capacity or promotion
qualification.

## 1. Freeze the comparison

Use one RTX 3090, an exclusive quiet endpoint, and exact image, engine patch
manifest, Bend acceptance identity and target/draft inventory hashes. Save
tokenizer identity, sampling settings, actual input IDs, output budget, cache
condition and power policy. Record failures and truncations explicitly;
operational completion is not a successful quality result. Never combine
percentage gains from different prompts or configurations, and never compare
numbers across runner-configuration changes.

Quality uses the frozen **Prime Envs + Verifiers** profiles under `eval/`
(prime-envs `c4d04dfe`, verifiers `ef47b2e9`). `bench/` orchestrates those
unchanged native tasks; it does not define their prompts, graders or a combined
intelligence score. No lane uses an LLM judge. GPQA is excluded: its dataset is
gated and its scorer can fall back to a remote LLM judge.

## 2. Frozen autoresearch lane

`bash autoresearch.sh` (`bench/autoresearch.py` supervisor/worker,
`bench/exl3.py` identity, native taskset and C1 logic) runs exactly once, in this
order:

| Order | Workload | Frozen selection and settings |
| --- | --- | --- |
| 1 | `aime25` | `eval/configs/tiny/aime25.toml` unchanged: 3 native seed-zero shuffled tasks, 32768 output-token budget |
| 2 | `mmlu-pro` | `eval/configs/broad/mmlu-pro.toml`: 20 tasks, zero-shot, 8192 budget; boxed-letter math-verify scoring |
| 3 | `i3-logic` | `eval/configs/broad/i3-logic.toml`: 6 tasks, 16384 budget |
| 4 | `livecodebench` | `eval/configs/broad/livecodebench.toml`: 3 tasks, 16384 budget, official v6 date filter (2024-08-01 through 2025-05-01, as `quick`); hidden tests in the sandbox |
| 5 | C1 depth matrix | Raw-content depths 1024/8192/32768 (±2 tokens), five repetitions each in depth-then-repetition order, 1024 output-token budget, greedy, `top_p` 1, `n` 1, normal EOS, non-streaming |

Every taskset uses one rollout per task, one model call per episode (null
harness), `max_concurrent` 1, the local Docker runtime image pinned by
`eval/.cache/sandbox-image`, native Docker timeouts (setup 600 s, rollout
1800 s, scoring 600 s) and `eval/configs/local.toml` sampling (greedy,
thinking enabled). A taskset profile may set only `sampling.max_tokens` (its
per-call budget, equal to `env.agent.max_output_tokens`); any other sampling
difference rejects the run.

### Operator contract

Main installs a fresh private descriptor at
`/run/user/1000/litos-autoresearch-operator.json` (uid 1000, mode 0600, regular
file, no symlink) with exactly `schema_version` 1, the full 64-hex
`container_id`, canonical absolute `api_key_file` (0400/0600),
`maintenance_directory` of an already armed guardian window, and a not yet
existing `output_directory`. The supervisor binds the descriptor's inode and
digest, verifies guardian lease/launch-lock/mutex ownership on every poll,
requires the container to be the guardian candidate publishing only
`127.0.0.1:18020`, and enforces `min(2400 s, guardian deadline - 120 s)` over
capture, every workload and admission. The worker runs inside pinned offline
Nix. There is no retry, task reduction, warmup, flush, capacity probe, power
change, deployment or promotion.

Prerequisites: prepared offline `eval/.venv` (including `tokenizers` and the
`mmlu-pro` package), pinned Prime/Verifiers sources, verified AIME25, MMLU-Pro,
I3 Logic and LiveCodeBench snapshots (`eval/scripts/data --check <taskset>`), the
pinned local sandbox image in `eval/.cache/sandbox-image`, host `docker` and
`nvidia-smi`, and a healthy owned EXL3 instance serving `qwen3.8-27b` with
target/draft mounted under `/models`. The server must accept the native client's
identity sampling fields (`top_p` 1, `min_p` 0, frequency/presence penalty 0,
repetition penalty 1) and reject other values.

### Serving identity

Before any workload and again after all of them, the worker captures and requires
byte-identical identity (`identity-before.json`, `identity-after.json`):

- Docker: full container ID, name, immutable image ID, creation and start time,
  PID, restart count, entrypoint/command, public `QWEN_*` environment, network,
  published ports, read-only root and mounts; image labels and layer digests.
- One read-only in-container probe (`docker exec` of the image's
  `/opt/venv/bin/python -I -B`): SHA256 of every file under `/opt/qwen` (baked
  server, launchers, engine patch manifest, Bend artifacts) and
  `/model-preparation`; the installed `exllamav3` package tree and its
  `exllamav3_ext` extension; engine distribution version and install URL; all
  installed distributions; target/draft inventories (every file size; SHA256 of
  each file up to 64 MiB, checked against `prepare/exl3-manifest.json`; weights
  are rehashed by the image's own startup inventory).
- Engine patch manifest `/opt/qwen/exl3-patches.json`: when present, its bytes
  must match image label `io.litos.exl3.patches-sha256` and every listed
  installed file must rehash to its recorded post-patch SHA256. When absent the
  record is explicit `null` and the label must be absent.
- Bend acceptance identity `/opt/qwen/bend-exl3/identity.json`: when present,
  schema `litos-exl3-bend-accept/1`, `identity_sha256` must recompute over the
  document's other keys and every listed artifact must match its baked bytes.
  When absent the record is explicit `null`.
- Authenticated `/health` and `/v1/models` (`max_model_len` 262144 is the
  reported limit, not a capacity test).
- Host `nvidia-smi`: exactly one `NVIDIA GeForce RTX 3090`, power limit and
  enforced limit 350 W (declared operating point; never changed here), UUID,
  bus, driver and memory.
- The host tokenizer file behind the target mount, whose bytes must equal both
  the served file and its manifest pin.

### Native tasksets and the primary

Each taskset `<ts>` is invoked directly as
`uv run --project eval --no-sync eval @ eval/configs/local.toml @ <launch>
-o <group>/<ts> --no-rich --no-push <data flags>`, where `<launch>` is its profile
with only the sandbox image replaced by the pin. Offline data loading is exactly
`eval/scripts/run`'s (`eval/README.md`): AIME25 gets
`--env.taskset.dataset-name <snapshot>` and I3 Logic
`--env.taskset.dataset.name <snapshot>/logic --env.taskset.dataset.subset default`,
both from `eval/.sources/prime-envs`; LiveCodeBench reads the owned HF cache whose
`refs/main` must name the locked revision; MMLU-Pro, which hardcodes
`TIGER-Lab/MMLU-Pro` and its revision, runs from `<group>/local-datasets`, where
that relative path links to the verified snapshot, and the taskset module's
hardcoded name and revision must equal the lock entry.

Before any generation, every taskset's evaluator/source/config/data hash closure
is frozen and its native seed-zero selection and resolved config are replayed
offline with the CLI's deep merge (`<ts>.evaluation-inputs-before.json`); the
same record is recomputed after that taskset's run and must be identical.
Admission then replays each taskset from raw files: the resolved config equals
the frozen plan (model, taskset, harness, sampling, budget, runtime); the log
states exactly one `<N>x1` run; exactly the planned tasks in planned order with
matching content hashes; every episode and trace `ok`, complete and scored by
the pinned Verifiers commit; exactly one call per episode with the expected
model, endpoint, wire sampling (including its budget) and a `stop`/`length`
finish; and every trace inside the identity capture window. Any failure rejects
the whole run.

`model_call_output_tok_s` is the **primary**: the completion tokens of every
native model call of all four tasksets divided by the sum of their native
model-call wall intervals (`bench.autoresearch.model_call_observations`). These
intervals cover request send through the fully received response, including
prefill, decode and HTTP; they are not decode-only or GPU time. The primary
therefore weights tasksets by their generated tokens. `<ts>_output_tok_s` is the
same ratio over one taskset's calls, `<ts>_reward` the mean native weighted
reward of its episodes and `<ts>_truncated` the number of its calls with finish
reason `length`, for `<ts>` in `aime25`, `mmlu_pro`, `i3_logic`,
`livecodebench`. Incorrect and length-truncated but operationally complete
graded answers stay in numerators, denominators and rewards.

Replaying the historical run-g7kafqt AIME25 traces through this admission path
reproduces `aime25_output_tok_s` 19714 tokens / 125.18 s = 157.4852 tok/s,
reward 1.0 and no truncation (a v1 run, not a baseline for this protocol).

### C1 whole-request secondaries

Before any generation, the worker sizes each of the 15 prompts from the frozen
`bench/throughput-prompts.jsonl` corpus (deterministic nonce
`[measurement run R of 5 at depth D]`, fixed instruction) to raw-content depth
within two tokens using the served tokenizer bytes on CPU, writes the exact
request bytes, and retains the server's `/v1/chat/completions/render` token IDs.
Raw-content depth is not total templated depth; both counts are recorded.

Each row is one non-streaming `/v1/chat/completions` request. Its wall time runs
from request send through the complete response body. Admission replays every
row from raw files: HTTP 200, one assistant choice, `stop`/`length` finish
(`length` only at the 1024 budget), `prompt_tokens` equal to the rendered ID
count, consistent totals, and sequential non-overlapping requests.

`c1_request_tok_s_<depth>` = sum of the five rows' completion tokens / sum of
their request wall times. It is **whole-request output throughput including
prefill**, not TTFT and not decode-only. TTFT and committed decode rates are
unavailable on this transport and are never reported or estimated.

### Speculative acceptance

When every C1 row's usage carries `exl3_spec` = `{rounds, committed}` (native
verify rounds and tokens committed by them; `rounds <= committed <=
min(completion_tokens, 8 * rounds)`), `spec_accept_length` = total committed /
total rounds over all 15 C1 rows is reported. It is absent when the server does
not report the field; partial reporting rejects the run. Native taskset traces do
not retain this field.

### Time budget

Expected wall time is about 25 minutes, inside the 2400 s hard deadline:
AIME25 ~150 s (measured on g7kafqt: 125 s of calls), MMLU-Pro ~310 s, I3 Logic
~210 s and LiveCodeBench ~290 s including sandbox scoring (estimates: about
2000/5000/9000 completion tokens per call at 160–185 tok/s plus ~4 s of Docker
episode overhead), C1 ~340 s (measured) and ~190 s of identity captures, Nix,
offline selection replays, input hashing (LiveCodeBench's 4.49 GB source is
hashed and loaded before and after its run) and evaluator startups. That leaves
roughly 900 s for longer outputs; output-bound worst cases (every call reaching
its budget, about 2600 s of generation alone) exceed the deadline. Such a run
is rejected, never shortened or retried.

### Admission and output

Artifacts: `supervisor.json`, `benchmark.json` (frozen workload and
`workload_sha256`), `identity-before.json`, `identity-after.json`,
`<ts>/{provenance,<ts>}` for each taskset (plus `mmlu-pro/local-datasets`),
`c1/{plan.json,depth-D-rep-R/}`, `logs/`, `sources/`, `admitted.json` (all
metrics, per-taskset/per-call/per-row records and the retained evidence hash
closure) and `measurement.json`. Only a complete admitted run prints `METRIC`
lines, in this order: `model_call_output_tok_s`; `<ts>_output_tok_s`,
`<ts>_reward`, `<ts>_truncated` per taskset in lane order; the three
`c1_request_tok_s_*`; optional `spec_accept_length`; and `elapsed_seconds`
(whole command, not a per-lane clock). Any rejection writes `failure.json` (and
`worker-failure.json` from the worker) and exits nonzero.

Not measured by this lane: TTFT, committed decode throughput, power/energy and
262144-token capacity.

## 3. Power

The declared operating point is 350 W, the RTX 3090's default limit, set by the
host NixOS power policy and checked but never changed by the lane. Segments
measured at the earlier 280 W cap are not comparable with 350 W results.
Sweep other caps only with explicit maintenance ownership, recording and
restoring the original cap; containers must not modify host power or fans.
Measure actual watts, clocks, temperature and throttle reasons over a stated
interval before reporting tokens per joule.

## 4. Engine state at the end of segment 4 (2026-09-25, 350 W)

**Best kept configuration:** candidate image `qwen-inference:exl3-cand-g7kafqt`,
`sha256:f2e72ec7c9b65aa0478119b7be980763162ed7837b1f2288ece6d46abbc795e7`. It was built
from this commit's `patches/` by `bash docker/build-exl3.sh candidate-ext`. The live
deployment (see [docker.md](docker.md)) is unchanged and still serves the promoted image
`fca4c263`; nothing was promoted.

- **exl3 series:** 0001 greedy batched verify, 0002 host overlap, 0003 draft graph,
  0005 DFlash2 reference draft block mask (window (W-1, W-1), bidirectional block).
- **exl3-ext series,** each patch after the one before it:
  - 0001–0004 GDN verify/commit;
  - 3001/3002 attention dequant and GQA split;
  - 5001 GDN small fusions;
  - 2001 M ≤ 16 GEMM;
  - 6001 draft graph;
  - 7001 norm/residual fusion;
  - 3004 attention partial bounds;
  - 3005 row-invariant split;
  - 9002 int4 draft head;
  - 8201 persistent fused MLP;
  - 3003 CUDA verify attention over fixed absolute 512-token chunks;
  - 5101 fused GDN front end, recurrence and norm;
  - 2102 grouped m16 qkv(+z) projections;
  - 8202 persistent layer tail (o/out-proj, residual, norm and MLP in one kernel).

Primary `model_call_output_tok_s` of the kept runs (each run is one full lane of
the earlier protocol `exl3-native-math3-c1-request-v1`, math-only primary; not
comparable with the broad v2 lane above, which needs its own baseline):

| Run | Image | Primary tok/s | tok/J | Note |
|---|---|---|---|---|
| #43 | g7n | 131.62 | 0.409 | segment baseline |
| #45 | g7j | 132.50 | 0.408 | 3004/3005 correctness, 9002 |
| #47 | g7km | 137.47 | 0.426 | 0005, 8201 (bit-exact) |
| #48 | g7kma | 141.73 | 0.432 | 3003 (numerics change) |
| #50 | g7kafq | 149.06 | 0.460 | 5101 (bit-exact), 2102 (numerics change) |
| #53 | g7kafqt | 157.49 | 0.494 | 8202 (numerics change) |

Numerics-changing keeps change the greedy text and with it the math call lengths.
Part of the primary gain from #48 on is a shorter long call, not faster steps. The
step-time traces below are text-independent.

Verify-step time from the CUPTI kernel traces
(`evidence/kernel-trace-N/trace.log`, unprofiled median). The floor is the
Bend-proven byte count of one round (`bend/roofline.bend`, 9002's smaller draft
head subtracted) at 875.6 GB/s:

| Image | Power | Step ms at depth 107 / 8190 / 32728 | Share of DRAM floor |
|---|---|---|---|
| g3 | 280 W | 35.1 / 38.0 / 45.7 | 51 / 47 / 40 % |
| g7n | 280 W | 30.9 / 32.6 / 36.7 | 58 / 55 / 50 % |
| g7j | 350 W | 28.6 / 30.1 / 34.3 | 61 / 59 / 53 % |
| g7kafqt | 350 W | 26.9 / 27.2 / 30.3 | 65 / 65 / 60 % |

The largest remaining losses per step at short depth:
- the MLP GEMMs (~78 % of DRAM bandwidth);
- the GDN projections (~64 %);
- ~1.3 ms of GPU idle between graphs;
- ~2.5 ms of latency-bound small kernels (GDN recurrence, norms, attention).

**Gates held for every kept change:**
- Bend gate green.
- The patch's Bend differential against the shipped source where the module has one
  (`bend/*_diff.py`; 5101 is checked by its quoted source fragments instead).
- Invariance: `ops/autoresearch/invariance.py run`. Target ids under the capped and
  all-wrong draft arms must equal the normal arm on all 15 parity cases, so the
  output is independent of the draft. Bit-exact candidates must also have ids
  identical to their base.
- tiny-math 3/3.

**Open items:**
- 8202 schedule laws: the baked header is byte-identical to
  `TAIL_M16_SCHED_TABLE.bend` output, but four laws were still unproven at the end of
  segment 4. They are proven and wired in segment 5 (see §5).
- Measured and dropped:
  - device-side acceptance with speculative next draft (+0.35 %, flat);
  - one whole-target CUDA graph (−4.2 %);
  - draft window > 2048 (8192: −28 % tokens per round);
  - L2 prefetch into inter-GEMM windows (within noise).

`ops/autoresearch/` is a snapshot of the operator scripts used for this segment.
They are run from `/tmp`: copy them back there, `invariance.py` to
`/tmp/kernel-work/Invariance/` and `kernel_trace.py` to `/tmp/kernel-work/KernelTrace/`.
- `mkcand.py` and `gpu-window.sh` precreate and run guarded GPU windows around the
  retained guardian.
- `build-one.sh` builds a candidate from the committed series plus extra patches.
- `ar-serve.sh` and `ar-when-built.sh` open the timing window for `bash autoresearch.sh`.
- `gpu-inv.sh` and `inv-compare.py` run the invariance gate.
- `ar-energy.py` and `step-report.py` give per-call tok/J and step efficiency.

Launch every script that owns a GPU window through `detach.sh`. A caller that is
killed mid-window leaves the guardian dead, and its library then refuses recovery.
In that case restore by hand, as the guardian would: stop the candidate, start
container `b5e51bc1…`, and require an authenticated `GET /v1/models` of 200.

## 5. Segment 5: broad lane (protocol `exl3-native-broad-c1-request-v2`, 350 W)

| Run | Image | Primary tok/s | tok/J | aime25 / mmlu-pro / i3-logic / lcb tok/s | Rewards | Note |
|---|---|---|---|---|---|---|
| #54 | g7kafqt | 137.39 | 0.426 | 158.34 / 132.07 / 151.37 / 117.15 | 3/3, 12/20, 2/6, 1/3 | baseline |
| #55 | c3006 | 139.54 | 0.431 | 152.83 / 129.65 / 155.51 / 118.14 | 3/3, 13/20, 2/6, 1/3 | 3006 (numerics change) |
| #56 | cs5 | 144.13 | 0.444 | 158.90 / 139.36 / 157.01 / 121.15 | 3/3, 12/20, 1/6, 1/3 | 8204, 9003b, 3007, 2105, 5106 |

3006 replaces 3003's fixed 512-token chunks in the verify attention split with
strided absolute 64-token tiles and one partial slot per split CTA
(`bend/attn_stride*.bend`).

**Judging numerics-changing keeps on this lane.** A numerics change alters the greedy
text, and with it the call lengths and depths of every taskset. On #55, aime25 wrote 60 %
more tokens than on #54, so per-taskset tok/s moves with the text mix and not only with
step time. The taskset traces carry no round counts. Step time therefore comes from the
C1 rows by regression: per depth, fit wall = intercept + rounds × step over both runs'
five rows, with one shared intercept (prefill plus per-token work, since every row
commits 1024 tokens) and one slope per image. #54 → #55: 27.55 → 26.82 ms at 1K
(−2.6 % ± 0.3), 26.30 → 26.34 ms at 8K (+0.2 % ± 0.1), 31.18 → 30.32 ms at 32K
(−2.8 % ± 0.4). These match 3006's component harness (−0.59, −0.08, −0.97 ms per round).

**#56 (cs5).** Five patches on c3006:
- 8204: the 8201/8202 kernels issue their input loads before the weight-ring prologue and
  publish phase-1 group completion once per block after its last flush, instead of with
  a fence at every mid-slice group boundary. Bit-exact.
- 9003b: the draft's q/k/v and K/V-refresh projections (and fc at 3-8 rows) run on the
  grouped m16g kernel. Draft numerics only; target text is draft-independent.
- 3007: deinterleave + RoPE + quantized cache append as one kernel, and the output gate
  inside the attention combine. Bit-exact.
- 2105: the m16g split-K partition weights each SM's second CTA at 0.91 of the first
  (the second CTA streams ~10 % slower). Numerics change; error vs fp32 no worse.
- 5106: the GDN verify kernel's b/a GEMV splits K across all 16 warps (one load round
  instead of five serial ~1 µs rounds). Numerics change; b/a error vs fp64 lower.

C1 regression against #55: 26.57 → 26.15 ms at 1K (−1.6 % ± 0.2), 26.31 → 25.81 ms at 8K
(−1.9 % ± 0.1), 30.20 → 29.86 ms at 32K (−1.1 % ± 0.5). Invariance 45/45. The primary's
+3.3 % is larger than the step gain because the text mix moved again. Rewards differ
from #55 only by single-task flips in both directions (i3-logic `cipher` went 0 → 1 → 0
over #54-#56; `numbrix` already hit the 16384 budget on #55), which a numerics change
causes at these sample sizes.

**Bend coverage after #56.** `bend/mlp_m16_defer*` (8204's deferred publish) and
`bend/attn_pre*` (3007's fused pre-attention kernel) are wired; their differentials and
`attn_stride_diff`, `tail_m16_sched_diff`, `mlp_m16_sched_diff` and `gemm_m16_group_diff`
pass on the #56 tree. Still unproven for the served code:
- 2105's weighted partition. `gemm_m16_group` models the uniform v2 partition, which 2105
  reproduces bit for bit only at equal weights (the draft rows); the target rows run at
  (100, 91).
- A differential for 9003b's draft shapes. It exists, but quotes 2102's kernel source and
  must be ported to 2105's.

5106's K-split GEMV is covered since: `bend/gdn_ba_ksplit*` proves that every half2
element of every b/a task is multiplied once, by one (warp, lane, iteration). The per-task
sum order (lane chain, shuffle tree, warps 0-15, bias) is fixed and independent of the
number of rows. The reduction reads only partials completed before the barrier, and more
than 8 rows or K > 5120 falls back to 5101's one-warp-per-task GEMV (still described by
`gdn_fast`'s `task_exactly_once`). `bend/gdn_ba_ksplit_diff.py` quotes the served kernel
lines and matches the Bend table byte for byte (801 lines).

**Differentials.** `bend/attn_chunk_diff.py` quotes 3003's chunk loop, which 3006
removes, so it applies only to trees before 3006. The attn_chunk laws stay in the gate as
the model of the removed partition, as attn_split did when 3003 replaced it.
`bend/attn_stride_diff.py` is the differential for the current tree.

**8202 schedule laws.** `bend/tail_m16_sched*.bend` are wired into `LAWS.bend`/`PROOF.bend`.
The four laws left open in segment 4 (`mc0_served`, `f0_partials_once`,
`norm_reads_partials`, `norm_cells_once`) are proven. `mc0_served` uses a scaling lemma so
the checker evaluates the owner bound at total 960 and G 41 instead of the served 3840 and
164. `bend/tail_m16_sched_diff.py` extracts the baked `exl3_tail_m16_sched.h` from the
committed 8202 patch and compares it byte for byte with the Bend table output.

**Measured and dropped in this segment:**
- 5102, the GDN commit replay folded into the next verify. Bit-exact, but the GDN part of
  a round grew 0.5-0.75 ms (a 3 MB state write per layer inside a latency-bound 48-SM
  kernel), against 0.49 ms of replay removed.
- 2103, the m16g projection without grid barriers. Bit-exact but slower: 79 against
  70 µs per GDN launch. Its slow blocks are the ones whose slice crosses a group
  boundary, where 2103 added a mid-loop fence. It is not SM speed: blockIdx lands on the
  same SM in every launch, and a plain stream of equal contiguous slices runs every SM
  within 2.5 % of the median at 811 GB/s. In 2102 the loop itself streams at ~95 % of the
  DRAM rate; the time goes to the kernel start (~8 µs of launch skew and the grid barrier;
  2104 below shows reordering the input loads does not shorten it), the finish (~5 µs) and
  the launch ramp (~5 µs).
- 8203, dataflow counters instead of the 8202 tail's barriers A/B/C. Bit-exact but
  +1.6 µs per layer. Its stamps show where the tail's time goes: 217 µs per layer against
  a 170 µs DRAM floor, with block spreads of 7.7 / 30 / 20 µs at the ends of the o_proj,
  gate+up and down loops.
- 2104, m16g start reorder (activation and Hadamard-scale loads before the weight-ring
  prologue, counter finish instead of the second grid barrier). Bit-exact, no gain: the
  input transform is still ready 8.4 µs after launch.
- 5103, GDN verify split over v-columns (192 blocks). Bit-exact; faster only at 1-2 rows,
  slower from 4 rows on.
- 5105, GDN verify prologue reorder. Bit-exact; only issuing the state loads after the
  conv helps (−0.65 µs per launch at 8 rows). The fix for that kernel was 5106.
- 5104, GDN commit replay from the verify's stored v′. Bit-exact, but the verify's extra
  stores (+29 µs per round) cancel the replay saving at ~3.4 committed tokens per round.
- 9004, streaming kernel for the draft's dynconv projections. Correct per call, but it
  packed its weight copy inside the loader's deferred-load bracket, before the weight was
  read, so the draft ran on garbage: acceptance fell from 4.82 to 3.48 tokens per round
  while the target text stayed identical. Fixed, it saves only 11 µs per round at the
  draft's fixed 8 rows, so it is not used. A component harness must load weights through
  the served path and gate the draft's end-to-end acceptance.
- 8205, the same slot weighting for the 8201/8202 kernels. Correct, and the per-block
  stamps move barrier D ~6 µs earlier per tail launch, but the 64-layer chain measured
  +1.2 µs per launch at every weighted setting. Not kept until that gap is explained.
