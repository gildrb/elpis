# Recorded runtime qualification runs

These are sanitized reports from actual runs, not newly executed benchmarks.
Private request data and raw model responses are deliberately not published.
The reports retain producer hashes and measurement limits; current code changes do not rewrite historical identities.

| Run | Report | Interpretation |
|---|---|---|
| Refactored FP8 startup | [refactor-fp8-startup.json](refactor-fp8-startup.json) | Requested262144; actual pool68004; stopped before API readiness; original service restored |
| KVarN packing repair | [240k-packing-repair-01.json](240k-packing-repair-01.json) | 90 attention + 2 status cases passed, zero memory-check errors; not model qualification |
| KVarN memory-check diagnostic | [240k-packing-memcheck-01.json](240k-packing-memcheck-01.json) | Key-packing shared-address failure localized; baseline restored; repair validation was pending at this attempt |
| Baseline native throughput and compatibility | [native.json](native.json) | **130.99–132.78 tokens/s end-to-end; 135.90–137.69 tokens/s decode**. Short-suite 64K baseline, not candidate qualification |
| Cache consistency | [cache-45k.json](cache-45k.json), [cache-45900.json](cache-45900.json) | Workload-specific cache evidence |
| Baseline video preprocessing failure | [multimodal-baseline.json](multimodal-baseline.json) | CUDA OOM/HTTP 500; following image request completed, not quality evidence |
| 240K candidate: first native attempt | [240k-native-attempt-01.json](240k-native-attempt-01.json) | Packed rows passed; KVarN CUDA illegal memory access before model startup; baseline restored in 95.0 s |
| Packed-embedding trial | [packed64-trial.json](packed64-trial.json) | GPU row arithmetic passed; candidate startup failed; baseline restored |
| Packed KVarN 0.94 admission | [packed-kvarn-094-admission.json](packed-kvarn-094-admission.json) | Valid packed load (14.75/1.22 GB weights); KVarN profile 211328 < requested pool 263168; strict startup reject; 0.98 retry deferred to a separate window; baseline restored |
| Packed KVarN 0.98 admission | [packed-kvarn-098-admission.json](packed-kvarn-098-admission.json) | Pool cap passed and pools allocated (1.09 GB still avail); startup failed later at hybrid backend wiring: KVarNAttnBackend lacks token_to_kv_pool; baseline restored |
| Packed KVarN 0.98 admission, stage 13 | [packed-kvarn-098-admission-stage13.json](packed-kvarn-098-admission-stage13.json) | Full 263168 pool built, all backends initialized, scheduler event loop entered; killed at first idle tick by a false pool leak (128-token KVarN graph-dummy page unaccounted); baseline restored |
| Packed KVarN 0.98 admission, stage 14 | [packed-kvarn-098-admission-stage14.json](packed-kvarn-098-admission-stage14.json) | First readiness pass: API ready in 80.3 s, idle invariant checks pass with reserved-page accounting, steady state 23441 MiB used / 686 MiB free / 25 W; admission-only, no request served; baseline restored |
| Packed KVarN 262144 deep probe | [packed-kvarn-262144-deep-probe.json](packed-kvarn-262144-deep-probe.json) | Inconclusive by deadline, not by memory: 45 chunks / 46,080 tokens prefilled in 1800 s at 15–27 tok/s declining (quadratic), GPU 100% util at 271 W median; extrapolated full prefill ~12.9 h; zero retractions, token usage 0.18 at 46 K; health timer suspended/restored, baseline restored |
| Packed KVarN 4096 prefill profile | [packed-kvarn-4096-prefill-profile.json](packed-kvarn-4096-prefill-profile.json) | First completed KVarN request (4096 in / 128 out, zero retractions); chunk-time slope 0.001376 s per cached token confirmed by a second window; ~263 s serving-start Triton JIT recorded; CPU+GPU trace export OOM-killed the 48 g container, baseline restored |
| Packed KVarN 2048 kernel profile | [packed-kvarn-2048-kernel-profile.json](packed-kvarn-2048-kernel-profile.json) | Gap localized: `_packed_attention_split` = 63% of GPU busy (n=4096, exactly 2 chunks × 16 layers × 128 eight-query micro-iterations), mean 252→1158 µs from chunk 1→2 while GEMM/GDN/store stay flat; kernel runs at ~0.7% of fp32 peak; GDN exonerated (0.68%); baseline restored |
| Stage-15 kernel parity | [stage15-kvarn-prefill-tile-parity.json](stage15-kvarn-prefill-tile-parity.json) | Query-tiled `_packed_attention_split`: 8 fixture cases match the PyTorch oracle (rmse ≤ 2.0e-4, packing-repair tolerances), sticky-status negatives correct, compute-sanitizer 0 errors, fixture passes under sanitizer; small-fixture scope, slope not yet measured; baseline restored |
| Stage-15 2048 kernel re-profile | [packed-kvarn-2048-kernel-profile-stage15.json](packed-kvarn-2048-kernel-profile-stage15.json) | Tiled split 3.06× total / 6.12× per launch vs stage-14; chunk1→chunk2 mean growth 4.6×→1.17×; Marlin now 47% of busy (unchanged 1442 ms); 26× gate not met; 2048-in/128-out in 15.0 s, zero retractions; baseline restored |
| Stage-15 8192 kernel re-profile | [packed-kvarn-8192-kernel-profile-stage15.json](packed-kvarn-8192-kernel-profile-stage15.json) | Eight chunks, split mean 101→453 µs (linear ~6.3 µs/page); empty-split elision helps only pages<16; 8192-in/128-out in 142.6 s, zero retractions; 26× gate not met; ~3.8 h split extrapolation at 262144; baseline restored |
| Stage-16 8192 kernel re-profile | [packed-kvarn-8192-kernel-profile-stage16.json](packed-kvarn-8192-kernel-profile-stage16.json) | 32-query fuse + BLOCK=32: launches 32768→4096, wall 143s→35s, busy fraction 0.54→0.90; Marlin 45%; 26× still unmet (~2.0 h split extrap at 262144); baseline restored |
| Stage-16 32768 wall | [packed-kvarn-32768-wall-stage16.json](packed-kvarn-32768-wall-stage16.json) | 32768-in/128-out in 105.5 s, 0 retractions, ~311 tok/s wall; 4× tokens in 3.0× the 8192 time; no profiler; baseline restored |
| C1 1024 FP8 vs KVarN | [c1-1024-fp8-vs-kvarn.json](c1-1024-fp8-vs-kvarn.json) | 1024-in/128-out wall 1.65 s FP8 baseline vs 4.05 s KVarN stage16 (2.45×); 0 retractions both; not official serving JSONL, not 1024-out fixture |
| KV-once attempt | [packed-kvarn-8192-kv-once-regression.json](packed-kvarn-8192-kv-once-regression.json) | Parity passed at BLOCK=16; 8192 wall 41.2 s vs stage16 35.0 s (regression); not the serving recipe |
| KV-once 32768 native | [packed-kvarn-32768-kv-once-regression.json](packed-kvarn-32768-kv-once-regression.json) | 262144 recipe, 32768-in/128-out 169.4 s vs stage16 105.5 s (1.61× worse); 0 retractions; not shipped |
| Fuse-q32 8192 overlay | [packed-kvarn-8192-fuse-q32.json](packed-kvarn-8192-fuse-q32.json) | Parity passed; 8192-in/128-out 16.8 s vs stage16 35.0 s; overlay on stage16, not a rebuilt image |
| Fuse-q32 32768 overlay | [packed-kvarn-32768-fuse-q32.json](packed-kvarn-32768-fuse-q32.json) | 32768-in/128-out 107.6 s vs stage16 105.5 s; no gain at 32k; do not ship |
| FlashInfer 8192 overlay | [packed-kvarn-8192-flashinfer.json](packed-kvarn-8192-flashinfer.json) | Rotated-space dequant+FA; 8192-in/128-out 15.2 s vs stage16 35.0 s; oracle rmse 7e-5; overlay, not rebuilt |
| FlashInfer 32768 overlay | [packed-kvarn-32768-flashinfer.json](packed-kvarn-32768-flashinfer.json) | Rotated-space; 32768-in/128-out 50.4 s vs stage16 105.5 s (2.09×, ~650 tok/s wall); still behind syv-ai; not in series |
| Stage-18 rebuilt walls | [packed-kvarn-stage18-rebuilt.json](packed-kvarn-stage18-rebuilt.json) | image f0df3d2f, FA patch in series (17 digests); oracle rmse 7e-5; 8192 17.9 s, 32768 52.9 s vs stage16 35/105.5; baseline restored |
| Stage-18b always-FA walls | [packed-kvarn-stage18b-always-fa.json](packed-kvarn-stage18b-always-fa.json) | image 7b2d45db; 8192 16.9 s, 32768 **45.7 s** (717 tok/s, 2.31× stage16); busy 0.914 profile; baseline restored |
| KVarN C1 8192+32768 stage18 | [c1-kvarn-stage18.json](c1-kvarn-stage18.json) | rebuilt image; 8/8 both depths; 32768 TTFT 40.7 s vs FP8 29.4 s; out 13.0 vs 23.8 tok/s; accept 5.37 vs 6.25; first deep official completion |
| Power rows 200-350 W | [power-rows-stage18.json](power-rows-stage18.json) | KVarN stage18 C1 window: p90 275 W, max 277 W, 0 over 280 W cap, 36% in band; FP8 replay p90 125 W, 8% in band |
| FlashInfer 8192 kernel profile | [packed-kvarn-8192-kernel-profile-flashinfer.json](packed-kvarn-8192-kernel-profile-flashinfer.json) | GPU trace: Marlin W4A16 6.16 s, FlashInfer prefill 0.25 s; attention solved, GEMM is the 32k leftover |
| Prime Envs quick (FP8 baseline) | [prime-envs-quick-baseline.json](prime-envs-quick-baseline.json) | 66/66 operational ok; AIME24/25/26 0.30/0.50/0.40, I3 0.33, LCB 0.42; many 8192 truncations; live baseline not KVarN; full/agentic not run |
| Official C1 FP8 baseline | [c1-official-fp8-baseline.json](c1-official-fp8-baseline.json) | sglang.benchmark.serving 8 prompts, 1024-out, seed 20260913; 1024/8192/32768 completed; 65536+ not admitted on 64k; accept_length ~6.1 |
| KVarN C1 1024 overlay | [c1-1024-kvarn-flashinfer.json](c1-1024-kvarn-flashinfer.json) | official serving 8 prompts 1024/1024; 114 s vs FP8 35 s; TTFT 1.2 s vs 0.84 s; TPOT 16 ms vs 3.5 ms; accept 5.65 vs 6.05 |
| GSP KVarN overlay | [gsp-kvarn-flashinfer.json](gsp-kvarn-flashinfer.json) | 32/32 ordered 8x4; 271 s vs FP8 54 s; median TTFT 335 ms vs p90 3220 ms (reuse works); accept 4.83 vs 5.08 |
| GSP FP8 baseline | [gsp-fp8-baseline.json](gsp-fp8-baseline.json) | 8 groups x 4, system 2048, question 128, out 256, ordered; 32/32; median TTFT 226 ms vs p90 2092 ms |

**No completed 245,760-token candidate inference benchmark is claimed.** Candidate source/CPU checks are separate from model quality, capacity and GPU sampling qualification.

Model-quality evaluation belongs in [eval/](../../eval/README.md), using upstream
Prime Envs environments. No upstream evaluation results are recorded here.

See [runtime benchmark guidance](../../docs/benchmarks.md), [qualification limits](../../docs/qualification.md), and the [uploaded patch chain](../../patches/README.md).

[Second KVarN maintenance window](refactor-kvarn-startup.json): candidate never launched; recovery restored the original service. No GPU measurement.
