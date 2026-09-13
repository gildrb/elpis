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

**No completed 245,760-token candidate inference benchmark is claimed.** Candidate source/CPU checks are separate from model quality, capacity and GPU sampling qualification.

Model-quality evaluation belongs in [eval/](../../eval/README.md), using upstream
Prime Envs environments. No upstream evaluation results are recorded here.

See [runtime benchmark guidance](../../docs/benchmarks.md), [qualification limits](../../docs/qualification.md), and the [uploaded patch chain](../../patches/README.md).

[Second KVarN maintenance window](refactor-kvarn-startup.json): candidate never launched; recovery restored the original service. No GPU measurement.
