---
name: native-262144-low-qty-only
description: "Native 262144 SGLang+DFlash2 mission: bottleneck-attack protocol, legit greedy benchmarks, deployable endpoint, honest syv-ai comparison"
condition: ["eval/scripts/run", "bench", "candidate window", "deploy"]
scope: "tool:bash"
---


**Highest tok/s, highest score, shortest TTFT on 262144 is the only work.** Everything below serves that; the benchmark-legitimacy and honesty rules are how it is measured truthfully, not a retreat from it.

**Bottleneck protocol (user-ordered):** profile, fix the biggest bottleneck, measure, repeat. Attack every measured bottleneck; close a "fix" only with measured evidence. Current ledger: attention solved (FA, 0.25 s/8k); Marlin W4A16 GEMM at the fp16 hardware ceiling (61-63 TFLOPs; int8 paths all slower on this stack); decode weight-bandwidth-bound (~15 ms/step floor). Next levers are big ports (vLLM marlin-int8), not quick wins — do not re-litigate closed measurements.

**Benchmarks must be legit (Prime Envs pins: prime-envs c4d04dfe, verifiers ef47b2e9 — never change tasks or scoring):**
- Runner parameters (sampling, output budget) MAY change when a flaw is demonstrated (e.g. 8192-token cap truncated ~70% of thinking episodes = measuring the cap). Current config: greedy (temperature 0, top_p 1, no top_k), 32768-token budget.
- Same runner config for every arm; numbers across config changes are never compared or merged.
- Full suite runs are authorized after the fix iterations close; per-taskset results are ledgered with their config.

**Deployment:** the winning candidate image becomes the live `qwen-inference` endpoint (OpenAI-compatible, 127.0.0.1:18020/v1, key auth). Commit and push all patch series, benches, and ledgers. Document the endpoint in the nix README.

**Honesty rules that never change:** no benchmark edits to improve scores; no silent clamping of depth; no claiming a syv-ai beat without wall-clock evidence; baseline FP8 64k restored after candidate windows; GPU windows only under the maintenance-lease + hard-recovery protocol.
