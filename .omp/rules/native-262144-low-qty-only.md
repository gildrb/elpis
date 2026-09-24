---
name: native-262144-low-qty-only
description: "Native 262144 EXL3+DFlash2 mission: bottleneck-attack protocol, legit greedy benchmarks, deployable endpoint, honest syv-ai comparison"
condition: ["eval/scripts/run", "bench", "candidate window", "deploy"]
scope: "tool:bash"
---


**Highest tok/s, highest score, shortest TTFT on 262144 is the only work.** Everything below serves that; the benchmark-legitimacy and honesty rules are how it is measured truthfully, not a retreat from it.

**Bottleneck protocol (user-ordered):** profile, fix the biggest bottleneck, measure, repeat. Attack every measured bottleneck; close a "fix" only with measured evidence. Measurements from the retired engine do not transfer: profile the EXL3 path before choosing the next lever, and do not re-litigate measurements already closed on this engine.

**Benchmarks must be legit (Prime Envs pins: prime-envs c4d04dfe, verifiers ef47b2e9 — never change tasks or scoring):**
- Runner parameters (sampling, output budget) MAY change when a flaw is demonstrated (e.g. 8192-token cap truncated ~70% of thinking episodes = measuring the cap). Current config: greedy (temperature 0, top_p 1, no top_k), 32768-token budget.
- Same runner config for every arm; numbers across config changes are never compared or merged.
- Full suite runs are authorized after the fix iterations close; per-taskset results are ledgered with their config.

**Deployment:** the winning candidate image becomes the live `qwen-inference` endpoint (OpenAI-compatible, 127.0.0.1:18020/v1, key auth). Commit and push all benches and ledgers. Document the endpoint in the nix README.

**Honesty rules that never change:** no benchmark edits to improve scores; no silent clamping of depth; no claiming a syv-ai beat without wall-clock evidence; live EXL3 baseline restored after candidate windows; GPU windows only under the maintenance-lease + hard-recovery protocol.
