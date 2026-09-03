# Qwen3.8-27B on RTX 3090

Private operational snapshot of the Qwen inference configuration used by `server` and Hermes Agent. The production source of truth remains `gildrb/nix`; this repository keeps the inference module, pinned artifact identities, benchmark probes, and measured decisions together.

## Selected configuration

| Item | Value |
|---|---|
| GPU | ZOTAC GAMING GeForce RTX 3090 Trinity, 24 GB |
| Power limit | 250 W deployment target; 200 W benchmark baseline |
| Model | Qwen3.8-27B AutoRound W4A16 fast variant |
| Runtime | Patched vLLM 0.27.1 image from syv-ai |
| Speculation | DFlash2, 7 draft tokens |
| Context | 65,536 tokens, BF16 KV cache |
| Prefix cache | Enabled |
| Concurrent sequences | 1 |
| API | OpenAI-compatible, authenticated, loopback-only |
| Hermes Agent | v0.21.0 (`v2026.8.31`) |
| Hermes alias | `qwen` |

At 250 W, the unchanged DFlash2 configuration reached **120.5 tok/s median**, up **66.0%** from the 72.6 tok/s 200 W baseline. Tokens per joule improved **32.8%**, from 0.363 to 0.482. GSM8K scored **95.5% on 200 questions**, all 12 API checks passed, and the 60,042-token needle was retrieved exactly in 71.862 seconds. MTP and the optional n-gram chain remain rejected by the controlled 200 W comparison.

Detailed measurements and artifact identities are in [`benchmark-results.json`](benchmark-results.json).

## Repository map

- `nix/qwen-inference.nix`: exact Qwen service module snapshot, including the boot-time state-directory repair.
- `nix/local-ai-backend.nix`: exact Hermes settings and boot-time managed-config synchronization from production.
- `nix/nvidia-quiet.nix`: exact GPU policy snapshot with the RTX 3090 capped at 250 W.
- `nix/hermes-integration.nix`: isolated Hermes custom-provider and API-key wiring.
- `nix/server.nix`: host import and SSD state-path snapshot.
- `prepare-pinned.sh`: one-time model preparation with immutable Hugging Face revisions.
- `needle-bench.py`: long-context retrieval probe with thinking disabled.
- `tool-smoke.py`: forced Hermes-style function-call probe.
- `gsm8k-bench.py` and `gsm8k-200.json`: dependency-free, pinned 200-question quality gate.
- `benchmark-results.json`: benchmark inputs, outputs, resource use, and selection rationale.

Model weights, API keys, caches, and generated corpora are not committed.

## Runtime layout

Persistent state lives at:

```text
/mnt/ssd/storage/ai/qwen3.8-27b/
├── api-key
├── hermes.env
├── cache/
└── models/
```

The preparation container has controlled network access for pinned downloads. The inference container receives the model mount read-only, runs without Linux capabilities, uses `no-new-privileges`, joins an internal Docker network, and publishes only `127.0.0.1:18020`.

Hermes reads `QWEN_API_KEY` from `hermes.env` and calls:

```text
http://127.0.0.1:18020/v1
```

## Verification

The deployment contract requires all of the following:

1. Build the x86_64 NixOS system closure.
2. Validate the generated Docker Compose configuration.
3. Run the authenticated completion and forced tool-call health probe.
4. Retrieve a needle from a measured 60K-token prompt.
5. Confirm the 250 W cap, stable fan command, and improved tok/s without a quality regression.

The selected runtime consumes approximately 22.5–23.0 GB VRAM and 3.43 GiB host RAM. At 250 W it held roughly 900–1050 MHz core clock, 69–71°C, and 54–57% fan command during sustained decoding. Keeping the model resident holds the card near 129–137 W while idle; unloading it returns the card to roughly 25 W and zero fan command.

## Provenance

- [RoyCorp SGLang, NVFP4, and DFlash2 whitepaper](https://roycorp.net/sglang/index.html)
- [syv-ai Qwen3.8-27B RTX 3090 runtime](https://github.com/syv-ai/qwen38-27b-rtx3090)
- [LocalMaxxing Qwen3.8-27B reference run](https://www.localmaxxing.com/en/runs/cmszj4klh0e4vms01944dfihh)
