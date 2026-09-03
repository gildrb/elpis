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
| Hermes alias | `qwen` |

At the 200 W baseline, DFlash2 without the optional n-gram chain won the real-prompt benchmark at **72.6 tok/s median**. MTP reached 63.2 tok/s. The n-gram chain reached 66.7–69.7 tok/s and was rejected for this workload. A 60,042-token needle probe retrieved the passcode exactly. The 250 W policy changes GPU headroom only; model, quantization, context, reasoning, and sampling remain unchanged.

Detailed measurements and artifact identities are in [`benchmark-results.json`](benchmark-results.json).

## Repository map

- `nix/qwen-inference.nix`: exact Qwen service module snapshot, including the boot-time state-directory repair.
- `nix/nvidia-quiet.nix`: exact GPU policy snapshot with the RTX 3090 capped at 250 W.
- `nix/hermes-integration.nix`: isolated Hermes custom-provider and API-key wiring.
- `nix/server.nix`: host import and SSD state-path snapshot.
- `prepare-pinned.sh`: one-time model preparation with immutable Hugging Face revisions.
- `needle-bench.py`: long-context retrieval probe with thinking disabled.
- `tool-smoke.py`: forced Hermes-style function-call probe.
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

The 200 W baseline consumed approximately 22.5–23.0 GB VRAM and 3.43 GiB host RAM. Steady decode reached the power cap. Keeping the model resident held the card near 129 W while idle; unloading it returned the card to roughly 25 W and zero fan command. The 250 W run is recorded separately after deployment so the baseline remains auditable.

## Provenance

- [RoyCorp SGLang, NVFP4, and DFlash2 whitepaper](https://roycorp.net/sglang/index.html)
- [syv-ai Qwen3.8-27B RTX 3090 runtime](https://github.com/syv-ai/qwen38-27b-rtx3090)
- [LocalMaxxing Qwen3.8-27B reference run](https://www.localmaxxing.com/en/runs/cmszj4klh0e4vms01944dfihh)
