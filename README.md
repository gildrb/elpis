# Local Qwen inference

SGLang serving config for Qwen3.8-27B on the RTX 3090. `gildrb/nix` imports these modules the same way it imports `gildrb/dotfiles`. GPU driver, power caps, and fan policy stay in `gildrb/nix`.

## Selected configuration

| Item | Value |
|---|---|
| GPU | ZOTAC GAMING GeForce RTX 3090 Trinity, 24 GB |
| Runtime | SGLang `lmsysorg/sglang:v0.5.19` |
| Model | `cyankiwi/Qwen3.8-27B-AWQ-INT4` revision `63768c10df38c0395e12ef49edac1bd539eaeeea` |
| Served name | `qwen3.8-27b` |
| API | OpenAI-compatible, authenticated, loopback-only `127.0.0.1:18020` |
| Concurrent sequences | 1 |

Ollama and llama.cpp are not part of this stack. Hermes, Autolith, and other local clients use `qwen-local` at `http://127.0.0.1:18020/v1`.

## Repository map

- `nix/qwen-inference.nix`: SGLang compose unit, credentials, and health timer
- `nix/qwen-inference-health.nix`: authenticated completion and tool-call probe
- `nix/qwen-observability.nix`: Prometheus scrape and Grafana dashboard
- `nix/sglang-entrypoint.sh`: pinned model download and `sglang.launch_server`

Model weights, API keys, caches, and generated corpora are not committed.

## Runtime layout

```text
/mnt/ssd/storage/ai/qwen3.8-27b/
├── api-key
├── hermes.env
├── cache/
└── models/
    └── Qwen3.8-27B-AWQ-INT4/
```
