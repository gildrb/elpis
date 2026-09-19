# Bonsai Oracle — Ternary-Bonsai-2-27B PQ2_0 (PrismML llama.cpp fork)

**PrismML fork reference output for parity qualification.**
This file records an independent CPU-only numerical reference captured from the
PrismML-Eng llama.cpp fork shipped inside the local docker image
`bonsai-inference:local`. Use it to qualify the parity of other Bonsai
implementations (token ids, logprobs, and top-k distributions must match).

## Image

- Image: `bonsai-inference:local`
- Image ID: `sha256:1a2bfcd386930b0f8f67c95aebbd3160f15ac69ba061d8c27c62880d8c84b1b5`
- RepoDigest: `bonsai-inference@sha256:1a2bfcd386930b0f8f67c95aebbd3160f15ac69ba061d8c27c62880d8c84b1b5`
- Created: 2026-09-18T10:28:57.337965242+02:00, size 5.99 GB
- Base: Ubuntu 22.04.5 LTS (glibc 2.35), CUDA 12.8.0

## Binary

- Path in image: `/opt/llama/llama-server`
- Self-reported version: `version: 0.2.0-dev (build 10683, commit d8f26eec7)`,
  `built with GNU 11.4.0 for Linux x86_64`
- Source: PrismML-Eng/llama.cpp, commit
  `d8f26eec76da6d09bb708bcba51ef64b8cd868a3` (2026-09-09)
- Model: `/models/Ternary-Bonsai-2-27B-PQ2_0.gguf`
  (host path `/mnt/ssd/storage/ai/qwen3.8-27b/models/Ternary-Bonsai-2-27B-PQ2_0.gguf`,
  7,206,168,928 bytes)

## Execution environment (CPU-only)

The GPU was owned by another process; nothing here touches it:

- The image does not ship `libgomp.so.1` (normally injected by the NVIDIA
  container runtime). It was provided read-only from the host by extracting
  Ubuntu 22.04 `libgomp1_12.3.0-1ubuntu1~22.04.3_amd64.deb`
  (deb sha256 `870c27299185a5dd4accad3b15bf82a7409fd7073cccaa8025875307da4d0ce2`,
  extracted `libgomp.so.1.0.0` sha256
  `d46f9225c1883039e8a6853e6d96ca1af11d034ce186a090952e4a7c8a7c2fdc`)
  and bind-mounting it to `/usr/lib/x86_64-linux-gnu/libgomp.so.1:ro`.
- `LD_LIBRARY_PATH=/opt/llama:/usr/local/cuda-12.8/compat` lets the CUDA
  backend library load from the image's own CUDA compat dir; without any
  `/dev/nvidia*` device the backend init fails harmlessly:
  `ggml_cuda_init: failed to initialize CUDA: no CUDA-capable device is detected`.
  Inference then runs entirely on the CPU backend (`-ngl 0`).
- No speculative decoding: the fork's `--spec-type` defaults to none
  (speculative decoding is opt-in in the image entrypoint via
  `BONSAI_SPECULATIVE=1`); no draft model was used or required.

## Exact docker command (oracle run)

```bash
timeout 1500 docker run --rm --name bonsai-oracle-cpu \
  --entrypoint /opt/llama/llama-server \
  --memory 24g \
  -v /mnt/ssd/storage/ai/qwen3.8-27b/models:/models:ro \
  -v /tmp/libgomp-u22.so.1.0.0:/usr/lib/x86_64-linux-gnu/libgomp.so.1:ro \
  -e LD_LIBRARY_PATH=/opt/llama:/usr/local/cuda-12.8/compat \
  -p 127.0.0.1:18100:18100 \
  bonsai-inference:local \
  -m /models/Ternary-Bonsai-2-27B-PQ2_0.gguf \
  --host 0.0.0.0 --port 18100 \
  -ngl 0 -t 8 -c 2048 -fa on --jinja \
  > /tmp/bonsai-oracle-server.log 2>&1
```

(The image entrypoint refuses command overrides, hence the explicit
`--entrypoint`. The production entrypoint at `/opt/bonsai/serve/entrypoint.sh`
runs the same binary with `-ngl -1 -fa on -c <ctx> --temp 1.0 --top-p 0.95
--top-k 20 --jinja` on port 18020 with an API key; those serving-side sampler
defaults do not affect this capture because the request JSON pins the
parameters.)

## Exact request

One request, native `/completion` endpoint, sent after the server printed
`listening on http://0.0.0.0:18100`:

```json
{"prompt": "The capital of France is", "n_predict": 0, "prompt_logprobs": true, "n_probs": 8, "temperature": 0.0}
```

Result: HTTP 200 in ~8.1 s (5 prompt tokens evaluated, 1 token sampled).

### Fork semantics for this exact body (verified against fork source)

- `prompt_logprobs` is **not a supported parameter** in this fork (the field
  does not exist in `tools/server/*`; the fork's `tools/server/README.md`
  documents `completion_probabilities` as generated-token probabilities only).
  The key is ignored silently.
- `completion_probabilities` therefore contains exactly **one entry**: the
  sampled next token after the full prompt, i.e. the **final prompt position**,
  with its `top_logprobs` list (8 candidates, `n_probs: 8`).
- `n_predict: 0` still produces that single sample: the loop samples the
  next token, populates its probabilities, then stops on budget
  (`n_predict_max = 0`). This one entry is the oracle's final-position
  distribution.
- Prompt token ids (via `POST /tokenize` with `{"content": "The capital of
  France is"}`): `[760, 6511, 314, 9338, 369]` — matches the response's
  `tokens_evaluated: 5`.

## Model metadata at load (server log lines)

```
I print_info: arch                  = qwen35
I print_info: vocab type            = BPE
I print_info: n_ctx_train           = 262144
I print_info: n_embd                = 5120
I print_info: n_layer               = 64
I print_info: n_layer_all           = 64
I print_info: n_head                = 24
I print_info: n_head_kv             = 4
I print_info: n_embd_head_k         = 256
I print_info: n_embd_head_v         = 256
I print_info: n_gqa                 = 6
I print_info: n_ff                  = 17408
I print_info: rope type             = 40
I print_info: rope scaling          = linear
I print_info: freq_base_train       = 10000000.0
I print_info: freq_scale_train      = 1
I print_info: model type            = 27B
I print_info: general.name          = Hf
I print_info: n_vocab               = 248320
I print_info: file type   = PQ2_0 - 2.13 bpw (group 128)
I llama_context: n_ctx              = 2048
I llama_context: n_ctx_seq          = 2048
I cmn  init: llama threadpool init, n_threads = 8
I srv  load_model: initializing, n_slots = 4, n_ctx_slot = 2048, kv_unified = 'true'
E ggml_cuda_init: failed to initialize CUDA: no CUDA-capable device is detected
```

`GET /props` (also captured) reports `"model_ftype": "PQ2_0 - 2.13 bpw (group 128)"`,
`n_ctx: 2048`, `total_slots: 4`, vision/video/audio modalities disabled.

## Key oracle numbers (final prompt position)

Sampled top token: `" Paris"` (id 11751), logprob -0.1818111687898636.
Top-8 candidates (id, token, logprob):

| id | token | logprob |
|---|---|---|
| 11751 | " Paris" | -0.1818111687898636 |
| 303 | " in" | -4.285635948181152 |
| 198 | "\n" | -4.330818176269531 |
| 524 | " not" | -4.439243316650391 |
| 264 | " a" | -4.565729141235352 |
| 25 | ":" | -4.643089294433594 |
| 248046 | "" | -4.746088981628418 |
| 1076 | "..." | -5.102964401245117 |

Full raw HTTP response body: `p1-prompt-logprobs.json` (includes
`generation_settings`, `timings`, and the complete
`completion_probabilities` array verbatim as returned).

## File sha256

| file | sha256 |
|---|---|
| `p1-prompt-logprobs.json` (raw HTTP body, 2,376 bytes) | `8d11beca67b9df3d5967160a5a113bcb9cb4afed1496e36650940bf2818176a3` |
| `Ternary-Bonsai-2-27B-PQ2_0.gguf` | `3907dc1658db1f78a9826bf8d5bcb8dc65db0d466388937af57f2294fae62ec1` |
| `bonsai-inference:local` image | `1a2bfcd386930b0f8f67c95aebbd3160f15ac69ba061d8c27c62880d8c84b1b5` |
| libgomp sidecar `.so` (bind-mounted) | `d46f9225c1883039e8a6853e6d96ca1af11d034ce186a090952e4a7c8a7c2fdc` |
