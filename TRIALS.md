# Trial log

## Target selection

“Qwen 27B Max” was resolved to the open `Qwen/Qwen3.8-27B` model. The API-only Max model is not a 27B checkpoint. LocalMaxxing and the syv-ai RTX 3090 work identified patched vLLM with AutoRound W4A16 as the fastest demonstrated single-card path that retained at least 64K context.

## 200 W baseline

The first controlled benchmark kept the existing 200 W policy. All candidates used the same pinned image, model revisions, 65,536 context, BF16 KV cache, prefix caching, one active sequence, and greedy real-prompt suite.

| Candidate | Median or observed decode | Outcome |
|---|---:|---|
| DFlash2, 7 drafts | 72.6 tok/s median | Selected |
| MTP, 4 drafts | 63.2 tok/s median | Rejected: about 15% slower |
| DFlash2 plus n-gram chain | 66.7–69.7 tok/s | Rejected: realistic regression |

DFlash2 used about 1 GB more VRAM than MTP but delivered the best tok/s and tok/J. The optional n-gram chain did not provide a useful gain on the document-copy task and reduced combined document throughput from 84.5 to 80.4 tok/s.

## Prefix cache

A repeated 23,196-token document prompt reached its first generated token in 1.22 seconds after the first turn, versus 29.71 seconds cold. This is a real agent benefit but is separate from steady decode throughput.

## Long-context false failure

The upstream needle script initially returned an empty visible answer at approximately 60K tokens. The model had spent its 32-token output allowance in the reasoning channel because the script did not disable thinking. This was a probe defect, not a context failure.

`needle-bench.py` makes the contract explicit: thinking disabled, greedy decoding, 64 output tokens, and measured API usage. It passed with 60,042 prompt tokens and recovered `ZXCVBNM12345` from 90% depth in 98.745 seconds.

## API and agent behavior

The selected DFlash2 configuration passed all 12 upstream API smoke checks, including deterministic greedy output, seeded sampling, logprobs, structured output, streaming, explicit thinking, and a 20K prompt. `tool-smoke.py` also produced the forced Hermes call `health_check({"status":"ok"})`.

## First guarded deployment

Commit `20bb430` built, staged, and booted successfully, but `qwen-inference.service` failed before `ExecStartPre` with systemd status `226/NAMESPACE`. The configured writable path did not exist. The guarded boot workflow installs a prebuilt generation and does not execute `system.activationScripts` in the way the module assumed.

The repair replaces that assumption with a root system service that creates the state directories after local filesystems mount and before user sessions. The user service allows the existing parent in its namespace and waits boundedly for the root service. A Nix contract now checks the root service ordering, required mount, oneshot persistence, and user-service writable parent. Full x86_64 Linux validation passes.

## 250 W policy

The 200 W trace kept GDDR6X at full speed while the GPU core fell to roughly 525–645 MHz. The user selected 250 W as the next efficiency point. This changes only power headroom: model weights, quantization, DFlash verification, context length, KV precision, prefix caching, reasoning, and sampling remain unchanged.

The 250 W result is accepted only after throughput, tok/J, thinking, tools, long-context retrieval, and the runtime quality battery pass on the deployed service.
