# Public checkpoint options

Keep the retained recipe for byte reproduction. Public HF metadata checked on
2026-09-13 does not identify a single checkpoint that matches its complete target
inventory. This is a bounded comparison, not a claim that no such repository can
exist. Exact API URLs, revisions, weight sizes and advertised LFS SHA256 values
are recorded in [public-options.json](public-options.json).

## Retained pair

| Repository and exact revision | Finding |
|---|---|
| `dbirks/Qwen3.8-27B-W4A16-AutoRound` @ `1f05c441c4e64ae0549de44fa9ea5a6d43610314` | Complete base; 7 main shards plus extra tensors. Original BF16 embedding shard is available. Its head and extras differ from the retained fast variant. |
| `syvai/qwen3.8-27b-3090-fast-variant` @ `124c14e7e8c7d2f5402933b9af368e772a9fcf0c` | Overlay only: shard 7, extra tensors, index, config and vocabulary files. No shards 1–6. Its config declares packed embeddings, but the required embedding shard is not published here. |
| `syvai/Qwen3.8-27B-DFlash2-W4A16` @ `4d30ec736ffc6b8688dc2ae2b502d9b48bdec279` | Public, ungated packed W4 draft. Advertised 1,280,633,960-byte weight hash and downloaded config match the retained draft inventory. |

Use the eleven base files and five overlay files mapped in
`source-provenance.json`, plus the exactly reproduced embedding shard. The draft
already comes from one pinned checkpoint; no draft quantization is needed.
This establishes an exact public source for the published W4 draft, not the
ability to rerun its upstream quantization. The upstream training/quantization
environment and calibration inputs are not reproduced here. Copy the published
bytes and require `draft.sha256`; do not requantize the larger incoai draft and
assume it matches.
The source then passes through the original compact converter and final verifier.
Do not replace dequantized int8 embeddings with the raw BF16 shard: those values
are different even though both tensors have the same final dtype and shape.

## Complete alternatives, not replacements

| Repository and exact revision | Evidence and limit |
|---|---|
| `cyankiwi/Qwen3.8-27B-AWQ-INT4` @ `6e134bae811fb5adac50ee042ae5f029ac6779aa` | Five published safetensors shards; API reports compressed-tensors, pack-quantized Linear W4. This is a different quantized checkpoint, not the retained 7-shard artifact. |
| `RedHatAI/Qwen3.8-27B-INT4` @ `bf08f3dbd9a324e53956920aad378a1f1b6dd24a` | Published 18,603,387,656-byte main safetensors plus 849,400,392-byte MTP file; API reports compressed-tensors Linear W4. Different bytes/layout; no local compatibility or memory result. |
| `incoai/Qwen3.8-27B-DFlash2` @ `dedf8df68adfb1afeaf7b7480c0a0243108177b4` | Published 3,848,817,896-byte draft; API does not report the retained W4 quantization. It is not the retained 1.28 GB packed draft. |

All six API responses reported public and ungated access. Repository labels and
API quantization summaries are not runtime compatibility proofs. The retained
recipe subsequently passed full CPU reproduction from supplied files with exact
public-origin hashes; see `reproduction-validation.json`. No alternative
weights were downloaded, tensor-validated, benchmarked or evaluated. Do not reuse
the existing timing, embedding proof or model inventory for these checkpoints.

## Simplification decision

A single complete target checkpoint would remove overlay assembly and embedding
round-trip preparation **for a newly qualified model**, not reproduce this model.
The least-change complete-checkpoint candidate is the pinned dbirks base, since
it supplies the current transformer shards. Its larger original head/extras and
raw embeddings still require a new memory budget, inventory, runtime checks and
quality evaluation. No 24 GB or 240K fit is established by this audit.

For the current contract, retain the small offline stages and strict hashes.
A later owner-approved publication of the exact final target as one public,
revision-pinned repository could eliminate assembly without changing model bytes.
No such artifact is invented or selected here. Publication, licensing review and
an independent complete-download hash verification would come first.
