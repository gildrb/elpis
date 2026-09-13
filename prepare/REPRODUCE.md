# Reproduce the compact embedding artifact

The current SGLang service uses the retained artifact recorded in `manifest.json`, plus the original quantized W4 DFlash2 draft. Serving verifies these files; it never runs this conversion, downloads a substitute or falls back automatically. This document describes a separate, explicitly approved CPU reproduction, not service startup or deployment.

Final-profile quality, short-suite speed and bounded memory/cache checks have completed; see [../docs/qualification.md](../docs/qualification.md). Deployment is not yet activated. The pinned manifest and proof authenticate artifact reproduction; current qualification results do not authorize changing their bytes or skipping verification.

## Offline source preparation (model installation is separate)

Supply the model files yourself. These scripts have no network or download path.
`source-provenance.json` maps each required file to its pinned upstream repository,
revision, size and SHA256. A directory name or Hugging Face cache receipt is not
proof of the current bytes. The local base directory was modified after download.

The assembled source is **not** a direct snapshot: eleven files come from
`dbirks/Qwen3.8-27B-W4A16-AutoRound` at
`1f05c441c4e64ae0549de44fa9ea5a6d43610314`, five from
`syvai/qwen3.8-27b-3090-fast-variant` at
`124c14e7e8c7d2f5402933b9af368e772a9fcf0c`, and shard 6 is derived locally.
The two draft files come from `syvai/Qwen3.8-27B-DFlash2-W4A16` at
`4d30ec736ffc6b8688dc2ae2b502d9b48bdec279`.

Raw shard 6 has SHA256
`55a14ee79d3e5a65a8731d89426f4df477e8bdc7daa7976d41254d8afb9432f0`.
It contains BF16 embeddings and the final norm. `quantize-embedding.py` reproduces
symmetric int8, group-128 embedding quantization, using round-to-nearest-even,
FP32 scales clamped to `1e-10`, int32 packing and BF16 stored scales. It preserves
the norm and requires the resulting shard's existing `source.sha256` hash
`b2e0854ed3be3141ed79f4204f7aa8e616da626d4662017117330490747c2036`.
Chunking bounds RAM without changing any per-group operation. The upstream
`quant_embed.py` recipe is archived verbatim as `upstream-quant-embed.py.txt`,
pinned by URL/revision and SHA256 in the provenance file. It is never executed:
the upstream script modifies files in place; our preparation does not.

1. Set absolute `REPO`, supplied `BASE`, `FAST`, `DRAFT`, and `RAW_EMBED` paths.
   `RAW_EMBED` must be the original BF16 shard, not the modified local shard.
   The retained base `model-00006-of-00007.safetensors.bak_embed` was independently
   hashed and matches the raw upstream SHA256. Set `ATTEMPT` to an **absent** path
   below an existing private parent. Symlink path components and existing output
   paths are rejected. Supplied directories may contain unused files; only the
   exact mapped files are copied.
2. Run offline assembly after explicit preparation approval. Reserve at least
   **45 GiB free disk** for supplied-file copies, raw shard, quantized intermediate
   and the later compact artifact; supplied originals are additional. Use the
   pinned image with **32 GiB RAM**, no GPU and no network for both transformations.
   Assembly creates `source/`, `draft/` and `input/` in its private attempt.
   It authenticates every copied file and leaves source incomplete pending shard 6.
3. Run the offline shard transformation below. It checks the raw hash and all
   other source hashes before computing. It requires the exact derived hash
   before publishing an independent, read-only copy. Failed attempts remain for
   inspection; do not retry into the same directory or delete them automatically.
4. Create an empty `conversion/` below this attempt. Set `SOURCE` to the new
   `source/` and `WORK` to the new `conversion/`. Follow the original converter
   invocation and proof checks below. Keep supplied originals read-only.
5. Run the final verifier on the new compact target and copied draft. Publication,
   service configuration and activation remain separate approvals.

```sh
python3 "$REPO/prepare/assemble-source.py" --base "$BASE" --fast "$FAST" --draft "$DRAFT" --embedding-input "$RAW_EMBED" --destination "$ATTEMPT"
docker run --rm --runtime runc --network none --read-only --cap-drop ALL --security-opt no-new-privileges:true --cpus 4 --memory 32g -e NVIDIA_VISIBLE_DEVICES=void -e CUDA_VISIBLE_DEVICES= -e PYTHONDONTWRITEBYTECODE=1 --tmpfs /tmp:rw,noexec,nosuid,size=1g --entrypoint python3 -v "$REPO/prepare:/preparation:ro" -v "$ATTEMPT:/work:rw" lmsysorg/sglang@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9 /preparation/quantize-embedding.py --work /work
mkdir -m 700 "$ATTEMPT/conversion"
SOURCE="$ATTEMPT/source"
WORK="$ATTEMPT/conversion"
# Run the original converter command below, then:
python3 "$REPO/prepare/verify-models.py" --target "$WORK/artifact" --draft "$ATTEMPT/draft"
```

**Validation boundary:** pinned HF API LFS SHA256/size metadata and downloaded
small non-LFS configuration bytes matched all 16 direct source files and both
draft files. Large upstream weights were not downloaded. Raw shard 6's retained
backup matches its upstream hash. The isolated chunked transformation passed in the pinned CPU image in
35.361 seconds: all 1,291,274,752 output bytes matched the existing shard SHA256.
See `shard-validation.json` for the bounded evidence. This used `--shard-only`,
which requires the raw hash and exact output hash but does not assemble or
publish source. The full offline assembly/conversion pipeline has not been run;
its exact inventory and output checks remain mandatory. Existing converter, manifest,
proof and model inventories are unchanged. No model installation is automated.

## Original compact conversion

1. **Verify provenance first.** `manifest.json` pins the native image, exact converter and numerical proof. `source.sha256` pins all17 retained fast-source files. The revision labels describe source ancestry; the file hashes identify the assembled source. Before reproduction, verify the converter/proof hashes against manifest.json, require the source directory inventory to be exactly the17 manifest entries, reject symlinks, and run `sha256sum --check` against source.sha256 from the source directory. Do not use a fresh download merely because its model name matches.
2. **Create an exclusively owned empty work directory.** Preserve retained originals. The exact script reads `/source`, writes `/work/artifact`, and rejects an existing artifact path. Use a fresh private directory per attempt; never mount an active artifact at `/work`. The script uses independent file copies, not hardlinks. Do not delete partial attempts automatically or treat a partial output as qualified.
3. **Run only with explicit preparation approval.** This CPU conversion reads and hashes roughly17GB and writes a new model copy. Reserve32GiB RAM and adequate disk; it is not a serving command. Use absolute values for REPO, SOURCE and WORK in the documented invocation below. Do not mount API keys or any production writable path.
4. **Verify completion.** Require exit0 and `/work/validation.json`. Require all output filenames to match artifact.sha256, then check every output file hash from the artifact directory. Compare numerical proof fields to embedding-validation.json: all248320 rows/1271398400 values, same dense tensor hash, same actual tensor-byte accounting, and unchanged source/output inventory. Rehash retained source. A newly reproduced safetensors file may have serialization-level differences across runtime changes; any mismatch is a failed exact reproduction requiring review, not permission to silently update the manifest.
5. **Publish separately.** Only after validation, expose the immutable artifact through explicit approved configuration. Do not overwrite the current model or automatically alter serving defaults. Output files are0444 and artifact directory0555; owner permissions alone do not establish content authenticity, so retain the manifest checks. Keep conversion logs/proof with the artifact but exclude secrets.

Reproduction invocation (not executed automatically):

```sh
docker run --rm --runtime runc --network none --read-only --cap-drop ALL --security-opt no-new-privileges:true --cpus 4 --memory 32g -e NVIDIA_VISIBLE_DEVICES=void -e CUDA_VISIBLE_DEVICES= -e PYTHONDONTWRITEBYTECODE=1 --tmpfs /tmp:rw,noexec,nosuid,size=1g --entrypoint python3 -v "$REPO/prepare:/preparation:ro" -v "$SOURCE:/source:ro" -v "$WORK:/work:rw" lmsysorg/sglang@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9 /preparation/convert-embedding.py
```

The original converter is intentionally copied byte-for-byte. It authenticates structure and unchanged source bytes during the run, not expected source revision by itself; step1 is mandatory. Its `validation.json` has source path `/source`, which is the reproducible container mount, not the host provenance path. The qualified host location is recorded in manifest.json.

Only embeddings are converted. The target compressed head and draft compressed FC require the separately reviewed compatibility assets in [../patches/](../patches/NOTES.md); numerical embedding validation alone does not qualify those execution paths or end-to-end quality. No FC or QKV conversion is included. The selected runtime also includes the reviewed Mamba checkpoint correction, qualified narrowly for `extra_buffer`, not `extra_buffer_lazy`.

For serving, preserve the guarded service's prepare-before-inference contract. `prepare` authenticates original pinned-image source without replacements and verifies the retained models. Inference authenticates the three read-only replacements and verifies the models again. Do not launch only the inference Compose service. Reproduction completion does not replace these checks or authorize activation. Independent guarded-generation rollback is documented in [../README.md](../README.md).
