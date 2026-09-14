# Reproduce the retained model pair

Use this offline recipe only after explicit CPU preparation approval. Serving
verifies installed files; it does not download, convert or select alternatives.
Publication and activation need separate approval. Final-profile qualification
remains pending; see [qualification](../docs/qualification.md).

## Exact inputs and tools

[source-provenance.json](source-provenance.json) maps every input to its public
repository, full revision, size and SHA256. The target is **not one snapshot**:

| Input | Public repository | Exact revision |
|---|---|---|
| 11 source files and raw BF16 shard 6 | `dbirks/Qwen3.8-27B-W4A16-AutoRound` | `1f05c441c4e64ae0549de44fa9ea5a6d43610314` |
| 5 source files | `syvai/qwen3.8-27b-3090-fast-variant` | `124c14e7e8c7d2f5402933b9af368e772a9fcf0c` |
| 2 draft files | `syvai/Qwen3.8-27B-DFlash2-W4A16` | `4d30ec736ffc6b8688dc2ae2b502d9b48bdec279` |

The seventeenth source file is derived shard 6. The fast repository is an overlay,
not a complete checkpoint. [Public options](PUBLIC-OPTIONS.md) explains why a
single-checkpoint substitution cannot preserve the retained bytes.

`preparation.sha256` pins all four local tools, provenance, inventories and
historical proof files. Authenticate this inventory through a trusted repository
checkout before using it; a checksum file cannot authenticate itself. From the
preparation directory, require every check to pass before running any tool:

```sh
cd "$REPO/prepare"
sha256sum --strict --check preparation.sha256
```

`manifest.json` separately pins the original converter, numerical proof and
runtime image. The unchanged converter is recoverable at
`06620297735fc55056b478c0ce2c85380d39835f:prepare/convert-embedding.py`;
its SHA256 matches `conversion_script_sha256` in the manifest.
Do not format or replace the original converter. The digest-pinned
image supplies Python, torch, safetensors and compressed-tensors 0.18.0; do not
install newer dependencies inside it. Host Python only copies and hashes bytes.

## One ordered offline recipe

1. Supply absolute `REPO`, `BASE`, `FAST`, `DRAFT` and `RAW_EMBED` paths.
   Keep originals read-only. `RAW_EMBED` must be the original BF16 shard, not the
   modified local shard. Its required SHA256 is
   `55a14ee79d3e5a65a8731d89426f4df477e8bdc7daa7976d41254d8afb9432f0`.
   The retained `.bak_embed` file matched this hash in the historical check.
2. Choose an **absent** `ATTEMPT` path below an existing private parent. Symlink
   components and existing outputs are rejected by assembly. Reserve **45 GiB
   free disk**, in addition to supplied originals, and **32 GiB RAM**. The scripts
   copy only mapped files, use no hardlinks and preserve failed attempts.
3. Run the commands below in order. Stop on any nonzero exit; do not continue
   after a failure or retry into the same attempt. Neither container exposes a
   GPU, network, key or production writable path. Provision the pinned image
   separately; `--pull never` prevents an implicit image download.
4. Require the exact output and proof checks in the next section. Read-only
   permissions are not a substitute for hashes. Keep logs and proof outside the
   model directory. Never update expected hashes to accept a mismatch.
5. Publish the verified immutable target and draft only with separate approval.
   Reproduction does not replace the service's prepare-before-inference guards
   or authorize changes to runtime defaults.

```sh
python3 "$REPO/prepare/assemble-source.py" --base "$BASE" --fast "$FAST" --draft "$DRAFT" --embedding-input "$RAW_EMBED" --destination "$ATTEMPT"
docker run --rm --pull never --runtime runc --network none --read-only --cap-drop ALL --security-opt no-new-privileges:true --cpus 4 --memory 32g --memory-swap 32g -e NVIDIA_VISIBLE_DEVICES=void -e CUDA_VISIBLE_DEVICES= -e PYTHONDONTWRITEBYTECODE=1 --tmpfs /tmp:rw,noexec,nosuid,size=1g --entrypoint python3 -v "$REPO/prepare:/preparation:ro" -v "$ATTEMPT:/work:rw" lmsysorg/sglang@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9 /preparation/quantize-embedding.py --work /work
mkdir -m 700 "$ATTEMPT/conversion"
SOURCE="$ATTEMPT/source"
WORK="$ATTEMPT/conversion"
cd "$SOURCE"
sha256sum --strict --check "$REPO/prepare/source.sha256"
docker run --rm --pull never --runtime runc --network none --read-only --cap-drop ALL --security-opt no-new-privileges:true --cpus 4 --memory 32g --memory-swap 32g -e NVIDIA_VISIBLE_DEVICES=void -e CUDA_VISIBLE_DEVICES= -e PYTHONDONTWRITEBYTECODE=1 --tmpfs /tmp:rw,noexec,nosuid,size=1g --entrypoint python3 -v "$REPO/prepare:/preparation:ro" -v "$SOURCE:/source:ro" -v "$WORK:/work:rw" lmsysorg/sglang@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9 /preparation/convert-embedding.py
python3 "$REPO/prepare/verify-models.py" --target "$WORK/artifact" --draft "$ATTEMPT/draft"
sha256sum --strict --check "$REPO/prepare/source.sha256"
```

Assembly authenticates all copied files. Quantization checks the other 16 source
hashes and the exact source layout before publishing shard 6. Its symmetric int8,
group-128 recipe uses round-to-nearest-even, FP32 scales clamped to `1e-10`, int32
packing and BF16 stored scales. Chunking bounds RAM without changing per-group
operations. The archived upstream recipe is hashed but never executed: it
modifies files in place. The required derived SHA256 is
`b2e0854ed3be3141ed79f4204f7aa8e616da626d4662017117330490747c2036`.

Conversion dequantizes these stored embeddings to BF16; it does **not** recover
the original BF16 values. Skipping quantization would change the model. It
preserves the compressed head, draft and standalone quantization configuration.
No FC or QKV conversion is included. Compatibility still requires the reviewed
[patches](../patches/NOTES.md), including the narrowly qualified `extra_buffer`
Mamba correction, not `extra_buffer_lazy`.

## Required proof and honest limits

Require exit 0 from every command and `$WORK/validation.json`. Compare its
numerical and inventory fields to `embedding-validation.json`: **248,320 rows**,
**1,271,398,400 values**, identical dense tensor SHA256, actual tensor-byte counts,
source/output hashes and unchanged-tensor hashes. The proof's `/source` is the
container mount, not a host provenance path. The final verifier checks exact
artifact layout and all 17 target plus 2 draft file hashes against the retained
inventories. A serialization-only mismatch is still a failed byte reproduction.

Public HF checks on 2026-09-13 matched all 16 direct target files, both draft files
and raw shard 6: downloaded small non-LFS bytes or LFS SHA256/size metadata.
[public-options.json](public-options.json) records the evidence boundary. Large
upstream weights were **not downloaded** during that audit.

[shard-validation.json](shard-validation.json) records an older isolated
`--shard-only` run: 1,291,274,752 output bytes matched in 35.361 seconds. It did not
assemble source, convert the full target or publish anything. Its producer hash
is `69bbe0a11ac8eb90688081624bf436d2f4be6f1f70294723a1af7cd96917da47`,
which differs from the current quantization tool pinned in `preparation.sha256`.
Do not treat this historical run as execution proof for the current tool.
The only version found in `git log --all --follow` is
`589d4c898e26ea4413b93d562d714915a313db1b:prepare/quantize-embedding.py`;
its SHA256 is `bfe39cf0030b8d52b44bbf053d9a67134e73ffa906730149261020b05acf7494`,
not the recorded producer. The historical producer bytes were not recovered
from this repository history. The separate full current-tool reproduction below
provides new evidence; it does not relabel or replace the old result.

**Full CPU reproduction passed on 2026-09-13.**
[reproduction-validation.json](reproduction-validation.json) records the exact
producer tools before the later packed-verifier extension. Assembly authenticated
all 19 supplied inputs against public-origin hashes. Quantization reproduced
shard 6, conversion reproduced the full 17-file compact target, and the final
verifier authenticated that target plus both draft files. The entire generated
`validation.json` matched `embedding-validation.json` byte-for-byte. Inputs were
read-only; outputs stayed in a new private attempt and were not deployed.

The recorded durations are not performance comparisons: a separate GPU startup
trial could share CPU and disk. Historical proofs remain unchanged. This new
result closes the current-tool byte-reproduction gap, not runtime memory,
end-to-end quality or final-profile qualification. Every future reproduction
must still pass all exact hashes and proof checks.

## Explicit packed representation for qualification

The reproduced `source/` directory is also the exact packed-embedding target.
An approved isolated candidate can use it **without** the compact conversion.
The default verifier remains dense; select packed explicitly:

```sh
python3 "$REPO/prepare/verify-models.py" --target "$ATTEMPT/source" --draft "$ATTEMPT/draft" --representation packed
```

Packed verification selects only `source.sha256`, authenticated against the
original embedding proof's `source_hashes`. It requires the W8 group-128
embedding config and all three packed embedding keys on shard 6. Dense mode
selects only `artifact.sha256` and the dense embedding key. Neither mode detects
representations or falls back after a mismatch. Both require all 17 target and
2 draft hashes. The packed index's stale declared size is checked against its
exact historical proof field, not silently corrected.

The original all-row proof binds packed source to dense output. Packed embeddings
save exactly 1,251,532,784 tensor bytes (about 1.166 GiB), but this does not prove a
runtime memory fit or packed-kernel correctness. The serving candidate needs its
separate reviewed patch, explicit path/representation, and runtime qualification.
No original files or serving defaults are changed by this preparation option.
[representation-validation.json](representation-validation.json) records separate
full dense and packed verifier passes with the final extended verifier's SHA256.
Both branches authenticated all 17 target and 2 draft files. Scoped verifier
typing and formatting passed; Ruff retained 37 existing diagnostics versus 38
before this extension, with no newly introduced rule counts.

[packed-forward-validation.json](packed-forward-validation.json) records the
module-level complement: the runtime `PackedW8Embedding` module, loaded from the
packed tensors in `source/`, reproduced all 248,320 dense artifact rows
bit-exactly in two independent CPU runs; packed-flow and dense-reference
SHA256 are identical. The second run's exact container invocation is recorded.
It used the frozen twelve-patch stage12 image with no GPU and no network. This
is CPU unpacking-arithmetic evidence only: no GPU forward, no serving, and no
sampler or quality claim.
