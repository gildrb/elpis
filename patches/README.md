# Runtime patches

The complete source chain is uploaded here. It contains **eight patch files covering 38 upstream files**.

| Stage | Patch files | Scope |
|---|---|---|
| Temporary baseline | [packed head](packed-head-predicate.patch), [draft FC](quant-aware-fc.patch), [Mamba cache](mamba-cache-prefix.patch) | 3 files |
| Packed embeddings | [model](qualification/qwen3_5.patch), [embedding layer](qualification/packed_w8_embedding.patch), [multimodal handling](qualification/mm_utils.patch) | 3 files |
| KVarN | [KVarN patch](qualification/kvarn-candidate.patch) | 25 files |
| Sampling repairs | [sampler checkpoint](qualification/sampler-checkpoint2.patch) | 9 files |

Stages overlap in the DFlash worker: the final union is 38, not 40.
See the [complete manifest](qualification/manifest.json), [source provenance](qualification/source-evidence.json), and [packaging guide](../docs/patches.md).

Only the baseline is wired into default serving. The complete candidate is build-only and is **not GPU-qualified or activated**.

Benchmark reports are in [bench/results](../bench/results/README.md).
