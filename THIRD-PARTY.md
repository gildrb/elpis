# Third-party source notices

`patches/base/` contains three unmodified SGLang source files from the exact
stock image identified in `patches/manifest.json`. The adjacent local patches
modify those files. Original source notices are retained; the SGLang Apache-2.0
license is included as `patches/LICENSE.sglang`.

`prepare/upstream-quant-embed.py.txt` preserves the upstream preparation recipe
from `syv-ai/qwen38-27b-rtx3090` at the revision and hash recorded in
`prepare/source-provenance.json`. Its Apache-2.0 license is included as
`prepare/LICENSE.upstream`. The local offline preparation scripts are separate
implementations; the archived recipe is not executed.

The serving/package layout is informed by
https://github.com/syv-ai/qwen38-27b-rtx3090. Its vLLM performance measurements
are not measurements of this SGLang implementation.

Reasoning Gym is a pinned external dependency. Its generator/scorer provenance
and the limits of fresh-instance evaluation are documented in `docs/benchmarks.md`.
These notices do not change the licenses of model weights or other dependencies.
