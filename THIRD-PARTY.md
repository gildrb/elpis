# Third-party source notices

`patches/` contains explicit diffs against the pinned public SGLang commit,
not copied upstream source files. Patch context and additions retain applicable
source notices. The SGLang Apache-2.0 license is included as
`patches/LICENSE.sglang`. See `patches/README.md` for provenance and ordering.

`prepare/upstream-quant-embed.py.txt` preserves the upstream preparation recipe
from `syv-ai/qwen38-27b-rtx3090` at the revision and hash recorded in
`prepare/source-provenance.json`. Its Apache-2.0 license is included as
`prepare/LICENSE.upstream`. The local offline preparation scripts are separate
implementations; the archived recipe is not executed.

The serving/package layout is informed by
https://github.com/syv-ai/qwen38-27b-rtx3090. Its vLLM performance measurements
are not measurements of this SGLang implementation.

Model-quality evaluation uses external upstream Prime Envs environments.
Their pinned source references and setup are documented in `eval/README.md`.
Environment code and data retain their upstream licenses and usage conditions.
These notices do not change the licenses of model weights or other dependencies.
