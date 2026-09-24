# Third-party source notices

Serving uses the ExLlamaV3 engine and its native DFlash2 extension as installed
in the authenticated base image recorded in `prepare/exl3-manifest.json`.
`patches/exl3/` holds explicit diffs against that installed engine, not copied
upstream files; the engine retains its upstream license.

The measurement methodology is informed by
https://github.com/syv-ai/qwen38-27b-rtx3090. Its vLLM performance measurements
are not measurements of this EXL3 deployment.

Model-quality evaluation uses external upstream Prime Envs environments.
Their pinned source references and setup are documented in `eval/README.md`.
Environment code and data retain their upstream licenses and usage conditions.
These notices do not change the licenses of model weights or other dependencies.
