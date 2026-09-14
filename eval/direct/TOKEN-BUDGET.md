# Direct smoke/quick token-budget diagnostic

**Do not run the frozen MRCR128k–256k quick tasks against a 262144-token service.** All eight already exceed that cap before any output is generated. No profiles or tasks were changed.

## Measured initial request budgets

Counts include the complete official prompt and the exact reproduced Qwen chat template. Budget total = templated input +8192 configured output tokens +2 engine-reserve tokens. The reserve is a diagnostic convention, not a universal engine guarantee.

| Profile / native task group | Entries | Templated input tokens | Budget total tokens |
|---|---:|---:|---:|
| smoke / MRCR32k–64k | 1 | 66824 | 75018 |
| quick / MRCR32k–64k | 8 | 66824 each | 75018 each |
| quick / MRCR128k–256k | 8 | 266695 each | 274889 each |
| smoke / GraphWalks bfs | 1 | 1354 | 9548 |
| smoke / GraphWalks parents | 1 | 1333 | 9527 |
| quick / GraphWalks bfs | 8 | 1341–1382 | 9535–9576 |
| quick / GraphWalks parents | 8 | 1324–1412 | 9518–9606 |

All 35 profile entries were counted (smoke tasks overlap quick). At **every** cap131072,163840,196608,229376,245760 and262144,27 entries fit this budget and the same 8 exceed it: `quick/direct-mrcr-128k-256k`, native selected indices/source rows0–7 inclusive. Each exceeds the final262144 budget by12745 tokens; input alone exceeds it by4551 tokens. There was no trimming, exclusion or substitution.

The frozen GraphWalks quick selection takes the first8 source-order tasks per operation. These are only about 1.3K–1.4K tokens despite the broad source-character cutoff. This smoke/quick result does not establish deeper GraphWalks quality or coverage. The existing full profile remains an unchanged750-task character-filtered subset of the unfiltered1150-task pool; it was not token-swept here.

## Exact tokenizer and native inputs

- Reproduced artifact: `/tmp/inference-full-reproduction-vz5z4cf0/attempt/conversion/artifact`.
- `tokenizer.json`, `tokenizer_config.json`, `chat_template.jinja`, `config.json`, `generation_config.json` and `processor_config.json` all match their expected SHA256 values in `prepare/artifact.sha256`. This diagnostic did not rehash model weight shards.
- Native image: `sha256:8a1eeb69ca67af0d54688cf11b46700448f15cde5395f013b0b5484244f1dfb7`. Transformers 5.12.1, tokenizers 0.22.2, native `Qwen2Tokenizer`.
- Each unchanged environment loaded its own smoke/quick configs and datasets through its existing isolated project. The exporter used native `vf.load_environment`, `get_eval_dataset`, system-prompt resolution/message normalization and GraphWalks’s first-turn `get_prompt_messages`. No task or scoring code was copied. MRCR serialized original-task prompts were checked against the exported messages, and original tasks had no extra system prompt or tools.
- Native exports were restricted to two CPU cores. The tokenizer ran with a 2-CPU Docker limit, no GPU, no network, read-only image/model mounts and private owned work/cache space. No dependency installation, tests, client construction, endpoint call, scoring or model execution occurred.

## Template and serving-path accounting

The native request has one user message, no task/Harness system message, and no tools. **The artifact template nevertheless injects a system message.** With `enable_thinking=true` and no effort override, its default is `xhigh`:

> Reasoning effort is set to xhigh. Please think carefully through the task, validate key assumptions, consider plausible alternatives, and prioritize correctness, consistency, and clarity in the final answer.

The template also adds the user delimiters and assistant generation prefix `<|im_start|>assistant\n<think>\n`. All are included. The measured template difference is 50–52 tokens, not merely an estimated role overhead. MRCR raw-user counts are 66772 and266643, versus templated 66824 and266695.

The exact image’s `serving_chat.py` uses the artifact Jinja template with `add_generation_prompt=true`, request template kwargs and no tools. This Qwen model is multimodal, but these inputs contain no media. Its text path decodes the rendered token IDs, then `TokenizerManager` tokenizes ordinary text and skips the multimodal processor for this non-MossVL/no-media case. Every one of 35 entries produced identical IDs through native `apply_chat_template(tokenize=true)`, render+encode, default/no-special encoding, decode/re-encode and the ordinary `tokenizer([text])` callable path. The tokenizer’s default encoding of the empty string has no special tokens.

These are exact local templated token counts with source-traced server preprocessing, **not observed endpoint token usage**. No live ServerArgs, TokenizerManager or serving process was constructed. Changed server defaults, template/tokenizer bytes, request system/tools or reasoning settings require a new count. Runtime capacity, completion success, truncation behavior and quality remain unqualified.

## Proof and next action

Machine-readable proof: `eval/direct/token-budget.json` and identical `/tmp/inference-direct-token-budget.json`. It binds source/config/dependency/tokenizer hashes and records every row, token-ID digest and cap result without publishing raw prompts or answers. Private diagnostic inputs/scripts remain under `/tmp/inference-direct-token-budget-fxflf8yp`.

Next: preserve the frozen profiles. Treat all eight current quick large-MRCR tasks as over-budget at every approved rung. Separately decide whether to approve the fitting smoke run; a new deeper token-fit profile needs separate frozen selection and unchanged official scoring. No additional endpoint approval is implied by this report.
