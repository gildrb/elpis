# Direct-context upstream evaluations

Run the model-free loader check first:

```sh
nix develop . --no-write-lock-file
eval/scripts/setup
eval/direct/setup
eval/scripts/data mrcr-v2
eval/scripts/data graphwalks
eval/direct/run smoke --dry-run
```

This separate lane uses the **last retained direct-prompt upstream environments**, not the current file-search tasksets in `eval/`. No task generator, prompt, answer parser or scorer is copied or patched. `run` calls the upstream `vf-eval` CLI; `--dry-run` calls its native TOML loader and `vf.load_environment`, then inspects the native selected dataset without constructing a client or sending requests.

## Exact compatibility boundary

| Input | Pin |
|---|---|
| Prime Envs | `a6f4ceedfd79cad4586064fb1c27f5ea5f4a10fd`, before removal of the retained direct environments |
| MRCR v2 | `environments/mrcr_v2`, package 0.1.1; Verifiers V1 `Taskset`/endpoint-backed `Harness`, one model turn |
| GraphWalks | `environments/graphwalks`, package 0.1.0; legacy `SingleTurnEnv`, one model turn |
| Verifiers | tag `v0.1.15.dev17`, commit`977e3fc4050893d938f68163ae0bd79a8672e8d7`; both upstream packages explicitly require at least this development version |
| Dependencies | Separate `mrcr/uv.lock` and `graphwalks/uv.lock`, Python 3.12, uv 0.12.1 from the repository Nix development shell |

Current Verifiers 0.3 taskset APIs are not substituted into these historical environments. Both isolated uv projects install unchanged source checkouts beneath ignored `.sources/`; neither affects `eval/.venv`. `setup` refuses dirty or wrong-revision existing checkouts. `--locked` prevents silent dependency re-resolution. Enter the Nix shell for native libraries; inherited `PYTHONPATH`/`PYTHONHOME` are removed to avoid mixing Python 3.13 with these Python 3.12 projects.

The native historical CLI uses `save_to_hf_hub=false`, not modern `--no-push`. There is no paid judge or sandbox. MRCR gets its complete official `queries` field, including transcript and few-shot content, as one user message. GraphWalks gets its full graph prompt as one user message. No retrieval tools or context-file search replaces those prompts.

## Frozen profiles

Profiles live in separate checked-in TOML files. They are not generated or widened at runtime.

| Profile | MRCR 8-needle tasks | Complementary GraphWalks tasks |
|---|---|---|
| smoke | First 1 from source bucket 32k–64k; one rollout | First 1 BFS and first 1 parents with `prompt_chars<=65536`; one rollout each |
| quick | First 8 from each source bucket 32k–64k and128k–256k; one rollout | First 8 BFS and first 8 parents with `prompt_chars<=262144`; one rollout each |
| full | Every task in each configured MRCR bucket; eight rollouts per task | Every BFS and parents task with `prompt_chars<=262144` (350 BFS +400 parents); one rollout |

Selection is upstream, with shuffle disabled and seed0 fixed. `num_examples=-1` means all native post-filter examples; there is no local sampler. MRCR source files contain85 and141 tasks, so its full profile alone schedules1808 long-context rollouts. That is expensive; run a single environment family when needed. GraphWalks full means the complete **configured character-bounded subset**, not all 1150 source tasks or the 1M-token track.

All profiles use model `qwen3.8-27b`, local URL `http://127.0.0.1:18020/v1`, C1, temperature0.6, top-p0.95, top-k20, min-p0, frequency/presence penalties0, repetition penalty1, thinking enabled and 8192 maximum output tokens. `independent_scoring=true` is explicit: this prevents legacy grouped-rollout scheduling from running all eight MRCR replicates concurrently despite C1. Each official task reward remains independent. The two GraphWalks operation families are reported separately. MRCR's upstream prefix-gated SequenceMatcher reward and GraphWalks' upstream exact node-set reward remain unchanged. Scores must not be merged into one synthetic intelligence metric.

**Source bucket labels and character counts are not Qwen token counts.** A32k–64k MRCR source bucket can have roughly300K characters. The GraphWalks filter uses the upstream `prompt_chars` column, which can differ from the full normalized prompt length. Its262144-character cutoff does not mean262144 model tokens. The pinned data uses lowercase `problem_type="bfs"`; the historical README’s uppercase example selects no rows, so profiles use the actual native data spelling. Count actual templated Qwen input tokens and reserve output/headroom before approving a run against a limited-context service. No wrapper trims, summarizes or silently removes oversized tasks. Server rejection/truncation remains an error or limitation to report. The serving objective is262144 total tokens; these profiles do not themselves prove that capacity.

### Qualifying a deeper, separate token-fit profile

The pinned unfiltered GraphWalks pool has1150 tasks. The current `full` profile stays fixed at its750-task character-filtered subset. It must not be silently widened or described as native262144-token quality.

To qualify deeper rows later, create a **new, separately named frozen profile**, not a runtime branch. Use the unchanged native loader and its `problem_type`/`prompt_chars_filter` arguments to define candidates. Measure each complete native prompt with the exact pinned target tokenizer and chat template. Reserve the configured output budget and serving headroom. Freeze the native filter, source row identities, measured input-token counts, tokenizer/template identities and explicit exclusions with reasons in that new profile's provenance. Recheck that every selected row fits the same declared budget.

Keep the official normalization and scoring unchanged. If the native filters cannot express a fitting subset, report that limitation rather than introduce a local task sampler or patched environment. Qualify the new profile only after an approved run succeeds without truncation. Report actual templated token ranges and coverage out of1150 separately from the existing750-task result; different populations are not interchangeable scores.

## Data and execution

The existing `eval/datasets.lock` authenticates unchanged MRCR CSV assets by GCS generation, size and SHA256, and GraphWalks parquet files by HF commit and hashes. `run` invokes `eval/scripts/data --check` before loading either family. It does not download data. Acquisition through `eval/scripts/data` requires the main eval setup because that helper owns the pinned Hub downloader; this is a data-preparation dependency, not a mixed Verifiers runtime.

Each invocation creates a private fresh `.runs/PROFILE.XXXXXXXX/`. Its working directory contains symlinks to verified raw datasets; GraphWalks' hardcoded `openai/graphwalks` resolves as that local path through the official datasets library. HF network access is disabled and the derived Arrow cache is fresh. No user/shared HF cache or source file is rewritten.

After endpoint approval only:

```sh
export QWEN_API_KEY_FILE=/absolute/path/to/private/api-key
export QWEN_RECIPE_ID=verified-serving-image-and-recipe-identity
export QWEN_EVAL_ALLOW_REQUESTS=1
eval/direct/run smoke
eval/direct/run quick mrcr
eval/direct/run full graphwalks
```

`run` validates the key's owner, regular-file status, private 0400/0600 permissions, length and printable non-whitespace bytes. The key is passed through `QWEN_API_KEY`, never a CLI argument or TOML secret. It does not start, replace or configure a serving process. Missing approval fails before a client is invoked. Remove `QWEN_EVAL_ALLOW_REQUESTS` after the approved run.

Native `results.jsonl` and `metadata.json` remain authoritative under each run's `work/results/`. Provenance includes source lock, dataset lock, both dependency locks, frozen configs and the supplied running-deployment identity (otherwise explicitly unverified). Do not publish raw traces by default: they contain full long prompts and model output. Inspect operational errors, token usage, truncations, exact effective counts and per-task rewards before comparing runs. A zero task reward is not the same as a failed API request.

## Validation scope

Dependency resolution, native CLI help and real-data native loaders can be validated without a GPU or key. These checks establish historical API compatibility and direct-prompt loading only. They do not establish successful remote inference, full-window fit, score parity, sampling correctness or runtime performance. No server requests were made while implementing this lane. Persistent CPU validation evidence is recorded in `validation.json`.
