# Upper current GraphWalks bucket: bounded fitting token sample

**The deepest measured fitting GraphWalks sample here is about179K input tokens, not262144.** All16 measured rows fit the196608 budget rung under input+8192output+2reserve. This is a local token-budget result, not runtime or quality qualification.

The unchanged native filter `prompt_chars_filter="131073-262144"` selects50 `bfs` and50 `parents` tasks, already inside the original full profile. Inspection preceded tokenization. Source character ranges are219425–219451 and219413–219438; actual native prompt strings are219563–219589 and219484–219509 characters. Characters are not tokens.

Exactly the first8 native post-filter rows per operation were measured using `env.get_eval_dataset(n=8)`, shuffle disabled and seed0. No score was computed or used to choose tasks. No task prompt or scorer was copied or changed.

| Operation | Measured / source-filter pool | Templated input tokens | Input +8192 output +2 reserve |
|---|---:|---:|---:|
| bfs | 8 /50 | 178769–179103 | 186963–187297 |
| parents | 8 /50 | 178672–179016 | 186866–187210 |

All16 sampled native indices0–7 per family exceed131072 and163840, and fit196608,229376,245760 and262144 under this budget convention. The84 unsampled rows remain untokenized and unqualified. None of the sampled inputs reaches200000 tokens; do not relabel this as200K–253950-token coverage or extrapolate full-population fit.

The exact reproduced tokenizer/template and image8a1eeb69 were reused and authenticated. Counts include the template-owned xhigh system instruction and assistant thinking prefix. Native template IDs matched the ordinary server text-tokenizer path for every measured row. Execution used at most two CPUs, no GPU and no network. No dependencies, test files, scoring, endpoint requests or existing runtime profiles changed.

The previous35-row smoke/quick proof and32-row oversized next-bucket proof are preserved and hashed in this result. Large-MRCR remains266695 input/274889 total; the next GraphWalks bucket’s32 sampled rows remain357135–357962 input tokens. Nothing was trimmed or replaced.

Proof: `eval/direct/graphwalks-upper-current-token-budget.json` and identical `/tmp/inference-graphwalks-upper-current-token-budget.json`. Private native diagnostic scripts and prompts remain under `/tmp/inference-graphwalks-upper-current-budget-79z430zl`.

Next: a separately frozen quality probe could explicitly use this native bucket and the first8 rows per operation, with its measured~179K depth and16-row scope. That would not prove all100 rows fit, and it still needs approval and the verified candidate endpoint. No new profile was created here.
