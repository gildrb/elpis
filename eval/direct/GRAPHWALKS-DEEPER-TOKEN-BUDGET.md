# Next native GraphWalks bucket: sampled token-budget rejection

**No deeper fitting profile is justified by this32-row diagnostic.** Keep all eleven existing frozen profiles and the35-row smoke/quick proof unchanged. No endpoint call or scoring occurred.

## Candidate inspection before tokenization

The unchanged native `prompt_chars_filter="262145-524288"`, applied separately to `problem_type="bfs"` and `"parents"`, selects100 rows each. Source `prompt_chars` ranges437425–437501 for bfs and437413–437488 for parents. Complete native prompt strings range437563–437639 and437484–437559 actual characters, respectively.

The next source-character interval524289–1048576 contains zero rows in either family. The following populated interval1048577–2097152 contains100 per family at about1.748M source characters. This is source metadata, not tokenizer evidence. No prompt was rewritten to fill the gap.

## Bounded native sample

Exactly the first16 native post-filter rows per operation were selected through `env.get_eval_dataset(n=16)` with shuffle disabled:32 additional rows total. All prompt loading/normalization and the verified Qwen tokenizer/template remain upstream. The native exact scorer was selected but never executed.

| Operation | Sampled / candidate pool | Templated input tokens | Input +8192 output +2 reserve |
|---|---:|---:|---:|
| bfs | 16 /100 | 357135–357905 | 365329–366099 |
| parents | 16 /100 | 357248–357962 | 365442–366156 |

Every sampled row exceeds every cap131072,163840,196608,229376,245760 and262144, even before output is added. None is in the requested200000–253950 templated-input-token band. The proof records every native selected index0–15 per family and all cap results. Native template tokenization and the server’s ordinary decoded-text callable path produced identical token IDs.

The168 unsampled candidate rows remain **untokenized and unqualified**. This sample does not prove that the entire200-row pool fails or fits. The previously frozen GraphWalks full profile is still its750-task source-character subset; no full token sweep was performed.

## Distinct proposal and decision

A separately named `graphwalks-next-native-char-bucket-probe16` could describe the precise native selection above, but it is an **over-budget diagnostic candidate**, not a fitting quality profile. Do not run it against the262144 objective. No runtime profile file was created and no existing profile was widened, trimmed or silently resampled. The frozen quick large-MRCR tasks remain recorded as266695 input/274889 budget tokens and oversized.

No new200K–253950-token profile can be recommended from the measured rows. Further token inspection needs separate bounded approval. A narrower native character interval may be inspected, but its fit must be measured rather than inferred from character size; no local task sampler, padding or prompt rewrite is justified.

## Provenance and limits

The tokenizer diagnostic used immutable image `sha256:8a1eeb69ca67af0d54688cf11b46700448f15cde5395f013b0b5484244f1dfb7`, two CPUs, no GPU and no network. Six tokenizer/config/template files again matched the reproduced artifact inventory. No dependency changes or tests were introduced. The full template-owned xhigh system instruction and assistant thinking prefix are counted.8192+2 is the same budget convention, not a guarantee of engine acceptance.

Proof: `eval/direct/graphwalks-deeper-token-budget.json`, identical to `/tmp/inference-graphwalks-deeper-token-budget.json`. Private native exports and diagnostic scripts: `/tmp/inference-graphwalks-deeper-budget-7d_275ed`.

Next: leave this candidate rejected for the sampled rows. Decide separately whether any further native-bucket token measurement is useful; do not launch an oversized quality run.
