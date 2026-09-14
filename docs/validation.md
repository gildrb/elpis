# Refactor validation ledger

Date: 2026-09-13. Build/source checks, hardware execution and capability scores
are different evidence. No complete native-context recipe is qualified.

| Check | Observed result | Boundary |
|---|---|---|
| Old chain → Git series | All 38 final files and all 10 intermediate stages identical | Packaging proof, not new kernel correctness |
| Wrong pin, dirty checkout, altered patch | Rejected before an acceptable build | No source reconstruction fallback |
| Unpatched upstream control | Exact clean commit, zero patches, checkout unchanged | Source control only; not model loading |
| Ordinary 3-patch Docker runtime | Built successfully; immutable image `sha256:b2c1b4fef1a39eb8bbcc3333c472b510e843e49f104c96f5bfc2c08b4c3d6d46` | Frozen trial image, not necessarily later edited Dockerfile |
| Experimental 10-patch Docker runtime | Built successfully; immutable image `sha256:494fe39c7746a911e87ed59f88ea2c2955f77f491fc46df1002b56202cc2a51b` | Before variable-capacity patch; not native-context qualification |
| Experimental 11-patch Docker runtime | Built `sha256:f26909d5c8e65ac5b928f3a5845668756e015eee3bc200d5ecd64f16956ae979`; all132 CPU admission/budget checks passed inside image | Native/eager six-rung admission, not GPU capacity |
| Zero-patch Docker runtime | Built `sha256:7ee96805a4efc95208ad942afa9ee1f2712fc265db1d261c63292c564d82be5b`; CPU help passed | No model-loading claim |
| FP8 hardware startup | Requested262144, effective pool68004; stopped before API readiness | No deep request or quality result; original service restored and authenticated |
| Full CPU artifact reproduction | [Preparation evidence](../prepare/REPRODUCE.md): exact17 source,17 dense and2 draft files; all-row proof byte-identical | Offline cached public inputs, no GPU; initial producer identity preserved |
| Final stage12 experimental image | `sha256:880b09a2cb697977eae8cbc3ec452a573d9c03b65bd38e2493ff66fc9820c0ea`;42 constructor checks and actual launcher boundary checks passed | Packed flag/load format/dtype bound; no GPU loader/capacity claim from CPU checks |
| Explicit dense/packed experimental image | `sha256:8a1eeb69ca67af0d54688cf11b46700448f15cde5395f013b0b5484244f1dfb7`; actual image verified17 target+2 draft files for each representation | CPU-only, read-only reproduced fixtures; no packed GPU startup or capacity claim |
| CPU model verification in ordinary image | 17 target + 2 draft files passed, 20.64 seconds | Existing installed bytes, not new public-input reconstruction |
| Official SGLang serving benchmark CLI | CPU help passed in frozen ordinary image | No throughput run; writable temporary/cache mounts required |
| SGLang CLI import/help | Ordinary and experimental passed without GPU/models/network | Does not resolve device-dependent configuration |
| Nix flake, Compose, shell checks | Passed for the frozen deployment snapshot | No host activation; Docker health is not automatic hang recovery |
| Official throughput fixture | [Pinned ShareGPT snapshot](../bench/throughput-fixture.json): full672837942-byte file SHA256-verified; eight exact-ID depth fixtures generated CPU-only in pinned image | Not sent HTTP payloads; no performance run |
| Direct candidate routing | `QWEN_EVAL_BASE_URL` override dry-ran against18021 (requests_sent0); invalid/other URLs fail closed with exit2; frozen config hashes unchanged | Loader routing only; no endpoint requests or scores |
| Direct token budgets | 35 frozen rows tokenized with exact artifact tokenizer/template: MRCR large needs274889 total (unusable at262144), smaller rows75018; deeper GraphWalks buckets measured separately | CPU budget facts only; 84+168 rows untokenized; no quality scores |
| Main evaluator smoke | Native AIME24 smoke dry-run exited0 in locked project environment | Configuration/provenance only; no model requests |
| Historical direct evaluators | All11 frozen loader configurations passed; native CLI help and isolated lint/type checks passed | Zero inference requests; bucket/character lengths are not Qwen token depths |
| Packed KVarN 0.94 GPU admission | [Valid packed load profile-rejected](../bench/results/packed-kvarn-094-admission.json): gate bound, no loader skip, 14.75/1.22 GB weights; KVarN profiled211328 against requested pool263168 | Strict startup refusal, not capacity; no readiness, deep request or quality result; 0.98 needs a separate window |
| Packed KVarN 0.98 GPU admission | [Pool cap passed, wiring failed](../bench/results/packed-kvarn-098-admission.json): pools allocated with 1.09 GB avail; AttributeError KVarNAttnBackend.token_to_kv_pool in HybridLinearAttnBackend | Source-level integration gap in the patch chain, not capacity; no readiness, deep request or quality result |
| Stage13 hybrid-attr fix image | `sha256:be7109dd…`; thirteen-patch series applies to upstream0bcd822; 9 CPU cases: real KVarN constructor and HybridLinear wrapper alias the three attributes, negative control reproduces the pre-fix AttributeError | Wiring proof only; subclassed stub pools, no tensors/GPU/serving; admission still requires the next GPU window |
| Stage13 0.98 window (GPU) | [Pool built, scheduler entered, false idle leak](../bench/results/packed-kvarn-098-admission-stage13.json): total=263168, available=263040, 128-token KVarN graph-dummy page unaccounted; killed at first idle tick ~1 s before readiness | Reservation is by design; failure datapoint only, no readiness/VRAM |
| Stage14 reserved-accounting fix image | `sha256:d69f861b…`; fourteen-patch series applies to upstream0bcd822; 22 CPU cases: real allocator reservation/clear/lifetime-free and real checker idle/busy paths, stock-allocator non-regression, pre-fix negative control | Accounting proof only; no tensors/GPU serving in the CPU check itself |
| Stage14 0.98 window (GPU) | [Readiness passed](../bench/results/packed-kvarn-098-admission-stage14.json): API ready in 80.3 s, idle invariants pass, 23441 MiB used / 686 MiB free / 25 W steady | Admission-only; no request served; throughput/quality unmeasured |
| Stage14 deep 262144 probe (GPU) | [Inconclusive: deadline](../bench/results/packed-kvarn-262144-deep-probe.json): 46,080 tokens in 1800 s, 15–27 tok/s declining, 100% util / 271 W median, no retractions | Prefill-time bound, not memory; no completed request, no quality evidence |
| All-row packed module forward | [CPU proof](../prepare/packed-forward-validation.json):248320/248320 rows bit-exact; identical packed-flow/dense-reference SHA256 in two runs (stage12 image, no GPU/network) | Unpacking arithmetic only; no GPU forward, serving, sampler or quality claim |
| Relative documentation links / Git whitespace | Passed during integration | Rerun after later edits |

The trial image's launch script hash is
`c58d34b5e0d9a4ea579e25115b21625148b60dbfb1108a18d1c0249078910b2a`.
Its Compose hash is
`37b8e0021c0f837c60564151aec2ca5fc82d5dced7b49e8d252c48e5c87c628d`.
The exact public source and patch order are in [patches](../patches/README.md).

Strict project checks remain enabled. The final locked Ruff run reports161 preparation findings (162 initially)
and the byte-preserved converter is not formatter-clean. Project `ty` reports
eleven unresolved imports: nine in preparation (torch, safetensors and
compressed-tensors are supplied by the separate pinned runtime image), and two
Verifiers imports in the isolated historical direct-evaluation inspector. The
inspector is checked separately inside its own pinned runtime. No rule
exclusions or type suppressions were added to hide these failures. Complete
repository lint/type success is not claimed.

See [qualification](qualification.md) for GPU results and remaining capacity,
cache, sampler, graph and capability gates. New experimental patches require
separate validation and a new image identity; they do not inherit this ledger.
