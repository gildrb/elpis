# Diagnose incorrect or ungrounded output

Keep a private copy of the failing request before changing the server. Do not
publish API keys, private conversations, tool results or evaluation answers.

1. **Check completion first.** Record `finish_reason`, requested output budget,
   and reported token usage. A `length` result is incomplete, not a successful
   answer. More output budget can help, but it does not guarantee correctness.
2. **Check what the model received.** Preserve the exact messages actually sent,
   including relevant tool results. Compare these with the client history.
   Missing facts can come from trimming or compaction; coherent unsupported
   claims alone do not establish either compaction or KV-cache corruption.
3. **Separate measurements.** Use upstream Prime Envs evaluation for model quality
   and the EXL3 benchmark lane for throughput. A pass in one is not proof of the
   other or of client compaction correctness.
4. **Keep comparisons controlled.** Record model/runtime identities, source and
   lock hashes, request settings, cache state and shared load. Follow the upstream environment protocol
   for controlled comparisons. Record model or budget changes explicitly; do not
   present tuning observations as independent evaluation.
5. **Change one cause at a time.** Keep the working deployment and rollback path.
   Do not raise context beyond measured allocation, silently change precision,
   or globally flush another client's cache to obtain a passing result.

See [benchmark instructions](benchmarks.md) and [capability evaluation](../eval/README.md).
No finite benchmark establishes that a model will never produce an incorrect
answer. Runtime recovery and answer correctness require separate evidence.
