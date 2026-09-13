# Diagnose incorrect or ungrounded output

Keep a private copy of the failing request before changing the server. Do not
publish API keys, private conversations, tool results, seeds or answers.

1. **Check completion first.** Record `finish_reason`, requested output budget,
   and reported token usage. A `length` result is incomplete, not a successful
   answer. More output budget can help, but it does not guarantee correctness.
2. **Check what the model received.** Preserve the exact messages actually sent,
   including relevant tool results. Compare these with the client history.
   Missing facts can come from trimming or compaction; coherent unsupported
   claims alone do not establish either compaction or KV-cache corruption.
3. **Separate measurements.** Use the fresh reasoning suite for problem-solving,
   the synthetic conversation diagnostic for controlled state/evidence tracking,
   and the salted cache probe for its narrow numerical consistency check.
   A pass in one is not proof of the others. The fixed-summary arm does not run
   a client's real compactor.
4. **Keep comparisons controlled.** Record model/runtime identities, source and
   lock hashes, request settings, cache state and shared load. Use strict replay
   for unchanged settings; use explicit bank import for declared model or budget
   changes. Never relabel a post-hoc comparison as fresh held-out evaluation.
5. **Change one cause at a time.** Keep the working deployment and rollback path.
   Do not raise context beyond measured allocation, silently change precision,
   or globally flush another client's cache to obtain a passing result.

See [benchmark instructions](benchmarks.md) and [measured results and limits](qualification.md).
No finite benchmark establishes that a model will never produce an incorrect
answer. Runtime recovery and answer correctness require separate evidence.
