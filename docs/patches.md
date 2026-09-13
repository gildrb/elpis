# Upstream pin and local patch policy

The engine is public upstream SGLang plus an ordered Git patch series.
[The patch directory](../patches/README.md) owns the exact base commit, order,
SHA256s, classifications and application commands. There is no second upstream
source tree, custom unified-diff parser or retained archive of original files.

## Reproduction boundary

Start from a clean checkout of the exact public commit. Verify the selected
patch hashes and apply with standard Git tooling. Build inside the digest-pinned
runtime image. Record the resulting image digest with the recipe revision and
model artifact hashes. Do not treat an image tag or local Docker image name as
an immutable result identity.

Patch hashes define source changes; they do not establish GPU correctness.
Migration equivalence to old source bytes only proves packaging fidelity. It
cannot promote an old experiment to the new default.

## Acceptance and removal

Every patch needs a base commit, purpose, subsystem, class, measured benefit,
correctness risk, validation and upstream issue/PR if one exists. Use explicit
“unmeasured” or “not found” where appropriate. A compatibility patch may have
startup/loader evidence instead of a speed delta, but broad capability still
needs independent qualification.

Production/default patches require evidence. Experimental series are opt-in;
including a patch in the repository or Docker build context must not select it.
KVarN, packed-weight changes and sampler repairs retain their existing evidence
and limits. Keep reference-vLLM results out of SGLang measurement columns.

When advancing upstream, inspect each affected subsystem for equivalent fixes.
Delete superseded patches, apply the remainder against the new pin, then rerun
[qualification](qualification.md). Rebase patches only with explicit review;
do not accept fuzzy application as correctness proof.

The desired patch layer gets smaller over time. A patch that is not specific
to SM86 should be structured as a plausible upstream change, with independent
correctness checks and no repository-specific paths or artifact assumptions.
