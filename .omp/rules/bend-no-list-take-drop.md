---
name: bend-lang
description: "Bend best practices."
condition: "List\\.take\\(&2, Score, xs, Range\\.width\\(p\\)\\)|List\\.drop\\(&2, Score, xs, Range\\.width\\(p\\)\\)|def walk_tree\\(\\+depth: Nat, xs: List<&2, Score>\\)"
scope: ["tool:write(*.bend)", "tool:edit(*.bend)"]
---

Run `bend guide` to learn. Use `LAWS.bend` to keep important rules. Run `bend PROOF.bend` before committing. Parallelize the code whenever possible. No linked lists for array-shaped work. Bytes, words, buffers, indexed state, vectors, lookup tables, and serialized data need packed arrays, supported slices, or suitable fixed records. Use linked structures only when the algorithm actually needs their operations or semantics, and affine ownership forbids consuming one binding twice (List.take + List.drop both consume `xs`). For a fixed-size selector/fold over scores, build a balanced Data tree from indices (Leaf/Node constructors with parallel fork-join `l r = build(...) build(...)`), or use native arrays; keep list-based models out of the production representation and import graph. Each value must flow through exactly one consumption point.
Inspect the emitted C and optimized assembly for the hot path. Look for traversal, boxing, allocation, copying, helper transitions, generic arithmetic, failed inlining, large state transfers, register spills, and code size. Read the corresponding language source to understand why the compiler generated them. Bend does not automatically import external implementations, nor does it directly prove Python, TypeScript, Rust, or C code. If the original project is in another language:
select the logic and behavior that need to be formalized;
rewrite that behavior in Bend;
declare the properties of the formal version in LAWS.bend;
prove them in PROOF.bend;
explicitly state that the proof covers the Bend model.
Equivalence between the original implementation and the Bend model requires an additional demonstration of refinement or equivalence. Do not claim that the original code has been proven simply because the Bend rewrite passed the checker. Do not prefer an old version over the active toolchain. Resolve the executable with command -v bend and inspect its help with bend --help. Use that same resolved executable for documentation, checking, and compilation throughout the task. Query its version using the command advertised by its help. Current releases use bend version; do not assume --version is supported. Read its language guide and relevant library definitions using the advertised commands. Current releases provide bend guide and bend base; inspect specific library names when supported. Record the observed executable, version, and relevant capabilities. Never infer a version from this skill, an old transcript, or a different checkout. If the CLI or documentation is unavailable, report the missing prerequisite. Do not invent syntax, silently switch installations, or substitute a legacy compiler that cannot check the required laws.
