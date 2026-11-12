# BGW source snapshot

Copied on 1 November 2026 from the local BGW-formalization project, with the
user's authorization to reuse the random-tree formalization.
Upstream: [Bienaymé–Galton–Watson Trees](https://github.com/igor-kortchemski/Bienayme-Galton-Watson-Trees).
The checkout HEAD was d818312f05742621cf0c5b76fca124c93ff1572e, but the reused
probability modules were uncommitted. This is a snapshot of those working files,
not a claim that they occur in that commit or in a public release.

The snapshot includes the transitive BGW source dependencies of size conditioning,
normalization, generation laws, and the conditional bridge law. Copyright and
adaptation notices are retained. SOURCE_SHA256SUMS records the original copied
contents. GenerationLaw.lean then received local elaboration repairs, recorded
in its header; its mathematical statements are unchanged. The original checksum
for that file describes the source before those repairs. BGW.lean is a new
curated entry point. Apache-2.0 is retained in LICENSE. The project uses the
same Lean 4.35.0 and Mathlib revision as this development.

The local BGW Lean library points here. There is no dependency on another local
checkout, no dependency update, and no automatic synchronization of future edits.
Some BGW modules attribute earlier constructions to the declumping project;
those notices are preserved. Scope and downstream proof status remain in the
root FORMALIZATION_REPORT.md.
