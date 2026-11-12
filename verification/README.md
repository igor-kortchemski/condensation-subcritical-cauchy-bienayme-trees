# Verification records

These records concern the current partial development under Lean 4.35.0 and
the pinned Mathlib revision. They do not certify whole-paper
coverage, source fidelity by themselves, or Palomar acceptance.

- `2026-11-11-official-comparator-final/`: the same official check on the final
  candidate `87dbd05` (export of `051c545`, Challenge docstrings revised, code
  unchanged), run 43078769747: passed.
- `2026-11-11-challenge-review.md`: independent review of the Challenge's
  docstrings; `2026-11-11-local-comparator-doc/`: local diagnostic after the
  docstring revision.
- `2026-11-11-official-comparator/`: the official sandboxed `lake comparator`
  with NanoDa and the Lean kernel, passed on Linux in GitHub Actions run
  43072119896 of the private repository, commit `ab42946` (export of `18e8a4e`):
  identity, source scan, build log, axiom audit and Comparator log.
- `2026-11-11-local-comparator/`: the local macOS diagnostic (not the official
  tool) of the same interface: statements and reachable constants match, only
  permitted axioms, `leanchecker` on the Solution export.
- `2026-11-11-leanchecker.txt`: full kernel replay, 169 project and 36 BGW
  modules, exit 0, commit `cf78f02`; `2026-11-11-leanchecker-changed.txt`: the
  four modules whose proofs were rewritten for the Challenge.
- `2026-11-11-freeze-rerecord.txt`: the five freeze records re-recorded for the
  new lakefile, with identical declaration and dependency hashes.

- `2026-11-01-integrated-tail-build.txt`, `2026-11-01-integrated-tail-axioms.txt`,
  `2026-11-01-integrated-tail-leanchecker.txt`: final verified checkpoint before
  the user requested a stop. Build passed without warnings, 3249 jobs. The
  audit passed for 1035 visible project and BGW declarations, only permitted
  axioms. Focused replay passed with exit zero for SlowVariationBoundary,
  SlowVariationPrimitive, SlowVariationRounding, EquivalentTails,
  CenteringTailSeries and RefinedCentering. The earlier full replay is retained
  for the unchanged 42 project modules; the root only gained imports.
  The library contains 48 modules including its root. Drafts under
  `handover/drafts` are outside this evidence and outside the import tree.
- `2026-11-01-analytic-windows-build.txt`, `2026-11-01-analytic-windows-axioms.txt`,
  `2026-11-01-analytic-windows-leanchecker.txt`: measurable-analysis milestone.
  Integrated build passed without warnings, 3242 jobs. The audit passed for
  987 visible project and BGW declarations with only permitted axioms. Full
  project-namespace replay passed with exit zero for all 42 project modules,
  including the root. Exact command:
  `LEAN_NUM_THREADS=2 lake env leanchecker -v SubcriticalCauchy`.
  The unchanged 28 tracked BGW modules retain their earlier replay evidence.
- `2026-11-01-coding-scale-build.txt`, `2026-11-01-coding-scale-axioms.txt`,
  `2026-11-01-coding-scale-leanchecker.txt`: degree/correction/scaling milestone.
  Build passed without warnings, 3195 jobs. The expanded transitive axiom audit
  passed for 887 visible project and BGW declarations, using only the three
  permitted axioms. Kernel replay passed with exit zero for all 31 project
  modules, including the root. Reproduce with
  `LEAN_NUM_THREADS=2 lake env leanchecker -v SubcriticalCauchy`.
  The unchanged 28 tracked BGW modules retain the earlier full-replay evidence.
- `2026-11-01-forest-log-build.txt`, `2026-11-01-forest-log-axioms.txt`,
  `2026-11-01-forest-log-leanchecker.txt`: logarithmic-forest milestone. Build
  passed without warnings, 3174 jobs; expanded axiom audit passed, 617 declarations.
  Focused kernel replay passed with exit zero for exactly
  `SubcriticalCauchy.LogarithmicThreshold` and `SubcriticalCauchy.BienaymeForestLog`.
  Reproduce it with `LEAN_NUM_THREADS=2 lake env leanchecker -v SubcriticalCauchy.LogarithmicThreshold SubcriticalCauchy.BienaymeForestLog`.
- `2026-11-01-survival-forest-build.txt`, `2026-11-01-survival-forest-axioms.txt`,
  `2026-11-01-survival-forest-leanchecker.txt`: earlier survival/forest milestone
  checks, all passed. Build: 3172 jobs without warnings. Axiom audit: 596 visible
  project and vendored BGW declarations, with only the three permitted axioms.
  Kernel replay: exit zero, all 14 project and 28 tracked BGW modules included.
  The same eight cached BGW extras were also replayed, adding no source coverage.
  See FORMALIZATION_REPORT.md for scope and verification limitations.
- `2026-11-01-build.txt`: earlier BGW milestone build of both libraries, successful.
- `2026-11-01-axioms.txt`: earlier BGW milestone audit of both namespaces.
- `2026-11-01-leanchecker.txt`: successful earlier BGW milestone replay, exit code zero.
  All 12 project and 28 tracked BGW modules were checked. The namespace scan
  additionally found eight cached BGW modules outside the shipped snapshot;
  these do not add source coverage to this development.
- `build.txt`: historical integrated build output, 29 October 2026.
- `axioms.txt`: historical audit output, 29 October 2026.
- `leanchecker.txt`: historical successful replay of nine project modules, exit code
  zero, using `LEAN_NUM_THREADS=2 lake env leanchecker -v SubcriticalCauchy`.

The full namespace replay command can add BGW to check that vendored source
again. The latest milestone replays the entire project namespace and retains
the earlier full replay for the unchanged BGW sources. It still uses
the imported Mathlib environments;
it is not fresh replay of all dependency declarations or NanoDa verification.

The namespace audit checks transitive axiom use. Its internal declaration counts
are not counts of theorems in the paper. Kernel replay checks project modules
against their imported environments; it is not an independent NanoDa check or
a fresh replay of all Mathlib dependencies.

Regenerate affected evidence after changes to proof code, definitions, imports,
dependencies, toolchain, or build configuration. GitHub CI and Palomar checks
have not run for a public candidate.
