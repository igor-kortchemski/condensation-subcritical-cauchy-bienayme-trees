# Condensation in subcritical Cauchy Bienaymé trees

[![Lean build and axiom audit](https://github.com/igor-kortchemski/condensation-subcritical-cauchy-bienayme-trees/actions/workflows/lean.yml/badge.svg)](https://github.com/igor-kortchemski/condensation-subcritical-cauchy-bienayme-trees/actions/workflows/lean.yml)
[![Comparator](https://github.com/igor-kortchemski/condensation-subcritical-cauchy-bienayme-trees/actions/workflows/comparator.yml/badge.svg)](https://github.com/igor-kortchemski/condensation-subcritical-cauchy-bienayme-trees/actions/workflows/comparator.yml)

Lean 4 and Mathlib formalization of *Condensation in subcritical Cauchy
Bienaymé trees* by Igor Kortchemski and Leonard Vetter
([arXiv:2503.07530v2](https://arxiv.org/abs/2503.07530v2)), published in
*Electron. Commun. Probab.* 30 (2025), paper no. 79,
[doi:10.1214/25-ECP726](https://doi.org/10.1214/25-ECP726).
**Every result of the paper is proved, four of them in corrected form, using
only the axioms `propext`, `Classical.choice` and `Quot.sound`, with no `sorry`
outside [Challenge.lean](Challenge.lean).**
Links: [statements](Challenge.lean) ·
[correspondence record](FORMALIZATION_REPORT.md) ·
[verification](verification/README.md) ·
[erratum](erratum-ECP2025.pdf).

## Main results

Let $\mathcal T_n$ be a Bienaymé tree conditioned to have $n$ vertices. Its
offspring law $\mu$ is subcritical with mean $m<1$ and $\mu_n\sim L(n)/n^2$, for
a slowly varying function $L$
([`IsMeasurableSubcriticalCauchyOffspring`](SubcriticalCauchy/MeasurableHypothesis.lean)).

| Paper | Lean | Statement |
| --- | --- | --- |
| Theorem 1.1 (i) | [`main_maxDegree_condensation`, `main_secondMaxDegree_negligible`](SubcriticalCauchy/MainTheorems.lean) | $\Delta(\mathcal T_n)/n\to1-m$ and the second largest degree is $o(n)$, in probability |
| Theorem 1.1 (ii) | [`main_maxDegreeDepth_geometric`](SubcriticalCauchy/MainTheorems.lean) | the height of the vertex of maximal degree converges to a geometric law: $\mathbb P(\cdot=j)\to(1-m)m^j$ |
| Theorem 1.1 (iii) | [`main_height_log`, `main_height_tight_iff`](SubcriticalCauchy/MainTheorems.lean) | $\mathsf H(\mathcal T_n)/\log n\to1/\log(1/m)$; $\mathsf H(\mathcal T_n)-\log n/\log(1/m)$ is tight iff $\sum_k k\log k\,\mu_k<\infty$ |
| Theorem 3.1 | [`paper_deleted_maximum_tvDist`](SubcriticalCauchy/Theorem31.lean), [`paper_route_deleted_maximum_tvDist`](SubcriticalCauchy/PaperRoute/Statements.lean) | once the largest jump is removed, the bridge increments are close in total variation to i.i.d. ones (two proofs) |
| (2.2), corrected | [`paper_stable_limit`](SubcriticalCauchy/Corollary41.lean) | $(X_1+\cdots+X_n-b_n)/a_n\to\mathcal C_1+1-\gamma_E$ in distribution |
| Corollary 4.1, corrected | [`paper_maxDegree_fluctuations`](SubcriticalCauchy/Corollary41.lean) | $(\Delta(\mathcal T_n)+b_n)/a_n\to-\mathcal C_1-(1-\gamma_E)$ in distribution |
| Propositions 4.2, 4.3 | [`paper_attached_forest_tvDist`, `paper_height_lower`, `paper_height_upper`](SubcriticalCauchy/Propositions42_43.lean) | the subtrees on the vertex of maximal degree are close to an i.i.d. forest; height thresholds from $nQ_{h_n}$ |
| Proposition 4.5, (ii) corrected | [`paper_height_second_order_log`, `paper_height_second_order_pow`](SubcriticalCauchy/Proposition45.lean) | second-order term of the height when $L(n)\sim c/\log(n)^{1+\beta}$ |
| Section 2.2, corrected | [`paper_heavyTail_classification`](SubcriticalCauchy/Classification.lean) | the five-case classification of heavy-tailed laws, for $\nu_0>0$ |

The equation numbers are those of the journal version; display (2.2) is
numbered (2.4) in arXiv v2. Slow variation is taken with $L$ Lebesgue
measurable, the authors' convention for the main statements. The corrected
statements change the centring constant of (2.2) and Corollary 4.1 by
$1-\gamma_E$, where $\gamma_E$ is Euler's constant, change a power of
$\log(1/m)$ in Proposition 4.5(ii), and add the hypothesis $\nu_0>0$ to the
classification; the unqualified claims refuted by Lean counterexamples are
listed in [MANUSCRIPT_RECOMMENDATIONS.md](MANUSCRIPT_RECOMMENDATIONS.md). The
[erratum](erratum-ECP2025.pdf) gives every correction with its location in the
journal version. The
results that the paper cites from Armendáriz–Loulakis and Berger are proved
here in the form its proof uses; the historical and background citations of
Section 1 are not formalized. The full correspondence, including every
unnumbered claim, is in the [correspondence record](FORMALIZATION_REPORT.md)
and the [coverage reconciliation](docs/COVERAGE_RECONCILIATION.md).

## Where to start

- [Challenge.lean](Challenge.lean): the 20 compared statements and the
  definitions they use, in one file that depends only on Mathlib.
- [SubcriticalCauchy/MainTheorems.lean](SubcriticalCauchy/MainTheorems.lean):
  Theorem 1.1.
- [SubcriticalCauchy/PaperRoute/Statements.lean](SubcriticalCauchy/PaperRoute/Statements.lean):
  the paper's own proof of Theorem 3.1, through the Armendáriz–Loulakis
  criterion and Berger's local limit theorem.
- [SubcriticalCauchy/MeasurableHypothesis.lean](SubcriticalCauchy/MeasurableHypothesis.lean)
  and [SubcriticalCauchy/AttachedSlots.lean](SubcriticalCauchy/AttachedSlots.lean):
  the hypothesis on $\mu$ and the attached forest.
- [Vendor/BGW](Vendor/BGW/README.md): plane trees and the Bienaymé law,
  from the [Bienaymé–Galton–Watson trees](https://github.com/igor-kortchemski/Bienayme-Galton-Watson-Trees)
  formalization.

## Verify

The project pins Lean 4.35.0 and Mathlib v4.35.0; the exact dependencies are
in [lake-manifest.json](lake-manifest.json). Install Lean with
[the official guide](https://leanprover-community.github.io/install/project.html),
then run:

```bash
git clone https://github.com/igor-kortchemski/condensation-subcritical-cauchy-bienayme-trees.git
cd condensation-subcritical-cauchy-bienayme-trees
lake exe cache get
lake build
lake env lean scripts/AxiomAudit.lean
lake env leanchecker SubcriticalCauchy BGW
```

Do not run `lake update`. The build reports `sorry` only in `Challenge.lean`,
whose statements are placeholders for comparison. The axiom audit fails if any
project declaration depends on an axiom other than the three above, and
`leanchecker` replays the project modules in Lean's kernel. To browse the code,
open the cloned folder in VS Code with the Lean 4 extension.

The [build workflow](.github/workflows/lean.yml) runs these checks on every
push. The [Comparator workflow](.github/workflows/comparator.yml) runs
`lake comparator` on Linux with NanoDa and the Lean kernel: it checks that
[Solution.lean](Solution.lean) proves the statements of `Challenge.lean`,
with the same definitions, using only the permitted axioms
([comparator.json](comparator.json)). Its last recorded pass, on 11 November
2026, is in [verification/](verification/README.md).

## How it was made

The formalization was produced with AI agents: Codex, then Claude Code
(Claude Opus 5.5) as coordinator, with Lean written mainly by Kimi K3.1 Pro
and GPT-6.1 Sol, research by GPT-6 Astra, and independent statement and
coverage audits by Claude Sonnet 5.5 and GPT-6.1 Sol. Igor Kortchemski, an
author of the paper, checked the main Lean statements against the paper before
they were proved. The
Lean kernel checks the proofs; no human has reviewed them line by line.

## License and citation

The Lean code is licensed under [Apache-2.0](LICENSE), as is the vendored
[BGW snapshot](Vendor/BGW/LICENSE), whose notices are preserved. The license
does not cover the paper. Maintainer: Igor Kortchemski. To cite the
mathematics, cite the paper; to cite this formalization, see
[CITATION.cff](CITATION.cff). Report problems in the
[issue tracker](https://github.com/igor-kortchemski/condensation-subcritical-cauchy-bienayme-trees/issues).
