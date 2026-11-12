# Coverage reconciliation — 11 November 2026

Two independent Sonnet auditors went through the paper line by line, against the
inventory ([PAPER_INVENTORY.md](PAPER_INVENTORY.md)), the report and the Lean
sources. Neither wrote any of the code. Auditor A took lines 1–298 (abstract,
Introduction, Section 2). Auditor B took lines 299–688 (Sections 3–4).

Each auditor checked that every Lean name exists. Its axioms were checked against
`verification/2026-11-11-all-axioms.txt` or a fresh `#print axioms`: 43 names by
A, all the remaining names by B, and `bridge_degree_permutation_event` by the
coordinator. All use only `propext`, `Classical.choice` and `Quot.sound`;
`isTreeExcursion_iff_existsUnique` uses only `propext` and `Quot.sound`. For each
proved claim the auditors also read the statement.

**Result.** No claim of the paper is open or missing. Every claim falls in one of
four groups:

- proved as stated;
- proved in a corrected form, approved by the author and listed in
  [MANUSCRIPT_RECOMMENDATIONS.md](../MANUSCRIPT_RECOMMENDATIONS.md);
- refuted as stated, with a Lean counterexample;
- a citation, or a historical or naming remark. B1–B5 are external citations by
  the author's decision of 10 November 2026.

Freeze evidence: [all five records PASS](../verification/2026-11-11-freeze-checks-labelled.txt).

## Status by item

| Item (inventory) | TeX | Status | Lean (main names) |
| --- | --- | --- | --- |
| Hypothesis (eq:H_loc_mu), D1 | 116–120 | setup; measurable $L$ (author's convention, 1 Nov) | `IsMeasurableSubcriticalCauchyOffspring`, `IsSubcriticalCauchyOffspring` |
| Theorem 1.1 (i)–(iii), M1–M5 | 149–163 | proved (frozen, approved 10 Nov) | `main_maxDegree_condensation`, `main_secondMaxDegree_negligible`, `main_maxDegreeDepth_geometric`, `main_height_log`, `main_height_tight_iff` |
| U1.1 unique macroscopic vertex | 165–166 | proved | `unnumbered_unique_macroscopic_degree` |
| U1.2 stable domain, index one | 141 | proved via corrected (2.4) | `exists_scaling`, `paper_stable_limit` |
| U1.3 log-moments; the example $c/((\log n)^{1+\beta}n^2)$ | 182 | proved (example existential in the constant) | `summable_logMoment_of_one_lt_alpha`, `exists_logMoment_divergent` |
| B1–B5 history and background | 170–184 | citation (author, 10 Nov) | — |
| U2.1, D2 law $\mathbb P_\mu(\tau)=\prod\mu_{k_u}$; conditioned tree | 196–201 | proved | `bienaymeLaw_toLocallyFinite`, `conditioned` |
| Proposition 2.1 (Kennedy) | 208–211 | proved (every $n$) | `conditioned_tilt_of_pos`, `conditioned_tilt` |
| U2.2 tilted PGF and mean | 206, 213 | proved | `TiltingFacts.exponential_tilt_U22` |
| U2.3 boundary criterion | 213 | refuted (R1) | `TiltingCounterexample.critical_equivalence_boundary_counterexample` |
| U2.4 supercritical ⇒ critical; $\alpha<1$ ⇒ infinite mean | 175, 213, 223 | refuted as stated (R2); proved with $\mu_0>0$; infinite mean proved for $0\le\alpha<1$ | `supercritical_equivalence_counterexample`, `supercritical_equivalent_critical_U24`, `infinite_first_moment_tsum_of_tail_alpha_lt_one`, `infinite_first_moment_tsum_of_tail_lt_one_U25` |
| U2.5 five-case classification | 215–223 | proved corrected (R13, $\nu_0>0$; approved 11 Nov) | `paper_heavyTail_classification` |
| U2.6 coding, excursion and Vervaat conditioning | 228 | proved | `isTreeExcursion_iff_existsUnique`, `iid_walkFirstPassage_eq_sizeEvent`, `map_cond_excursionWords_decodeTree`, `map_cond_countBridges_vervaatTree` |
| U2.7 degrees are bridge jumps; $\mathbb E X=m-1$ | 228–231, 369 | proved | `bridge_degree_permutation_event`, `integral_offspringIncrement` |
| U2.8 scales; (2.4); law of $\mathcal C_1$; regular variation of $a_n,b_n$ | 233–240 | proved; (2.4) corrected (R9, approved 10 Nov) | `exists_scaling`, `paper_stable_limit`, `exists_cauchyOneLaw`, `unnumbered_scaling_regularly_varying` |
| Lemma 2.2 (i)–(iii), U2.9 | 253–274 | proved ((i)–(ii) existential in the witness $L$; every-$L$ forms separate) | `paper_integratedTail_properties`, `paper_centering_asymptotics`, `scaling_div_nat_tendsto_zero`, `incrementTail_div_tendsto_one` |
| U2.10 (2.5) and no limit for mean-centred sums | 277–281 | proved | `unnumbered_walk_drift_ratio`, `unnumbered_meanCenteredWalk_not_convergent_in_distribution` |
| Example 2.3 (i)–(iii) | 286–295 | proved | `example23_i_*`, `example23_ii_*`, `example23_iii_*` |
| Theorem 3.1 | 312–319 | proved by two routes: endpoint D12 and the paper's own D18 | `paper_deleted_maximum_tvDist`, `paper_route_deleted_maximum_tvDist` |
| U3.1–U3.4, X4, X5 (paper's proof) | 322–359 | proved (R8 window; AL in the form of its proof, R11; Berger specialised, R12) | `al_criterion`, `berger_local_limit`, `paper_eq26`, `paper_eq33` |
| U4.1–U4.2 TV transfers, Fréchet limit | 369–377 | proved | `conditioned_maxDegree_tvDist`, `incrementMaximum_le_tendsto_frechet` |
| Corollary 4.1 | 380–386 | proved corrected (R9, approved 10 Nov) | `paper_maxDegree_fluctuations` |
| O1 local limit (open direction) | 388 | not a claim | — |
| U4.3 transfers from Kortchemski (2013) | 378, 402 | covered by replacement (D13–D15) | M3, Propositions 4.2–4.3 |
| U4.4, X7 HSVJ criterion | 390 | proved (D11; approved 10 Nov) | `survival_div_mean_pow_tendsto_pos_iff`, `survival_div_mean_pow_tendsto_zero` |
| Propositions 4.2, 4.3 (i)–(ii) | 397–432 | proved (D14, D15; `leaf` padding approved) | `paper_attached_forest_tvDist`, `paper_height_lower`, `paper_height_upper` |
| Lemma 4.4 (i)–(ii), U4.6–U4.7 | 438–473 | proved ((i) approved 10 Nov; typos R4, R5) | `paper_survival_correction_lemma`, `survival_geometric_bounds` |
| Proof of Theorem 1.1(iii), U4.8–U4.10 | 476–500 | proved (D16) | `main_height_log`, `main_height_tight_iff` |
| Proposition 4.5 (i)–(ii), U4.11–U4.12 | 502–537 | proved; (ii) corrected (R10, approved 10 Nov) | `paper_height_second_order_log`, `paper_height_second_order_pow` |

Claims outside the inventory:

- the always-tight centred height for $\alpha>1$ (line 182): a citation (B1);
- $Q_n\sim c\,m^n$ holds for $\alpha>1$ and fails for $\alpha=1$ (line 187): proved by combining the HSVJ criterion with U1.3;
- the scaling-limit comparisons (line 184): citations (B1, B4);
- "asymmetric Cauchy" (line 240): naming only;
- attributions at lines 303, 362, 388, 390: citations.

## Findings and their treatment

1. **Stale wording in the report**: "open" for U2.4, U2.10, the Fréchet claim and (2.6)/(3.3); "approval pending" for Lemma 4.4(i) and X7; the date of the obligations list.
   *Fixed* (11 Nov). Two module docstrings, `Centering.lean` and `BienaymeSurvival.lean`, were also corrected.
2. **X4 called "proved"** without qualification.
   *Fixed*: the report says it is proved in the form of its proof, without the existence of a threshold or $\Delta$-subexponentiality (D18, R11).
3. **Literal `eq:26` and `eq:ber`** are not separate statements.
   *Note added to D18*: they are covered by the centred `paper_eq26` and by the shifted form of `berger_local_limit`.
4. **The printed (2.4), Corollary 4.1 and Proposition 4.5(ii) are called false**, but no Lean statement refutes them. Only the corrected forms are proved, and Feller's (8.15) was not checked.
   *Open for the corrections stage*: a Lean refutation needs uniqueness of weak limits and, for Proposition 4.5(ii), an example law with $m\ne1/e$, since the printed and corrected coefficients agree at $m=1/e$.
   *Corrections stage (11 November 2026)*: listed as C3, C5 and C7 in the authors' list of corrections, with the uniqueness argument and numerics, audited; no Lean refutation, by the author's choice.
5. **Approvals.** Proposition 2.1, Lemma 2.2, Example 2.3, U1.x, the U2.3 and U2.4 counterexamples and the corrected U2.4 have independent statement audits, but no author approval record. Only the main results, Theorem 3.1, Propositions 4.2, 4.3 and 4.5, (2.4), Corollary 4.1, Lemma 4.4(i), X7, the paper-route statements and U2.5 were approved.
   *Recorded*; the author may approve the rest at the final verification.
6. **Name clash**: inventory D1–D6 (definitions) against report D1–D18 (routes).
   *Note added to the report.*
7. **Conventions.** The measurable convention is approved; M1–M5 under the literal ratio-only hypothesis are not stated. Lemma 2.2(i)–(ii) are existential in the witness. The example of U1.3 is existential in its constant. `leaf` padding is used in Proposition 4.2.
   *Recorded; all approved or harmless.*
8. **The inventory has no status column.**
   *A status note was added to its header*, pointing here; the inventory itself is unchanged.
