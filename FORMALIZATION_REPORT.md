# Formalization report

## Scope and status

The requested scope is every theorem, proposition, lemma, corollary, and
substantive claim in *Condensation in subcritical Cauchy Bienaymé trees*,
Igor Kortchemski and Leonard Vetter,
[arXiv:2503.07530v2](https://arxiv.org/abs/2503.07530v2).

**Every result of the paper is proved, four of them in corrected form, with
the axioms `propext`, `Classical.choice` and `Quot.sound` only and no `sorry`
outside `Challenge.lean`.** The 20 author-approved, frozen statements are
Theorem 1.1 (M1–M5); Theorem 3.1, by an endpoint route (D12) and by the
paper's own route (D18) through the Armendáriz–Loulakis criterion, Berger's
Theorem 2.4 and the paper's (2.6) and (3.3); Propositions 4.2, 4.3 and 4.5;
(2.4) with the existence of the law of $\mathcal C_1$; Corollary 4.1; and the
classification of Section 2.2. Four are corrected: (2.4), Corollary 4.1,
Proposition 4.5(ii) and the classification (R9, R10 and R13 of
[MANUSCRIPT_RECOMMENDATIONS.md](MANUSCRIPT_RECOMMENDATIONS.md)); the
[erratum](erratum-ECP2025.pdf) lists every correction with its location in the
journal version. The [coverage reconciliation](docs/COVERAGE_RECONCILIATION.md) of 11 November 2026
found no claim of the paper open or missing. The
[final verification](#final-verification-11-november-2026) records the kernel
replay and the official Comparator.

The paper is published as *Electron. Commun. Probab.* 30 (2025), paper no. 79,
doi:10.1214/25-ECP726, with the same text as arXiv v2; display (2.4) of v2 is
numbered (2.2) there. Section numbers, line numbers and equation numbers in
this report refer to the arXiv v2 source. The proof campaign ran from 29
October to 1 November 2026 under Codex coordination and from 10 to 11
November 2026 under Claude Code coordination.

Source: subcritical_cauchy_final_arxiv.tex, version 2 of 8 October 2025,
SHA-256 088f21ed02ea30565d3b6f61ef9b28babd07380be869773dd5f145fa221ecef5.
The manuscript is unchanged. Lean is 4.35.0; Mathlib is v4.35.0 at
56a005855ea17e0b0958f73ec801ae140b0a1679, with dependencies in the Lake manifest.

[The independently checked inventory](docs/PAPER_INVENTORY.md) retains all
nine active numbered result environments, the example's three cases,
substantive unnumbered claims, and cited/background obligations. The local-limit
extension is an open direction, not a theorem to prove. Every inventory entry
not explicitly treated below remains unproved; none has been silently excluded.

## Main results

| ID | Introduction conclusion | Status | Missing inputs |
| --- | --- | --- | --- |
| M1 | Linear maximal-degree condensation | **Proved** (10 Nov 2026) | `main_maxDegree_condensation`; see D12. |
| M2 | Negligible second-largest degree | **Proved** (10 Nov 2026) | `main_secondMaxDegree_negligible`; see D12. |
| M3 | Geometric depth of the condensation vertex | **Proved** (10 Nov 2026) | `main_maxDegreeDepth_geometric`; see D13. |
| M4 | Logarithmic height convergence | **Proved** (10 Nov 2026) | `main_height_log`; from Proposition 4.3 and Lemma 4.4(ii). |
| M5 | Tightness iff the logarithmic offspring moment is finite | **Proved** (10 Nov 2026) | `main_height_tight_iff`; see D16. |

On 10 November 2026 the author approved the Lean statements of M1–M5 and of
Theorem 3.1 ([approval record](docs/key-statements/APPROVAL.md)); they are frozen
in `SubcriticalCauchy/MainTheorems.lean` and `SubcriticalCauchy/Theorem31.lean`
with registered `sorry` holes, which are proof obligations, not proofs. The
same day the author approved Propositions 4.2 and 4.3, frozen in
`SubcriticalCauchy/Propositions42_43.lean` (definitions in
`SubcriticalCauchy/AttachedSlots.lean`, with the `leaf` padding of absent
slots). All eight holes are now filled with proof text only; both freeze
records pass.

## Proved components and correspondence

Names below are under the SubcriticalCauchy namespace.
[SubcriticalCauchy.lean](SubcriticalCauchy.lean) imports every library module.

| Source obligation | Lean declarations / module | Actual coverage |
| --- | --- | --- |
| D2 and R2.1, finite-tree combinatorics | PlaneTree.edges_add_one, edges_eq_size_sub_one, finite_size_le, finite_size_eq | Finite rooted ordered trees, their preorder degree list, the edge/vertex identity, and finiteness of each size class are established. |
| R2.1, algebraic tilt | PlaneTree.weight_tilt | The finite-product argument gives exactly $a^n r^{n-1}$ for a size-$n$ tree. |
| R2.1, earlier normalization helper | partition_ne_top, partition_tilt, normalize_scale, conditionedTreeOfPMF_tilt in [Tilting.lean](SubcriticalCauchy/Tilting.lean) | Equality of canonical normalized fixed-size offspring-product laws; retained as a helper. The actual branching-law version is now proved below. |
| R2.1, Proposition 2.1 | Bienayme.conditioned_tilt_of_pos, conditioned_tilt, admissible_tilt_iff, conditioned_isProbability in [BienaymeTilting.lean](SubcriticalCauchy/BienaymeTilting.lean) | **Complete.** Equality of the actual iid-constructed Bienaymé laws conditioned on size. Positive finite tilt factors, admissibility and probability-law semantics are explicit. The generalized equality also holds at null sizes, where both conditional measures are zero. |
| D1, standing offspring setup | Bienayme.IsSubcriticalCauchyOffspring, eventually_mass_pos, branching_mass_pos, offspringMean_pos_of_paper, mass_zero_pos_of_subcritical, eventually_size_admissible in [OffspringHypothesis.lean](SubcriticalCauchy/OffspringHypothesis.lean) | Literal local asymptotic and pointwise slow-variation hypothesis, with probability supplied explicitly by theorem instances. Unbounded support, positive mean and positive mass at zero and eventual admissibility are derived. No measurability or stable-domain conclusion is bundled in. |
| D1, author-approved measurable convention | Bienayme.IsMeasurableSubcriticalCauchyOffspring and to_literal in [MeasurableHypothesis.lean](SubcriticalCauchy/MeasurableHypothesis.lean) | **Recorded author clarification, 1 November 2026.** Future main statements use Lebesgue-measurable slow variation. The literal weaker hypothesis is preserved; no asymptotic conclusion is assumed. |
| D2/D6, maximal vertex and attached forest | Bienayme.maxDegree, maxDegreeVertex, maxDegreeFringe, attachedChild, attachedForestSlice in [MaxDegree.lean](SubcriticalCauchy/MaxDegree.lean), and secondMaxDegree in [DegreeStatistics.lean](SubcriticalCauchy/DegreeStatistics.lean) | Largest/second-largest degrees preserve multiplicity. The first lexicographic maximizer, its actual fringe, one-based child slots and general interval slices are characterized. Positive-address conversion preserves lexical order. An absent tree is `none`, distinct from a leaf. |
| U2.7, X1 bridge-degree component | Bienayme.bridge_degree_permutation_event in [BienaymeBridgeStatistics.lean](SubcriticalCauchy/BienaymeBridgeStatistics.lean); conditioned_degree_pair_event and marginals in [ConditionedDegreeStatistics.lean](SubcriticalCauchy/ConditionedDegreeStatistics.lean) | **Collection-law component complete.** Every permutation-invariant degree event, including both leading degrees jointly, has exactly the iid count-bridge conditional probability. The actual tree law is used. Null sizes vanish; $n\ne0$ is retained. No one-big-jump limit is supplied. |
| U4.5, deterministic height input | Bienayme.height_fringe_add_le, attachedForestHeight_le_height, depth_add_one_add_attachedForestHeight_le in [AttachedForestHeight.lean](SubcriticalCauchy/AttachedForestHeight.lean) | Correct full-height lower bounds from selected fringes and child forests. The depth-shifted maximum bound requires a nonempty forest. This does not give the missing full-height upper control. |
| R2.2b, Lemma 2.2(ii) | Bienayme.paper_centering_asymptotics, centering_shift_ratio_tendsto_one, tailIncrementMean_div_ellStarReal_tendsto_one in [RefinedCentering.lean](SubcriticalCauchy/RefinedCentering.lean), using [CenteringTailSeries.lean](SubcriticalCauchy/CenteringTailSeries.lean) and [EquivalentTails.lean](SubcriticalCauchy/EquivalentTails.lean) | **Complete under the approved measurable convention, given the defining scale normalization.** Both refined and first-order centering asymptotics use one common slowly varying witness for every normalized scale. The strict absolute cutoff and real rounding are proved. |
| R2.2c, Lemma 2.2(iii) | Bienayme.scaling_tendsto_atTop, scaling_div_nat_tendsto_zero in [ScalingSublinear.lean](SubcriticalCauchy/ScalingSublinear.lean) | **Complete given the source defining scale normalization.** For any real sequence with $n\mathbb P(X\ge a_n)\to1$, the paper hypothesis implies $a_n\to\infty$ and $a_n/n\to0$. Scale existence and its stable/RV properties remain separate obligations. |
| U2.7 expectation; U2.10 weak-law component | Bienayme.integral_offspringIncrement, walkAverage_ae_tendsto, finiteWalkAverage_deviation_tendsto_zero, finitePreviousWalkAverage_deviation_tendsto_zero, finiteWalk_driftRatio_deviation_tendsto_zero in [OffspringWalk.lean](SubcriticalCauchy/OffspringWalk.lean) | **Finite-mean walk input complete.** Actual infinite iid product law, its finite-prefix law, integer increments, expectation and strong/weak laws. The $n-1$ sum divided by $n$ has the correct sign/normalization. U2.10's nonconvergence on the finer scale is now proved (`unnumbered_meanCenteredWalk_not_convergent_in_distribution`, in the row for U1.1, U1.3, U2.2 below). |
| D5, deletion identities | Bienayme.deleteMaxCounts_first, deletedMaximumWord_eq_erase, maxDegree_eq_neg_deleted_sum, incrementMaximum_deleted_word in [DeleteMaximum.lean](SubcriticalCauchy/DeleteMaximum.lean) | Exact first-maximum deletion, preservation of relative order, bridge maximum/remainder sum and second maximum identity. Integer casts precede subtraction. These are deterministic inputs, not Theorem 3.1. |
| M2 unconditioned maximum input | Bienayme.finiteMaximumAverage_deviation_tendsto_zero, finitePreviousMaximumAverage_deviation_tendsto_zero in [OffspringMaximum.lean](SubcriticalCauchy/OffspringMaximum.lean) | The maximum of iid offspring counts divided by $n$ tends to zero in probability under finite mean, including $n-1$ samples divided by $n$. This alternative input does not prove the source's Fréchet limit or the conditional main result. |
| X3/R2.2a analytic helper | tailMass_floor_mul_div_tendsto_one, mul_tail_div_tailMass_tendsto_zero in [CriticalTail.lean](SubcriticalCauchy/CriticalTail.lean) | A summable nonnegative antitone positive tail with the stated dyadic index-minus-one ratios has a slowly varying primitive and negligible $nT_n$ relative to it. **Conditional helper:** the dyadic ratios have not yet been derived for the paper's offspring tails. Lemma 2.2(i) is now proved by the different route below; Lemma 4.4(i) is proved (D10). |
| R2.2a, Lemma 2.2(i), and D4 | Bienayme.paper_integratedTail_properties in [SlowVariationRounding.lean](SubcriticalCauchy/SlowVariationRounding.lean), with [SlowVariationTail.lean](SubcriticalCauchy/SlowVariationTail.lean), [SlowVariationBoundary.lean](SubcriticalCauchy/SlowVariationBoundary.lean) and [SlowVariationPrimitive.lean](SubcriticalCauchy/SlowVariationPrimitive.lean) | **Complete under the approved measurable convention.** Actual offspring assumptions imply genuine summability, positivity, vanishing, slow variation and $L=o(\ell^\star)$. The real floor extension agrees at integers and has proved ceiling/floor asymptotic equivalence. |
| U3.3, uniform slow variation | slowlyVarying_uniform_sequential, slowlyVarying_uniform_relative_tail, slowlyVarying_uniform_relative_window, slowlyVarying_uniform_additive_window, slowlyVarying_uniform_compact_tail in [MultiplicativeUniformSlowVariation.lean](SubcriticalCauchy/MultiplicativeUniformSlowVariation.lean), [SlowVariationWindows.lean](SubcriticalCauchy/SlowVariationWindows.lean), [CompactSlowVariation.lean](SubcriticalCauchy/CompactSlowVariation.lean) | **Complete under the author-approved measurable convention.** Includes shrinking relative windows and additive $o(n)$ windows uniformly over all $x\ge\varepsilon n$, with the tolerance fixed before eventual indices and basepoints. The representation theorem itself is bypassed. |
| U3.2, elementary window geometry | Bienayme.paper_centering_shift_div_nat_tendsto_zero, paper_centering_uniform_windows in [LinearWindows.lean](SubcriticalCauchy/LinearWindows.lean) | The actual centering shift is sublinear; its relative effect vanishes uniformly above every positive linear threshold, and the shifted argument divided by the source scale diverges uniformly. The external local probability estimate is now proved by the paper route (D18). |
| U3.2/U3.4, local mass input | Bienayme.paper_mass_ratio_of_relative_tendsto_one, incrementUnitWindow_eq_mass_floor, paper_unitWindow_ratio_of_relative_tendsto_one in [LocalMassVariation.lean](SubcriticalCauchy/LocalMassVariation.lean) | Actual singleton masses and open-left, closed-right increment unit windows have ratio tending to one at relatively equal diverging indices or thresholds. No estimate for sums of increments is assumed or concluded. |
| U3.2/U3.4, uniform local mass input | Bienayme.paper_unitWindow_uniform_additive_window, paper_centeredUnitWindow_uniform_additive_window in [LocalMassWindows.lean](SubcriticalCauchy/LocalMassWindows.lean) | The actual local unit-window ratio tends uniformly to one for every sublinear window width, above every positive linear threshold, including fixed drift corrections. Eventual positive window mass is also derived. The tightness and local estimates for the walk sum are now proved by the paper route (D18). |
| U3.1, lattice and deletion-law components | centered_lattice_window_neg_one, corrected_window_eventually_ge, Bienayme.finiteWalk_centered_window in [LatticeWindow.lean](SubcriticalCauchy/LatticeWindow.lean); MaximumSwapLaw.bridgeCountsLaw_map_rotation, swap_take_event_eq_delete_event in [MaximumSwapLaw.lean](SubcriticalCauchy/MaximumSwapLaw.lean) | Exact corrected lattice event and eventual linear threshold; equality of the actual conditional iid laws of ordered deletion and swap-to-last residuals, including ties and null sizes. Centering commutation and the one-big-jump limit remain separate. |
| U2.1, finite-tree atoms | BGW.LocallyFinite.bienaymeLaw_toLocallyFinite | **Complete by reuse.** The probability of each finite tree is its offspring-product weight, derived from the constructed branching law. |
| U4.7, actual survival inputs | Bienayme.survival_zero, survival_succ, survival_toReal_succ, survival_le_mean_pow, survival_toReal_tendsto_zero, ae_finite_of_subcritical | Initial value, PGF recursion, geometric upper bound and subcritical decay/finiteness are proved for the actual law. pgfReal_eq_tsum and summable_pgfReal establish the generating series on the probability interval. Positivity, ratio and lower bound are proved. The elementary correction, its exact finite-product recurrence, right-limit zero and corrected tail-series identity are now proved in BienaymeCorrection; slow variation is proved (D10). |
| D2/U4.7, height semantics | Bienayme.toLocallyFinite_mem_survivalEvent_iff in [BienaymeHeight.lean](SubcriticalCauchy/BienaymeHeight.lean) | **Complete.** Survival at generation n is precisely finite-tree height at least n, including generation zero. |
| R4.4a elementary content; U4.6–7 | Bienayme.survivalCorrection_pos, survivalCorrection_lt_mean, survivalCorrection_tendsto_zero, survivalCorrection_eq_tsum_tail, survivalCorrection_eq_tsum_kernel, survival_toReal_eq_prod_correction in [BienaymeCorrection.lean](SubcriticalCauchy/BienaymeCorrection.lean); paper_survivalCorrection in [OffspringHypothesis.lean](SubcriticalCauchy/OffspringHypothesis.lean) | The actual correction is positive and below the mean on $(0,1]$ under the paper hypothesis; bounds, monotonicity, continuity, limit zero, tail formula and recurrence are proved. Slow variation and the tail equivalence are now proved in the next row. |
| R4.4a, Lemma 4.4(i); U4.6 asymptotic | Bienayme.paper_survival_correction_lemma, survivalCorrection_div_ellStarReal_tendsto_one, survivalCorrection_slowlyVarying_atZero in [CorrectionAsymptotics.lean](SubcriticalCauchy/CorrectionAsymptotics.lean), using CorrectionKernel, FirstMomentTail, SlowTailPartialSums, TailPrefixMoments, CorrectionCutoffs, AbelianCutoffSqueeze | **Complete under the approved measurable convention (10 November 2026); statement approved by the author on 10 November 2026.** Lemma 4.4(i) is proved with $\ell$ the actual survival correction, together with $\ell(x)\sim\ell^\star(1/x)$ as $x\downarrow0$, where $\ell^\star(1/x)$ is read as `ellStar L ⌊1/x⌋₊`. See D10. |
| U4.4 / X7, Heathcote–Seneta–Vere-Jones Theorem 2 | Bienayme.survival_div_mean_pow_antitone, survival_div_mean_pow_tendsto_pos_iff, survival_div_mean_pow_tendsto_zero in [SurvivalCriterion.lean](SubcriticalCauchy/SurvivalCriterion.lean), with [SurvivalCriterionAux.lean](SubcriticalCauchy/SurvivalCriterionAux.lean) | **Complete for every probability law on ℕ with $0<m<1$ (10 November 2026); statement approved by the author on 10 November 2026.** For the actual Bienaymé law, $Q_n/m^n$ is antitone, converges to a positive constant iff $\sum_k k\log k\,\mu_k<\infty$, and tends to zero otherwise. The cited theorem is proved, not assumed. See D11. |
| R3.1, Theorem 3.1 | Bienayme.paper_deleted_maximum_tvDist in [Theorem31.lean](SubcriticalCauchy/Theorem31.lean) (frozen; proof in [MainProofs/Theorem31.lean](SubcriticalCauchy/MainProofs/Theorem31.lean)), from PotterBounds, LatticeFourier, LatticeSmallFrequency, LatticeConcentration(Aux), TruncatedExponential(Aux), NoLargeJump(Aux), EndpointLocal(Aux), InsertionCombinatorics, DeletedMaximumDensity, TotalVariationTypical | **Complete (10 November 2026), author-approved statement.** Conditionally on $W_n=-1$, the $n-1$ increments left after deleting the first maximal one converge in total variation to $n-1$ iid increments. By a new endpoint route, bypassing the cited Armendáriz–Loulakis and Berger theorems; see D12. Sealing re-audit passed. |
| Theorem 3.1 by the paper's own proof; U3.1–U3.4, X4, X5 | `ArmendarizLoulakis.al_criterion`, `Bienayme.berger_local_limit`, `paper_eq26`, `paper_eq33`, `paper_route_deleted_maximum_tvDist` in [PaperRoute/Statements.lean](SubcriticalCauchy/PaperRoute/Statements.lean) (frozen 11 November 2026; definitions in [PaperRoute/Defs.lean](SubcriticalCauchy/PaperRoute/Defs.lean); proofs in `PaperRoute/{ALProof*,BergerConcentration,BergerTight*,BergerFukNagaev*,BergerSmallMax*,BergerProof*,Eq26Proof*,Eq33Proof,FinalProof*}.lean`) | **Complete (11 November 2026), author-approved statements.** X4: the Armendáriz–Loulakis criterion in the form of its proof (not the published existence-of-$q_n$ statement). X5: Berger's local limit $\mathbb P(W_n-\lfloor b_n\rfloor=z)\sim n\mathbb P(X=z)$ jointly as $n\to\infty$, $z/a_n\to\infty$. U3.2: (2.6) uniformly on $x\ge\varepsilon n$. U3.3–U3.4: (3.3) with tightness at $\widehat b_n=n\ell^\star(a_n)$. U3.1: the corrected window $x=\gamma n-2$ (R8) and the swap-to-deletion bridge. No dependency on D12. See D18. Sealing re-audit passed with remarks. |
| M1, M2, Theorem 1.1(i) | Bienayme.main_maxDegree_condensation, main_secondMaxDegree_negligible in [MainTheorems.lean](SubcriticalCauchy/MainTheorems.lean) (frozen; proofs in `MainProofs/M1.lean`, `M2.lean`) | **Complete (10 November 2026), author-approved statements.** $\Delta(\mathcal T_n)/(n(1-m))\to1$ and $\Delta^2(\mathcal T_n)/n\to0$ in probability. See D12. Sealing re-audit passed. |
| M4, M5, Theorem 1.1(iii) | Bienayme.main_height_log, main_height_tight_iff in [MainTheorems.lean](SubcriticalCauchy/MainTheorems.lean) (frozen; proofs in `MainProofs/M4.lean`, `M5.lean`, `M5Aux.lean`, `M5Diagonal.lean`) | **Complete (10 November 2026), author-approved statements.** $H(\mathcal T_n)/\log n\to1/\log(1/m)$ in probability; the centred heights are tight (one $K$ for all $n\ge1$) iff $\sum k\log k\,\mu_k<\infty$. See D16. Sealing re-audit passed. |
| Proposition 4.2 | Bienayme.paper_attached_forest_tvDist in [Propositions42_43.lean](SubcriticalCauchy/Propositions42_43.lean) (frozen; proof in `PropProofs/P42Aux.lean`, [BlockLaw.lean](SubcriticalCauchy/PropProofs/BlockLaw.lean)) | **Complete (10 November 2026), author-approved statement.** The first $\lfloor\delta n\rfloor$ attached subtrees converge in TV to independent Bienaymé trees for $\delta\in[0,1-m)$. Includes the iid block law `iid_firstBlocks_law`. See D14. Sealing re-audit passed. |
| Proposition 4.3 | Bienayme.paper_height_lower, paper_height_upper in [Propositions42_43.lean](SubcriticalCauchy/Propositions42_43.lean) (frozen; proofs in `PropProofs/P43i.lean`, `P43ii*.lean`, [ExteriorTight.lean](SubcriticalCauchy/ExteriorTight.lean)) | **Complete (10 November 2026), author-approved statements.** (i) follows the paper from Proposition 4.2; (ii) uses a different route that also closes the full-height gap R6. See D15. Sealing re-audit passed. |
| (2.4), law of $\mathcal C_1$, Corollary 4.1 (corrected, R9) | Bienayme.paper_stable_limit, exists_cauchyOneLaw, paper_maxDegree_fluctuations in [Corollary41.lean](SubcriticalCauchy/Corollary41.lean), `IsCauchyOneLaw` in [CauchyOneLaw.lean](SubcriticalCauchy/CauchyOneLaw.lean) (frozen; proofs in `LateProofs/{C1Exists,C1Witness,StableLimit*,Cor41*}.lean`, [StableKernel.lean](SubcriticalCauchy/StableKernel.lean), `StableLaplace*.lean`, [CauchyOneUnique.lean](SubcriticalCauchy/CauchyOneUnique.lean), `StableOneStep*.lean`) | **Complete (10 November 2026), author-approved statements.** $(W_n-b_n)/a_n\to\mathcal C_1+(1-\gamma_E)$ and $(\Delta(\mathcal T_n)+b_n)/a_n\to-\mathcal C_1-(1-\gamma_E)$ with the paper's exact $b_n$; the law of $\mathcal C_1$ exists and is unique. See D17. Sealing re-audit passed. |
| U1.1, U1.3, U2.2, U2.4 (qualified), U2.8, U2.10 | unnumbered_unique_macroscopic_degree, unnumbered_scaling_regularly_varying, unnumbered_abs_centering_regularly_varying, unnumbered_walk_drift_ratio, unnumbered_meanCenteredWalk_not_convergent_in_distribution in [UnnumberedConsequences.lean](SubcriticalCauchy/UnnumberedConsequences.lean); summable_logMoment_of_one_lt_alpha, exists_logMoment_divergent, logMoment_moment_summable_of_one_lt in [LogMomentExamples.lean](SubcriticalCauchy/LogMomentExamples.lean); TiltingFacts.exponential_tilt_U22, infinite_first_moment_tsum_of_tail_alpha_lt_one, supercritical_equivalent_critical_U24 in [TiltingFacts.lean](SubcriticalCauchy/TiltingFacts.lean) | **Complete (10 November 2026).** Unique macroscopic vertex; $a_n$ and $\lvert b_n\rvert$ regularly varying of index 1; the mean-centred sums have no real limit law; finite $n\log n$ moment for index $>1$ and an actual index-one law with divergent moment for every $\beta\in(0,1]$ (finite for $\beta>1$); tilt PGF/mean/equivalence inside the radius; infinite mean for $\alpha<1$; supercritical laws with $\mu_0>0$ are equivalent to a critical law with all moments finite (the unqualified claim is refuted, row U2.4 below). |
| Proposition 4.5 (corrected, R10) | Bienayme.paper_height_second_order_log, paper_height_second_order_pow in [Proposition45.lean](SubcriticalCauchy/Proposition45.lean) (frozen; proofs in `LateProofs/P45*.lean`, [HeightSecondOrder.lean](SubcriticalCauchy/HeightSecondOrder.lean)) | **Complete (10 November 2026), author-approved statements.** Second-order height for $\mu_n\sim c/(n^2(\log n)^{1+\beta})$; for $0<\beta<1$ with the corrected coefficient $c/((1-\beta)\beta m\log(1/m)^2)$ (manuscript R10). Inputs: Lemma 4.4(i), Example 2.3(i). |
| Example 2.3(i)–(ii), U4.1, U4.2 | example23_i_ellStar, example23_i_scale, example23_ii_ellStar, example23_ii_scale in [ExampleScales.lean](SubcriticalCauchy/ExampleScales.lean); conditioned_maxDegree_tvDist, conditioned_secondMaxDegree_tvDist, incrementMaximum_le_tendsto_frechet, conditioned_secondMaxDegree_le_tendsto_frechet in [DegreeFluctuations.lean](SubcriticalCauchy/DegreeFluctuations.lean) | **Complete (10 November 2026).** Explicit $\ell^\star$ and $a_n\sim nL(n)$ for the logarithmic and iterated-logarithmic tails; TV transfers for $\Delta$ and $\Delta^2-1$; the Fréchet limit $e^{-1/u}$. Example 2.3(iii) is proved in [ExampleScalesIII.lean](SubcriticalCauchy/ExampleScalesIII.lean) (`example23_iii_ellStar`, `example23_iii_scale_small`, `example23_iii_scale_mid`). |
| M3, Theorem 1.1(ii) | Bienayme.main_maxDegreeDepth_geometric in [MainTheorems.lean](SubcriticalCauchy/MainTheorems.lean) (frozen; proof in `MainProofs/M3.lean`, [M3Transfer.lean](SubcriticalCauchy/M3Transfer.lean)), from CyclicResidual, CyclicResidualTree, PreorderHeight, DeletionPositionLaw, ExplorationLaw, WeakRecordRenewal | **Complete (10 November 2026), author-approved statement.** $\mathbb P(H_\Delta(\mathcal T_n)=j)\to(1-m)m^j$ for every $j$. See D13. Sealing re-audit passed. |
| U2.9; scale existence in U2.8 | Bienayme.incrementTail_div_tendsto_one, exists_scaling, scaling_div_mul_tendsto_one in [IncrementTailAsymptotics.lean](SubcriticalCauchy/IncrementTailAsymptotics.lean), with [IncrementTailAux.lean](SubcriticalCauchy/IncrementTailAux.lean) | **Complete under the approved measurable convention (10 November 2026).** $\mathbb P(X\ge x)\sim L(x)/x$ along real $x\to\infty$ for every witness $L$; a real scaling sequence with $n\mathbb P(X\ge a_n)\to1$ exists (least integer $j$ with $n\mathbb P(X\ge j)\le1$; $a_0=0$ is a harmless junk value); every scaling sequence satisfies $a_n\sim nL(a_n)$. The proof uses a discrete Karamata bound from four-adic blocks and the measurable uniform convergence theorem, with no monotonicity of $L$. Lemma 2.2(ii)–(iii) therefore hold for an actual scale, not only under its defining normalization. Sealing audit passed. |
| R4.4b, U4.7 | Bienayme.survival_pos, survival_ratio_tendsto, survival_geometric_bounds in [BienaymeSurvivalRatio.lean](SubcriticalCauchy/BienaymeSurvivalRatio.lean), using [SurvivalBounds.lean](SubcriticalCauchy/SurvivalBounds.lean) | **Lemma 4.4(ii) complete.** The actual survival sequence is strictly positive and its successive ratio tends to the mean for $0<m<1$. Both geometric bounds follow. The theorem holds for every positive-mean subcritical law. Lemma 4.4(i), including slow variation, is proved (D10). |
| R4.3a–b, U4.5 | Bienayme.forestBelow_mass, forest_height_bounds, forestBelowReal_floor_tendsto_one, forestBelowReal_floor_tendsto_zero in [BienaymeForestHeight.lean](SubcriticalCauchy/BienaymeForestHeight.lean), using [ForestBounds.lean](SubcriticalCauchy/ForestBounds.lean) | **Independent-forest input complete.** The actual product law gives $(1-q)^k$, union/exponential bounds and both limits. Natural and real thresholds, ceiling height indices, floor component counts and the empty forest are explicit. Proposition 4.3 is now proved (D15). |
| U4.8 and the independent-forest input to M4 | Bienayme.survival_log_upper_tendsto_zero, survival_log_lower_tendsto_atTop, exists_eta_log_exponent, forest_log_band_tendsto_one in [BienaymeForestLog.lean](SubcriticalCauchy/BienaymeForestLog.lean), using [LogarithmicThreshold.lean](SubcriticalCauchy/LogarithmicThreshold.lean) | **Threshold limits and auxiliary parameter existence complete.** For every fixed positive fraction of components, the actual independent-forest maximum lies between the lower and upper logarithmic thresholds with probability tending to one. Floors, ceilings and strict endpoints are explicit. M4 is now proved from it and Proposition 4.3. |
| U4.11, sublinearity component | Bienayme.survival_log_div_nat_tendsto, survival_log_normalized_inv_div_nat in [BienaymeSurvivalRatio.lean](SubcriticalCauchy/BienaymeSurvivalRatio.lean), using [SurvivalLog.lean](SubcriticalCauchy/SurvivalLog.lean) | **Sublinearity component complete for the actual law:** with $u_n=q_n/m^n$, $\log(1/u_n)/n\to0$. Uses Cesàro averaging. The heavy-tail recurrence components of U4.11–U4.12 and Proposition 4.5 are now proved (`HeightSecondOrder*.lean`). |
| U2.4, supercritical component | SupercriticalTiltingCounterexample.supercritical_equivalence_counterexample in [SupercriticalTiltingCounterexample.lean](SubcriticalCauchy/SupercriticalTiltingCounterexample.lean) | **Contradicted as stated, with a proved actual $\delta_2$ counterexample.** The original universal assertion is not counted as proved. U2.4's infinite-mean component is now proved: `infinite_first_moment_tsum_of_tail_alpha_lt_one` for $0<\alpha<1$ ([TiltingFacts.lean](SubcriticalCauchy/TiltingFacts.lean)) and `infinite_first_moment_tsum_of_tail_lt_one_U25` for $0\le\alpha<1$ ([ClassificationProof.lean](SubcriticalCauchy/ClassificationProof.lean)). |
| U2.5, five-case classification (corrected) | `paper_heavyTail_classification` in [Classification.lean](SubcriticalCauchy/Classification.lean) (frozen 11 November 2026; `IsTiltEquivalent`, `HasHeavyTail` in [ClassificationDefs.lean](SubcriticalCauchy/ClassificationDefs.lean); proof in [ClassificationProof.lean](SubcriticalCauchy/ClassificationProof.lean)) | **Complete (11 November 2026), author-approved corrected statement.** Assume $\nu_0>0$ and $\nu_n\sim L(n)/n^{1+\alpha}$ with $\alpha\ge0$ and $L$ positive, measurable and slowly varying. Then $\nu$ is Kennedy-equivalent to a law $\mu$ in one of the cases (a)–(e) of the paper. In (b)–(e), $\mu$ has the same tail (so $\mu=\nu$). The hypothesis $\nu_0>0$ is added: it is necessary, as the example $\nu_n=6/(\pi^2n^2)$, $n\ge1$, $\nu_0=0$ is in no case. Given the heavy tail it is also sufficient. Supercritical laws, including those with infinite mean, tilt to a critical law with finite second moment through the proved U2.4. Sealing re-audit passed with remarks. |
| U2.6, Łukasiewicz coding, excursion and Vervaat conditioning | `BGW.PlaneTree.isTreeExcursion_iff_existsUnique` (Vendor/BGW/BGW/Tree/Excursion.lean); `iid_walkFirstPassage_eq_sizeEvent`, `walkFirstPassage_eq_iff_treeExcursion` ([ExplorationLaw.lean](SubcriticalCauchy/ExplorationLaw.lean)); `iid_firstBlocks_law` ([BlockLaw.lean](SubcriticalCauchy/PropProofs/BlockLaw.lean)); `BGW.exists_unique_rotate_isTreeExcursion`, `cond_pi_countBridges_apply_eq_tsum` (vendored cycle lemma and bridge law); `map_cond_excursionWords_decodeTree`, `map_cond_countBridges_vervaatTree` ([WalkCoding.lean](SubcriticalCauchy/WalkCoding.lean)); `bridge_degree_permutation_event` ([BienaymeBridgeStatistics.lean](SubcriticalCauchy/BienaymeBridgeStatistics.lean)) | **Complete (11 November 2026).** Plane trees are in bijection with tree excursions. The walk stopped at its first passage below 0 codes a Bienaymé tree, and first passage at $n$ is distinguished from $W_n=-1$. The conditioned tree is the decoded walk conditioned to first pass at time $n$. The Vervaat-type statement, for every $\mu$ and $n$: rotating a bridge with $W_n=-1$ to its unique excursion and decoding sends the bridge law to the conditioned tree. The degree multiset of $\mathcal T_n$ has the law of the bridge jumps plus one. Coverage audit passed. |
| U4.3, transfers from Kortchemski (2013) | M3, Propositions 4.2 and 4.3 (rows above) | **Covered by replacement (11 November 2026).** The transferred arguments are replaced by the formal proofs D13–D15, which cite nothing. The paper's claim that Kortchemski's own arguments "remain valid" is not itself checked. Coverage audit passed. |
| U2.3 | TiltingCounterexample.critical_equivalence_boundary_counterexample in [TiltingCounterexample.lean](SubcriticalCauchy/TiltingCounterexample.lean) | **Contradicted as stated, with a proved counterexample.** The original assertion is not counted as proved. |

The setup example in Basic.lean is not paper coverage.

## Substantive differences and source issues

In this section D1–D18 name route sections. They are not the inventory's standing
definitions D1–D6 of [docs/PAPER_INVENTORY.md](docs/PAPER_INVENTORY.md).

### D1 — Unattained critical-tilt boundary

At source line 213, the paper asserts that equivalence to a critical law is
equivalent to a boundary limit of tilted means at least one. For masses $1/2$
at zero and one, the PGF satisfies

$$
F(x)=\frac{1+x}{2},\qquad
\frac{xF'(x)}{F(x)}=\frac{x}{1+x}\longrightarrow1.
$$

Every law equivalent by the paper's finite positive exponential relation still
has positive mass at zero and support in $\{0,1\}$, hence mean strictly below
one. The code proves normalization, the PGF series at every real input,
derivative, boundary limit, and impossibility of **any** equivalent normalized
law with mean one. Thus literal proof of every claim as written is impossible.
This does not refute the main subcritical Cauchy results, whose hypotheses force
unbounded support. The background criterion needs qualifications and an
endpoint-attainment argument, or an attained admissible-tilt formulation.
No manuscript correction has been made.

### D2 — Cesàro route for logarithmic sublinearity

Source line 523 uses geometric bounds and a squeeze in the comparison parameter.
The Lean helper instead averages successive logarithmic increments and
telescopes their sum. The analytic conclusion is unchanged, with positivity
and ratio convergence explicit. This checks the alternative analytic argument;
it does not check the paper's squeeze proof. BienaymeSurvivalRatio now supplies the actual survival-law inputs and exports the sublinearity conclusion.

### D3 — Reuse of the constructed BGW law (1 November 2026)

The earlier local finite-tree PMFs are retained. New probability statements use
the canonical locally finite BGW carrier and the law obtained by pruning an iid
offspring field, imported from the user's BGW project. Its branching property,
finite atoms and size conditioning close the earlier missing probabilistic
bridge for Proposition 2.1. No subcriticality or aperiodicity is added there.
The two finite-tree representations are not silently identified; new source
probability theorems explicitly use BGW trees and their proved finite embedding.

The [snapshot notice](Vendor/BGW/README.md) records 27 source modules, their
original checksums, license, and uncommitted-source provenance. GenerationLaw
needed elaboration repairs; its mathematical statement types are unchanged.
The source BGW checkout was not edited. The default build checks the entire
vendored library as well as this project's root library.

The actual survival recursion follows the same root-branching argument as the
paper. The geometric upper bound instead uses expected generation size followed
by Markov's inequality. This checks an alternative upper-bound argument, not
the paper's correction-function proof. The lower bound is now proved by the ratio route below; regular variation of the correction is now proved (D10).

The declumping project's regularly varying sequence tools were also inspected.
Its stable toolkit assumes index strictly greater than one, so it cannot be
used as a black box for this paper's index-one stable law.

### D4 — Survival ratio by dominated convergence; actual independent forests

On 1 November 2026, BienaymeSurvivalRatio proves positive survival from positive
mean, with infinite mean allowed for positivity. For finite mean, the PGF secant
slope is the convergent sum of the mass at $k$ times the finite geometric sum
$\sum_{j<k}(1-q)^j$. The summand lies between zero and $k\mu_k$, whose sum is
the mean. Dominated convergence as $q\to0$ gives the successive-survival-ratio
limit. Applying the existing geometric comparison proves Lemma 4.4(ii) without
the source's Karamata argument or its heavy-tail hypothesis. This verifies an
alternative proof of (ii); it does **not** check Karamata's Abelian theorem, the
slow variation of the correction in (i), or its equivalence to the integrated
tail. Those remain obligations.

BienaymeForestHeight constructs the finite product of actual Bienaymé laws and
proves the probability identity used in the proof of Proposition 4.3. It then
applies the existing scalar union/exponential estimates and limits. Real height
thresholds use natural ceilings; finite-tree strict-height semantics are proved.
The event for an empty forest is universal, even at threshold zero; it is not
identified with a natural-number maximum under an inconsistent empty convention.
The floor-number-of-components limits discharge the source's deterministic
rounding step. This checks the independent-forest calculation, not the comparison
with the conditioned tree's largest-degree forest or the transfer to its full
height. Those steps, including the previously recorded full-height gap, remain
unresolved.

### D5 — Logarithmic thresholds and independent-forest concentration

BienaymeForestLog proves the two threshold limits at source lines 478–481 for
the actual survival law, using its already proved logarithmic rate. The helper
LogarithmicThreshold shows that if $\log q_j/j\to L$, then
$\log(nq_{\lceil a\log n\rceil})/\log n\to1+aL$ for $a>0$.
Taking $a=(1\pm\varepsilon)/\log(1/m)$ gives exponent
$\mp\varepsilon$. The upper limit requires $\varepsilon>0$ and the lower
limit $0<\varepsilon<1$. All logarithm/division cancellations are justified
at sufficiently large indices; the values at zero and one are immaterial.

This route bypasses the source's quantitative geometric squeeze. The auxiliary
choice $0<\eta<m$ satisfying the source's exponent inequality is separately
proved by continuity at zero in exists_eta_log_exponent. Thus the two U4.8
limits and the choice of $\eta$ are checked, but the paper's intermediate
polynomial comparison inequalities are not checked by this proof route.

The actual product-law forest limits then give forest_log_band_tendsto_one:
for fixed $\delta>0$ and $0<\varepsilon<1$, a forest of
$\lfloor\delta n\rfloor$ independent trees has every height below
$(1+\varepsilon)\log n/\log(1/m)$ and at least one height at or above
$(1-\varepsilon)\log n/\log(1/m)$ with probability tending to one. The
band event is the upper-below event intersected with the complement of the
lower-below event; it is false for an empty forest. Its finite-tree
characterization is proved. The joint probability uses the complement union
bound. This completes the independent-forest first-order calculation and does
not establish any new conclusion about the size-conditioned tree.

### D6 — Actual degree coding, tail formula and finite-mean scale bounds

The maximal-degree selection uses a finite lexicographic minimum among actual
vertex addresses. The positive-address map preserves that order. The attached
forest consists of the selected fringe's actual ordered children; arbitrary
source intervals retain absent slots as options. The second maximum erases one
maximum, so tied maxima retain their multiplicities. The supplied height bounds
are lower bounds for the whole tree only; no control of competing branches is
inferred.

BienaymeBridgeStatistics specializes the reused uniform-cyclic-shift identity.
Rotation invariance removes the uniform index, and finite-tree atom sums identify
the actual size-conditioned event. Permutation-invariant degree predicates then
give the source collection law and the joint largest/second-degree law. This
checks the exact coding input and does not establish any condensation limit.

BienaymeCorrection supplies the intended tail-series formula by nonnegative
Tonelli summation, with separate finite-mean real summability. It also proves
continuity, monotonicity, strict positivity under branching mass, and the exact
recurrence/product. The paper hypothesis now supplies branching mass. The source's
swapped mass/power indices in its intermediate double sum are not literally
verified; the intended correctly indexed formula is proved. Karamata slow
variation and equivalence to the integrated tail remain open.

ScalingSublinear proves Lemma 2.2(iii) by a different finite-mean argument. The
source scale normalization and unbounded support first force $a_n\to\infty$.
Dominated convergence of truncated offspring first moments gives
$a_n\mathbb P(X\ge a_n)\to0$; division by
$n\mathbb P(X\ge a_n)\to1$ yields $a_n/n\to0$. This bypasses the
paper's regular-variation and integrated-tail proof. It neither constructs the
scaling sequence nor proves a stable-domain theorem.

OffspringWalk uses Mathlib's strong law on the constructed infinite product law.
The coordinate expectation is proved from the finite extended offspring mean;
the finite-prefix pushforward is the actual finite product measure. Almost sure
convergence gives the finite-product weak-law probabilities. This checks an
alternative route for the source weak-law input, including its $n-1$ indexing.

### D7 — First-order centering, iid maxima and the measurable convention

Centering uses the source's signed increment and absolute cutoff. Dominated
convergence proves $b_n/n\to m-1$, hence $b_n\sim-n(1-m)$, and the exact
complementary signed-tail identity holds for every cutoff. This bypasses the
integrated-tail proof for first-order centering. The refined integrated-tail
asymptotic is now proved separately in RefinedCentering by direct comparison
of summable signed-mass tails, retaining the strict absolute cutoff.

OffspringMaximum derives individual count sublinearity from consecutive walk
averages, then maximum sublinearity by a deterministic prefix-maximum bound.
The exact finite-prefix law supplies actual finite-product probabilities,
including $n-1$ counts normalized by $n$. This is an alternative finite-mean
input for M2; the source's Fréchet extreme-value claim was then open and is now proved (`incrementMaximum_le_tendsto_frechet`, `conditioned_secondMaxDegree_le_tendsto_frechet`, row U4.1–U4.2).

CriticalTail proves the new integrable index-minus-one boundary estimate by
arbitrarily many fixed dyadic blocks. Integer-scale comparisons and an antitone
squeeze then give slow variation of its primitive. This is a proved general
analytic tool with explicit dyadic-ratio hypotheses, not a replacement for the
missing source regular-variation bridge.

On 1 November 2026 the author explicitly selected **measurable slow variation**
for the main statements after the source's omitted regularity was identified.
[MeasurableHypothesis.lean](SubcriticalCauchy/MeasurableHypothesis.lean) records
that interpretation as IsMeasurableSubcriticalCauchyOffspring. It adds
Lebesgue measurability on the positive half-line using AEMeasurable, while
positivity, slow-variation ratios and integer mass asymptotics remain pointwise.
The original literal ratio-only predicate is preserved, and the accepted
predicate implies it. No uniform convergence, representation theorem or stable
limit is bundled into either predicate. An a.e. Borel representative is not
silently substituted for the original function's integer values or ratios.
The manuscript is unchanged.

The exact ordered deletion is distinct from the maximal-coordinate swap used by
[Armendáriz–Loulakis, Theorem 1](https://arxiv.org/pdf/0912.1516).
A distributional bridge under exchangeability must be proved when using that
result. The source's local estimate also depends on
[Berger, Theorem 2.4](https://arxiv.org/pdf/1706.07924).
Those external probability results have been located and their interfaces
inspected; their proofs are not yet formalized or counted as checked.

### D8 — Lattice-window correction in the one-big-jump application

The [primary Armendáriz–Loulakis paper](https://arxiv.org/pdf/0912.1516) uses
$x+\Delta=(x,x+1]$ when $\Delta=(0,1]$. The source's line 322 sets
$x=\gamma n-1$ for $\overline W_n=W_n+\gamma n$, selecting
$W_n\in(-1,0]$, hence $W_n=0$ for integer $W_n$. The needed bridge event is
$W_n=-1$, which instead requires $x=\gamma n-2$ under that convention.
Independent source review confirmed this matching error. The corrected argument
is still above $\varepsilon n$ eventually when $0<\varepsilon<\gamma$;
the exact lattice-event identities and eventual threshold are now proved in
[LatticeWindow.lean](SubcriticalCauchy/LatticeWindow.lean), including their
specialization to the actual finite iid walk. This is a proof-interface correction, not
a refutation of Theorem 3.1. The TeX is unchanged.

### D9 — Measurable uniform convergence and elementary linear windows

[UniformSlowVariation.lean](SubcriticalCauchy/UniformSlowVariation.lean) proves
the additive sequential uniform-convergence theorem directly by convergence in
measure on a finite interval and translation invariance. The exponential
change of variables is proved nonsingular using the differentiable logarithmic
inverse. [MultiplicativeUniformSlowVariation.lean](SubcriticalCauchy/MultiplicativeUniformSlowVariation.lean)
then proves the moving-factor ratio limit under the approved measurability
convention, using the original pointwise values throughout. This proves the
needed uniform-convergence ingredient by a different route; the source's cited
representation theorem itself has not been formalized or checked in full.

[LinearWindows.lean](SubcriticalCauchy/LinearWindows.lean) proves that the actual
centering shift is $o(n)$, negligible uniformly above $\varepsilon n$, and that
the shifted window divided by $a_n$ tends uniformly to infinity. It uses the
finite-mean centering and scaling proofs and bypasses the source's refined
integrated-tail asymptotics. The external local probability estimate remains
unproved.

The deterministic suffix rotation in
[MaximumSwapBridge.lean](SubcriticalCauchy/MaximumSwapBridge.lean) is a
multiset-preserving bijection fixing the first maximum's index. Swapping that
maximum to the last position after this rotation and discarding the last
coordinate is exactly the ordered deletion used in the source, including ties.
The invariance of the actual conditioned iid law is now proved in
[MaximumSwapLaw.lean](SubcriticalCauchy/MaximumSwapLaw.lean) by equal singleton
weights and a bijection of count vectors. This establishes the distributional
bridge, with ties and null sizes included. It does not establish Theorem 3.1's
total-variation limit or the later centered-real conversion.

Other source qualifications are retained in the inventory and
[manuscript recommendations](MANUSCRIPT_RECOMMENDATIONS.md): real thresholds and
tail-sum rounding, the unrestricted supercritical assertion, calculation typos,
the author-clarified measurable convention, remaining regular-variation estimates, uniform local estimates, and full-height transfer.

### D10 — Lemma 4.4(i) by an elementary cutoff squeeze (10 November 2026)

The source obtains $G_\mu(s)=1-m(1-s)+(1-s)\ell(1-s)$ with
$\ell(x)\sim\ell^\star(1/x)$ from Karamata's Abelian theorem (BGT 8.1.6). The
formal proof instead writes the correction as $\sum_k\mu_kK(q,k)$ with
$K(q,k)=k-\sum_{j<k}(1-q)^j$, bounds the kernel by $k$, $qk^2$ and $k-1/q$, and
squeezes the correction between cutoff bounds involving the first-moment tail
$A(n)=\sum_{k\ge n}k\mu_k$. A partial-sum bound $\sum_{j\le n}A(j)\le CnA(n)$, with
$C$ fixed before the cutoff parameters, controls the prefix. The tail
equivalence $A\sim\ell^\star$ and the slow variation of $\ell^\star$ give the
asymptotic; slow variation of $\ell$ at zero follows from it. No monotonicity of
$L(k)/k$ and no summability of $A$ is assumed. The paper evaluates $\ell^\star$
only at integers; at real arguments the formalization uses the floor extension
`ellStarReal`, which agrees at integers and is asymptotically equivalent to the
ceiling extension. Statement audit and sealing re-audit: independent Sonnet
reviews on 10 November 2026, both passed.

### D11 — A self-contained proof of the Heathcote–Seneta–Vere-Jones criterion (10 November 2026)

The source cites HSVJ Theorem 2 (lines 390, 483). The formal proof writes
$Q_n/m^n=\prod_{k<n}(1-\ell(Q_k)/m)$ from the actual survival recurrence, shows
that the product has a positive limit iff $\sum_k\ell(Q_k)<\infty$, compares this
sum with $\sum_n\ell(m^n)$ using the eventual sandwich $m^{2n}\le Q_n\le m^n$
(from Lemma 4.4(ii)) and monotonicity of $\ell$, changes the geometric rate, and
reaches $\sum_kk\log k\,\mu_k$ through the tail series of $\ell$ and discrete
Tonelli arguments with explicit kernel constants. No real integral or external
result is used. Statement audit and sealing re-audit: independent Sonnet
reviews on 10 November 2026, both passed.

### D12 — Theorem 3.1 by an endpoint route; Theorem 1.1(i) by weak laws (10 November 2026)

The source proves Theorem 3.1 by checking conditions (2.6) and (3.3) of
Armendáriz–Loulakis (Theorem 1) with Berger's uniform local estimate, the
centring and scale asymptotics, and uniform slow variation. The formal proof
follows instead the audited endpoint route of
[docs/blueprint/R31_ROUTE.md](docs/blueprint/R31_ROUTE.md) §2: Potter bounds;
a Fourier lattice concentration bound $\mathbb P(S_j=k)\le C/(nL_n^2)$ uniform
in $k$ and in $j\in[n/3,2n/3]$; a truncated exponential bound; no large jump
at the endpoint, $\mathbb P(S_n=n-1,\max\xi_i\le cn)=o(L_n/n)$; the endpoint
asymptotic $\mathbb P(S_n=n-1)\sim n\mu_{\lfloor(1-m)n\rfloor}$; the explicit
insertion density of the deleted-maximum law on a typical set; and a total
variation bound from a density close to 1 on a set of probability tending to 1.
This route bypasses the cited theorems. The paper's uniform estimate (2.6)
over all $x\ge\varepsilon n$ (inventory U3.2), condition (3.3), and the cited
Armendáriz–Loulakis and Berger results are proved separately by the paper's own
route, D18 (11 November 2026). The laws live on $\mathbb Z^{n-1}$, and Mathlib's `tvDist` is twice the
paper's distance; neither affects the conclusion.

Theorem 1.1(i) follows as in the source from the exact degree coding, the
identities $\Delta=-\sum(\text{deleted increments})$ and
$\Delta^2-1=\max(\text{deleted increments})$, and Theorem 3.1; the last step
uses the weak laws for the sum and the maximum of $n-1$ iid increments divided
by $n$ (finite mean suffices) instead of the paper's $a_n$-scale Cauchy and
Fréchet limits. Independent sealing re-audits of Theorem 3.1 and of M1–M2
passed on 10 November 2026; all three depend only on `propext`,
`Classical.choice` and `Quot.sound`
([axioms](verification/2026-11-10-thm31-axioms.txt)).

### D13 — Theorem 1.1(ii) by weak records of the cyclic residual (10 November 2026)

The source cites the spine and local-limit argument of Kortchemski (2013),
with the one-big-jump principle as input. The formal proof instead shows:
(a) deterministically, the depth of the first maximal-degree vertex equals the
number of positive-time weak records of the reversed cyclic residual word (the
increments read after the maximal vertex); (b) the conditioned tree and the
bridge give the same law to rotation-invariant residual events, and the
bridge's cyclic residual is the deleted word rotated by the insertion
position; ties are controlled by the probability of a non-unique maximum,
which vanishes by M1 and M2 (a dependency absent from the paper's route);
(c) the joint law of (insertion position, deleted word) converges in total
variation to a uniform position independent of iid increments; (d) for the
iid walk, the hitting time of $-1$ has the law of the total progeny
($\mathbb E\tau=1/(1-m)$), and the weak-record count is geometric with
parameter $m$ by a renewal argument at the first record, overshoots included.
Independent sealing re-audit passed on 10 November 2026; axioms `propext`,
`Classical.choice`, `Quot.sound` ([axioms](verification/2026-11-10-m3-axioms.txt)).

### D14 — Proposition 4.2 through the cyclic residual and an iid block law (10 November 2026)

The source cites Kortchemski (2013), Cor. 2.7. The formal proof reads the
first $k=\lfloor\delta n\rfloor$ attached subtrees as the first $k$
excursion blocks of the cyclic residual word, transfers the residual of the
conditioned tree to the bridge and then to an iid word of length $n-1$ in
total variation (ties controlled by M1–M2, as in D13), uses the hitting-time
law of large numbers ($\tau_k/n\to\delta/(1-m)<1$) to place the $k$ blocks
inside the word, and proves that the first $k$ blocks of the infinite iid walk
have exactly the law of $k$ independent Bienaymé trees (`iid_firstBlocks_law`,
by summing cylinder atoms).

### D15 — Proposition 4.3(ii) by an exterior split (10 November 2026)

The source proves (ii) by replacing $H(\mathcal T_n)$ with the height of the
attached forest, citing Theorem 1.1(ii), and by a symmetry between the two
halves of the attached forest (manuscript recommendation R6). The formal proof
does not use Proposition 4.2. It uses the deterministic bound
$H(t)\le|\text{exterior}|+1+H(\text{attached forest})$, tightness of the
exterior size (`exteriorSize_tight`: the last zero of the reversed residual,
compared with an iid walk of negative drift), and a union bound over the
complete blocks of the residual word, which are among the first $n-1$ blocks
of an iid walk and so independent Bienaymé trees by `iid_firstBlocks_law`; the
fixed shift of the threshold costs a constant factor since
$Q_{j+1}/Q_j\to m>0$. This supplies the full-height comparison asked for in R6.
Proposition 4.3(i) follows the paper (every slot is a subtree; `leaf` padding
has height 0).

### D16 — Theorem 1.1(iii)(b): uniform tightness and an explicit diagonal (10 November 2026)

The paper shows $\mathbb P(|H(\mathcal T_n)-\log n/\log(1/m)|\ge\lambda_n)\to0$
for every $\lambda_n\to\infty$ and concludes tightness; the frozen statement asks
for one $K$ valid for every $n\ge1$. The formal proof argues by contradiction
with a piecewise diagonal rate built from bad indices $n_j\to\infty$ (small $n$
are excluded because $H<n$), and includes a $+1$ adjustment for the ceiling at
the lower threshold. In the non-summable direction an explicit logarithmic
diagonal replaces the paper's $a_p,p_n$ construction (whose "$c_n\le1/p$"
should read $u_n\le1/p$). Theorem 1.1(iii)(a) (M4) follows the paper.

Independent sealing re-audit of D14–D16, M4 and M5 passed on 10 November 2026
(remarks only: the route departures above); axioms `propext`,
`Classical.choice`, `Quot.sound`
([axioms](verification/2026-11-10-theorem11-props42-43-axioms.txt)).

### D17 — The index-one stable limit by Laplace transforms (10 November 2026)

The source cites Feller for (2.4). The formal proof uses Laplace transforms
throughout (finite since $X\ge-1$): the one-step exponent
$n(\mathbb Ee^{-sX/a_n}-1)+sb_n/a_n\to\int_0^\infty(e^{-sx}-1+sx\mathbf1_{x\le1})x^{-2}dx
=s\log s+(\gamma_E-1)s$ (split layer-cake at the truncation point, a
strict/non-strict lattice-tail bridge, Potter bounds near zero), then the iid
product, then weak convergence from Laplace transforms (tightness from the
Laplace bounds at $s$ and $2s$; Prokhorov), and uniqueness of a law from its
Laplace values on $(0,\infty)$ by analytic continuation of the complex MGF. The
uniqueness and weak-convergence arguments are adapted, with attribution, from
the author's BGW-formalization (`StableTrees/Scalar/LimitLaw.lean`,
`Attraction/LaplaceContinuity.lean`, index $1<\theta\le2$). The law of
$\mathcal C_1$ is obtained as the shifted limit for an explicit offspring law
satisfying the paper's hypothesis. Corollary 4.1 follows from (2.4) along
$n-1$ ($a_{n-1}/a_n\to1$, $(b_n-b_{n-1})/a_n\to0$), an affine-perturbation
lemma and the total-variation transfer U4.1(a). The constant $1-\gamma_E$ of
R9 is forced by the exact truncated centring; the paper's limit without it is
false. Independent sealing re-audit passed on 10 November 2026
([axioms](verification/2026-11-10-all-frozen-axioms.txt)).

### D18 — The paper's own proof of Theorem 3.1 (11 November 2026)

At the author's request, the paper's route is formalized as well, next to D12.
The author chose intermediate generality and no $\Delta$-subexponentiality
certificate (11 November 2026). An Astra review accepted the five key statements,
which made the author's conditional approval effective. The proof follows the
paper:

1. Theorem 3.1 is the Armendáriz–Loulakis criterion applied to the law of
   $\overline X=X+\gamma$ with $d_n=\ell_n=\varepsilon n$, $c_n=n\ell^\star(a_n)$
   and the corrected window $x=\gamma n-2$ (R8). The swap-to-last law is then
   identified with ordered deletion of the first maximum, ties included.
2. Condition (2.6) follows from Berger's local limit through the lattice window
   arithmetic and local regular variation.
3. Condition (3.3) and the tightness of $\overline W_n/\widehat b_n$ follow
   from Lemma 2.2 and uniform local mass ratios.
4. Berger's Theorem 2.4 is proved from:
   - the concentration bound $\sup_k\mathbb P(W_j=k)\le C/a_n$ for
     $j\in[n/3,n]$;
   - tightness of the centred block sums and maxima at scale $a_n$;
   - a restricted Fuk–Nagaev bound;
   - negligibility of walks whose maximum is below $\delta z$, by two blocks
     and dyadic bands;
   - the one-big-jump upper and lower bounds.

The paper's displays `eq:26` (with $m_n$) and `eq:ber` (a supremum over
$x\ge\varepsilon n$) are not separate Lean statements. They are covered by
`paper_eq26`, in its centred form, and `berger_local_limit`, in the form
$z=x-m_n+O(1)\ge Ra_n$ with shift $\lfloor b_n\rfloor$; the change of
variables is in `Eq26ProofAux.lean`.

Recorded adaptations, approved with the statements:

- the concentration bound replaces Gnedenko's local limit theorem;
- a direct Bennett bound replaces Nagaev's inequality and Berger's Prop. 5.2;
- the maximum-tail hypothesis replaces AL's (3.8);
- the thresholds are supplied directly, so AL's Theorem 1 itself (existence of
  $q_n$) and $\Delta$-subexponentiality are not claimed;
- tightness is proved by truncated Chebyshev rather than from the stable limit.

The frozen `al_criterion` keeps AL's standing hypothesis $\ell_n/c_n\to\infty$,
which its proof does not use: AL assume it, and the criterion holds without it.
It is reported, not removed.

A declaration-level dependency walk (`scripts/PaperRouteDeps.lean`; the control
run on the D12 theorem flags 76 constants) finds no constant from the endpoint
modules. The only hit is `incrementLaw.eq_1`, the lazily generated unfolding
equation of the frozen definition `incrementLaw`. All five statements use only
`propext`, `Classical.choice` and `Quot.sound`
([axioms](verification/2026-11-11-paper-route-axioms.txt),
[dependencies](verification/2026-11-11-paper-route-deps.txt)). All four freeze
records pass, and an independent sealing re-audit passed with remarks. The
remarks are two declaration-scoped `maxHeartbeats` settings and local
`Classical.propDecidable` instances, none affecting the statements.

## Independent reviews

- Initial inventory, 29 October 2026: reconstructed by paper_inventory and
  independently checked by the coordinating agent against the entire TeX.
  Pass for coverage enumeration, not a proof of its claims.
- Early survival checkpoint: publication_prep reviewed the two compiled
  Prop-valued geometric-bound targets. Pass for the explicit conditional scope.
  The exploratory targets are superseded by proved declarations.
- Early tree checkpoint: paper_inventory reviewed the carrier, preorder degrees,
  edge/vertex identity and algebraic tilt target. Pass for this interface.
- Milestone review: paper_inventory independently reviewed survival, forest,
  logarithmic and counterexample modules. mathlib_foundations independently
  reviewed tree finiteness/normalization and the final counterexample equivalence
  bridge. Both passed at the stated scopes, retaining all missing bridges.

These are independent **agent** reviews, not human peer review. Reuse them only
while the reviewed source, statements, and semantic definitions are unchanged.

On 1 November 2026, paper_inventory independently passed the actual-law tilting,
survival and height interfaces and the generation-law repairs. The review caught
and resolved a missing probability-measure assumption in the real PGF series
lemma. At that earlier milestone it confirmed full R2.1 coverage and retained
the then-open lower-bound and heavy-tail obligations. Compilation and axiom evidence are recorded separately.

The later survival_forest_review agent independently passed the early target
statements and the implemented BienaymeSurvivalRatio and BienaymeForestHeight
exports. It checked finite-mean coercions, summability, positivity before division,
root-generation indexing, strict height and ceiling semantics, empty forests,
and floor-count limits. The review confirmed complete R4.4b coverage and only
the sublinearity component of U4.11, retaining R4.4a and R4.3 as open. The floor
bridge was added in response to its missing-input observation. This review did
not run builds or replace the mechanical evidence below.

At the logarithmic-forest milestone, survival_forest_review independently passed
the early targets and both implemented modules, including the later auxiliary
parameter lemma. It checked fixed parameter quantifiers, eventual positivity,
finite-mean coercions, ceiling/floor rounding and the maximum-height band
semantics. It confirmed U4.8 coverage and retained M4 as open. The reviews remain
agent reviews, distinct from human peer review and mechanical verification.

At the measurable-analysis milestone, survival_forest_review passed the early
targets and the ten implemented analytic/coding modules. It checked original
pointwise values under a.e. measurability, fixed uniform quantifiers, integer
window endpoints, actual conditional atoms, tied maxima and null sizes. It
confirmed U3.3 under the approved convention, only elementary/local-mass
components of U3.2–U3.4, and only finiteness/vanishing components of R2.2(i).
Subsequent integrated evidence and the final uniform local-window module are
recorded at the current milestone below.

## Current integration: integrated tails and refined centering

The six new modules for the integrated tail, real rounding, equivalent series
tails and refined centering passed the integrated build without warnings
(3249 jobs) and the transitive axiom audit (1035 visible project and BGW
declarations, only permitted axioms). Focused kernel replay passed with exit
zero for all six new modules; outputs use the `2026-11-01-integrated-tail-` prefix in
[verification](verification/). The earlier 42 project modules retain the full
replay evidence below; only the root import list has grown. All 48 current
project modules build together.

Independent milestone reviews passed the complete statements and proof routes
of Lemma 2.2(i) and (ii), under the approved measurable convention and the
source's defining scale normalization. The same slowly varying witness works
for every normalized scale. The integer tail's floor extension agrees at
integer points and has proved ceiling/floor asymptotic equivalence. These
entries are closed at this verified checkpoint; scale existence, stable limits
and increment-tail probability asymptotics remain open.

The proof uses compact uniform convergence and dyadic blocks for the integrated
tail, then direct comparison of genuine summable series tails for refined
centering. It bypasses the source's intermediate increment-tail probability
asymptotic and its cited BGT proof route. Those bypassed arguments and the
increment-tail probability asymptotic are not counted as checked or proved.

## Verification at the measurable-analysis and deletion-law milestone

Focused builds passed for the additive, multiplicative, shrinking-window and
compact-factor uniform-convergence modules, actual local mass ratios, linear
windows, corrected lattice endpoints, exact swap/deletion laws and integrated
tail summability. The final uniform local-window module passed its focused
compiler probe. The integrated build passed without warnings (3242 jobs), and
the expanded audit passed for 987 visible project and BGW declarations with
only the three permitted axioms. Full project-namespace kernel replay passed
with exit zero for all 42 project modules, including the root; outputs use the
`2026-11-01-analytic-windows-` prefix in [verification](verification/).
Static checks passed for all 42 project modules: manuscript and pins unchanged,
every module imported, no proof-hole/native-evaluation/custom-axiom text in
proof sources, all 70 shipped project/vendor modules within the size limit,
YAML parses, and local links and Markdown mathematics delimiters remain valid.
Exact replay command: `LEAN_NUM_THREADS=2 lake env leanchecker -v SubcriticalCauchy`.
The unchanged 28 vendor modules retain their earlier replay evidence. New
boundary-domination, primitive slow-variation and refined-centering work is
being checked and integrated after this milestone. The evidence here does not
certify those later proof bodies.

## Verification at the degree, correction and scaling milestone

Focused builds have passed for the maximal-degree/forest and bridge-statistic
modules, correction and tail identities, standing hypotheses, scale sublinearity,
walk laws, first-order centering, iid maximum sublinearity and both critical-tail
helper stages. Their interfaces have passing independent agent reviews.
The current integrated build passed without warnings (3195 jobs), and the
expanded axiom audit passed for 887 visible project and BGW declarations, with
only the three permitted axioms. Kernel replay passed with exit zero for all
31 project modules, including the root. The outputs use the
`2026-11-01-coding-scale-` prefix in [verification](verification/).
Exact replay command: `LEAN_NUM_THREADS=2 lake env leanchecker -v SubcriticalCauchy`.
The 28 unchanged vendored BGW modules retain their earlier full-replay evidence;
this command did not request a fresh BGW replay. These checks use imported
dependency environments and do not establish Comparator, NanoDa, Palomar, or
whole-paper completion.

The independent review at this milestone reconciled all 63 inventory entries
against the unchanged manuscript: nine numbered environments, the three-case
example, definitions and substantive unnumbered claims remain retained. It
confirmed completed scale sublinearity and only first-order centering, and kept
the stable-law, regular-variation, one-big-jump and full-height obligations open.

## Verification at the logarithmic-forest milestone, 1 November 2026

- Default `lake build` passed without warnings, 3174 jobs, including both libraries
  and the root importing both new modules.
  [Build output](verification/2026-11-01-forest-log-build.txt).
- Transitive axiom audit passed for 617 visible project and vendored BGW
  declarations, with only propext, Classical.choice and Quot.sound. Named
  queries include both threshold limits, the auxiliary parameter lemma and
  the joint forest concentration theorem.
  [Axiom output](verification/2026-11-01-forest-log-axioms.txt).
- Focused bundled kernel replay passed with exit code zero for both new proof
  modules, LogarithmicThreshold and BienaymeForestLog.
  [Replay output](verification/2026-11-01-forest-log-leanchecker.txt).
  Exact command: `LEAN_NUM_THREADS=2 lake env leanchecker -v SubcriticalCauchy.LogarithmicThreshold SubcriticalCauchy.BienaymeForestLog`.
  The earlier full replay below is retained for the unchanged module sources
  and imports; the library root has only gained imports and contains no proofs.
  A fresh full public-candidate replay is still required before publication.
- Static checks passed: manuscript checksum and pins unchanged, all 44 tracked
  modules within size limits, every project module imported, no proof holes,
  custom axioms or native evaluation in proof sources, YAML parses and updated
  Markdown links and mathematics delimiters are valid.

## Verification at the survival/forest milestone, 1 November 2026 (earlier)


- Final default `lake build` passed without warnings, 3172 jobs, covering both
  libraries and all affected consumers.
  [Build output](verification/2026-11-01-survival-forest-build.txt).
- The transitive axiom audit passed for 596 visible project and vendored BGW
  declarations. Only propext, Classical.choice and Quot.sound occur. Named
  queries include the ratio, geometric bounds, logarithmic sublinearity and
  natural/real/floor-count forest limits.
  [Axiom output](verification/2026-11-01-survival-forest-axioms.txt).
- Source checks passed: manuscript checksum and dependency pins unchanged,
  no proof holes/custom axioms/native evaluation, every project module imported,
  metadata parses and module paths resolve. Original vendor hashes differ only
  at the previously documented GenerationLaw repair.
- Bundled kernel replay passed with exit code zero for all 14 project modules
  and all 28 tracked BGW modules (42 tracked modules, including both roots).
  [Replay output](verification/2026-11-01-survival-forest-leanchecker.txt).
  The namespace scan additionally replayed the same eight cached BGW modules
  outside the shipped snapshot, for 50 replayed modules in total; these extras
  add no source coverage. This is replay against imported Mathlib environments,
  not fresh replay of all dependencies, independent NanoDa, Comparator, or
  official Palomar verification.

## Verification at the earlier BGW milestone, 1 November 2026 (historical)

- The default build checks both libraries, SubcriticalCauchy and the complete
  vendored BGW snapshot. It passed without warnings, 3169 jobs.
  [Earlier build output](verification/2026-11-01-build.txt).
- The expanded axiom audit passed for 555 visible project and BGW declarations.
  Only propext, Classical.choice and Quot.sound occur in the reported closures.
  [Earlier audit output](verification/2026-11-01-axioms.txt) includes the new
  actual-law tilting, survival, finiteness and height declarations.
- Source inspection found no proof holes, custom axioms or native evaluation
  in the project and vendored Lean sources. All original vendor checksums match
  except the explicitly documented GenerationLaw elaboration repairs.
- Bundled kernel replay passed with exit code zero for all 12 project modules
  and all 28 tracked BGW modules (including both library roots).
  [Earlier replay output](verification/2026-11-01-leanchecker.txt).
  The namespace scan also replayed eight older cached BGW modules not shipped
  in the snapshot; no source coverage is assigned to those extra cache entries.
  This is replay against imported Mathlib environments, not a fresh replay of
  all dependencies or an independent NanoDa check. The older replay below is
  historical evidence.

## Verification at the 29 October milestone (historical)

- Focused builds passed for all eight library modules without warnings.
- Integrated lake build passed: 3056 jobs, Lean 4.35.0.
- The transitive namespace audit passed for 107 visible project declarations.
  The only axioms reported were propext, Classical.choice, and Quot.sound.
  [Actual audit output](verification/axioms.txt) includes named queries.
- Source inspection found no sorry, admit, custom axioms, native_decide, or
  bv_decide in project proof code. All library files use the module system.
- Bundled Lean kernel replay passed with exit code zero for all nine project
  modules, including the root entry point. [Actual replay output](verification/leanchecker.txt)
  records the checked modules. This was not a fresh replay of Mathlib or an
  external NanoDa check.
- YAML parses and alignment paths resolve. This is structural validation,
  not complete JSON Schema validation or a Palomar preflight pass.

Reproduce the checks from this folder:

    lake build
    lake env lean scripts/AxiomAudit.lean
    LEAN_NUM_THREADS=2 lake env leanchecker -v SubcriticalCauchy BGW

Lean kernel replay checks project declarations against imported environments.
It is distinct from NanoDa and from fresh replay of all dependency declarations.

## Final verification (11 November 2026)

- **Kernel replay.** `LEAN_NUM_THREADS=2 lake env leanchecker -v SubcriticalCauchy BGW`
  replayed all 169 project modules and 36 BGW modules with exit 0 on commit
  `cf78f02` ([record](verification/2026-11-11-leanchecker.txt)). After the
  Challenge work, the four modules whose proofs changed were replayed again
  ([record](verification/2026-11-11-leanchecker-changed.txt)).
- **Comparison interface.** [Challenge.lean](Challenge.lean) imports only Mathlib
  and restates the 20 frozen statements with the 100 project definitions and
  lemmas they reach (922 lines, 37.5 KiB); [Solution.lean](Solution.lean)
  re-exports the library; [comparator.json](comparator.json) lists the 20
  theorems and the three permitted axioms. To make a one-file Challenge
  possible, the proofs of five lemmas (`canonical_offspringAt`,
  `mem_vertices_iff`, `vertices_nonempty`, `maxDegreeVertex_isVertex`,
  `canonical_pruneRaw`) were rewritten without module-private auxiliaries;
  no statement or definition changed. Two spellings in the Challenge are
  documented there: a scoped `bootstrap.genMatcherCode` option, so that
  `pruneRaw` gets its own matcher as in the development, and the explicit
  `NormedSpace ℝ ℝ` instance in `IsCauchyOneLaw`.
- **Local Comparator diagnostic** (macOS, not the official tool): statements
  and reachable constants match, only permitted axioms; the Solution export
  passes `leanchecker` ([record](verification/2026-11-11-local-comparator/)).
- **Official Comparator** (`lake comparator` in the Bubblewrap sandbox, with
  NanoDa and the Lean kernel) passed on Linux on 11 November 2026 in the private
  repository `igor-kortchemski/condensation-subcritical-cauchy-bienayme-trees`,
  after a source scan, the build and the axiom audit: first on commit `ab42946`
  (run 43072119896, [evidence](verification/2026-11-11-official-comparator/)),
  then on the final candidate `87dbd05`, an export of this development at
  `051c545` by `scripts/export_candidate.py` (run 43078769747,
  [evidence](verification/2026-11-11-official-comparator-final/)). The second
  workflow of each commit (build, axiom audit of 2,092 declarations, full
  `leanchecker` replay on Linux) passed as well (runs 43072111980, 43078767972).
- **Challenge review.** An independent Sonnet review of the Challenge's
  docstrings ([report](verification/2026-11-11-challenge-review.md)) led to a
  docstring for every target and corrected definition docstrings (child
  numbering, the full hypothesis, `leaf` padding, the `tvDist` factor); the
  code was unchanged (988 lines).
- **Freeze records.** Adding the Challenge and Solution libraries changed
  `lakefile.toml`, which the freeze records fingerprint. The five records were
  re-recorded (`-v2`), freezing the completed statement files whole; every
  declaration hash and dependency `.olean` hash is identical to the approved
  records ([record](verification/2026-11-11-freeze-rerecord.txt)).
- **Public repository (12 November 2026).** At the author's request the
  repository was recreated with a single commit, `e112dcf`, with the same files
  as `29c42d8` (the export of `72139d7`), so that its history leaves out
  records for the authors only; the earlier history is kept in a private
  backup. The build workflow (run 43164523853) and the official Comparator
  (run 43164576822, [evidence](verification/2026-11-12-official-comparator/))
  passed on `e112dcf`, and the repository was made public.
- **Not done.** The Palomar mechanical report was not run.

## Unresolved obligations and publication

**Author's decision (10 November 2026):** the cited background claims B1–B5 of
the inventory (condensation for $\alpha>1$; Brownian CRT and stable-tree
limits; critical Cauchy condensation; the application encodings) are recorded
as **external citations, not proof obligations**: the paper only quotes them,
and no result of the paper depends on them. They are not counted as proved.

Obligations (state of 11 November 2026; coverage reconciled, see [docs/COVERAGE_RECONCILIATION.md](docs/COVERAGE_RECONCILIATION.md)):

1. (2.4) with the law of $\mathcal C_1$, and Corollary 4.1: **proved** (D17).
2. Proposition 4.5: **proved** (10 November 2026).
3. Example 2.3: **proved** in full; U4.11–U4.12 are covered by `HeightSecondOrder*.lean`.
4. Unnumbered claims U1.1, U1.3, U2.2, U2.4 (qualified), U2.8, U2.10: **proved**.
   U2.6 **proved** and U4.3 **covered by replacement** (11 November 2026).
   U2.5 **proved** in corrected form (11 November 2026). The paper's own Theorem 3.1 steps U3.1–U3.4
   and the cited X4, X5 are **proved** in the form the paper uses (D18, 11
   November 2026: Berger's Theorem 2.4 for the paper's laws; the
   Armendáriz–Loulakis criterion in the form of its proof, without their
   existence-of-threshold statement or $\Delta$-subexponentiality); the other external inputs X1–X6 are covered where the
   paper's results use them (X7 proved, D11). False U2.3 and
   unqualified U2.4 are recorded with counterexamples, not proved.
   Corrections drafted and audited (11 November 2026, see above).
5. Cleanup (done), final Challenge/Solution interfaces (done), Linux Comparator
   (passed, 11 November 2026, see "Final verification"); the official Palomar
   mechanical report waits for a public repository.
