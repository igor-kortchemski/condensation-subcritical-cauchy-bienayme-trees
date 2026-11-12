# Independent review of `Challenge.lean` (docstrings and comments), 11 November 2026

Scope: documentation only (docstrings, comments, module header). Definition bodies and statements are not questioned. Sources read: `Challenge.lean` (922 lines), `comparator.json`, `subcritical_cauchy_final_arxiv.tex` (Theorem 1.1, Sections 2.3, 3, 4), `FORMALIZATION_REPORT.md` (D18, D12 note on `tvDist`). No Lean build was run. Severity: **M** must fix, **S** should fix, **O** optional.

## 1. Definition docstrings

| Line | Sev | Finding | Replacement |
| --- | --- | --- | --- |
| 52 | M | `Address` is called "zero-based", but in the locally finite carrier children are numbered from 1 (`Canonical`, `Present`, `generation`, `pruneRaw`). Only the `PlaneTree` API (`fringe?`, `vertices`) is zero-based. A reader will misread every address. | `/-- Lists of natural numbers used as vertex addresses. In the locally finite carrier (`Tree`, `Present`, `generation`) the children of a vertex are numbered `1, …, degree`; the `PlaneTree` API (`fringe?`, `vertices`) numbers them from `0`. `PlaneTree.toLocallyFinite` converts between the two. -/` |
| 58 | S | Does not say what "valid" means. | `/-- Offspring field in which an address `u ++ [j]` carries count `0` unless `1 ≤ j ≤ f u`, that is, unless it is an actual child of `u`. Applied at every `u`, this makes counts at absent addresses vanish together with all their descendants. -/` |
| 73 | S | Add convention. | `/-- `Present T u`: the address `u` (children numbered from `1`) is a vertex of `T`: the root, or a child `j` with `1 ≤ j ≤ degree T` whose subtree contains the rest of `u`. -/` |
| 87 | O | "decidable enumeration" is inaccurate: `Encodable` is a countable coding, used for the countable sum over trees. | `/-- Mathlib's `Encodable` instance for W-types; it makes `PlaneTree` countable, as needed for sums over all finite plane trees. -/` |
| 140 | S | Zero-based convention not stated. | add: "Addresses are zero-based: `i :: u` descends to the `i`-th child counting from `0`." |
| 163 | O | | `/-- All vertex addresses (zero-based, see `fringe?`), without repetition, listed in root-first depth-first (pre)order. -/` |
| 219 | S | Not clear that this is the zero-to-one-based translation. | `/-- Offspring field of the tree on one-based addresses: the step `i + 1` enters the `i`-th child (zero-based list index), the step `0` and any absent child give count `0`, and `[]` gives the root degree. -/` |
| 264 | O | | `/-- View a finite plane tree as a finite tree of the locally finite carrier (children renumbered from `1`). The map is injective. -/` |
| 272 | O | | add "Leaves contribute `0`." |
| 279 to 283 | S | Comment is accurate, but a reader cannot tell it has no mathematical content. | Append: "This only makes the Challenge's auxiliary declaration names agree with the development's, which is what the Comparator checks; it has no mathematical meaning." |
| 326 to 331 | S | `bienaymeLaw` should say it lives on the full carrier (infinite trees allowed) and that nothing is conditioned. | `/-- The Bienaymé–Galton–Watson law with offspring law `μ`, on the locally finite carrier `Tree`: the image of the independent-offspring field under `prune`. Infinite trees are allowed and not excluded. -/` |
| 358 | S | `tsum` of a non-summable series is `0`; say so, since `ellStar` depends on it. | `/-- The tail `∑_{j ≥ 0} T (n + j)`, endpoint included (Lean's `tsum`: value `0` if the series is not summable). -/` |
| 370 to 376 | O | `survival` should name the paper's `Q_n`. | `/-- `Q_n = P(H(𝒯) ≥ n)` for an unconditioned `μ`-tree 𝒯 (the paper's `Q_n`), as an extended nonnegative real. -/` |
| 389 | S | Fine on null sizes, but say the conditioning is on the carrier and that it is supported on finite trees. | `/-- The Bienaymé law conditioned on the event "finite with exactly `n` vertices" (the paper's `𝒯_n`), as a measure on `Tree`. If that event has probability zero (e.g. `n = 0`, or sizes `n` unreachable under `μ`), Mathlib's convention gives the zero measure, not a probability measure. -/` |
| 400 to 403, 416, 446, 462 | S | The `@Finset.sup … Lattice.toSemilatticeSup …` terms are unexplained and look arbitrary. | Add above each (once, at line 400): `-- The explicit instance arguments pin the `SemilatticeSup`/`OrderBot` path so that the term is identical to the development's; mathematically this is just `Finset.sup` on `ℕ`.` |
| 445 | S | "obtained from lookup success" hides that `Classical.choose` picks the unique value. | `/-- The subtree rooted at the selected vertex. `Classical.choose` only extracts the witness of `IsVertex`; it is unique (the value of `fringe?`), so no choice is involved. -/` |
| 452 | S | `i = 0` and `i - 1` truncation not documented. | `/-- The `i`-th child subtree of the selected vertex, children numbered from `1`; `none` if `i` exceeds the degree. For `i = 0` the truncated subtraction returns the first child; the statements use only `i ≥ 1`. -/` |
| 410 | O | Fine. | |
| 487 | O | | add "`toLocallyFinite` is injective, so this is the event `{t | P t}` on finite trees." |
| 512 | S | Add: not measurable, ratio with Lean division (`x / 0 = 0`). | `/-- Slow variation at infinity in the ratio form of the Introduction: `L (a x) / L x → 1` for every `a > 0`. No measurability is included. -/` |
| 523 to 531 | M | Omits that the predicate includes `m < 1` and the local tail `μ_n ~ L(n)/n²` (index `α = 1`), and positivity of `L`. This is the hypothesis of every main theorem. | `/-- The paper's hypothesis `(H^loc_μ)`, in the version accepted for the main statements: the mean `m` of `μ` is `< 1`, and there is a positive function `L` on `(0, ∞)`, slowly varying (`IsSlowlyVaryingAtTop`) and Lebesgue measurable on `(0, ∞)`, with `μ_n ~ L(n)/n²`. The measurability of `L` is the author's convention of 1 November 2026; the paper does not require it. -/` |
| 549 | S | State the inequality. | `/-- `P(X ≥ x)` for the increment `X = ξ - 1` (closed inequality), `ξ ~ μ`; used in `n P(X ≥ a_n) → 1`. -/` |
| 557 | O | | add "(the first maximal index `V_n` in the paper)" |
| 573 | S | "existing actual" is not meaningful to a reader; `attribute [local instance] Classical.propDecidable` is unexplained. | `/-- Law of `(ξ_1, …, ξ_n)` i.i.d. `μ` conditioned on `∑ ξ_i = n - 1` (the bridge `W_n = -1` of the paper), as a measure on `Fin n → ℕ`; zero if that event is null (Mathlib convention). -/` and above line 568: `-- Classical decidability is used only to elaborate the conditional measure; it does not affect the meaning.` (confirm with the author that this is its only use; if it is needed for `countBridges` decidability, say so). |
| 584 to 589 | S | `deletedIncrements` pads with `0` via `getD`; for `n ≥ 1` the word has length exactly `n - 1`, for `n = 0` the index type is empty. | `/-- The `n - 1` increments `ω_i - 1` left after deleting the first maximal one (the paper's `(X^{(n)}_i)`), as a vector in `ℤ`. The default `0` of `getD` is never used for `n ≥ 1`. -/` |
| 603 | O | | `/-- The paper's `b_n = n E[X 1_{|X| ≤ a_n}]`, with the cutoff `a_n` used as a real number (no rounding). -/` |
| 614 to 621 | S | Docstring good. The comment is accurate but vague. | `-- `∫ x, exp (-(s * x)) ∂ν`, written with an explicit `NormedSpace ℝ ℝ` argument. With the imports of this file instance search could return a different (propositionally equal) term; the development's term is spelled out so that the two statements agree as kernel terms.` Also say in the docstring: "this characterises the law of `𝒞₁`; existence is `exists_cauchyOneLaw`". |
| 631 | S | Docstring uses `λ`; the body uses `r`. | `/-- Kennedy equivalence: there are `a, r > 0` with `μ_k = a r^k ν_k` for all `k` (the paper's `λ` is `r`). -/` |
| 635 | O | | add "for `α ≥ 0`, with `L` the slowly varying function". |
| 648 to 656 | S | `alSwapDrop` for `n = 0` is junk; domain. | `/-- Armendáriz–Loulakis' `π ∘ T`: swap the first maximal coordinate of `x : Fin n → ℝ` with the last one and drop the last coordinate (zero-based `Fin`; for `n = 0` there is no coordinate and the value is vacuous). -/` |
| 661 | O | | add "(`m` totalised by `toReal`; only used when `m < 1`)". |
| 674 | M | The paper (before Prop. 4.2) pads with the empty tree `∅` for `i > Δ(τ)`; Lean pads with `leaf` (one vertex). A reader comparing with the paper sees a silent deviation. | `/-- The first `k` child subtrees of the maximal vertex, children numbered from `1`. Missing children (`i > Δ`) are padded with `leaf` (a single vertex), whereas the paper pads with the empty tree `∅`. The choice is immaterial for Proposition 4.2, since `Δ ≥ ⌊δ n⌋` with probability tending to one. -/` |
| 678 | S | | `/-- Law of the first `k` attached subtrees under the conditioned tree `𝒯_n`: a countable mixture over finite plane trees, equal to the image of `conditioned μ n` since that measure is supported on finite trees. -/` |
| 691 to 702 | S | State `ℓ*(n) = ∑_{k ≥ n} L(k)/k` and the real extension and junk values. | `/-- The paper's `ℓ*(n) = ∑_{k ≥ n} L(k)/k` (summable under `(H^loc_μ)`; `0` otherwise, by Lean's `tsum`). -/`; `/-- `ℓ*` at a real argument: `ℓ*(⌊x⌋)`. The paper evaluates `ℓ*(a_n)` at the real `a_n`. -/` |

## 2. Target statements

None of the 20 theorems (lines 712 to 919, except `al_criterion`) has a docstring or comment. This is the main gap: the Challenge is what a reader checks against the paper. Recommended docstrings follow; each matches the Lean statement and the TeX.

| Line | Theorem | Replacement docstring | Sev |
| --- | --- | --- | --- |
| 712 | `main_maxDegree_condensation` | `/-- Theorem 1.1 (i), first part: `Δ(𝒯_n) / (n (1 - m)) → 1` in probability, where `𝒯_n` is the `μ`-tree conditioned on `n` vertices. -/` | M |
| 719 | `main_secondMaxDegree_negligible` | `/-- Theorem 1.1 (i), second part: `Δ²(𝒯_n) / n → 0` in probability (second largest outdegree, with multiplicity). -/` | M |
| 726 | `main_maxDegreeDepth_geometric` | `/-- Theorem 1.1 (ii): `P(H_Δ(𝒯_n) = j) → (1 - m) m^j` for every `j ≥ 0`, with `H_Δ` the depth of the first maximal-degree vertex. -/` | M |
| 733 | `main_height_log` | `/-- Theorem 1.1 (iii)(a): `H(𝒯_n) / log n → 1 / log(1/m)` in probability. -/` | M |
| 740 | `main_height_tight_iff` | `/-- Theorem 1.1 (iii)(b): `H(𝒯_n) - log n / log(1/m)` is tight (over `n ≥ 1`) if and only if `∑ n log n · μ_n < ∞`. -/` | M |
| 749 | `paper_deleted_maximum_tvDist` | `/-- Theorem 3.1 (`th:asy iid`), proved by the author's direct route (D12): the law of the `n - 1` increments left after deleting the first maximum of the bridge `W_n = -1` is asymptotically the i.i.d. increment law in total variation. Normalisation: Mathlib's `tvDist` is twice the paper's `d_TV`; the convergence to `0` is the same. -/` | M |
| 756 | `paper_attached_forest_tvDist` | `/-- Proposition 4.2: for `δ ∈ [0, 1 - m)`, the first `⌊δ n⌋` subtrees attached to the maximal vertex of `𝒯_n` are asymptotically `⌊δ n⌋` independent `μ`-trees in total variation (Mathlib normalisation, twice the paper's). Missing subtrees are padded by `leaf`, see `attachedSlotsTree`. -/` | M |
| 764 | `paper_height_lower` | `/-- Proposition 4.3 (i): if `h_n > 0`, `h_n → ∞` and `n Q_{h_n} → ∞` then `P(H(𝒯_n) ≥ h_n) → 1`. `Q_{h}` is `survival μ ⌈h⌉₊`, equal to `P(H ≥ h)` since `H` is integer valued. -/` | M |
| 772 | `paper_height_upper` | `/-- Proposition 4.3 (ii): if `h_n > 0`, `h_n → ∞` and `n Q_{h_n} → 0` then `P(H(𝒯_n) < h_n) → 1`. -/` | M |
| 780 | `exists_cauchyOneLaw` | `/-- Existence of the law of `𝒞₁`, the totally asymmetric Cauchy variable with `E[e^{-λ𝒞₁}] = e^{λ log λ}` (Section 2.3, citing Feller), needed to state (2.4). -/` | M |
| 783 | `paper_stable_limit` | `/-- Equation (2.4), corrected version (R9): `(W_n - b_n)/a_n → 𝒞₁ + (1 - γ_E)` in distribution, where `n P(X ≥ a_n) → 1` and `γ_E` is the Euler–Mascheroni constant. The paper's (2.4) omits the shift `1 - γ_E`. Stated as convergence of `E f(·)` for bounded continuous `f`. -/` | M |
| 792 | `paper_maxDegree_fluctuations` | `/-- Corollary 4.1, corrected version (R9): `(Δ(𝒯_n) + b_n)/a_n → -𝒞₁ - (1 - γ_E)` in distribution. The paper's Corollary 4.1 omits `1 - γ_E`. The expectation is written as a sum over finite plane trees. -/` | M |
| 801 | `paper_height_second_order_log` | `/-- Proposition 4.5 (i) (`β = 1`): for `μ_n ~ c/(n² log² n)`, `H(𝒯_n) = log n/log(1/m) - (c/(m log(1/m)²)) log log n + o(log log n)` in probability. -/` | M |
| 814 | `paper_height_second_order_pow` | `/-- Proposition 4.5 (ii), corrected version (R10), for `μ_n ~ c/(n² log^{1+β} n)`, `0 < β < 1`: the correction term is `c / ((1-β) β m log(1/m)²) · (log n)^{1-β}`. The paper has `log(1/m)^{1+β}` in the denominator, which is wrong. -/` | M |
| 829 | `berger_local_limit` | `/-- Berger's local limit theorem (Theorem 2.4 of the cited [Ber17]) for `α = 1`, in the form used by the proof of Theorem 3.1, under `(H^loc_μ)`: `P(W_n = z + ⌊b_n⌋) ~ n P(X = z)` uniformly in `z ≥ R a_n`, `R` large (`z / a_n → ∞`). It is not Berger's theorem in its published generality. -/` | M |
| 838 | `paper_eq26` | `/-- Condition (2.6) of Armendáriz–Loulakis for the centred law `X̄ = X + (1 - m)`, uniformly in `x ≥ ε n`: `P(W̄_n ∈ (x, x+1]) ~ n P(X̄ ∈ (x, x+1])`. This is the first display of the "Condition (2.6)" step; the paper's `eq:26` (with `m_n`) follows by the change of variables `x ↦ x - m_n`. -/` | S |
| 846 | `paper_eq33` | `/-- Condition (3.3) of AL for `X̄` with `b̂_n = n ℓ*(a_n)` (the paper's `eq:33`), together with the facts the proof uses: tightness of `W̄_n / b̂_n`, `a_n = o(b̂_n)`, and `(b_n + (1-m) n)/b̂_n → -1` (Lemma 2.2 (ii)). The statement is therefore stronger than `eq:33` alone. -/` | S |
| 864 | `paper_route_deleted_maximum_tvDist` | `/-- Theorem 3.1, again, proved by the paper's own route (Armendáriz–Loulakis criterion, `paper_eq26`, `paper_eq33`, `berger_local_limit`). The statement is identical to `paper_deleted_maximum_tvDist`; the two proofs are independent. -/` | M |
| 871 | `paper_heavyTail_classification` | `/-- The five-case classification of Section 2.2 (cases (a) to (e)), corrected version (U2.5): the hypothesis `ν₀ > 0` is added. Every `ν` with `ν_n ~ L(n)/n^{1+α}`, `α ≥ 0`, is Kennedy-equivalent to a probability `μ` which is: critical with finite variance (a); critical with infinite variance and `1 < α ≤ 2` (b); critical with `α = 1` (c); subcritical with `α > 1` (d); subcritical with `α = 1` (e). -/` | M |
| 894 | `al_criterion` | Existing docstring is accurate and honest. Suggest one added sentence: "The normalisation of `tvDist` is Mathlib's, twice the paper's; only the threshold `τ` changes." | O |

Specific checks against the paper:

- Theorems 1.1, 3.1, Propositions 4.2, 4.3, 4.5 and (2.4): hypotheses and conclusions match; `ε < |…|` versus the paper's `≥ ε` in Proposition 4.5 are complements of each other and equivalent.
- `paper_deleted_maximum_tvDist` and `paper_route_deleted_maximum_tvDist` are verbatim identical statements; without a docstring a reader will take this for a copy error (hence M).
- `paper_eq26` and `paper_eq33` do not formalize the labelled displays `eq:26` and `eq:33` literally (see D18); the names are misleading unless the docstrings above are added.
- `berger_local_limit` and `al_criterion` are the proof-forms, as D18 states; they must not be read as the published theorems.
- `paper_stable_limit` and `paper_maxDegree_fluctuations` rely on `ha : n P(X ≥ a_n) → 1`, the paper's choice of `a_n`, and on `centering` (`b_n`). The `+ centering` sign in `paper_maxDegree_fluctuations` is the paper's `Δ + b_n`; consistent.

## 3. Module docstring and the two comments

- The module docstring is accurate but thin. It says "twenty approved statements" and "Helper theorems occurring in definition bodies retain their proofs". Suggested addition (S): list the conventions and the status of the twenty.

  ```
  Conventions. `PlaneTree` addresses are zero-based; the locally finite carrier `Tree` uses
  one-based children. `conditioned μ n` is the `μ`-tree conditioned on having exactly `n`
  vertices (zero measure if that has probability zero). Mathlib's `tvDist` is twice the
  paper's total variation distance. The theorems at the end are the Comparator targets:
  Theorem 1.1 (five statements), Theorem 3.1 (two routes), Propositions 4.2, 4.3, 4.5,
  (2.4) and Corollary 4.1 with the constant `1 - γ_E`, Proposition 4.5 (ii) with
  `log(1/m)²`, the Armendáriz–Loulakis criterion, Berger's local limit in the form used by
  the proof, conditions (2.6) and (3.3), and the classification with `ν₀ > 0`.
  Declarations without docstrings (for example `canonical_pruneRaw`, `vertices_nonempty`,
  `maximalVertices_nonempty`, `maxDegreeVertex_mem`, `maxDegreeVertex_isVertex`) are
  helpers whose proofs are needed by the definitions that follow.
  ```
- The `bootstrap.genMatcherCode` comment (279 to 283): accurate; see the S suggestion in Section 1. It says "Present.match_1" without saying why a name matters; the added last sentence fixes that.
- The `NormedSpace ℝ ℝ` comment (618 to 619): accurate, slightly cryptic ("the development's imports select"); replacement given in Section 1.

## 4. Readability

1. (S) `attribute [local instance] Classical.propDecidable` at line 568: add a one-line comment (Section 1, line 573).
2. (S) The `@Finset.sup` terms: single explanatory comment (Section 1).
3. (O) The `open` lines (323, 346, 355 and similar) are repeated per block and harmless; a header comment "namespace blocks mirror the development's files; the `open` lines are copied from there" would head off questions.
4. (O) The `noncomputable section ... end` wrappers around single definitions mirror the development; same remark.
5. (O) `countBridges` (348): add "(a bridge condition only: no first-passage requirement)".
6. (S) Place a short comment before line 712: "Targets (Comparator holes): the proofs are in `SubcriticalCauchy`."
7. (O) The long import list lines 3 to 33 is needed for term identity; one comment is optional.
