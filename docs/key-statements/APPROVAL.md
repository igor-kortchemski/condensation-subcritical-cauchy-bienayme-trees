# Key statements for the author's approval — 10 November 2026

The campaign profile asks the author to approve the main theorems and important
propositions as exact Lean declarations before proofs depend on them. Approved
statements that are still unproved are then frozen (registered `sorry` holes,
checked byte for byte); proved ones are recorded as approved. Nothing is frozen
yet.

Common hypothesis: `[IsProbabilityMeasure μ]` and
`IsMeasurableSubcriticalCauchyOffspring μ`, i.e. $m<1$ and
$\mu_n\sim L(n)/n^2$ with $L$ positive, slowly varying (ratio sense) and
Lebesgue-measurable on $(0,\infty)$ — the convention you chose on 1 November.
`conditioned μ n` is the actual Bienaymé law conditioned on $n$ vertices (zero
measure at a null size; every large $n$ is admissible). Real division by zero
and $\log 0=\log1=0$ only affect finitely many $n$.

## Reviews

| Statement | Sonnet audit | Sol audit (other model family) | Blind read-back |
| --- | --- | --- | --- |
| M1–M5 (`MainTheorems.lean`) | pass | pass | [READBACKS.md](READBACKS.md) |
| Lemma 4.4(i) and its companion asymptotic | pass (companion needed for Prop. 4.5) | pass | — |
| X7, HSVJ criterion | pass | incomplete (reviewed before the module existed) | — |
| Theorem 3.1 (`Theorem31.lean`) | pass | not run | — |

## Theorem 1.1 — unproved, to be frozen after approval

**M1.** For every $\varepsilon>0$,
$\mathbb P\big(\varepsilon<\lvert\Delta(\mathcal T_n)/(n(1-m))-1\rvert\big)\to0$.

```lean
theorem main_maxDegree_condensation (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
        ε < |(maxDegree t : ℝ) / ((n : ℝ) * (1 - (offspringMean μ).toReal)) - 1|))
      atTop (𝓝 0)
```

**M2.** For every $\varepsilon>0$, $\mathbb P(\varepsilon<\Delta^2(\mathcal T_n)/n)\to0$, the second
maximum counted with multiplicity.

```lean
theorem main_secondMaxDegree_negligible (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
        ε < (secondMaxDegree t : ℝ) / n))
      atTop (𝓝 0)
```

**M3.** For every $j\ge0$, $\mathbb P(H_\Delta(\mathcal T_n)=j)\to(1-m)m^j$, where
$H_\Delta$ is the depth of the lexicographically first maximal-degree vertex
(root at depth 0).

```lean
theorem main_maxDegreeDepth_geometric (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (j : ℕ) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t => maxDegreeDepth t = j))
      atTop (𝓝 (ENNReal.ofReal
        ((1 - (offspringMean μ).toReal) * (offspringMean μ).toReal ^ j)))
```

**M4.** For every $\varepsilon>0$,
$\mathbb P\big(\varepsilon<\lvert H(\mathcal T_n)/\log n-1/\log(1/m)\rvert\big)\to0$.

```lean
theorem main_height_log (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t =>
        ε < |(height t : ℝ) / Real.log n - 1 / Real.log (1 / (offspringMean μ).toReal)|))
      atTop (𝓝 0)
```

**M5.** The family $H(\mathcal T_n)-\log n/\log(1/m)$, $n\ge1$, is tight iff
$\sum_k k\log k\,\mu_k<\infty$; tightness is written as
$\forall\varepsilon>0\ \exists K\ \forall n\ge1$, $\mathbb P(\lvert\cdot\rvert>K)\le\varepsilon$.

```lean
theorem main_height_tight_iff (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n →
        conditioned μ n (finiteTreeEvent fun t =>
          K < |(height t : ℝ) - Real.log n / Real.log (1 / (offspringMean μ).toReal)|)
          ≤ ENNReal.ofReal ε) ↔
      Summable (fun k : ℕ => (k : ℝ) * Real.log k * (μ {k}).toReal)
```

## Theorem 3.1 — unproved, to be frozen after approval

Conditionally on $W_n=-1$, the $n-1$ increments left after deleting the first
maximal one are asymptotically iid in total variation. Mathlib's `tvDist` is
twice the paper's distance; the laws live on $\mathbb Z^{n-1}$, which gives the
same distance as $\mathbb R^{n-1}$.

```lean
theorem paper_deleted_maximum_tvDist (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (fun n : ℕ => tvDist ((MaximumSwapLaw.bridgeCountsLaw μ n).map (deletedIncrements n))
        (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ))
      atTop (𝓝 0)
```

## Lemma 4.4(i) — proved

There is $\ell:(0,1]\to(0,\infty)$, slowly varying at 0, with $\ell(0+)=0$ and
$Q_{n+1}=Q_n(m-\ell(Q_n))$ for all $n\ge0$; it is proved with $\ell$ the actual
survival correction, which also satisfies $\ell(x)\sim\ell^\star(1/x)$.

```lean
theorem paper_survival_correction_lemma
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    ∃ ℓ : ℝ → ℝ, (∀ x : ℝ, 0 < x → x ≤ 1 → 0 < ℓ x) ∧
      (∀ a : ℝ, 0 < a → Tendsto (fun x : ℝ => ℓ (a * x) / ℓ x) (𝓝[>] 0) (𝓝 1)) ∧
      Tendsto ℓ (𝓝[>] 0) (𝓝 0) ∧
      ∀ n : ℕ, (survival μ (n + 1)).toReal =
        (survival μ n).toReal * ((offspringMean μ).toReal - ℓ (survival μ n).toReal)

theorem survivalCorrection_div_ellStarReal_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (hm : offspringMean μ < 1)
    {L : ℝ → ℝ} (hpos : ∀ x : ℝ, 0 < x → 0 < L x)
    (hL : AEMeasurable L (volume.restrict (Set.Ioi 0)))
    (hsv : IsSlowlyVaryingAtTop L)
    (hlocal : Tendsto (fun n : ℕ => (μ {n}).toReal / (L n / (n : ℝ) ^ 2))
      atTop (𝓝 1)) :
    Tendsto (fun x : ℝ => survivalCorrection μ x / ellStarReal L x⁻¹)
      (𝓝[>] 0) (𝓝 1)
```

## Heathcote–Seneta–Vere-Jones criterion (X7) — proved

For every probability law on ℕ with $0<m<1$: $Q_n/m^n$ is antitone, has a
positive limit iff $\sum_kk\log k\,\mu_k<\infty$, and tends to 0 otherwise.

```lean
theorem survival_div_mean_pow_tendsto_pos_iff
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hm1 : offspringMean μ < 1) :
    (∃ c : ℝ, 0 < c ∧ Tendsto
        (fun n : ℕ => (survival μ n).toReal / (offspringMean μ).toReal ^ n)
        atTop (𝓝 c)) ↔
      Summable (fun k : ℕ => (k : ℝ) * Real.log k * (μ {k}).toReal)

theorem survival_div_mean_pow_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm0 : 0 < offspringMean μ) (hm1 : offspringMean μ < 1)
    (h : ¬ Summable (fun k : ℕ => (k : ℝ) * Real.log k * (μ {k}).toReal)) :
    Tendsto (fun n : ℕ => (survival μ n).toReal / (offspringMean μ).toReal ^ n)
      atTop (𝓝 0)
```

## Approval record

| Statement | Decision | Date |
| --- | --- | --- |
| M1–M5 | approved as mathematical statements, measurable convention; no amendment | 10 November 2026 |
| Theorem 3.1 | approved as mathematical statement, measurable convention; no amendment | 10 November 2026 |
| Lemma 4.4(i) and companion | approved; already proved | 10 November 2026 |
| X7 | approved; already proved | 10 November 2026 |

Author's words (10 November 2026): "I approve all four entries in APPROVAL.md
as mathematical statements, under the agreed measurable slow-variation
convention. No mathematical amendments are needed."

**Freeze.** M1–M5 are in `SubcriticalCauchy/MainTheorems.lean` and Theorem 3.1
in `SubcriticalCauchy/Theorem31.lean`, byte for byte as above, each with one
registered `sorry` hole; `FiniteTreeEvent.lean` and `DeletedIncrements.lean`
are frozen whole. Record `~/LeanFormalization/subcauchy-campaign-records/freeze/record-2026-11-10.json`,
SHA-256 `17d303698e15cef424c05529ed17b982d823166f51e7be4c4e03b32b98d45224`,
taken at commit `4a6e84d` (working tree of `da97f3d`); `freeze_check.py check`
passed on `4a6e84d`.

## Second round — Propositions 4.2 and 4.3 (10 November 2026), approved

Draft: `Propositions42_43.lean`. Independent Sonnet
statement audit: pass for all five declarations, no correction needed.

**Proposition 4.2.** For every $\delta\in[0,1-m)$, the first $\lfloor\delta n\rfloor$
subtrees attached to the first maximal-degree vertex of $\mathcal T_n$ converge
in total variation to $\lfloor\delta n\rfloor$ independent Bienaymé trees.
**Convention to approve:** absent slots are padded by the one-vertex tree
`leaf`, since Lean's tree type has no empty tree; the two paddings differ only
on $\{\Delta(\mathcal T_n)<\lfloor\delta n\rfloor\}$, whose probability tends to
0 by M1, so the statements are equivalent.

```lean
def attachedSlotsTree (k : ℕ) (t : PlaneTree) : Fin k → Tree :=
  fun i => ((attachedChild t (i.val + 1)).getD PlaneTree.leaf).toLocallyFinite

def attachedSlotsLaw (μ : Measure ℕ) [IsProbabilityMeasure μ] (n k : ℕ) :
    Measure (Fin k → Tree) :=
  Measure.sum fun t : PlaneTree =>
    conditioned μ n {t.toLocallyFinite} • Measure.dirac (attachedSlotsTree k t)

theorem paper_attached_forest_tvDist (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1 - (offspringMean μ).toReal) :
    Tendsto (fun n : ℕ =>
        tvDist (attachedSlotsLaw μ n ⌊δ * n⌋₊) (forestLaw μ ⌊δ * n⌋₊))
      atTop (𝓝 0)
```

**Proposition 4.3.** For positive $h_n\to\infty$, with $Q_h=\mathbb P(H(\mathcal T)\ge h)=$
`survival μ ⌈h⌉₊`: (i) if $nQ_{h_n}\to\infty$ then $\mathbb P(H(\mathcal T_n)\ge h_n)\to1$;
(ii) if $nQ_{h_n}\to0$ then $\mathbb P(H(\mathcal T_n)<h_n)\to1$.

```lean
theorem paper_height_lower (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (h : ℕ → ℝ)
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop atTop)
    (hQ : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈h n⌉₊).toReal) atTop atTop) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t => h n ≤ (height t : ℝ)))
      atTop (𝓝 1)

theorem paper_height_upper (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (h : ℕ → ℝ)
    (hpos : ∀ n, 0 < h n) (hh : Tendsto h atTop atTop)
    (hQ : Tendsto (fun n : ℕ => (n : ℝ) * (survival μ ⌈h n⌉₊).toReal) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => conditioned μ n (finiteTreeEvent fun t => (height t : ℝ) < h n))
      atTop (𝓝 1)
```

| Statement | Decision | Date |
| --- | --- | --- |
| Proposition 4.2 (with the `leaf` padding) | approved: "Approve both" | 10 Nov 2026 |
| Proposition 4.3(i)–(ii) | approved: "Approve both" | 10 Nov 2026 |

## Third round — (2.4), Corollary 4.1 and Proposition 4.5 (10 November 2026), approved

Drafts: `Corollary41.lean`, `Proposition45.lean`;
both elaborate. Independent Sonnet statement audit: pass for all six
declarations, corrections re-derived. Two statements deliberately **correct**
the paper, each confirmed by an independent derivation (Opus, written without
the candidate answer); see `MANUSCRIPT_RECOMMENDATIONS.md` R9, R10.

**(2.4), corrected (R9).** With exactly $b_n=n\mathbb E[X\mathbf1_{|X|\le a_n}]$,
$(W_n-b_n)/a_n\to\mathcal C_1+(1-\gamma_E)$ in distribution, where
$\mathbb E[e^{-\lambda\mathcal C_1}]=e^{\lambda\log\lambda}$. Also: the law of
$\mathcal C_1$ exists (`exists_cauchyOneLaw`).

**Corollary 4.1, corrected (R9).** $(\Delta(\mathcal T_n)+b_n)/a_n\to-\mathcal C_1-(1-\gamma_E)$.

Encoding: `IsCauchyOneLaw ν` (probability measure with the Laplace values);
statements quantify over every such `ν` and every scale `a`; convergence in
distribution against every bounded continuous `f`; the law of $\mathcal T_n$
as the sum of its atoms.

**Proposition 4.5.** Tail hypothesis on $\mu$: $\mu_n\sim c/(n^2(\log n)^{1+\beta})$.
(i) $\beta=1$: as in the paper, with $\varepsilon\log\log n\le|\cdot|$.
(ii) $0<\beta<1$, **corrected (R10)**: coefficient $c/((1-\beta)\beta m\log(1/m)^2)$
instead of $c/((1-\beta)\beta m\log(1/m)^{1+\beta})$, deviation scale
$\varepsilon(\log n)^{1-\beta}$.

| Statement | Decision | Date |
| --- | --- | --- |
| (2.4) and existence of $\mathcal C_1$, corrected | approved: "Approve all four" | 10 Nov 2026 |
| Corollary 4.1, corrected | approved: "Approve all four" | 10 Nov 2026 |
| Proposition 4.5(i) | approved: "Approve all four" | 10 Nov 2026 |
| Proposition 4.5(ii), corrected | approved: "Approve all four" | 10 Nov 2026 |

## Fourth round — the paper's own proof of Theorem 3.1 (11 November 2026)

Draft: `PaperRoute.lean`, which elaborates. Scope chosen by the
author on 11 November: intermediate generality, and no $\Delta$-subexponentiality
certificate. Independent checks:

- at the author's request, an Astra review (gpt-6-astra, high; `.orchestration/astra-paperroute-statements`) returned `VERDICT: ACCEPT` with no amendment, which made the author's conditional approval effective;
- the Sonnet statement audit and the Sol audit from another model family both pass all five declarations with no correction;
- blind read-backs are in [READBACKS_PAPER_ROUTE.md](READBACKS_PAPER_ROUTE.md);
- research and audit are in [PAPER_R31_RESEARCH.md](../blueprint/PAPER_R31_RESEARCH.md) and [PAPER_R31_AUDIT.md](../blueprint/PAPER_R31_AUDIT.md).

Notation: $\Delta=(0,1]$, $\gamma=1-m$, $\overline X=X+\gamma$, $\overline W_n=W_n+\gamma n$, and $\widehat b_n=n\ell^\star(a_n)$.

**AL criterion** (`al_criterion`), the Armendáriz–Loulakis theorem in the form of
its proof. Let $\nu$ be a probability law on $\mathbb R$ and $d_n,\ell_n,c_n$ real
sequences. Assume:

- $c_n>0$ eventually, and $\ell_n/c_n\to\infty$;
- (2.6) uniformly on $x\ge d_n$;
- (3.2) uniformly on $x\ge\ell_n$ and $|y|\le Ac_n$;
- $S_{n-1}/c_n$ is tight;
- $n\,\nu(\ell_n-Ac_n,\infty)\to0$ for every $A>0$.

Then, uniformly on $x\ge\max(d_n,\ell_n)$, the law of $\pi T X$ given
$S_n\in x+\Delta$ converges in total variation to $\nu^{\otimes(n-1)}$. Here $T$
swaps the first maximum with the last coordinate and $\pi$ drops the last
coordinate. AL's Theorem 1 asserts only that some threshold exists, so its
statement as published is not claimed.

**Berger, Theorem 2.4** (`berger_local_limit`), for the paper's offspring laws and
any scale $a$ with $n\mathbb P(X\ge a_n)\to1$:

$$
\mathbb P(W_n-\lfloor b_n\rfloor=z)\sim n\,\mathbb P(X=z)
$$

jointly as $n\to\infty$ and $z/a_n\to\infty$. The denominator $n\,\mathbb P(X=z)$
replaces Berger's $nL(z)/z^2$; the two are equivalent by local regular variation.

**(2.6) of the paper** (`paper_eq26`). For every $\varepsilon>0$, $\mathbb P(\overline W_n\in x+\Delta)\sim n\,\mathbb P(\overline X\in x+\Delta)$ uniformly in $x\ge\varepsilon n$.

**(3.3) of the paper with its tightness claim** (`paper_eq33`):

- $\overline W_n/\widehat b_n$ is tight;
- $a_n/\widehat b_n\to0$;
- $(b_n+\gamma n)/\widehat b_n\to-1$;
- $\mathbb P(\overline X\in x-y+\Delta)/\mathbb P(\overline X\in x+\Delta)\to1$ uniformly in $x\ge\varepsilon n$ and $|y|\le A\widehat b_n$.

**Theorem 3.1 by the paper's route** (`paper_route_deleted_maximum_tvDist`). This
has the same statement as the frozen `paper_deleted_maximum_tvDist`. It is to be
proved from the four results above, with $d_n=\ell_n=\varepsilon n$,
$c_n=\widehat b_n$ and the corrected window $x=\gamma n-2$ (R8), without the
endpoint route D12.

Recorded adaptations:

- the concentration bound $\sup_k\mathbb P(W_n=k)\le C/a_n$ replaces Gnedenko's local limit theorem;
- a direct Bennett bound replaces Nagaev's inequality and Berger's Prop. 5.2;
- the maximum-tail hypothesis replaces AL (3.8);
- AL's thresholds are supplied directly.

| Statement | Decision | Date |
| --- | --- | --- |
| AL criterion | approved: "Ask astra, if astra is ok i'm ok"; Astra review: VERDICT: ACCEPT | 11 Nov 2026 |
| Berger 2.4, specialized | approved: "Ask astra, if astra is ok i'm ok"; Astra review: VERDICT: ACCEPT | 11 Nov 2026 |
| (2.6) of the paper | approved: "Ask astra, if astra is ok i'm ok"; Astra review: VERDICT: ACCEPT | 11 Nov 2026 |
| (3.3) of the paper, with tightness | approved: "Ask astra, if astra is ok i'm ok"; Astra review: VERDICT: ACCEPT | 11 Nov 2026 |
| Theorem 3.1, paper's route | approved: "Ask astra, if astra is ok i'm ok"; Astra review: VERDICT: ACCEPT | 11 Nov 2026 |

## Fifth round — the five-case classification U2.5, corrected (11 November 2026)

Draft: `Classification.lean`, which elaborates. Source: Section 2.2, lines 215–223.

**Statement.** Let $\nu$ be a probability on $\mathbb N$ with $\nu_0>0$ and $\nu_n\sim L(n)/n^{1+\alpha}$, where $\alpha\ge0$ and $L$ is positive, measurable and slowly varying. Then $\nu$ is Kennedy-equivalent to some probability $\mu$ ($\mu_k=a\lambda^k\nu_k$ with $a,\lambda>0$) that falls in one of five cases:

- (a) critical with finite second moment;
- (b) critical, infinite second moment, $1<\alpha\le2$;
- (c) critical, $\alpha=1$;
- (d) subcritical, $\alpha>1$;
- (e) subcritical, $\alpha=1$.

In (b)–(e), $\mu$ also has the tail $\mu_n\sim L(n)/n^{1+\alpha}$, which forces $\mu=\nu$.

**Correction.** The hypothesis $\nu_0>0$ is added. It is necessary: with $\nu_n=6/(\pi^2n^2)$ for $n\ge1$ and $\nu_0=0$, every tilt has mean $>1$, so $\nu$ is in none of the cases. Given the heavy tail, it is also sufficient.

**Checks.**

- An independent Sonnet audit passed. It recommended the heavy-tail clause in (b)–(e), which is now adopted.
- The blind read-back of the unstrengthened version matched. The strengthening only adds the clause `HasHeavyTail μ α L` to (b)–(e).

| Statement | Decision | Date |
| --- | --- | --- |
| U2.5, corrected | approved: "Approve" | 11 Nov 2026 |
