# Route blueprint: the index-one stable limit

## 0. Scope and decision

This is a research and implementation blueprint for the three frozen holes in
`SubcriticalCauchy/Corollary41.lean`. It does not change any frozen statement and
does not assume a new axiom. All helper declarations are in the namespace
`SubcriticalCauchy.Bienayme` and live only in

- `SubcriticalCauchy/LateProofs/C1Exists.lean`;
- `SubcriticalCauchy/LateProofs/StableLimit.lean`;
- `SubcriticalCauchy/LateProofs/Cor41.lean`.

The dependency direction is `C1Exists -> StableLimit -> Cor41`; in particular,
none of these modules imports `SubcriticalCauchy.Corollary41`.

**Use Laplace transforms, not characteristic functions, for both convergence
proofs.** One-step Laplace asymptotics avoid the complex logarithm of an iid
product and make the lower bound `X >= -1` work for us. Characteristic functions
are needed only to prove uniqueness of `IsCauchyOneLaw`, by analytic continuation
from the negative real axis.

Write

$$
\gamma = \gamma_E, \qquad c = 1-\gamma,
$$

and, for $\lambda>0$ and $x>0$,

$$
K_\lambda(x)=e^{-\lambda x}-1+\lambda x\mathbf 1_{\{x\le1\}}, \qquad
I(\lambda)=\int_0^\infty K_\lambda(x)x^{-2}\,dx.
$$

The normalization identity to prove is

$$
I(\lambda)=\lambda\log\lambda+(\gamma_E-1)\lambda.
\tag{N}
$$

The centered walk has Laplace exponent tending to $I(\lambda)$. Its limit is
therefore $\mathcal C_1+c$, since

$$
\mathbb E e^{-\lambda(\mathcal C_1+c)}
 =\exp(\lambda\log\lambda-c\lambda)
 =\exp I(\lambda).
$$

This is the R9 correction. No additional sign or centering convention is left
open: the centered one-step expectation is **plus** $K_\lambda$.

## 1. Answers to the five questions

### 1. Existence of $\mathcal C_1$, with all negative exponential moments

Choose route **(b), but use a particularly explicit telescoping Pareto law**, not
a compound-Poisson approximation and not a general offspring witness. On
$\mathbb Z$, put mass

$$
p_k=\frac1{k(k+1)}\qquad(k\ge1),
$$

and zero elsewhere. Then $\sum_{k\ge1}p_k=1$ and
$\mathbb P(X\ge N)=1/N$ exactly for $N\ge1$. Take $a_n=n$ and
$b_n=n\mathbb E[X\mathbf1_{X\le n}]$. The same kernel/Fubini argument as for
(2.4), with exact tails instead of slow-variation estimates, gives

$$
n(\mathbb E e^{-\lambda X/n}-1)+\lambda b_n/n\longrightarrow I(\lambda).
$$

The normalized sums have finite $\mathbb Ee^{-\lambda Z_n}$ because $X\ge0$.
Their tightness and the passage of Laplace transforms to weak limits are proved
once, abstractly, from the Laplace limit. Their limit $Q$ has Laplace exponent
$I(\lambda)$, hence $Q$ is the law of $\mathcal C_1+c$. Translating $Q$ by $-c$
constructs a $\nu$ satisfying `IsCauchyOneLaw`. The existence helper and the weak
limit machinery return the `Integrable` clause, not merely the integral value.

This is cheaper than route (a): Mathlib v4.35.0 has Poisson laws, but no
compound-Poisson/Poisson-point-process/Lévy-process construction that would
supply the required law. Route (c) is therefore unavailable; the pinned library
has no ready-made general stable law at index one.

### 2. Uniqueness of the law

Port the analytic-continuation argument of `scratch/bgw-ref/LimitLaw.lean`, with
an attribution comment to that file. For any `IsCauchyOneLaw ν`, all negative
real parameters lie in the interior of `integrableExpSet id ν`. On the left
half-plane $\Re z<0$, the identity theorem gives

$$
\operatorname{complexMGF}(\mathrm{id},\nu,z)
 =\exp((-z)\operatorname{Log}(-z)).
$$

Take the boundary $z=-\varepsilon+it$, $\varepsilon\downarrow0$. Domination by
$1+e^{-x}$ is uniform for $0<\varepsilon<1$, and `complexMGF_id_mul_I` converts
the boundary value to `charFun`. One obtains, with the principal complex log,

$$
\mathbb E e^{it\mathcal C_1}
 =\exp\!\left(-\frac\pi2|t|-it\log|t|\right).
\tag{CF}
$$

`Measure.ext_of_charFun` then proves `cauchyOneLaw_unique`. The related
`Measure.ext_of_complexMGF_id_eq` requires equality of **whole** complex MGFs;
`eqOn_complexMGF_of_mgf'` requires an equality of real MGFs. Those stronger
inputs are not what the frozen predicate directly supplies, so the BGW analytic
route is preferable.

For the shifted law, multiplication by $e^{ict}$ gives the canonical exponent

$$
\psi(t)=\int_0^\infty(e^{itx}-1-itx\mathbf1_{x\le1})x^{-2}\,dx
 =-\frac\pi2|t|-it\log|t|+ict.
$$

### 3. Convergence (2.4)

For fixed $\lambda>0$, the exact one-step identity is

$$
\begin{aligned}
&n(\mathcal L_X(\lambda/a_n)-1)+\lambda b_n/a_n\\
&\qquad=n\mathbb E\left[K_\lambda(X/a_n)
 \mathbf1_{\{X>0\}}\right]
 +n\left(e^{\lambda/a_n}-1-\lambda/a_n\right)
\end{aligned}
$$

eventually, because the only negative increment is $-1$. The last term is
$O(n/a_n^2)\to0$.

For the positive part, **do not develop a new vague-convergence library**.
Integrate the piecewise $C^1$ kernel by parts/Fubini:

$$
n\mathbb E K_\lambda(X/a_n)
 =\int_0^\infty K_\lambda'(u)\,
   n\mathbb P(X\ge u a_n)\,du.
$$

The project tail asymptotic and $a_n\to\infty$ give the pointwise limit
$n\mathbb P(X\ge ua_n)\to1/u$. Potter bounds and the existing truncated second
moment estimate provide a single integrable majorant, including near $u=0$;
$K_\lambda'(u)=O(u)$ there, while the exponential factor controls the far
tail. Dominated convergence identifies the limit as
$\int_0^\infty K_\lambda'(u)u^{-1}du=I(\lambda)$.

The product Laplace transform is

$$
\mathbb E e^{-\lambda(S_n-b_n)/a_n}
 =\mathcal L_X(\lambda/a_n)^n e^{\lambda b_n/a_n}.
$$

Since $n(\mathcal L_X-1)\to I(\lambda)$ and $\mathcal L_X\to1$, the derivative
of $\log$ at $1$ gives $n\log\mathcal L_X\to I(\lambda)$. No characteristic-log
lemma is needed. The abstract Laplace weak-convergence theorem then gives weak
convergence to the shifted law. Finally,
`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` and `integral_map`
produce exactly the frozen bounded-continuous test-function statement.

### 4. Corollary 4.1

Use `paper_deleted_maximum_tvDist` as input **U4.1(a)**; do not reprove it.
Two deterministic lemmas are proved in `Cor41.lean`:

$$
a_{n-1}/a_n\longrightarrow1,\qquad
(b_n-b_{n-1})/a_n\longrightarrow0.
$$

The first follows from the scale normalization, the tail asymptotic, monotonicity
of the tail, and the proved compact-uniform slow variation theorem. For the
second, write $m(r)=\mathbb E[X\mathbf1_{\{|X|\le r\}}]$. The term
$m(a_n)/a_n\to0$ follows from finite mean. The remaining cutoff-shell term is
controlled by $a_n$ times a tail difference, so the factors $a_n$ cancel; the
two scale normalizations show that this tail difference vanishes. Thus neither
an asymptotic expansion of $b_n$ nor a rate for slow variation is needed.

Apply (2.4) at time $n-1$, then the affine reindexing with ratio $a_{n-1}/a_n$
and translation $(b_{n-1}-b_n)/a_n$. Negate the limiting variable. Transfer the
bounded test-function expectations from deleted increments to the conditioned
maximum using the exact bridge identity
$\Delta=-\sum X_i^{\mathrm{deleted}}$. Total variation gives an error at most
$\|f\|_\infty\,d_{TV}(P_n,Q_n)$ for the project's unhalved discrete `tvDist`.
Map contraction (`tvDist_map_le`) handles all statistics at once.

### 5. Worker split

Five nodes below separate analytic normalization, the witness, the general
one-step estimate, iid assembly, and the total-variation corollary. Nodes 1 and 3
are the only mathematically heavy analytic tasks; Node 2 can start after the
abstract interface of Node 1 is frozen.

## 2. Exact implementation interfaces

The Lean snippets below specify names and statements, not proof holes to add now.
Internal elementary lemmas may be private. The declarations listed as exported
are the contracts between worker nodes.

### Node 1 — normalization, uniqueness, and Laplace weak convergence

**Owner:** `LateProofs/C1Exists.lean`. **Dependencies:** none of the other nodes.

```lean
noncomputable def stableKernel (s x : ℝ) : ℝ :=
  Real.exp (-s * x) - 1 + if x ≤ 1 then s * x else 0

noncomputable def stableKernelIntegral (s : ℝ) : ℝ :=
  ∫ x in Set.Ioi 0, stableKernel s x / x ^ 2

theorem stableKernelIntegral_one :
    stableKernelIntegral 1 = Real.eulerMascheroniConstant - 1

theorem stableKernelIntegral_eq {s : ℝ} (hs : 0 < s) :
    stableKernelIntegral s =
      s * Real.log s + (Real.eulerMascheroniConstant - 1) * s

noncomputable def cauchyOneCF (t : ℝ) : ℂ :=
  Complex.exp (-((Real.pi / 2 * |t| : ℝ) : ℂ) -
    (t * Real.log |t| : ℝ) * Complex.I)

theorem charFun_of_isCauchyOneLaw {ν : Measure ℝ} (hν : IsCauchyOneLaw ν) (t : ℝ) :
    charFun ν t = cauchyOneCF t

theorem cauchyOneLaw_unique {ν₁ ν₂ : Measure ℝ}
    (h₁ : IsCauchyOneLaw ν₁) (h₂ : IsCauchyOneLaw ν₂) : ν₁ = ν₂

/-- Existence and identification of a weak limit from negative exponential moments. -/
theorem exists_tendsto_of_exponential_laplace_limit
    (Λ : ℝ → ℝ) (hΛ0 : Λ 0 = 0)
    (hΛcont : ContinuousWithinAt (fun s => Real.exp (Λ s)) (Set.Ioi 0) 0)
    (P : ℕ → ProbabilityMeasure ℝ)
    (hL : ∀ s : ℝ, 0 < s → Tendsto
      (fun n => ∫ x, Real.exp (-s * x) ∂(P n : Measure ℝ)) atTop
      (𝓝 (Real.exp (Λ s)))) :
    ∃ Q : ProbabilityMeasure ℝ, Tendsto P atTop (𝓝 Q) ∧
      ∀ s : ℝ, 0 < s → Integrable (fun x => Real.exp (-s * x)) (Q : Measure ℝ) ∧
        ∫ x, Real.exp (-s * x) ∂(Q : Measure ℝ) = Real.exp (Λ s)
```

Also export the known-limit variant obtained by combining the preceding theorem
with `cauchyOneLaw_unique`; this is the form used by Node 4. Put the generic
kernel/Fubini lemma and the finite-product Laplace identity in this module as
well, so Nodes 2 and 4 do not duplicate them. Node 1's weak-limit proof also
needs the general statement that negative Laplace values on $(0,\infty)$
determine a finite measure; prove it by the same two-sided analytic continuation,
then specialize to `cauchyOneLaw_unique`.

**Mathematical steps.** For `stableKernelIntegral_one`, integrate by parts on
$(0,1)$ and $(1,\infty)$ to obtain

$$
I(1)=-1+\int_0^1\frac{1-e^{-x}}x\,dx-\int_1^\infty\frac{e^{-x}}x\,dx.
$$

Two further integration-by-parts identities identify the sum of the last two
integrals as $-\int_0^\infty e^{-x}\log x\,dx=\gamma_E$. Use
`Real.eulerMascheroniConstant_eq_neg_integral_log`. For arbitrary $\lambda$,
use `integral_comp_mul_left_Ioi` at zero and $\partial I/\partial\lambda=I(\lambda)/\lambda$;
equivalently, differentiate the cutoff primitive $J(r)=I(r)/r$, whose derivative
is exactly $1/r$.

For tightness, retain eventual integrability at $s$ and $2s$ from the nonzero
finite Laplace limits. For a lower-tail bound use

$$
P_n(X<-R)\le e^{-sR}\,\mathbb E_ne^{-sX}.
$$

For an upper-tail bound use

$$
(1-e^{-sR})P_n(X>R)\le1-\mathbb E_ne^{-sX}.
$$

First choose $s$ small using $\exp\Lambda(s)\to1$, then $R$ large, and finally use
convergence in $n$. Discard a finite initial segment and add it back with finite
unions of singleton tight families. Use Prokhorov compactness. Port the truncated
Laplace passage from `LaplaceContinuity.lean`; its error is bounded by
$\mathbb Ee^{-2sX}/(k+1)$, and every subsequential limit is identified by
`cauchyOneLaw_unique` (or the same transform-uniqueness argument after
translation).

**Risk: high-medium.** The improper-integral endpoint bookkeeping and the
analytic continuation are substantial, but the route is isolated from all
project-specific combinatorics.

### Node 2 — explicit telescoping witness and `exists_cauchyOneLaw`

**Owner:** `LateProofs/C1Exists.lean`. **Dependencies:** Node 1.

```lean
/-- Concrete law supported on positive integers, with mass 1/(k(k+1)) at k. -/
noncomputable def telescopingParetoLaw : Measure ℤ

instance : IsProbabilityMeasure telescopingParetoLaw

theorem telescopingPareto_tail (N : ℕ) (hN : 1 ≤ N) :
    (telescopingParetoLaw {z : ℤ | (N : ℤ) ≤ z}).toReal = 1 / (N : ℝ)

/-- Its normalized centered sums supply the shifted index-one law. -/
theorem exists_shifted_cauchyOneLaw :
    ∃ Q : ProbabilityMeasure ℝ,
      (∀ s : ℝ, 0 < s → Integrable (fun x => Real.exp (-s * x)) (Q : Measure ℝ) ∧
        ∫ x, Real.exp (-s * x) ∂(Q : Measure ℝ) =
          Real.exp (s * Real.log s +
            (Real.eulerMascheroniConstant - 1) * s))

theorem cauchyOneLaw_exists : ∃ ν : Measure ℝ, IsCauchyOneLaw ν
```

The frozen hole is filled by `cauchyOneLaw_exists`. Translate the `Q` from
`exists_shifted_cauchyOneLaw` by `x ↦ x - (1-γ_E)` and use `integral_map`; the
integrability clause follows from the corresponding clause for `Q`.

**Mathematical steps.** Use the exact telescoping sum already familiar from
`incrementTelescopeSq`; no zeta normalization and no finite first moment is
needed. Prove the one-step kernel limit by the same Fubini lemma as Node 3, but
with the exact tail. The norming is $a_n=n$. Node 1 supplies the weak limit and
all its negative exponential moments.

**Risk: medium.** Most work is discrete tail/integral bookkeeping. Sharing the
kernel-integration lemma with Node 3 is essential to avoid two analytic proofs.

### Node 3 — the project one-step Laplace exponent

**Owner:** `LateProofs/StableLimit.lean`. **Dependencies:** Node 1 for the kernel
normalization; project tail, Potter, and centering modules.

```lean
theorem rescaled_incrementTail_tendsto
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (u * a n)).toReal)
      atTop (𝓝 (1 / u))

theorem oneStep_increment_laplace_exponent_tendsto
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      ∫ k, (Real.exp (-(s / a n) * offspringIncrement k) - 1 +
        (s / a n) * (if |offspringIncrement k| ≤ a n
          then offspringIncrement k else 0)) ∂μ)
      atTop (𝓝 (stableKernelIntegral s))
```

The second statement is the central analytic contract. Prove the equivalent form
with `n * (oneStepLaplace - 1) + s * centering / a` as an algebraic corollary.

For the majorant, use `scaling_tendsto_atTop`,
`incrementTail_div_tendsto_one`, `scaling_div_mul_tendsto_one`,
`slowlyVarying_uniform_compact_tail`, and `truncated_second_moment_cutoff`.
The last lemma supplies the small-$u$ domination after multiplication by
$n/a_n^2$; no proof of the exact asymptotic constant of the truncated second
moment is necessary.

**Risk: high.** The delicate points are strict versus non-strict increment tails,
real-to-natural floor conversions, and a genuinely uniform integrable majorant
near $u=0$. Do not silently assume monotonicity of $L$ or a finite second moment.

### Node 4 — iid products and the frozen (2.4) interface

**Owner:** `LateProofs/StableLimit.lean`. **Dependencies:** Nodes 1 and 3.

```lean
noncomputable def normalizedIncrementLaw
    (μ : Measure ℕ) [IsProbabilityMeasure μ] (a : ℕ → ℝ) (n : ℕ) :
    ProbabilityMeasure ℝ :=
  ⟨(Measure.pi fun _ : Fin n => incrementLaw μ).map (fun x =>
      (((∑ i, x i : ℤ) : ℝ) - centering μ a n) / a n), inferInstance⟩

theorem normalizedIncrementLaw_laplace_tendsto
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n => ∫ y, Real.exp (-s * y) ∂(normalizedIncrementLaw μ a n))
      atTop (𝓝 (Real.exp (s * Real.log s +
        (Real.eulerMascheroniConstant - 1) * s)))

theorem stable_limit_test (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1))
    (ν : Measure ℝ) (hν : IsCauchyOneLaw ν) (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n : ℕ => ∫ x, f (((∑ i, (x i : ℝ)) - centering μ a n) / a n)
        ∂(Measure.pi fun _ : Fin n => incrementLaw μ))
      atTop (𝓝 (∫ y, f (y + (1 - Real.eulerMascheroniConstant)) ∂ν))
```

The frozen `paper_stable_limit` is exactly `stable_limit_test`.

Use the generic finite-product Laplace identity from Node 1 on the offspring
product, then transport it with `pi_incrementLaw_eq_map`. `Measure.pi_map_pi`,
`integral_prod_mul`, and induction on `Fin n` are sufficient; another option is
to adapt only the short convolution induction in `TransformConvergence.lean`.
Use `Real.exp_log` and the derivative of `Real.log` at one for the power step.

**Risk: medium-low.** The mathematics is now routine; most effort is coercions
between `ℤ`, `ℝ`, finite products, and mapped `ProbabilityMeasure`s.

### Node 5 — deterministic reindexing and Corollary 4.1

**Owner:** `LateProofs/Cor41.lean`. **Dependencies:** Node 4 and U4.1(a).

```lean
theorem scaling_pred_div_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => a (n - 1) / a n) atTop (𝓝 1)

theorem centering_pred_sub_div_tendsto_zero
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ =>
      (centering μ a n - centering μ a (n - 1)) / a n) atTop (𝓝 0)

theorem bounded_integral_sub_le_tvDist
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {g : α → ℝ} (hg : ∀ x, |g x| ≤ 1) :
    |∫ x, g x ∂P - ∫ x, g x ∂Q| ≤ tvDist P Q

theorem maxDegree_fluctuations_test (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) (a : ℕ → ℝ)
    (ha : Tendsto (fun n : ℕ => (n : ℝ) * (incrementTail μ (a n)).toReal)
      atTop (𝓝 1))
    (ν : Measure ℝ) (hν : IsCauchyOneLaw ν) (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun n : ℕ => ∑' t : PlaneTree, (conditioned μ n {t.toLocallyFinite}).toReal *
        f (((maxDegree t : ℝ) + centering μ a n) / a n))
      atTop (𝓝 (∫ y, f (-y - (1 - Real.eulerMascheroniConstant)) ∂ν))
```

The frozen `paper_maxDegree_fluctuations` is exactly
`maxDegree_fluctuations_test`.

For exact coding, use `conditioned_maxDegree_event` to identify the one-dimensional
maximum law with the bridge maximum, then
`maxDegree_eq_deletedIncrements_sum` to replace its negative by the deleted sum.
`conditionedPlaneTreeLaw` in `PropProofs/P42Aux.lean` is available if packaging
the frozen atomic sum as a Bochner integral is convenient; importing that helper
does not import either frozen proposition file. Use `integral_countable` and
`integral_sum_measure` for the sum/integral conversion.

For reindexing, either package everything as `TendstoInDistribution` and apply
`TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`, or
prove the two-line affine estimate directly on weak laws. The latter avoids
constructing an artificial common probability space.

**Risk: medium.** The mathematical content is standard, but exact conditioned
atoms and `n-1` coercions are error-prone. U4.1(a) remains an external dependency,
not a new hypothesis of the frozen theorem.

## 3. Reuse decisions for `scratch/bgw-ref/`

All ported material must carry an attribution comment naming the BGW source file
and its Apache-2.0 provenance. No Lake dependency is introduced.

| BGW file | Decision | Reason |
| --- | --- | --- |
| `LimitLaw.lean` | **Port and adapt** `Iio_subset_interior_integrableExpSet`, half-plane identity, boundary convergence, and `limitLaw_unique`; replace principal power by `(-z) * Complex.log (-z)`. | This is exactly the uniqueness/analytic continuation needed at index one. No density or integrability of the CF is needed. |
| `LaplaceContinuity.lean` | **Port** `truncExp`, `exp_sub_trunc_le`, and the weak-limit Laplace passage; **re-prove tightness** using the two Laplace tail bounds above. | Its mean-zero/first-moment tightness is false as an assumption at index one. |
| `TransformConvergence.lean` | **Re-prove the small product identity**, optionally adapting the induction; do not port convergence of types. | Only finite iid products and affine scaling are needed. |
| `LaplaceExpansion.lean` | **Do not port; re-prove index-one kernel asymptotics.** Reuse the useful exponential/Taylor inequalities only if they match exactly. | Its $\theta>1$ Karamata/second-moment route and $\lambda^\theta$ target are not the index-one normalization. |
| `KaramataTransforms.lean` | **Do not port.** | Project tail asymptotics plus one Fubini/kernel argument is shorter and avoids unneeded general Laplace–Karamata machinery. |
| `TailTransfer.lean` | **Do not port.** | `incrementTail_div_tendsto_one` already supplies the project tail transfer. |
| `StableDomainTail.lean` | **Do not port.** | The telescoping Pareto witness has an exact tail, so no domain criterion is required. |
| `StableLawWitness.lean` | **Re-prove a simpler witness.** | Its normalized zeta/Pareto construction assumes $1<\theta$ and criticality; mass $1/(k(k+1))$ is substantially cheaper at index one. |
| `StableLaw.lean`, `Defs.lean`, `RealAttraction.lean` | **Do not port.** Reuse only local packaging patterns. | Densities, convolution semigroups, and stable-attraction predicates are outside the frozen targets. |

## 4. Verified Mathlib and project API

Small scratch probes were run with `lake env lean` against the pinned Mathlib;
no `import Mathlib` umbrella was used. The following names and hypothesis shapes
were confirmed:

- `ProbabilityMeasure.tendsto_iff_tendsto_charFun` and
  `ProbabilityMeasure.tendsto_of_tendsto_charFun` require a known limit law;
- `isTightMeasureSet_of_tendsto_charFun` takes continuity of the candidate at
  zero and pointwise CF convergence;
- `isCompact_closure_of_isTightMeasureSet` has exactly the tightness interface
  used in Node 1;
- `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` is the frozen real
  bounded-continuous test-function form;
- `Measure.ext_of_charFun`, `Measure.ext_of_complexMGF_id_eq`,
  `eqOn_complexMGF_of_mgf'`, `analyticOnNhd_complexMGF`,
  `complexMGF_id_mul_I`, and `charFun_map_sum_pi_eq_prod` were checked;
- `continuousAt_clog`, `ContinuousAt.clog`, `Complex.log_neg_I`, and
  `Complex.log_ofReal_mul` support the index-one continuation;
- `integral_comp_mul_left_Ioi` and `integral_comp_mul_left_Ioi'` support (N);
- `Real.eulerMascheroniConstant_eq_neg_integral_log` and
  `Real.deriv_Gamma_one_eq_integral_log` are available;
- `MeasureTheory.integral_map`, `Measure.pi_map_pi`, `Measure.map_map`,
  `integral_prod_mul`, `integral_countable`, and `integral_sum_measure` were
  checked;
- `BoundedContinuousFunction.integrable` needs a finite measure and the usual
  Borel/second-countable hypotheses;
- `TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const` is
  available for affine reindexing, though the direct weak-law route is shorter.

Project inspection additionally confirms the exact interfaces
`incrementTail_div_tendsto_one`, `scaling_tendsto_atTop`,
`scaling_div_mul_tendsto_one`, `slowlyVarying_uniform_compact_tail`,
`truncated_second_moment_cutoff`, `paper_deleted_maximum_tvDist`,
`pi_incrementLaw_eq_map`, `maxDegree_eq_deletedIncrements_sum`,
`conditioned_maxDegree_event`, `tvDist_map_le`, and `tvDist_eq_tsum_abs`.

## 5. Integration order and remaining risks

1. Implement Node 1 and compile `LateProofs/C1Exists.lean`; check the axiom list
   of `cauchyOneLaw_unique` and `exists_tendsto_of_exponential_laplace_limit`.
2. Implement Node 2 and fill only `exists_cauchyOneLaw`; run the integration
   freeze check.
3. Implement Nodes 3–4, fill only `paper_stable_limit`, and validate the frozen
   statement file and its consumers.
4. Implement Node 5 after U4.1(a) is available, fill only
   `paper_maxDegree_fluctuations`, then run the full build, axiom checks, and all
   three freeze records.

The principal residual risk is the dominated-kernel majorant in Node 3, not the
stable-law normalization. The normalization signs are fixed by (N) and the exact
one-step identity above. The other unresolved operational dependency is U4.1(a);
it is deliberately not duplicated here. No mathematical gap requiring a new
axiom or a weaker statement has been identified.
