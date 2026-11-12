# Research — the paper's own proof of Theorem 3.1 (11 November 2026)

Produced by a read-only research worker (gpt-6-astra, high; task `.orchestration/paper-r31-research`). Not yet independently audited. Not proof evidence.

I recommend an **abstract unit-window Armendáriz–Loulakis criterion, plus Berger’s full joint limit specialized to this offspring model**. This preserves the manuscript’s proof structure while avoiding general stable densities and a full Gnedenko local limit theorem.

I checked arXiv:0912.1516v4 and arXiv:1706.07924v4, the manuscript, report, and relevant Lean declarations. This is a research blueprint, not an independent approval or fresh compilation certificate. No files were changed, builds run, or agents launched.

**1. Exact source statements and proof structure**

Write $H(x)=\nu(x+\Delta)$, $H_n(x)=\nu^{*n}(x+\Delta)$.

For Armendáriz–Loulakis, $\nu$ is a probability measure on $\mathbb R$, $\Delta=(0,s]$, $s>0$, also allowing $(0,\infty)$. Their $\Delta$-subexponentiality means eventual positivity of $H$ and

$$
\forall y\in\mathbb R,\quad H(x+y)/H(x)\to1,
\qquad
\forall r\ge1,\quad H_r(x)/(rH(x))\to1.
$$

Their conditions are

$$
\tag{2.6}
\sup_{x\ge d_n}\left|H_n(x)/(nH(x))-1\right|\to0,
$$

$$
\tag{3.2}
\forall A>0,\quad
\sup_{x\ge\ell_n,\ |y|\le Ac_n}
\left(1-H(x-y)/H(x)\right)\to0,
$$

$$
\tag{3.3}
\forall A>0,\quad
\sup_{x\ge m_n,\ -Ac_n\le y\le c_n}
\left|H(x-y)/H(x)-1\right|\to0.
$$

Here $c_n\to\infty$, $S_{n-1}/c_n$ is tight, and $\ell_n/c_n\to\infty$. Theorem 1 asserts existence of $q_n$ with

$$
\sup_{x\ge q_n}\sup_{A\in\mathcal B(\mathbb R^{n-1})}
\left|
\mathcal L(\pi T(X)\mid S_n\in x+\Delta)(A)-\nu^{\otimes(n-1)}(A)
\right|\to0.
$$

$T$ swaps the **first maximum** with the last coordinate; $\pi$ drops the last coordinate. The proof permits $q_n=\max(d_n,\ell_n)$.

Proof: construct translation thresholds; use permutation invariance to obtain a lower bound valid with ties; integrate over a typical residual set; apply the same inequality to complements; control residual sums by tightness and maxima by their tail estimate (3.8). See [§2, pp. 2–3; §3, pp. 5–7](https://arxiv.org/pdf/0912.1516v4).

For Berger, the standing assumptions are integer iid increments, $0<\alpha<2$, slowly varying $L$, $p,q\ge0$, $p+q=1$, and

$$
\tag{1.1}
\mathbb P(|X|>t)\sim L(t)t^{-\alpha},\quad
\mathbb P(X>t)\sim pL(t)t^{-\alpha},\quad
\mathbb P(X<-t)\sim qL(t)t^{-\alpha}.
$$

Zero coefficients mean little-$o$. Choose $a_n$ with $nL(a_n)a_n^{-\alpha}\to1$, and

$$
b_n=
\begin{cases}
0,&\alpha<1,\\
n\mathbb E[X\mathbf1_{\{|X|\le a_n\}}],&\alpha=1,\\
n\mathbb E[X],&\alpha>1.
\end{cases}
$$

Theorem 2.4: the bound $\mathbb P(X=k)\le C_1L(k)(1+k)^{-1-\alpha}$ implies

$$
\mathbb P(S_n-\lfloor b_n\rfloor=z)\le CnL(z)z^{-1-\alpha}
\qquad(z\ge a_n).
$$

The stronger assumption

$$
\tag{2.7}
\mathbb P(X=k)\sim p\alpha L(k)k^{-1-\alpha}
$$

implies

$$
\frac{\mathbb P(S_n-\lfloor b_n\rfloor=z)}
     {nL(z)z^{-1-\alpha}}\to p\alpha
\quad\text{jointly as }n\to\infty,\ z/a_n\to\infty.
$$

There are reflected left-tail versions.

Proof: partition according to the maximum; estimate large maxima by local masses, intermediate maxima by tightness, and small maxima by local Fuk–Nagaev plus dyadic decomposition; obtain the lower bound from one distinguished large jump. See [§1.1, pp. 1–2; §2.2, p. 4; §§5–6, pp. 11–18](https://arxiv.org/pdf/1706.07924v4).

**2. Ingredients and their present status**

The following separates source-proof requirements from proposed replacements.

| Ingredient | Project status and implementation consequence |
|---|---|
| Fixed-$r$ convolution asymptotics | Not supplied by the growing-$n$ endpoint theorem. Prove separately by endpoint/middle splitting and induction. **Substantial.** |
| Uniform translation ratios | Available: `paper_unitWindow_uniform_additive_window`, `paper_centeredUnitWindow_uniform_additive_window`. **Routine wrappers.** |
| AL permutation inequality, including ties | Existing combinatorics helps; the generic conditional-window inequality is new. **Substantial.** |
| AL residual-sum tightness | Stable limit available; converting it to the required tail formulation is straightforward measure-theoretic work. **Substantial.** |
| AL maximum-tail control | General deduction (3.8) from tightness is not established here. For centered integrable increments and linear thresholds, finite-mean tail bounds suffice. Existing `finitePreviousMaximumAverage_deviation_tendsto_zero` helps. **Routine/substantial.** |
| Tail regular variation and scale normalization | Available: `incrementTail_div_tendsto_one`, `exists_scaling`, `scaling_div_mul_tendsto_one`. Strict/non-strict bridges also exist in `StableOneStepTail.lean`. |
| Stable convergence and predecessor corrections | Available: `paper_stable_limit`, `scaling_pred_div_tendsto_one`, `centering_pred_sub_div_tendsto_zero`. Only tightness is needed. |
| Potter bounds; truncated second moments | Available: `potter_bounds`, `truncated_second_moment_le`. |
| Scale comparison between $n$ and $\lfloor n/2\rfloor$; corresponding centering comparison | Predecessor results exist; block comparisons need new lemmas. **Substantial.** |
| Gnedenko local limit theorem and bounded stable density | Absent from the project; my focused Mathlib search found no ready theorem. Full development would be **hard**. |
| Sharp concentration $\sup_k\mathbb P(W_n=k)\le C/a_n$ | Absent. `lattice_concentration` gives only $C/(nL(n)^2)$ for comparable block sizes. Upgrade the existing Fourier argument. **Hard**, but much smaller than a full LLT. |
| Fuk–Nagaev at arbitrary $a_n\ll z$, cutoff $y$ | Existing `truncated_exponential_bound` handles fixed linear deviations/cutoffs, not this regime. Its MGF machinery is reusable. **Hard.** |
| Local Fuk–Nagaev | New block-splitting argument using sharp concentration. **Substantial.** |
| Dyadic small-maximum decomposition | New finite-sum/combinatorial estimates and summable majorants. **Substantial.** |
| Uniform integrability | Neither selected theorem needs it as a separate hypothesis. The AL complement argument avoids an $L^1$ density-convergence detour. Stable convergence supplies tightness, not uniform integrability. |

Berger’s general Fuk–Nagaev derivation also uses positive/negative decomposition, truncated-mean comparisons, and exponential estimates for downward deviations. For $X\ge-1$, a direct truncated-MGF proof can remove that machinery while retaining his maximum decomposition.

**3. Generality choices**

These sizes are planning estimates, not measured implementation costs.

| Choice | Encoding and extra infrastructure | Estimated new lemmas; risks |
|---|---|---|
| **(a) Published generality** | `Measure ℝ`, arbitrary finite/infinite $\Delta$, general subexponentiality; integer Berger for every $\alpha\in(0,2)$ and both tails. General threshold selection, tightness-to-tail theorem, stable attraction/concentration for all indices, general Fuk–Nagaev. | Roughly **200–400+**, many hard. Broad scope, normalization and lattice issues; substantial work irrelevant to this manuscript. |
| **(b) Entirely paper-specific** | All statements parameterized by `μ : Measure ℕ` and `IsMeasurableSubcriticalCauchyOffspring μ`; centered unit windows and linear thresholds. | Roughly **60–110**, including two hard analytic components. Lowest cost, but AL becomes difficult to distinguish from its application. |
| **(c) Recommended intermediate** | A reusable AL criterion for centered integrable real laws, unit windows, linear thresholds; Berger’s **full joint limit**, specialized to the paper’s offspring laws. | Roughly **80–140**. Clear theorem/application separation; no stable density required. |

For (c), explicitly record two adaptations: replace Gnedenko by a direct proof of its concentration consequence; replace AL’s general maximum-tail argument by the finite-mean argument. The manuscript’s central sequence remains Berger → (2.6), Lemma 2.2/stable tightness → (3.3), then AL.

**4. Dependency graph and precise proposed nodes**

Fix one witness $L$ throughout. Put

$$
p(k)=\mathbb P(X=k),\quad
\gamma=1-m,\quad
m_n=b_n+\gamma n,\quad
c_n=\widehat b_n=n\ell^\star(a_n).
$$

All ordinary sequence limits use `atTop`. Define the joint filter

$$
\mathcal J_a=
\{(n,z)\in\mathbb N\times\mathbb Z:
n\to\infty,\ z/a_n\to\infty\}.
$$

Concretely, a uniform joint conclusion means: for every tolerance $\tau>0$, there exist $N,R>0$ such that it holds whenever $n\ge N$ and $z\ge Ra_n$.

The graph is

```text
A ──► B
A ──► C
A ──► D ──► E
C,D,E ──► F ──► G
A,D ──► H
G,A ──► I ──► J
H,A ──► K
B,H,J,K ──► L ──► M
```

**A. Model and scale bridges — routine/substantial.**

From the accepted hypothesis and any scale satisfying

$$
n\mathbb P(X\ge a_n)\to1,
$$

prove/use $a_n\to\infty$, $a_n/n\to0$, $nL(a_n)/a_n\to1$, $p(k)\sim L(k)/k^2$, eventual positive masses, and the strict-tail equivalents.

Inputs: `exists_scaling`, `scaling_tendsto_atTop`, `scaling_div_nat_tendsto_zero`, `scaling_div_mul_tendsto_one`, `eventually_mass_pos`, local-mass lemmas. Do not independently choose incompatible existential witnesses from the two Lemma 2.2 exports.

**B. Unit-window subexponentiality — substantial.**

For $\nu=\mathcal L(X+\gamma)$, prove eventual $H(x)>0$ and

$$
\forall h\in\mathbb R,\quad H(x+h)/H(x)\to1,
\qquad
\forall r\ge1,\quad H_r(x)/(rH(x))\to1
\quad(x\to\infty).
$$

First establish fixed-$r$ convolution asymptotics for nonnegative offspring counts. Split convolution sums into two endpoint regions and a middle region; control the latter by Potter bounds and summable tails. Induct in $r$, then handle the fixed lattice offsets. Existing window-ratio lemmas supply translation invariance.

**C. Sharp concentration — hard.**

Prove

$$
\exists C>0,N,\ \forall n\ge N,\ \forall k\in\mathbb Z,\quad
\mathbb P(W_n=k)\le C/a_n.
$$

Prefer also the block version, uniform for $n/3\le j\le2n/3$, with denominator $a_n$.

Use `iid_lattice_inversion_bound`, `lattice_small_frequency`, and `offspring_lattice_spectral_gap`. Split frequencies at $1/a_n$ and a fixed small constant. Potter bounds give, for $1/a_n\le |t|\le t_0$,

$$
n|t|L(1/|t|)\ge c(a_n|t|)^{1-\eta},
\qquad 0<\eta<1.
$$

Integrating the resulting exponential gives $O(1/a_n)$. The smallest-frequency interval has that length; the remaining interval has geometric decay. This is a proposed proof, not an existing theorem.

**D. Tightness and block centering — substantial.**

Establish

$$
\forall\tau>0,\ \exists K,N,\ \forall n\ge N,\quad
\mathbb P(|W_{n-1}-\lfloor b_n\rfloor|>Ka_n)
+\mathbb P(M_{n-1}>Ka_n)<\tau.
$$

The sum term follows from the corrected stable limit and predecessor corrections. For maxima use the union bound and Potter estimates; a Fréchet limit is unnecessary.

For $j=\lfloor n/2\rfloor,\lceil n/2\rceil$, also prove $a_j\asymp a_n$ and

$$
|b_j-(j/n)b_n|\le Ca_n
$$

eventually. Derive scale comparison by monotone tail inversion and centering comparison from truncated-mean differences.

**E. Restricted Fuk–Nagaev — hard.**

A sufficient target is: some $c,K>0,N$ satisfy, for all $n\ge N$ and real $z,y$,

$$
z\ge Ka_n,\quad a_n\le y\le z
\quad\Longrightarrow\quad
\mathbb P(W_n-b_n\ge z,\ M_n\le y)
\le
e^{z/y}\left(1+\frac{cz}{nL(y)}\right)^{-z/(2y)}.
$$

Use exponential Markov and a Bennett-type truncated-MGF estimate. The required centering bound is

$$
n\big(\mathbb E[X\mathbf1_{X\le y}]
-\mathbb E[X\mathbf1_{X\le a_n}]\big)\le z/2
$$

uniformly over this range after increasing $K$. Potter bounds prove it. Reuse `truncated_mgf_le`, second-moment bounds, and iid product integration; the existing final linear-scale theorem is insufficient.

**F. Small maxima are negligible — substantial/hard.**

Prove the quantified statement

$$
\forall\tau>0,\ \exists\delta\in(0,1/2),N,R,\ 
\forall n\ge N,\ z\in\mathbb Z,\ z\ge Ra_n,
$$

$$
\mathbb P(W_n-\lfloor b_n\rfloor=z,\ M_n\le\delta z)
\le\tau\,nL(z)/z^2.
$$

First handle $M_n\le Aa_n$, for fixed sufficiently large $A$, by splitting into two blocks, applying C to one block and E to the other. The bound decays faster than any power of $z/a_n$.

For $Aa_n<M_n\le\delta z$, partition into dyadic bands. Expose one maximal coordinate, use local-mass bounds, then E on the residual sum. A summable majorant has the form

$$
C2^{(3+\eta)j}e^{C2^j}(1+c2^j)^{-c'2^j}.
$$

Its tail tends to zero as $\delta\downarrow0$. Make floor/ceiling endpoints explicit.

**G. Specialized Berger theorem — substantial assembly.**

Prove

$$
\frac{\mathbb P(W_n-\lfloor b_n\rfloor=z)}
     {nL(z)/z^2}\longrightarrow1
\quad\text{along }\mathcal J_a.
$$

For the upper bound split maxima into $\ge(1-\delta)z$, intermediate, and $\le\delta z$. Use uniform local masses, D, and F respectively. For the lower bound require one jump near $z$, residual centered sum within $\delta z$, and all residual jumps below $z/2$; these distinguished-jump events are disjoint.

No endpoint conditional theorem may enter this proof.

**H. The manuscript’s tightness scale — routine/substantial.**

Prove eventual positivity and

$$
c_n\to\infty,\quad c_n/n\to0,\quad
a_n/c_n\to0,\quad m_n/c_n\to-1.
$$

Inputs: `paper_integratedTail_properties`, `centering_shift_ratio_tendsto_one`, `paper_centering_asymptotics`, and A. Then

$$
\frac{\overline W_n}{c_n}
=
\frac{W_n-b_n}{a_n}\frac{a_n}{c_n}
+\frac{m_n}{c_n}
\longrightarrow-1
\quad\text{in probability}.
$$

Use stable tightness times a vanishing scalar. Also establish tightness of $\overline W_{n-1}/c_n$, as AL requires. Modify finitely many $c_n$ to positive values if necessary.

**I. Lattice conversion and `eq:ber` — substantial.**

For every $\varepsilon>0$, uniformly over $x\ge\varepsilon n$, set

$$
k_n(x)=\lfloor x-\gamma n\rfloor+1,\qquad
z_n(x)=k_n(x)-\lfloor b_n\rfloor.
$$

The numerator is exactly $\mathbb P(W_n=k_n(x))$, and

$$
z_n(x)=x-m_n+O(1)
$$

with an absolute uniform rounding bound. `paper_centering_uniform_windows` and A imply uniform divergence of $z_n(x)/a_n$.

Apply G, then compare its denominator with $p(\lfloor x-m_n\rfloor+1)$ using local regular variation. This proves `eq:ber`; it is not a literal substitution into Berger.

**J. Shift comparison and (2.6) — routine.**

For every $\varepsilon>0$, prove uniformly over $x\ge\varepsilon n$,

$$
\frac{\mathbb P(X\in(x-m_n,x-m_n+1])}
     {\mathbb P(X\in(x-\gamma,x-\gamma+1])}\to1.
$$

Apply `paper_unitWindow_uniform_additive_window` with displacement $\gamma-m_n=o(n)$. Multiply with I to obtain `eq:26`, equivalently

$$
\sup_{x\ge\varepsilon n}
\left|\frac{\mathbb P(\overline W_n\in(x,x+1])}
{n\mathbb P(\overline X\in(x,x+1])}-1\right|\to0.
$$

**K. `eq:33` — routine.**

For every $\varepsilon,A,\tau>0$, eventually for every $x,y\in\mathbb R$,

$$
x\ge\varepsilon n,\ |y|\le Ac_n
\Longrightarrow
\left|
\frac{\mathbb P(\overline X\in(x-y,x-y+1])}
{\mathbb P(\overline X\in(x,x+1])}-1
\right|<\tau.
$$

Use `paper_centeredUnitWindow_uniform_additive_window` with width $Ac_n=o(n)$. This supplies both the asymmetric (3.3) and one-sided (3.2).

**L. AL criterion — substantial.**

For any centered integrable real probability law $\nu$, positive $c_n\to\infty$ with $c_n/n\to0$, tight $S_{n-1}/c_n$, and J/K at every positive linear threshold, prove uniform swap/projection TV convergence.

On

$$
G=\{|S_{n-1}|<Ac_n,\ M_{n-1}\le x-Ac_n\},
$$

derive the conditional lower bound by exchangeability and integrate the window mass. Apply it to complements. For each fixed $A$, finite mean gives uniform negligibility of the maximum event above $\varepsilon n-Ac_n$; then let $A\to\infty$.

Retain B as a separate export establishing that this is an application within the cited theorem’s class.

**M. Corrected final application — routine/substantial.**

Choose $0<\varepsilon<\gamma$ and $x_n=\gamma n-2$. Existing `corrected_window_eventually_ge` and `finiteWalk_centered_window` give

$$
x_n\ge\varepsilon n\ \text{eventually},\qquad
\{\overline W_n\in(x_n,x_n+1]\}=\{W_n=-1\}.
$$

Translate residual coordinates back, transfer between lattice and real laws, and use `MaximumSwapLaw.map_swap_take_eq_map_delete`, including ties. Account for Mathlib’s factor-two TV normalization.

**5. Six declarations for approval**

These are schematic signatures, not elaborated code. Define their predicates by the exact mathematical clauses above:

- `Model μ L`: the existing measurable offspring hypothesis with witness $L$ exposed.
- `Scale μ a`: $n\,\texttt{incrementTail}(a_n)\to1$.
- `UnitSubexponential`: B.
- `LinearOB` and `LinearShift`: J and K.
- `ScaledTight`: the quantified eventual tail-tightness statement.
- `UniformSwapTV`: L’s conclusion using actual normalized restrictions and measurable maps.

```lean
theorem paper_unit_subexponential
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    UnitSubexponential (centeredIncrementLaw μ)

theorem berger24_cauchy_joint
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hL : Model μ L) (ha : Scale μ a) :
    Tendsto
      (fun nz : ℕ × ℤ =>
        (incrementSumLaw μ nz.1
          {nz.2 + Int.floor (centering μ a nz.1)}).toReal /
        ((nz.1 : ℝ) * L nz.2 / (nz.2 : ℝ)^2))
      (jointLargeDeviationFilter a) (𝓝 1)

theorem al_unit_linear
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ x, x ∂ν = 0)
    (hsub : UnitSubexponential ν)
    (hc : PositiveDivergentSublinear c)
    (htight : ScaledTight (previousSumLaw ν) c)
    (h26 : LinearOB ν) (h33 : LinearShift ν c) :
    UniformSwapTV ν

theorem paper_AL26
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    LinearOB (centeredIncrementLaw μ)

theorem paper_AL33_and_tightness
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hL : Model μ L) (ha : Scale μ a) :
    let c := fun n => (n : ℝ) * ellStarReal L (a n)
    ScaledTight (previousSumLaw (centeredIncrementLaw μ)) c ∧
      LinearShift (centeredIncrementLaw μ) c
```

The final declaration must preserve the frozen type exactly:

```lean
theorem paper_route_deleted_maximum_tvDist
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (fun n : ℕ =>
      tvDist
        ((MaximumSwapLaw.bridgeCountsLaw μ n).map
          (deletedIncrements n))
        (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ))
      atTop (𝓝 0)
```

Place the new route in separate modules imported by the root. Avoid importing it back into the existing endpoint provider: stable-limit modules already import downstream helpers, so that arrangement could create cycles. Audit actual proof dependencies for use of the old endpoint theorem.

**6. Risks and findings requiring review**

- **Confirmed manuscript issue:** R8’s corrected $x=\gamma n-2$ is necessary. The manuscript’s suggested single Berger value $z=-\lfloor b_n\rfloor-1$ handles only the endpoint, not the asserted uniform range.
- **Lattice span:** Berger’s displayed Gnedenko formula (1.4) requires span-one handling absent from its stated setup. An even-supported law illustrates the problem. Positive local asymptotics in our setting imply eventual consecutive positive atoms, so the application is safe.
- **Auxiliary formula issue:** Berger’s Claim 5.3 (5.6), as printed, fails for $L=1$: it bounds $\log(v/u)$ by $C(u/v)^\delta$. Prove the needed corrected Potter estimate directly. This is a checked mathematical observation, **not an independently reviewed erratum**. [Claim 5.3, p. 14](https://arxiv.org/html/1706.07924v4#S5.SS3)
- **No unjustified UI:** H gives $\overline W_n/c_n\to-1$ in probability, although every normalized variable has mean zero. Consequently these variables cannot be uniformly integrable.
- **Measurability:** retain the approved pointwise slowly varying function with its measurability hypothesis; an a.e. representative cannot replace integer values silently.
- **Zero atom and conditioning:** `mass_zero_pos_of_subcritical` derives $\mu_0>0$; do not add it as an assumption. Prove eventual positive conditioning probabilities before treating normalized restrictions as probability measures.
- **Proof status:** sharp concentration, restricted Fuk–Nagaev, and the dyadic estimates above are proposed constructions. Existing theorem names and source formulas were inspected; their integration and permitted axiom closures remain future verification obligations.