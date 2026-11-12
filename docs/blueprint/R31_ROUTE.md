# Research blueprint — Theorem 3.1 and consumers (10 November 2026)

Produced by a read-only research worker (gpt-6-astra, high; task `.orchestration/r31-research`). Not yet independently audited. Not proof evidence.

**Recommended route:** prove a local estimate only at $W_n=-1$, then compute the conditional deletion law directly. This can bypass Armendáriz–Loulakis, Berger, scale existence, and the stable limit. The substantial new analytic input is a lattice concentration bound; weak laws alone do not control the rare conditioning event.

This is a mathematical blueprint, not a verified implementation or independent statement approval. I read the cited primary papers; the alternative arguments below are my own proposed reconstruction. No files were edited and no builds were run.

**1. What the cited results actually supply**

Write $\gamma=1-m$, $\nu=\mathcal L(X+\gamma)$, $\Delta=(0,1]$, and $\overline W_n=W_n+\gamma n$.

Armendáriz–Loulakis assumes $\Delta$-subexponentiality: eventual positive window mass, invariance of its asymptotics under every fixed translation, and, for every fixed integer $r\ge1$,

$$
\nu^{*r}(x+\Delta)\sim r\nu(x+\Delta).
$$

Its Theorem 1 gives uniform TV convergence of the first $n-1$ coordinates after swapping the first maximum to the last coordinate. The proof permits threshold $q_n=d_n\vee\ell_n$ when

$$
\sup_{x\ge d_n}
\left|\frac{\nu^{*n}(x+\Delta)}{n\nu(x+\Delta)}-1\right|\longrightarrow0,
$$

and a positive scale $c_n\to\infty$ makes $\overline W_{n-1}/c_n$ tight, with $\ell_n/c_n\to\infty$ and, for every fixed $A>0$,

$$
\sup_{x\ge\ell_n,\ |y|\le Ac_n}
\left|\frac{\nu(x-y+\Delta)}{\nu(x+\Delta)}-1\right|\longrightarrow0.
$$

The latter absolute-ratio condition is sufficient for the proof’s one-sided condition (3.2); the paper informally calls it condition (3.3). [Armendáriz–Loulakis, Theorem 1 and §3](https://arxiv.org/pdf/0912.1516)

Here:

- Local regular variation supplies translation invariance. Fixed-$r$ convolution asymptotics need a separate proof: split the convolution into its two endpoint regions and a negligible middle region, then induct.
- Existing additive-window lemmas supply the ratio condition for **any** $c_n=o(n)$.
- The weak law allows a deterministic $c_n=o(n)$, $c_n\to\infty$, with $\overline W_{n-1}/c_n\to0$ in probability, by diagonal selection. Thus even this application need not use $\widehat b_n$ or the stable limit.
- Take $d_n=\ell_n=\varepsilon n$, $0<\varepsilon<\gamma$.

The corrected conditioning is exactly

$$
\overline W_n\in(\gamma n-2,\gamma n-1]
\quad\Longleftrightarrow\quad W_n=-1.
$$

The printed $\gamma n-1$ selects $W_n=0$. Existing `finiteWalk_centered_window` and `corrected_window_eventually_ge` address this correction; `MaximumSwapLaw.map_swap_take_eq_map_delete` addresses the operator discrepancy.

Berger’s relevant specialization assumes integer iid increments satisfying

$$
\mathbb P(X>t)\sim L(t)/t,\qquad
\mathbb P(X<-t)=o(L(t)/t),\qquad
p(k):=\mathbb P(X=k)\sim L(k)/k^2.
$$

With $nL(a_n)/a_n\to1$ and $b_n=n\mathbb E[X\mathbf1_{\{|X|\le a_n\}}]$, Theorem 2.4 yields, jointly as $n\to\infty$ and integer $z/a_n\to\infty$,

$$
\mathbb P(W_n-\lfloor b_n\rfloor=z)
\sim nL(z)/z^2.
$$

Its weaker local upper-bound hypothesis supplies only an upper bound, not this equivalence. [Berger, assumptions (1.1), (2.7), Theorem 2.4](https://arxiv.org/pdf/1706.07924)

Our local offspring assumption gives these hypotheses by summation and boundedness of the negative tail; eventual positive consecutive masses ensure span one. These tail-summation bridges remain proof obligations.

For the paper’s uniform application, put

$$
k_n(x)=\lfloor x-\gamma n\rfloor+1,\qquad
z_n(x)=k_n(x)-\lfloor b_n\rfloor.
$$

Then $z_n(x)=x-(b_n+\gamma n)+O(1)$. Lemma 2.2 gives uniformly $z_n(x)/a_n\to\infty$ for $x\ge\varepsilon n$. Sequential uniformization and existing mass-ratio lemmas produce the displayed window estimate. The source’s single indicated value $z=-\lfloor b_n\rfloor-1$ establishes only the bridge endpoint, not that uniform range.

**2. A self-contained endpoint proof**

Use offspring counts $\xi_i=X_i+1$, and define

$$
S_j=\sum_{i=1}^j\xi_i,\quad
Z_n=\mathbb P(S_n=n-1),\quad
q_n=\mu_{\lfloor\gamma n\rfloor},\quad L_n=L(n).
$$

It suffices to prove $Z_n\sim nq_n$.

All limits below are along `atTop` on $\mathbb N$; all eventual constants depend on the fixed offspring law and stated fixed parameters. Existing names below belong to `SubcriticalCauchy.Bienayme` unless otherwise indicated.

1. **Analytic bounds — substantial.**

   Establish $L_n\to0$, $nL_n^r\to\infty$ for every fixed $r>0$, and a Potter bound

   $$
   C^{-1}(v/u)^{-\eta}\le L(v)/L(u)\le C(v/u)^\eta
   \qquad(v\ge u\ge N)
   $$

   for every $\eta>0$. Deduce, eventually,

   $$
   \mathbb E[\xi^2\mathbf1_{\{\xi\le y\}}]\le CyL(y).
   $$

   Derive Potter bounds by iterating compact-factor comparisons; bound the truncated sum using $\eta=1/2$. Inputs: `paper_integratedTail_properties`, `SubcriticalCauchy.slowlyVarying_uniform_compact_tail`, and the local mass asymptotic. No monotonicity of $L$ is needed.

2. **Lattice concentration — hard; reusable probability infrastructure.**

   Prove that some $C,N$ satisfy, for every $n\ge N$, every integer $n/3\le j\le2n/3$, and every integer $k$,

   $$
   \mathbb P(S_j=k)\le\frac{C}{nL_n^2}.
   $$

   Here is a concrete Fourier proof, avoiding a stable local limit theorem. For $\phi(t)=\mathbb E[e^{it\xi}]$, symmetrization, $\mu_0>0$, and masses at indices comparable to $1/|t|$ give

   $$
   1-|\phi(t)|^2\ge c|t|L(1/|t|)
   $$

   for sufficiently small nonzero $t$. Consecutive positive atoms give $|\phi(t)|\le\rho<1$ away from zero in $[-\pi,\pi]$.

   Lattice Fourier inversion bounds each atom by $(2\pi)^{-1}\int|\phi(t)|^j\,dt$. For $|t|\ge1/n$, Potter yields an integrand bounded by

   $$
   \exp\{-cL_n\sqrt{n|t|}\},
   $$

   whose integral is $O((nL_n^2)^{-1})$. The remaining regions are smaller.

   Inputs: lemma 1, `mass_zero_pos_of_subcritical`, `eventually_mass_pos`. Integer Fourier inversion and the symmetrization identity are worthwhile general lemmas. This is the principal implementation risk.

3. **Truncated exponential estimate — substantial; reusable.**

   For every fixed $a,c>0$, eventually, uniformly over $1\le j\le n$,

   $$
   \mathbb P\!\left(S_j-mj\ge an,\ \max_{i\le j}\xi_i\le cn\right)
   \le eL_n^{a/(2c)}.
   $$

   Set $t_n=\log(1/L_n)/(2cn)$. Taylor’s inequality, the nonpositive truncated centered first moment, and lemma 1 show

   $$
   \mathbb E[e^{t_n(\xi-m)}\mathbf1_{\{\xi\le cn\}}]
   \le 1+C_ct_n^2nL_n e^{t_ncn}.
   $$

   The logarithm of its $n$th power is
   $O(\log^2(1/L_n)\sqrt{L_n})=o(1)$. Apply exponential Markov and independence.

4. **No large jump at the bridge endpoint — substantial.**

   Fix $c=\gamma/64$. Prove

   $$
   \mathbb P(S_n=n-1,\ \max_{i\le n}\xi_i\le cn)
   =o(L_n/n)=o(nq_n).
   $$

   Split into two blocks of approximately equal size. Since the total centered excess is $\gamma n-1$, one block has excess at least $\gamma n/4$, eventually. Lemma 3 bounds that block’s event by $eL_n^8$; lemma 2 bounds the other block’s required atom. Sum over the first block’s possible sums and interchange the blocks. The resulting bound is $O(L_n^6/n)$.

   This explains precisely why a tail estimate alone is insufficient: localization supplies the essential factor approximately $1/n$.

5. **A typical residual set — routine.**

   Choose deterministic $h_n\to\infty$, $h_n/n\to0$, such that under $\mu^{\otimes(n-1)}$,

   $$
   G_n=\{|S_{n-1}-m(n-1)|\le h_n,\ \max_{i<n}\xi_i\le h_n\}
   $$

   has probability tending to one. Use diagonal selection from `finitePreviousWalkAverage_deviation_tendsto_zero` and `finitePreviousMaximumAverage_deviation_tendsto_zero`.

   For every tolerance $\tau>0$, eventually, uniformly over residual vectors in $G_n$,

   $$
   r=n-1-S_{n-1}>\max_{i<n}\xi_i,\qquad
   |\mu_r/q_n-1|<\tau.
   $$

   Input: `paper_unitWindow_uniform_additive_window`, translated to singleton masses, or `paper_mass_ratio_of_relative_tendsto_one` plus uniformization.

6. **Endpoint local asymptotic — substantial.**

   Prove $Z_n/(nq_n)\to1$.

   Lower bound: insert $r$ into each of the $n$ positions of a residual vector in $G_n$. These events are disjoint because the inserted count is the unique maximum.

   Upper bound: outside lemma 4’s event, use

   $$
   \mathbb P(S_n=n-1,\max\xi_i>cn)
   \le n\,\mathbb E[\mu_{n-1-S_{n-1}}
                    \mathbf1_{\{n-1-S_{n-1}>cn\}}].
   $$

   On the typical sum window the ratio to $q_n$ tends uniformly to one. Elsewhere, the required count lies in $(cn,n-1]$, so compact-factor regular variation bounds that ratio by a fixed constant; the weak law makes this contribution negligible.

   **No separate two-large-jump estimate is necessary.**

7. **Conditional deletion formula — substantial combinatorics.**

   Let $P_n=\mu^{\otimes(n-1)}$ and $Q_n$ be ordered first-maximum deletion under $S_n=n-1$. For every $z\in G_n$,

   $$
   Q_n(\{z\})=
   \frac{n\mu_{\,n-1-\sum z_i}}{Z_n}P_n(\{z\}).
   $$

   Count the $n$ distinct insertion positions. Lemmas 5–6 make the displayed density uniformly close to one.

8. **TV from a typical set — routine; general probability fact.**

   For probability measures $P,Q$ on a countable space, if $Q|_G=fP|_G$ and $\sup_G|f-1|\le\delta$, prove

   $$
   d_{\rm TV}(P,Q)\le P(G^c)+\delta.
   $$

   Apply lemma 7, then subtract one coordinatewise to obtain Theorem 3.1 on increments. A measurable embedding identifies the discrete and real-vector TV statements.

   Also prove once: TV contraction under measurable maps, invariance under measurable equivalences, equality after tensoring with a common probability law, finite-product subadditivity, and error bounds when maps agree outside a small event. Product subadditivity is optional for this proof.

This route needs **neither** $a_n$, $b_n$, $\widehat b_n$, nor tightness on their scales. Chebyshev/truncation can replace the weak-law input, but cannot replace lemma 4 without additional quantitative work. The endpoint argument does not by itself certify the paper’s stronger uniform estimate for all $x\ge\varepsilon n$; retain that as a separate obligation.

**3. Consumers and a route avoiding general spine theory**

**M1 and M2 — routine after Theorem 3.1.** Combine TV contraction with `conditioned_degree_pair_event`, `maxDegree_eq_neg_deleted_sum`, and `incrementMaximum_deleted_word`. Obtain the paper’s two statistic-level TV comparisons. The existing previous-sum and previous-maximum weak laws then give $\Delta/n\to\gamma$ and $\Delta^2/n\to0$. Neither the Fréchet limit nor the stable limit is needed. The fluctuation corollary still needs stable convergence.

**Common path interface — hard.** Establish the law of the increment word obtained by reading cyclically immediately after the unique maximum and deleting that maximum. Its law approaches the iid word in TV. This requires actual excursion/Vervaat coding and cyclic exchangeability; the existing permutation-invariant degree interface alone is insufficient. Uniqueness follows from M1–M2.

For comparison, Kortchemski proves this rotated-word statement in Proposition 2.6, obtains forests by stopping at descending levels, and proves geometric depth using local convergence to a condensation tree plus localization of the maximal vertex. Thus the citation conceals additional work beyond TV. [Kortchemski, §§2.2–2.3](https://arxiv.org/pdf/1205.3145)

A proposed **alternative for M3**, avoiding infinite-degree tree topology:

- Prove the deterministic height formula identifying the maximal vertex’s depth with the number of weak ascending record times, excluding time zero, of the reversed residual walk.
- Negative drift makes the total record count finite almost surely.
- Restarting the iid walk at each weak record makes that count geometric. If $r$ is the probability of another record, its mean plus one is $1/(1-r)$.
- Time reversal gives
  $\mathbb P(k\text{ is a weak record})=\mathbb P(\tau>k)$,
  where $\tau$ is the first hitting time of $-1$.
- Exploration coding and expected generation sizes give
  $\mathbb E\tau=\mathbb E|\mathcal T|=\sum_{j\ge0}m^j=1/\gamma$.
  Hence $r=m$, yielding $\mathbb P(H_\Delta=j)\to\gamma m^j$.

Inputs include `walkAverage_ae_tendsto` and the vendor theorem `BGW.LocallyFinite.lintegral_generationSize`. Stopped-block independence, exploration coding, and the record/height identity are substantial new obligations. This is a proposed proof, requiring independent review of its endpoint conventions.

**Proposition 4.2 — substantial.** For $0<\delta<\gamma$, stop the rotated residual walk when it first reaches $-\lfloor\delta n\rfloor$. Its stopped word codes precisely those attached children. The iid hitting time divided by $n$ tends to $\delta/\gamma<1$ by the strong law and downward skip-free property. Successive stopped blocks are independent unconditioned Bienaymé trees. TV contraction and a vanishing failure probability finish the comparison. Handle $\delta=0$ directly.

**Proposition 4.3 — substantial, with an explicit repair of finding 7.**

Let the residual walk have length $N=n-1$, endpoint $-d$, and first hitting time $\tau_d$ of $-d$. Prove the deterministic identity

$$
R_n:=n-|\text{fringe at the maximal vertex}|=N-\tau_d.
$$

After reversal this is the last visit to zero. For an iid negative-drift walk, the infinite last visit to zero is finite almost surely. The rotated-word TV comparison therefore makes $R_n$ tight. This controls all exterior branches, not merely the maximal vertex’s depth.

Now:

- The lower height bound follows from Proposition 4.2 and existing independent-forest bounds.
- For the attached forest’s upper bound, cover it by two blocks, use child-order reversal on the unique-maximum event, and compare each block with $\lfloor2\gamma n/3\rfloor$ iid trees.
- On $R_n\le K$,

  $$
  H(\mathcal T_n)\le\max\{K,\ K+1+H_{\rm forest}\}.
  $$

- Use `survival_ratio_tendsto`: for fixed integer $K$, shifting a diverging threshold by $K+1$ changes survival probabilities by an asymptotically finite factor. Thus $nQ_{h_n}\to0$ still controls the shifted threshold.

Use $Q_h=Q_{\lceil h\rceil}$ throughout. Tightness of $H_\Delta$ alone does not justify the source’s reduction.

**4. Risks and priorities**

- Preserve local mass regular variation: tail regular variation alone does not supply local conditioning asymptotics.
- Do not assume a finite variance or any moment strictly above one.
- First-maximum tie breaking does not automatically preserve child-order symmetry; establish uniqueness first or prove a tie-sensitive identity.
- The unrestricted tilt assertions remain false as recorded in the inventory; they are unnecessary here.
- **Additional normalization question for independent review:** with Lévy measure $x^{-2}\mathbf1_{x>0}\,dx$ and truncation at one,

  $$
  \int_0^\infty
  \frac{e^{-\lambda x}-1+\lambda x\mathbf1_{\{x\le1\}}}{x^2}\,dx
  =\lambda\log\lambda+(\gamma_E-1)\lambda.
  $$

  This suggests checking whether the paper’s exact truncated-mean centering matches its stated Laplace exponent $\lambda\log\lambda$, or needs a location adjustment. I flag this as an unresolved normalization concern, not an independently confirmed correction; it does not affect the proposed Theorem 3.1 route.

I am confident in the endpoint estimate strategy and its explicit bounds. The best next research checkpoint is independent review of lemmas 2–4; the best bounded implementation task is lemma 8 together with the exact insertion formula.