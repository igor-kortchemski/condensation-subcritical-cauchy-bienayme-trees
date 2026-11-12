# Paper inventory

> **Status note (11 November 2026).** This is the initial checked inventory and is
> kept unchanged as the reference list. The current status of every entry is in
> [COVERAGE_RECONCILIATION.md](COVERAGE_RECONCILIATION.md) and
> [FORMALIZATION_REPORT.md](../FORMALIZATION_REPORT.md). Corrected statements
> (R8–R10, R13) are in [MANUSCRIPT_RECOMMENDATIONS.md](../MANUSCRIPT_RECOMMENDATIONS.md).

## Source, scope, and review status

Source: `subcritical_cauchy_final_arxiv.tex`, *Condensation in subcritical Cauchy
Bienaymé trees*, arXiv:2503.07530v2, Igor Kortchemski and Leonard Vetter.
The source SHA-256 at this inventory is
`088f21ed02ea30565d3b6f61ef9b28babd07380be869773dd5f145fa221ecef5`.
Line locations below refer to that file. The inventory was reconstructed from
the complete source, including the abstract, examples, discussion, and proof
paragraphs, independently of Lean implementation.

Scope is every theorem, proposition, lemma, corollary, and substantive
mathematical claim stated in the paper. Claims attributed to other works are
retained as external dependencies or background obligations; this does not
extend the task to all results of every cited work. Historical attribution,
the simulation caption, acknowledgments, and bibliographic data are not
mathematical proof obligations. The local-limit extension at line 388 is an
open direction, not a proved result.

There are **nine active theorem/proposition/lemma/corollary environments** and
**one active example with three mathematical cases**. The Potter proposition at
lines 241–252 is commented out and is not a numbered result of this version.
The underlying regular-variation tools remain relevant external dependencies.

**Initial status:** all paper results and substantive claims below are unproved
in Lean; no source-facing Lean statement has passed statement-fidelity review.
This file is an inventory, not proof evidence. Its author is the
`paper_inventory` agent. The coordinating agent independently checked the active
environments, Introduction conclusions, examples, unnumbered proof bridges,
background categories, and recorded source issues against the TeX on 29 October
2026. The inventory passes this initial coverage review; this does not certify
the mathematics of any pending result. Update actual
coverage and review findings in [FORMALIZATION_REPORT.md](../FORMALIZATION_REPORT.md)
at milestones, without treating this initial status as a permanent assertion.

## Standing definitions and side conditions

- `D1` — Lines 135–141, `eq:H_loc_mu`: an offspring probability mass function
  $\mu$ on $\mathbb N$, mean $m=\sum_{k\geq0}k\mu_k<1$, and a positive slowly
  varying function $L$ satisfying $\mu_n\sim L(n)/n^2$. Slow variation is stated
  as $L(ax)/L(x)\to1$ for each $a>0$. The local tail condition implies unbounded
  support and, together with subcriticality, $0<m<1$ and $\mu_0>0$; these facts
  must be derived where needed, not added as replacements for the hypothesis.
  On 1 November 2026 the author approved the standard measurable convention
  for future main statements; the literal ratio-only predicate remains in the
  development, with an implication from the approved measurable predicate.
- `D2` — Lines 147, 196–201: finite rooted ordered trees; offspring degree,
  maximum degree $\Delta$, second maximum $\Delta^2$, height $H$, and the
  lexicographically first maximum-degree vertex with height $H_\Delta$.
  For every finite tree $\tau$, the Bienaymé law assigns the product of its
  offspring probabilities. The conditioned tree $\mathcal T_n$ is only used
  for positive-probability sizes. Specify the second maximum at size one and
  the asymptotic filter on admissible sizes explicitly.
- `D3` — Lines 226–239: integer increments $X\geq-1$ with
  $\mathbb P(X=i)=\mu_{i+1}$; independent identically distributed copies $X_i$;
  $W_n=\sum_{i=1}^nX_i$; scaling $a_n$ with
  $n\mathbb P(X\geq a_n)\to1$; centering
  $b_n=n\mathbb E[X\mathbf1_{\{\lvert X\rvert\leq a_n\}}]$.
  Clarify positivity and real/integer conventions for $a_n$.
- `D4` — Line 253: $\ell^\star(n)=\sum_{k=n}^\infty L(k)/k$ for integer
  $n\geq1$. Later evaluation at real $a_n$ requires an extension, for example
  a ceiling-index tail sum, and a checked convention-invariance argument.
- `D5` — Lines 307–311: remove the first index attaining the maximum jump from
  the bridge conditioned on $W_n=-1$; preserve the order of the other jumps.
- `D6` — Lines 394–406: ordered fringe subtrees attached to the first
  maximum-degree vertex, padded with the empty tree; forest intervals
  $[\tau]_{j,k}$; independent-tree forest $\mathcal F^i$; survival tail
  $Q_n=\mathbb P(H(\mathcal T)\geq n)$ for the unconditioned tree.
  Include the zero-tree forest and real-threshold extension of $Q$.

## Numbered results and the Introduction's main conclusions

Each row is a separate obligation; conjunctions are split when they have
distinct mathematical content. All convergence below is as $n\to\infty$
through admissible conditioning sizes where appropriate.

| ID | Source | Mathematical target | Main dependencies |
| --- | --- | --- | --- |
| M1 | Theorem 1.1(i), `thm:main`, 149–163 | $\Delta(\mathcal T_n)/(n(1-m))\to1$ in probability. | One-big-jump result, degree/jump correspondence, weak law. |
| M2 | Theorem 1.1(i), 153 | $\Delta^2(\mathcal T_n)/n\to0$ in probability. | One-big-jump result, extreme-value law, $a_n=o(n)$. |
| M3 | Theorem 1.1(ii), 154–155 | For every integer $j\geq0$, $\mathbb P(H_\Delta(\mathcal T_n)=j)\to(1-m)m^j$. | One-big-jump result and the source-referenced spine argument. |
| M4 | Theorem 1.1(iii)(a), 156–159 | $H(\mathcal T_n)/\log n\to1/\log(1/m)$ in probability. | Proposition 4.3, Lemma 4.4(ii), logarithmic threshold estimates. |
| M5 | Theorem 1.1(iii)(b), 160 | The family $H(\mathcal T_n)-\log n/\log(1/m)$ is tight if and only if $\sum_{n\geq1}(n\log n)\mu_n<\infty$. | Proposition 4.3, Heathcote–Seneta–Vere-Jones criterion, diagonal threshold construction. |
| R2.1 | Proposition 2.1 (Kennedy), `prop:tilting`, 208–211 | If probability laws $\mu,\nu$ satisfy $\mu_k=a\lambda^k\nu_k$ for every $k\geq0$ and finite $a,\lambda>0$, then their size-$n$ conditioned tree laws coincide, for admissible $n$. | Tree probability product and total-degree identity; normalization. |
| R2.2a | Lemma 2.2(i), `lem:bnan`, 255–262 | $\ell^\star$ is slowly varying, tends to zero, and $L=o(\ell^\star)$. | Finite mean, tail summation, BGT Proposition 1.5.9b. |
| R2.2b | Lemma 2.2(ii), 259 | $b_n+n(1-m)\sim-n\ell^\star(a_n)$ and $b_n\sim-n(1-m)$. | Truncated first moment and R2.2a. |
| R2.2c | Lemma 2.2(iii), 260 | $a_n=o(n)$. | Tail asymptotic, $a_n\sim nL(a_n)$, R2.2a. |
| E2.3a | Example 2.3(i), `ex:anl`, 286–290 | For $L(n)\sim c/(\log n)^{1+\beta}$, $c,\beta>0$, $\ell^\star(n)\sim c/(\beta(\log n)^\beta)$, $\log a_n\sim\log n$, and $a_n\sim nL(n)$. | Sum/integral asymptotics and scale inversion. |
| E2.3b | Example 2.3(ii), 291–294 | For integer $k\geq2$, $L(n)\sim c(\log_{(k)}n)^{-2}\prod_{i=1}^{k-1}(\log_{(i)}n)^{-1}$, $c>0$, one has $\ell^\star(n)\sim c/\log_{(k)}n$, $\log a_n\sim\log n$, and $a_n\sim nL(n)$. | Iterated logarithms, sum/integral asymptotics, scale inversion. |
| E2.3c | Example 2.3(iii), 295 | For $L(n)\sim c\exp(- (\log n)^\beta)$, $0<\beta<1$, $c>0$, $\ell^\star(n)\sim(c/\beta)(\log n)^{1-\beta}\exp(- (\log n)^\beta)$. For $\beta<1/2$, $a_n\sim cn\exp(- (\log n)^\beta)$; for $1/2\leq\beta<2/3$, $a_n\sim cn\exp(- (\log n)^\beta+\beta(\log n)^{2\beta-1})$. | Tail integral and inversion with the stated error orders; neither scale formula is asserted for $\beta\geq2/3$. |
| R3.1 | Theorem 3.1, `th:asy iid`, 312–319 | Total variation distance between the $(n-1)$ bridge increments after deleting their first maximum and $(n-1)$ independent unconditioned increments tends to zero. | Armendáriz–Loulakis theorem, Berger local estimate, R2.2, uniform slow variation. |
| R4.1 | Corollary 4.1, `cor:fluctuations`, 382–386 | $(\Delta(\mathcal T_n)+b_n)/a_n$ converges in distribution to $-\mathcal C_1$. | Stable limit U2.8, total variation comparison U4.1, adjacent-index scaling/centering control. |
| R4.2 | Proposition 4.2, `prop:forests`, 397–400 | For every $\delta\in[0,1-m)$, $d_{\mathrm{TV}}([\mathcal T_n]_{1,\lfloor\delta n\rfloor},\mathcal F^{\lfloor\delta n\rfloor})\to0$. Include $\delta=0$. | R3.1 and the source-referenced forest argument. |
| R4.3a | Proposition 4.3(i), `prop:height`, 410–417 | For every positive real sequence $h_n\to\infty$, if $nQ_{h_n}\to\infty$, then $\mathbb P(H(\mathcal T_n)\geq h_n)\to1$. | M1, M3, R4.2, independent forest maxima, transfer from condensation forest to full height. |
| R4.3b | Proposition 4.3(ii), 415 | For every positive real sequence $h_n\to\infty$, if $nQ_{h_n}\to0$, then $\mathbb P(H(\mathcal T_n)<h_n)\to1$. | Same, including reflection/exchangeability of attached subtrees and control of heights outside them. |
| R4.4a | Lemma 4.4(i), `lem:bounds`, 438–444 | There exists one positive $\ell:(0,1]\to\mathbb R$ slowly varying at zero with $\ell(x)\to0$ and $Q_{n+1}=Q_n(m-\ell(Q_n))$ for every integer $n\geq0$. | PGF identity and Karamata Abelian theorem; branching recursion. |
| R4.4b | Lemma 4.4(ii), 442 | For every $\eta\in(0,m)$, eventually $(m-\eta)^n\leq Q_n\leq m^n$. | R4.4a, positivity, convergence of $Q_n$ to zero, geometric comparison. |
| R4.5a | Proposition 4.5(i), `prop:ex`, 506–515 | If $L(n)\sim c/(\log n)^2$, for every $\varepsilon>0$, the probability that $\left\lvert H(\mathcal T_n)-\log n/\log(1/m)+c\log\log n/(m\log(1/m)^2)\right\rvert\geq\varepsilon\log\log n$ tends to zero. Here $c>0$ is inherited from the positive asymptotic model. | E2.3a, R4.4a–b, R4.3, logarithmic recurrence asymptotics. |
| R4.5b | Proposition 4.5(ii), 512–513 | If $L(n)\sim c/(\log n)^{1+\beta}$, $c>0$, $0<\beta<1$, the same statement holds with correction $c(\log n)^{1-\beta}/((1-\beta)\beta m\log(1/m)^{1+\beta})$ and deviation scale $\varepsilon(\log n)^{1-\beta}$. | Same dependencies with power-sum recurrence asymptotics. |

## Substantive claims outside numbered statements

These rows include source constructions and proof bridges. Elementary algebra
inside a displayed calculation can be discharged as part of the corresponding
row; it need not acquire an unrelated public theorem. No row may be marked
complete merely by assuming its conclusion in a helper.

| ID | Source lines / label | Claim or construction to cover | Status or qualification |
| --- | --- | --- | --- |
| U1.1 | 117, 153–164 | A unique vertex has macroscopic degree with probability tending to one; the others have negligible linear degree. | Corollary of M1–M2, with a precise macroscopic threshold. |
| U1.2 | 141 | The local tail assumption puts the offspring law in a stable domain of attraction of index one. | External stable-limit theory; matched to U2.8. |
| U1.3 | 182 | For a subcritical regularly varying offspring law of exponent $1+\alpha$ with $\alpha>1$, the $n\log n$ moment is finite; for $\alpha=1$ it may diverge, including $L(n)\sim c/(\log n)^{1+\beta}$ with $0<\beta\leq1$. | Includes existence of an actual subcritical probability law with this tail, not just a formal tail expression. |
| U2.1 | 198–199 | The probability of a finite plane tree is the product of offspring masses. | Characterization bridge for any chosen Bienaymé construction. |
| U2.2 | 213 | For $0<\lambda<\rho$, normalized exponential tilt has PGF $F(\lambda x)/F(\lambda)$ and mean $\lambda F'(\lambda)/F(\lambda)$, and is equivalent to the original law. | Must specify the PGF's convergence domain and positive finite normalization. |
| U2.3 | 213 | Equivalence to a critical law iff the boundary limit of $\lambda F'(\lambda)/F(\lambda)$ is at least one. | **Contradicted as stated:** Bernoulli counterexample in the findings below. Original claim cannot be certified. |
| U2.4 | 213, 223 | Every supercritical law is equivalent to a critical finite-variance law; $\alpha<1$ implies infinite mean. | The first statement needs nondegeneracy/admissibility qualifications; see findings. Tail implication remains an obligation. |
| U2.5 | 215–223 | Exhaustive five-case classification of heavy-tailed laws up to exponential tilt: critical finite variance, critical infinite variance $1<\alpha\leq2$, critical $\alpha=1$, subcritical $\alpha>1$, subcritical $\alpha=1$. | Requires U2.2–U2.4 and moment/radius criteria, with corrected hypotheses. |
| U2.6 | 228 | Bijection of finite plane trees with Łukasiewicz excursions; Bienaymé exploration is the increment walk stopped on first entering the negatives; Vervaat transform relates the excursion conditioning and bridge conditioning. | External combinatorial/probabilistic construction; distinguish first hitting at $n$ from merely $W_n=-1$. |
| U2.7 | 228, 231 | Outdegrees minus one, as a collection, have the bridge increment collection's law; $\mathbb E[X]=m-1$. | The law claim concerns the collection, not the unrotated lexicographic vector. |
| U2.8 | 233–239, `eq:conv to C_1` | Existence of scales $a_n$; $(W_n-b_n)/a_n\Rightarrow\mathcal C_1$, with $\mathbb E[e^{-\lambda\mathcal C_1}]=e^{\lambda\log\lambda}$ for every $\lambda>0$; $a_n$ and the magnitude of $b_n$ are regularly varying of index one. | Stable law is maximally skewed index-one stable, not Mathlib's symmetric Cauchy distribution. Signed $b_n$ needs a stated convention. |
| U2.9 | 253, 265–274 | Finiteness of $\ell^\star$; $a_n\to\infty$; $\mathbb P(X\geq u)\sim L(u)/u$; $a_n\sim nL(a_n)$; $\mathbb E[X\mathbf1_{\{\lvert X\rvert>a_n\}}]\sim\ell^\star(a_n)$. | Tail regular variation and truncated-moment bridges underlying R2.2. |
| U2.10 | 277–281, `eq:proba` | $W_n/(n(m-1))\to1$ in probability; mean-centered $(W_n-\mathbb E W_n)/a_n$ does not converge in distribution to a finite real law. | A weak law can give the first conclusion by a different route; the second needs the diverging centering shift. |
| U3.1 | 322–326 | Centering increments by $\gamma=1-m$ preserves total variation comparison and the index of the first maximum; chosen conditioning matches the Armendáriz–Loulakis theorem. | The source's $x=\gamma n-1$ with $\Delta=(0,1]$ selects $W_n=0$; use $x=\gamma n-2$ to select $W_n=-1$. Verify the corrected eventual threshold and the cited theorem's swap/projection versus ordered-deletion law bridge. |
| U3.2 | 330–345, `eq:26`, `eq:ber` | Uniform local one-big-jump estimate on $x\geq\varepsilon n$, with all three source numerator/denominator shifts. Includes $m_n=o(n)$, uniform $\lvert x-m_n\rvert\sim x$, and uniform $(x-m_n)/a_n\to\infty$. | Berger estimate is external; the shift comparison is a separate regular-variation bridge. |
| U3.3 | 343, 355–357 | Uniform slow variation on shrinking relative windows, including uniformly over $x\geq\varepsilon n$ and $\lvert u\rvert\leq\eta_n=o(n)$. | Check regularity hypotheses of the representation/uniform convergence theorem. |
| U3.4 | 348–354, `eq:33` | With $\widehat b_n=n\ell^\star(a_n)$, $\overline W_n/\widehat b_n$ is tight, $a_n/\widehat b_n\to0$, $(b_n+\gamma n)/\widehat b_n\to-1$, and the local mass ratio is uniformly one for shifts $\lvert y\rvert\leq A\widehat b_n$, each fixed $A>0$. | The scale is different from $a_n$; the source's letter $L$ for a bound is unrelated to its slowly varying function. |
| U4.1 | 369–375, `eq:dtvDelta` | $d_{\mathrm{TV}}(\Delta(\mathcal T_n),-\sum_{i=1}^{n-1}X_i)\to0$ and $d_{\mathrm{TV}}(\Delta^2(\mathcal T_n)-1,\max_{i<n}X_i)\to0$. | Account for degree/jump shifts and deleting the first maximum. |
| U4.2 | 376 | $\max_{i<n}X_i/a_n\Rightarrow Y$ with $\mathbb P(Y\leq u)=\exp(-1/u)$ for $u>0$. | Tail asymptotic, independence, and limiting power; define the CDF for $u\leq0$. |
| U4.3 | 378, 402 | The proof transfers from Kortchemski's geometric-height and forest results remain valid with the new one-big-jump input. | External arguments must actually be reconstructed or replaced and the departure recorded. Citation alone is not proof. |
| U4.4 | 390, 483 | For $u_n=Q_n/m^n$, $u_n$ converges to a positive constant iff $\sum n\log n\,\mu_n<\infty$ and otherwise converges to zero. | Heathcote–Seneta–Vere-Jones Theorem 2; central dependency of M5. |
| U4.5 | 420–432 | Transfer between full height and the maximum-degree vertex's descendant forest; asymptotic bounds on $\Delta_n$; distributional reversal/exchangeability of its attached subtrees; independent-forest maximum formula $(1-Q_h)^k$. | Full-height transfer needs precise control, not just an informal appeal to tightness of $H_\Delta$. |
| U4.6 | 446–460, `eq: pgf`, `eq: l(s)` | PGF representation $G(s)=1-m(1-s)+(1-s)\ell(1-s)$; $\ell(x)\sim\ell^\star(1/x)$; $\ell(s)=m-\sum_{k\geq0}\mu([k+1,\infty))(1-s)^k$; $\ell(0+)=0$, $\ell(1)=m-1+\mu_0$, monotonicity and $0<\ell(s)<m$ on $(0,1]$. | Includes Karamata and a corrected summation calculation; endpoint conventions are required. |
| U4.7 | 462–471 | Branching identity $Q_{n+1}=1-G(1-Q_n)$, $Q_0=1$, $0<Q_n\leq1$, geometric upper bound, product formula for the recurrence, and eventual lower bound. | A probabilistic construction must justify the branching identity; an abstract recurrence alone is only a helper. |
| U4.8 | 478–481 | At upper/lower logarithmic thresholds, $nQ_h\to0$ / $\infty$; choice of $\eta$ preserving the specified exponent bound. | Real-threshold rounding must be retained; it may introduce bounded factors. |
| U4.9 | 485–487 | Under the finite logarithmic moment, every diverging tolerance $\lambda_n$ gives vanishing centered-height deviation probability, implying tightness. | Need the exact sequential characterization of tightness and treatment of nonpositive lower thresholds. |
| U4.10 | 489–500, `eq:rn` | Under the infinite logarithmic moment, construct $r_n\to\infty$ with $\mathbb P(H(\mathcal T_n)\leq\log n/\log(1/m)-r_n)\to1$; conclude failure of tightness. | Diagonal index construction, $h_n\to\infty$, and $nQ_{h_n}\to0$, with corrected notation. |
| U4.11 | 518–528, `eq:recrel1`, `eq:recrel2` | For logarithmic tails, the two multiplicative recurrences for $u_n$ with errors tending to zero, and $\log(1/u_n)=o(n)$. | E2.3a, R4.4, positivity, logarithmic asymptotics; check the range of $\eta$. |
| U4.12 | 530–537 | For $\beta=1$, $\log u_n\sim-c\log n/(m\log(1/m))$; for $0<\beta<1$, $\log u_n\sim-c n^{1-\beta}/((1-\beta)\beta m\log(1/m)^\beta)$; evaluation at the proposed shifted thresholds gives the needed signs of $\log(nQ_h)$. | Infinite product/logarithmic sum asymptotics and errors small relative to the second-order scale. |

## Background claims and external inputs

These obligations are retained because the requested scope includes substantive
claims throughout the source. They are lower priority than the Introduction's
new results. They must not be silently marked out of scope.

**Author's decision, 10 November 2026:** B1–B5 are recorded as external
citations, not proof obligations (the paper quotes them; none of its results
depends on them). The X rows remain inputs to be proved or bypassed where the
paper's results use them.

| ID | Source / citation | Content actually used or asserted |
| --- | --- | --- |
| B1 | 170, Jonsson–Stefánsson and Kortchemski | Condensation and the same four groups of height/degree conclusions for subcritical tails of index $\alpha>1$, with the cited hypotheses. |
| B2 | 173, Aldous | Critical finite-variance conditioned trees have Brownian CRT scaling limits; no macroscopic condensation. |
| B3 | 173, Duquesne | Critical infinite-variance tails with $1<\alpha\leq2$ have stable-tree limits; no macroscopic condensation. |
| B4 | 175, 177, 185, Kortchemski–Richier; Addario-Berry–Donderwinkel–Kortchemski | Critical Cauchy condensation has a dominating but sublinear maximum degree; stated height behavior and absence of a nontrivial scaling limit need the cited results' exact normalization/topology. |
| B5 | 179, application references | Condensation trees encode the listed random structures (maps, percolation clusters, permutations, parking, factorizations). Broad motivational claims require precise theorem statements before possible formal coverage; no invented universal encoding claim. |
| X1 | 228, Pitman §6.1 and Le Gall §1 | Plane-tree/excursion coding, cyclic/Vervaat transform, and bridge degree law. |
| X2 | 239, Feller IX.8 and (8.15) | Index-one stable-domain limit, chosen centering, Laplace characterization. |
| X3 | 265, 343, 357, 446; Bingham–Goldie–Teugels | Integrated slow-variation theorem 1.5.9b, representation theorem 1.3.1, Karamata Abelian theorem 8.1.6, and applicable sum/tail consequences. |
| X4 | 322, 328; Armendáriz–Loulakis Theorem 1 | Conditional deletion-of-maximum theorem with its conditions (2.6), (3.3), and the actual lattice/window formulation. |
| X5 | 339–341; Berger Theorem 2.4 | Uniform local large-deviation estimate in the index-one regime. |
| X6 | 378, 402, 420; Kortchemski Theorem 2, Corollary 2.7, Theorem 4 | Geometric depth, independent fringe forest, and height comparison methods. |
| X7 | 390, 483; Heathcote–Seneta–Vere-Jones Theorem 2 | Positive survival-ratio limit exactly under the logarithmic offspring moment. |
| O1 | 388 | Extension of the maximum-degree fluctuation law to a local limit theorem: **open direction**, not claimed as proved and not a completion obligation to solve. |

The complete statements of external inputs must be read and matched before
use. No source citation licenses adding an unproved estimate as an axiom or as
a new assumption in a theorem advertised as the paper's result.

## Source findings needing explicit treatment

1. **False critical-tilt criterion in the stated generality (line 213).**
   Take $\mu_0=\mu_1=1/2$ and $\mu_k=0$ for $k\geq2$. Then
   $F(\lambda)=(1+\lambda)/2$, its radius is infinite, and
   $\lambda F'(\lambda)/F(\lambda)=\lambda/(1+\lambda)\to1$.
   Every distribution equivalent by finite positive exponential weights still
   has positive mass at both zero and one, so its mean is strictly less than
   one. Thus U2.3 cannot be proved as written, even with $\mu_0>0$.
   An exact criterion can instead assert existence of an admissible finite
   tilt with finite positive normalization and tilted mean one. Replacing that
   existence by a boundary inequality requires an endpoint-attainment theorem
   and suitable hypotheses. This does not invalidate the main subcritical
   Cauchy results, whose offspring distributions have unbounded support.
2. **Supercritical assertion requires a support condition (lines 175, 213).**
   The law concentrated at two is supercritical, and all its finite positive
   tilts remain concentrated at two; none is critical. A positive-probability
   finite-tree conditioning implies $\mu_0>0$, but this condition is not stated
   in the general assertion. Record a qualified version separately rather than
   certifying the unrestricted text.
3. **Real thresholds and integer survival indices (lines 404–415 onward).**
   $Q$ is defined on integer indices and then evaluated at arbitrary positive
   real $h$. The natural convention is $Q_h=\mathbb P(H\geq h)=Q_{\lceil h\rceil}$.
   Power estimates must tolerate the associated bounded geometric factors;
   expressions such as $Q_h\leq m^h$ can remain valid in one direction but
   opposite estimates require careful rounding.
4. **Tail-sum arguments at real scales (lines 253–270).**
   Specify the extension of $\ell^\star$ and show rounding does not affect the
   asserted asymptotics. Do not silently type a real scale as an integer.
5. **Typographical errors in proof calculations.** At line 458 the middle
   double sum has swapped indices; the intended expansion is
   $\sum_{k\geq1}\mu_k\sum_{j=0}^{k-1}s^j$ before exchanging sums.
   At line 460 the expression for the limit omits $\ell(s)$; the PGF formula at
   $s=1$ uses a limiting convention for $\ell(0)$.
   At line 494, $c_n$ appears where the preceding argument defines $u_n$.
   At line 523, the comparison using $m-\eta$ requires $0<\eta<m$, not the
   displayed $0<\eta<1$. These are source observations, not manuscript edits.
6. **Cited theorem applications require checking.** The Berger discussion at
   line 339 mentions a single value $x=-\lfloor b_n\rfloor-1$ while the displayed
   target is a uniform estimate over $x\geq\varepsilon n$. Verify the precise
   external theorem rather than treating the parenthetical as sufficient.
   The slow-variation definition gives only pointwise ratio convergence;
   confirm the regularity hypotheses needed by the representation theorem.
7. **Full-height versus condensation-forest height (line 420).** Tightness of
   $H_\Delta$ alone is not a deterministic bound on heights in branches outside
   the maximum-degree vertex's descendants. Reconstruct the source-referenced
   argument and all probability bounds needed for U4.5. Preserve the one-level
   offset between a child's tree height and its height above the condensation
   vertex. This is an identified proof obligation, not a verdict that R4.3 is
   false.
8. **Uniform geometric tightness.** The limiting point masses in M3 imply
   tightness only after showing that $(1-m)m^j$ sums to one. Tightness in M5 is
   a property of the family of distributions, not a separate boundedness claim
   for each finite tree.

## Dependency order and feasible first implementations

The main route is:

1. Define probability laws, finite ordered trees, offspring weights, and
   conditioned laws with their characterization bridges. Prove the degree-sum
   identity and product-factor identity for exponential tilting; these directly
   support R2.1 and the later bridge representation.
2. Develop the PGF/offspring-tail summation identity and branching survival
   recursion. Abstract recurrence comparison lemmas can be proved early, but
   remain conditional helpers until the actual Bienaymé survival law is linked
   to them. This route supplies R4.4 and the height main results' analytic input.
3. Develop regular variation, scales/centering, and the index-one stable limit.
   Prove R2.2, the uniform windows, and check X4–X5 to obtain R3.1.
4. Transfer R3.1 through the tree coding to M1–M3 and R4.2, then establish
   R4.3. Combine R4.3 with R4.4 for M4 and with X7 for M5.
5. Obtain R4.1 and the examples/second-order results; complete retained
   background and unnumbered obligations; reconcile all rows before any claim
   of complete coverage.

The finite-tree degree/product identities and elementary survival recurrence
comparisons are feasible initial pieces using existing finite sums, products,
and analysis APIs. The one-big-jump theorem, index-one stable-domain theory,
branching-law construction, and external survival criterion are substantial
mathematical developments, not packages already supplied by this inventory.
The false U2.3 and unqualified U2.4 assertions must be recorded as unresolved
source corrections while independent main-result work continues.
