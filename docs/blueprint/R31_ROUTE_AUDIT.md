# Audit of the Theorem 3.1 research blueprint — 10 November 2026

Independent Opus subagent, read-only, refute-first, on [R31_ROUTE.md](R31_ROUTE.md). Verdict: adopt the endpoint route with the small repairs below. Coordinator check: the Lévy integral $I(1)=\gamma_E-1$ was confirmed to 40 digits (series plus $E_1(1)$, mpmath, 10 November).

## Verdicts

| Item | Verdict | Note |
| --- | --- | --- |
| Lemma 1 (Potter, $L_n\to0$, truncated second moment) | sound | $L_n\to0$ is a full limit: $\sum_{n}^{2n}L(k)/k=L(n)(\log2+o(1))$ is a tail of a convergent series. Potter needs the measurable uniform convergence theorem. |
| Lemma 2 (lattice concentration $C/(nL_n^2)$) | sound, cosmetic repair | Apply Potter only for $N\le1/\lvert t\rvert\le n$: split at $t_0=\min(t_1,1/N)$. The bound is weaker than the true order $1/a_n$ but sufficient; order $1/n$ up to slowly varying factors is essential (Esseen-type bounds give $n^{-1/2}$). |
| Lemma 3 (truncated exponential bound) | sound | Sign of the truncated centred mean checked; the MGF factor is $\le e$ uniformly in $j\le n$. |
| Lemma 4 (no large jump at the endpoint) | sound | $a/(2c)=8$; total $O(L_n^6/n)$ against $nq_n\asymp L_n/n$. |
| Lemmas 5–7 (typical set, $Z_n\sim nq_n$, insertion density) | sound | Preimages of $z\in G_n$ under first-maximum deletion are exactly the $n$ insertions of $r>\max z$. |
| Lemma 8 (TV from a typical set) | sound | Use the $(P-Q)^+$ side: $d_{TV}\le\delta+P(G^c)$. |
| Coverage of Theorem 3.1 | exact | Ordered first-maximum deletion under $W_n=-1$, all $n-1$ coordinates, against iid increments. |
| Not covered | — | The paper's internal uniform estimate over $x\ge\varepsilon n$ (U3.2); no downstream claim uses it. Record as bypassed, or extend by the same method. |
| M1, M2 from Theorem 3.1 | sound | Weak law and $\max/n\to0$; neither Fréchet nor stable limit needed. |
| M3 by weak records | sound | Weak (not strict) records; $\mathbb EN=\mathbb E\tau-1=m/\gamma$ gives $r=m$. |
| Rotated-word interface | simpler than stated | Strengthen Lemma 7 to the joint law of (insertion position, deleted word): the position is uniform and independent on $G_n$. |
| $R_n=N-\tau_\Delta$ and the Proposition 4.3 repair | sound | Fixes manuscript recommendation R6. Child reversal at $u_*$ keeps it the first maximum even with ties. |
| Normalization of the Cauchy limit (TeX 233–239) | **location constant needed** (≈90%) | $\int_0^\infty(e^{-\lambda x}-1+\lambda x\mathbf1_{x\le1})x^{-2}dx=\lambda\log\lambda+(\gamma_E-1)\lambda$, so with $b_n=n\mathbb E[X\mathbf1_{\lvert X\rvert\le a_n}]$ one gets $(W_n-b_n)/a_n\to\mathcal C_1+(1-\gamma_E)$. Affects (2.4) and Corollary 4.1 only. Residual doubt: Feller (8.15)'s centring convention, not consulted. |

## Risk ranking

1. Lemma 2 (lattice Fourier inversion, Potter on the reals, three-region integral).
2. Rotated-word coding and the record/height identity (M3, Proposition 4.3).
3. Lemmas 7–8 bookkeeping.
4. Lemma 3 inequalities.
