# Blind read-backs of the paper-route key statements — 11 November 2026

Three fresh Sonnet subagents each received only the elaborated Lean text of the
statements in `PaperRoute.lean`, with the declaration names
replaced by neutral labels (`alSwapDrop` printed as `swapDrop`), and the
printed project definitions they rest on (`scratch/paperroute-probe.out`). They
received no source, blueprint or audit. Coordinator notes glossed `firstMaxIndex`'s
elided nonemptiness proof and which subtractions are taken in ℤ or ℝ. This is an
aid for comparison with the paper, not an audit. Labels: P = `al_criterion`,
Q = `berger_local_limit`, R1 = `paper_eq26`, R2 = `paper_eq33`. The fifth
statement, `paper_route_deleted_maximum_tvDist`, has the type of the frozen
`paper_deleted_maximum_tvDist`, whose read-back is in [READBACKS.md](READBACKS.md).

## Statement P

The statement is a universally quantified implication with six hypotheses and one conclusion. Throughout, $\nu$ is a Borel probability measure on $\mathbb R$. For each $n$, $\nu^{\otimes n}$ is the product measure on $\mathbb R^{\{0,\dots,n-1\}}$ (for $n=0$ the one-point space with total mass 1), and $S_n(y)=\sum_{i<n} y_i$. Measures are converted to reals with `.toReal`; all values here are finite. Division is total, so $a/0=0$. The index $n-1$ uses truncated subtraction, so $n-1=0$ when $n=0$.

Auxiliary definitions:

- For $x\in\mathbb R^{m+1}$, `firstMaxIndex x` is the smallest index $i$ with $x_j\le x_i$ for all $j$.
- `swapDrop n x` is a vector in $\mathbb R^{n-1}$. For $n=0$ it is empty. For $n=m+1$ it is $i\mapsto x_{\sigma(i)}$ for $i<m$, where $\sigma$ swaps the first maximal index with the last index $m$. In words: swap the first maximal coordinate to the last place, then delete the last place.

For every probability measure $\nu$ on $\mathbb R$ and all sequences $d,\ell,c:\mathbb N\to\mathbb R$, assume the following.

- **(H1)** Eventually $c_n>0$.
- **(H2)** $\ell_n/c_n\to+\infty$.
- **(H3)** For every $\tau>0$, eventually, for every real $x\ge d_n$,

$$
\left|\frac{\nu^{\otimes n}\{S_n\in(x,x+1]\}}{n\,\nu((x,x+1])}-1\right|\le\tau .
$$

  The quotient is $0$ if the denominator is $0$.
- **(H4)** For every $A>0$ and $\tau>0$, eventually, for all reals $x\ge\ell_n$ and $|y|\le Ac_n$,

$$
1-\frac{\nu((x-y,x-y+1])}{\nu((x,x+1])}\le\tau .
$$

  This bound is one-sided.
- **(H5)** For every $\tau>0$ there is a real $A$ such that eventually

$$
\nu^{\otimes(n-1)}\{A c_n<|S_{n-1}|\}\le\tau .
$$

  $A$ need not be positive.
- **(H6)** For every $A>0$, $n\,\nu((\ell_n-Ac_n,\infty))\to0$.

Conclusion: for every $\tau>0$, eventually, for every real $x\ge\max(d_n,\ell_n)$,

$$
d_{TV}\Big((\mathrm{swapDrop}\ n)_*\,\nu^{\otimes n}[\,\cdot\mid S_n\in(x,x+1]\,],\ \nu^{\otimes(n-1)}\Big)\le\tau .
$$

The conditional measure is Mathlib's: it is the zero measure when the event is null. `tvDist` is Mathlib's total variation distance. The threshold in $n$ is chosen before $x$.

## Statement Q

The statement is about every probability measure $\mu$ on $\mathbb N$. Let $\nu$ be the law of $k-1$ under $\mu$, computed in $\mathbb Z$, so $\nu\{z\}=\mu\{z+1\}$ for $z\ge-1$ and $\nu\{z\}=0$ for $z<-1$. Let $c_n=n\int\mathbf 1_{\{|k-1|\le a_n\}}(k-1)\,d\mu(k)$, a Bochner integral that is $0$ for $a_n<0$.

The hypothesis `IsMeasurableSubcriticalCauchyOffspring` has two parts:

- the lower Lebesgue integral $\int^-k\,d\mu<1$;
- there is $L:\mathbb R\to\mathbb R$ that is positive on $(0,\infty)$, slowly varying at $+\infty$ in the ratio sense, a.e. measurable on $(0,\infty)$, and satisfies $\mu\{n\}/(L(n)/n^2)\to1$.

Let $a:\mathbb N\to\mathbb R$ be any sequence, not assumed positive or divergent, with $n\,\mu\{k: a_n\le k-1\}\to1$. Then for every $\tau>0$ there exist $N\in\mathbb N$ and $R\in\mathbb R$ such that, for all $n\ge N$ and all $z\in\mathbb Z$ with $R\,a_n\le z$,

$$
\left|\frac{\nu^{\otimes n}\{x\in\mathbb Z^n:\ \sum_{i<n}x_i=z+\lfloor c_n\rfloor\}}{n\,\nu\{z\}}-1\right|\le\tau .
$$

The numbers $N$ and $R$ are chosen after $\mu$, $a$ and $\tau$. $R$ may be any real. If $z<-1$ or $n=0$, the denominator is $0$ and the left side equals $1$. The existential choice of $N$ and $R$ can avoid these cases where possible.

## Statement R1

Let $\mu$ be a probability measure on $\mathbb N$ satisfying the same two-part hypothesis as in Q, and let $m=\int^-k\,d\mu$. Let $\nu$ be the law on $\mathbb R$ of $k-m$ under $\mu$ (the map is $k\mapsto(k-1)+(1-m)$). For every $\varepsilon>0$ and every $\tau>0$ there is $N$ such that, for all $n\ge N$ and all real $x\ge\varepsilon n$,

$$
\left|\frac{\nu^{\otimes n}\{y:\ \sum_{i<n}y_i\in(x,x+1]\}}{n\,\nu((x,x+1])}-1\right|\le\tau .
$$

A zero denominator makes the quotient $0$.

## Statement R2

Let $\mu$ be a probability measure on $\mathbb N$ with $m<1$, and let $\nu$ be as in R1. Let $L$ be positive on $(0,\infty)$, slowly varying, a.e. measurable on $(0,\infty)$, with $\mu\{n\}/(L(n)/n^2)\to1$. Let $a$ satisfy $n\,\mu\{k:a_n\le k-1\}\to1$. Define:

- $\ell^*(r)=\sum_{j\ge0}L(\lfloor r\rfloor_++j)/(\lfloor r\rfloor_++j)$, where the $0$ term is $0$ and an unconditional sum is taken as $0$ if not summable;
- $c_n$ as in Q;
- $s_n=n\,\ell^*(a_n)$.

The conclusion is the conjunction of four clauses:

1. For every $\tau>0$ there is a real $K$ such that, eventually, $\nu^{\otimes n}\{K s_n<|\sum_{i<n}y_i|\}\le\tau$.
2. $a_n/s_n\to0$.
3. $(c_n+(1-m)n)/s_n\to-1$.
4. For all $\varepsilon,A,\tau>0$ there is $N$ such that, for all $n\ge N$, all $x\ge\varepsilon n$ and all $|y|\le A s_n$,

$$
\left|1-\frac{\nu((x-y,x-y+1])}{\nu((x,x+1])}\right|\le\tau .
$$

Division by $0$ gives $0$. The statement does not assert that suitable $L$ and $a$ exist.

## Statement U (U2.5 draft, before the heavy-tail strengthening)

A fresh Sonnet read-back of `paper_heavyTail_classification` (neutral label):

- **Hypotheses.** $\nu$ is a probability on $\mathbb N$ with $0<\nu\{0\}$, and $\alpha\ge0$ is real. $L:\mathbb R\to\mathbb R$ is positive on $(0,\infty)$, a.e. measurable on $(0,\infty)$ and slowly varying, and $\nu\{n\}/(L(n)/n^{1+\alpha})\to1$.
- **Conclusion.** There is a probability $\mu$ on $\mathbb N$ with $\mu\{k\}=a\,r^k\,\nu\{k\}$ for all $k$, for some reals $a,r>0$. Moreover, with $m(\mu)=\sum_k k\mu\{k\}\in[0,\infty]$ and $S(\mu)=\sum_k k^2\mu\{k\}\in[0,\infty]$, one of the following holds:
  - $m=1\wedge S<\infty$;
  - $m=1\wedge S=\infty\wedge1<\alpha\le2$;
  - $m=1\wedge\alpha=1$;
  - $m<1\wedge\alpha>1$;
  - $m<1\wedge\alpha=1$.
- **Reader's notes.** The cases overlap and are not exhaustive as formulas. The hypotheses are jointly satisfiable.

The approved version adds, in the last four cases, the same heavy tail for $\mu$.
