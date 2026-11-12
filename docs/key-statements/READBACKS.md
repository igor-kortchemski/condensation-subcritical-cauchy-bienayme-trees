# Blind read-backs of the draft main statements — 10 November 2026

Three fresh Sonnet subagents received only the Lean text of the statements in
`MainTheorems.lean`, with neutral names, and the printed
definitions they rest on (`scratch/readback-prints.txt`); no source, no
blueprint, no audit. Coordinator-written one-line summaries replaced three
recursive definitions whose printed form is unreadable (`prune`, `Present`,
`toLocallyFinite`). This is an aid for comparison with the paper, not an audit.

Common reading of the hypothesis (all three agree): $\mu$ is a probability
measure on $\mathbb N$ with mean $m<1$, and there is $L:\mathbb R\to\mathbb R$,
positive on $(0,\infty)$, slowly varying at $+\infty$ in the ratio sense,
a.e. measurable on $(0,\infty)$, with $\mu\{n\}/(L(n)/n^2)\to1$. The law
`conditioned μ n` is the Bienaymé law built from iid labels on all addresses,
pruned, conditioned (Mathlib's conditional measure) on having exactly $n$
vertices; it is the zero measure at a null size. Events are images of sets of
finite plane trees.

## Statement A1 (M1)

For every $\varepsilon>0$,

$$
\mathrm{conditioned}_\mu(n)\Big\{\iota(t):\ \varepsilon<\Big|\frac{\Delta(t)}{n(1-m)}-1\Big|\Big\}\longrightarrow0,
$$

with $\Delta(t)$ the maximal number of children; $x/0=0$ at $n=0$.

## Statement A2 (M2)

For every $\varepsilon>0$, $\mathrm{conditioned}_\mu(n)\{\iota(t):\varepsilon<\Delta^2(t)/n\}\to0$,
where $\Delta^2(t)$ is the largest entry of the depth-first degree list after
removing one occurrence of the maximum: the second largest degree counted with
multiplicity, $0$ for a one-vertex tree.

## Statement B (M3)

For every $j\in\mathbb N$, $\mathrm{conditioned}_\mu(n)(E_j)\to(1-m)m^j$, where
$E_j$ is the set of trees whose lexicographically least maximal-degree vertex
has address length (depth) exactly $j$, the root having depth $0$.

## Statements C1 and C2 (M4, M5)

C1: for every $\varepsilon>0$, with $\lambda=\log(1/m)$ and $h(t)$ the maximal
address length (height),

$$
\mathrm{conditioned}_\mu(n)\Big\{\iota(t):\ \Big|\frac{h(t)}{\log n}-\frac1\lambda\Big|>\varepsilon\Big\}\longrightarrow0 .
$$

C2: the biconditional

$$
\Big[\forall\varepsilon>0\ \exists K\in\mathbb R\ \forall n\ge1:\ \mathrm{conditioned}_\mu(n)\Big\{\Big|h(t)-\frac{\log n}{\lambda}\Big|>K\Big\}\le\varepsilon\Big]\iff\sum_k k\log k\,\mu\{k\}<\infty .
$$

The read-back notes that the $k=0,1$ terms vanish ($\log0=\log1=0$), and that
$m=0$ would give junk values ($\log(1/0)=0$); the hypothesis forces $m>0$ (it
forces $\mu\{n\}>0$ for all large $n$).
