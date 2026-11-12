# Audit of the paper-route research (11 November 2026)

Independent audit of [PAPER_R31_RESEARCH.md](PAPER_R31_RESEARCH.md) by a native Opus subagent (high effort; author of neither document), against the primary PDFs of Armendáriz–Loulakis (arXiv:0912.1516v4, pp. 1–8) and Berger (arXiv:1706.07924v4, pp. 1–6, 11–18). Not verified: Feller IX.7, Nagaev's theorem, Gnedenko's local limit theorem. No builds were run.

## Verdicts

1. **Cited statements:** transcribed correctly. Corrections:
   - AL (3.1)–(3.3) are constructed in AL's proof (p. 6), not hypotheses of Theorem 1, which only asserts that some $q_n$ exists. "Theorem 1 with $q_n=\varepsilon n$" is extracted from the proof.
   - The paper never checks $\Delta$-subexponentiality.
   - The paper's "(3.3)" is the condition AL's proof uses as (3.2); its two-sided `eq:33` implies both.
   - Berger's hypotheses all hold here ($\alpha=1$, $p=1$, span one from eventually consecutive positive atoms).
   - R8 is confirmed.
   - The paper's single value $z=-\lfloor b_n\rfloor-1$ covers only the endpoint. AL's proof is pointwise in $x$, so this suffices for Theorem 3.1; only the uniform (2.6) needs Berger's joint limit.
2. **Ingredients:**
   - Berger's proof uses Gnedenko only through the concentration bound $\mathbb P(S_k=y)\le C/a_k$ (p. 16, (6.1)); no stable density is needed.
   - Berger's (2.1) rests on Nagaev's theorem (cited, not proved) and the $X^\pm$ split of Prop. 5.2.
   - AL's (3.8) is used only through $n\bar F(\ell_n-Lb_n)$, so the finite-mean replacement is valid.
   - AL p. 7 omits a cross term $D_n(L)|r-1|$ in $R(n,L,x)$.
3. **Hard nodes C, E, F, G, L:** mathematically sound. F's exponent can be $2+\eta$.
   - Circularity risk: `LateProofs/StableLimit.lean` imports `MainProofs.M1`, which imports the endpoint `Theorem31`. Absence of the endpoint theorem must be checked at declaration level.
   - Tightness can be proved by truncated Chebyshev instead of the stable limit.
4. **Errors in the cited works:**
   - Berger's Claim 5.3, (5.6), fails for $L\equiv1$ as printed. The corrected form is $\ell(v)-\ell(u)\le c_\delta L(u)(v/u)^\delta$, and Berger's results stand.
   - $\overline W_n/\widehat b_n\to-1$ in probability; the paper's tightness claim is correct.
5. **Generality:** option (c) is a faithful formalization of the paper's proof, provided four adaptations are recorded:
   1. Gnedenko is replaced by the concentration bound;
   2. Nagaev and Prop. 5.2 are replaced by a direct Bennett bound;
   3. AL (3.8) is replaced by finite mean;
   4. AL's thresholds are supplied directly.

   AL's Theorem 1 statement itself (existence of $q_n$) is then not formalized and must not be claimed. Estimate: 100–170 lemmas.

   Recommended refinement:
   - state the AL criterion in AL's proof form, with general $d_n,\ell_n,c_n$ and a maximum-tail hypothesis;
   - drop the unused $\Delta$-subexponentiality and mean hypotheses, keeping subexponentiality as an optional certificate;
   - prove tightness by Chebyshev.
6. **Draft declarations:**
   - **Blocking:** `incrementSumLaw μ n` is the law of $-\sum$ of $n-1$ increments, not of $W_n$; Berger's statement needs a new law.
   - The joint filter must be $\bigsqcap_{N,R}\mathcal P\{n\ge N,\ z\ge Ra_n\}$, not `atTop ×ˢ atTop`, and needs a NeBot proof.
   - The witness $L$ must be fixed, with explicit casts.
   - The final type matches the frozen statement.
