# Coding-interface blueprint for M3, Propositions 4.2–4.3, M4–M5 (10 November 2026)

Read-only research worker (gpt-6.1-sol, medium; task `.orchestration/coding-interface-research`). Proposed signatures are not yet elaborated; not proof evidence.

The recommended common interface is a **cyclic residual word**, followed by two deterministic statistics: its reversed weak-record count and its first passage to a negative level. This supports M3 and Proposition 4.2; adding the exterior-size identity repairs Proposition 4.3.

I checked the frozen statements, manuscript passages, route blueprint and audit, and the declarations listed below. This is an exploratory design review: proposed signatures have not been elaborated. I edited nothing, ran no builds, and launched no agents or model processes.

**1. Shared coding interface**

Use `PlaneTree` for deterministic work and retain `finiteTreeEvent` for the frozen probability statements.

The checked conventions are:

- `PlaneTree` addresses use zero-based child indices; `positiveAddress` adds one to every index for `LocallyFinite`.
- `vertices`, `degrees`, and `increments` are root-first preorder. `map_degreeAt_vertices` connects degrees to actual vertex occurrences.
- `maxDegreeVertex` is the lexicographically first maximizer, including prefix order. `positiveAddress_lt_iff` and `positiveAddress_le_iff` preserve this choice.
- `attachedChild t i` uses source slots $i\ge1$ and accesses child index `i - 1`. Its value at zero is totalized and should never enter a source-facing theorem.
- `none` means an absent child; `some leaf` is a present tree of height zero.
- Records must be **weak ascending records**, comparing with time zero and excluding time zero from the count.

Here is a proposed small deterministic API, in `SubcriticalCauchy.Bienayme`, with `open BGW`. These definitions are exact proposed Lean text, subject to elaboration:

```lean
noncomputable def firstMaxIndex (ds : List ℕ) : ℕ :=
  ds.idxOf (listMaxDegree ds)

noncomputable def cyclicResidual (x : List ℤ) : List ℤ :=
  (x.rotate (firstMaxIndex (wordDegrees x) + 1)).take (x.length - 1)

def prefixSum (x : List ℤ) (k : ℕ) : ℤ :=
  (x.take k).sum

noncomputable def weakRecordCount (x : List ℤ) : ℕ :=
  ((Finset.range (x.length + 1)).filter fun k =>
    0 < k ∧ ∀ i < k, prefixSum x i ≤ prefixSum x k).card

def firstHit? (d : ℕ) (x : List ℤ) : Option ℕ :=
  (List.range (x.length + 1)).find?
    (fun k => decide (prefixSum x k = -(d : ℤ)))

noncomputable def lastZero (x : List ℤ) : ℕ :=
  ((Finset.range (x.length + 1)).filter fun k =>
    prefixSum x k = 0).sup id

def exteriorSize (t : PlaneTree) : ℕ :=
  t.size - (maxDegreeFringe t).size
```

The coordinator should fix these contracts first:

```lean
theorem firstMaxIndex_degrees (t : PlaneTree) :
    firstMaxIndex t.degrees =
      t.vertices.idxOf (maxDegreeVertex t)

theorem length_cyclicResidual_tree (t : PlaneTree) :
    (cyclicResidual t.increments).length = t.size - 1

theorem sum_cyclicResidual_tree (t : PlaneTree) :
    (cyclicResidual t.increments).sum = -(maxDegree t : ℤ)

theorem maxDegreeDepth_eq_weakRecordCount (t : PlaneTree) :
    maxDegreeDepth t =
      weakRecordCount (cyclicResidual t.increments).reverse

theorem firstHit_cyclicResidual_tree (t : PlaneTree) :
    firstHit? (maxDegree t) (cyclicResidual t.increments) =
      some ((maxDegreeFringe t).size - 1)

theorem take_firstHit_eq_attachedForest (t : PlaneTree) :
    (cyclicResidual t.increments).take
        ((maxDegreeFringe t).size - 1) =
      PlaneForest.increments (attachedForest t)

theorem exteriorSize_eq_lastZero (t : PlaneTree) :
    exteriorSize t =
      lastZero (cyclicResidual t.increments).reverse

theorem height_le_exteriorSize_add (t : PlaneTree) :
    height t ≤ exteriorSize t + 1 + attachedForestHeight t
```

The stopping theorem should also have a version for every `k ≤ maxDegree t`: the prefix ending at its first hit of `-k` is the increment word of `(attachedForest t).take k`.

For the depth formula, first prove the general preorder identity. For the vertex at index $j$, with walk $S$,

$$
|u_j|
=
\#\{0\le i<j:S_i=\min_{i\le r\le j}S_r\}.
$$

Reversing the first $j$ increments gives weak ascending records. A further excursion argument shows that extending to the **entire reversed cyclic residual** adds no records. That extension is a substantive lemma, not merely list rewriting.

Existing pieces:

| Requirement | Checked existing support | Missing work |
|---|---|---|
| Tree excursion | `isTreeExcursion_increments`, `sum_take_increments_nonneg`, `sum_increments` | Vertex-level height formula |
| Unique decoding | `ofIncrements?_eq_some_iff`, `isTreeExcursion_iff_existsUnique` | Stopped-prefix decoder |
| Forest decoding | `IsForestCode`, `isForestCode_iff_existsUnique`, `PlaneForest.ofDegrees?` | Identify successive first-passage blocks |
| Downward skip-free passage | `exists_first_sum_take_eq` | Packaged first-hit identities |
| Cyclic tree/bridge correspondence | `shiftEquiv`, `cond_pi_countBridges_singleton_shift`, `cond_pi_countBridges_apply_eq_tsum` | Residual statistic law |
| Fringe/forest semantics | `fringe_maxDegreeVertex`, `length_attachedForest`, `fringe?_append` | Contiguous preorder fringe block |
| Height lower bounds | `attachedForestHeight_le_height`, `depth_add_one_add_attachedForestHeight_le` | Exterior-size upper bound |

Preorder is lexicographic on valid addresses, but I did not find an exported sortedness theorem in `Vertices.lean`; add that helper before identifying the two first-maximum conventions.

**2. Law interface: strengthen insertion density**

Theorem 3.1 alone concerns ordered deletion. A rotation chosen from the same residual word need not preserve an iid law. The joint insertion-position law supplies the missing information.

For length $n$, define:

```lean
noncomputable def uniformInsertionPosition (n : ℕ) : Measure ℕ :=
  (n : ℝ≥0∞)⁻¹ •
    ∑ i : Fin n, Measure.dirac i.val

noncomputable def deletionWithPosition (n : ℕ)
    (ω : Fin n → ℕ) : ℕ × (Fin (n - 1) → ℤ) :=
  (firstMaxIndex (List.ofFn ω), deletedIncrements n ω)
```

The useful exact atom statement is:

```lean
theorem deletionWithPosition_succ_atom
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {m : ℕ} (i : Fin (m + 1)) (z : Fin m → ℕ) (r : ℕ)
    (hr : ∀ j, z j < r) (hsum : r + ∑ j, z j = m) :
    ((MaximumSwapLaw.bridgeCountsLaw μ (m + 1)).map
        (deletionWithPosition (m + 1)))
      {(i.val, fun j => (z j : ℤ) - 1)} =
      μ {r} * (∏ j, μ {z j}) /
        (Measure.pi fun _ : Fin (m + 1) => μ)
          (BGW.countBridges (m + 1))
```

This follows from `deletedIncrements_succ_preimage`, `insertNth_injective_left_of_lt`, and the existing insertion identities: specifying the position selects exactly one preimage. The existing deleted-law atom has an additional factor $m+1$ because it sums over positions.

Target:

```lean
theorem deletionWithPosition_tvDist
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (fun n : ℕ =>
      tvDist
        ((MaximumSwapLaw.bridgeCountsLaw μ n).map
          (deletionWithPosition n))
        ((uniformInsertionPosition n).prod
          (Measure.pi fun _ : Fin (n - 1) => incrementLaw μ)))
      atTop (𝓝 0)
```

Reuse `endpoint_typical_residual_set`, the endpoint normalization, and `tvDist_le_of_density_on_of_nonneg`. This is **substantial**, but closely follows the proved Theorem 3.1 assembly.

If insertion occurs at zero-based position $i$, the cyclic residual is `deletedWord.rotate i`. There are $n=N+1$ insertion positions for a residual of length $N$; positions zero and $N$ induce the same rotation. No problem arises: every fixed rotation preserves the iid law, so their mixture does too. Do not replace the position law with an unsupported uniform law on `Fin N`.

For tree-law packaging, a convenient auxiliary carrier is:

```lean
noncomputable def finitePlaneLaw (μ : Measure ℕ) (n : ℕ) :
    Measure PlaneTree :=
  Measure.sum fun t : PlaneTree =>
    conditioned μ n {t.toLocallyFinite} • Measure.dirac t
```

Prove its event characterization using `conditioned_apply_eq_tsum`. Then export:

```lean
theorem cyclicResidual_tvDist
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ) :
    Tendsto (fun n : ℕ =>
      tvDist
        ((finitePlaneLaw μ n).map
          (fun t => cyclicResidual t.increments))
        ((Measure.pi fun _ : Fin (n - 1) => incrementLaw μ).map
          (fun x => List.ofFn x)))
      atTop (𝓝 0)
```

Use the existing discrete measurable-space conventions for lists and `PlaneTree`.

On a unique maximum, the cyclic residual is rotation invariant, so the existing `conditioned_bridge_rotation_invariant_event` applies. Ties require care: obtain their vanishing probability from M1–M2, or directly from the strict-maximum typical set. Exact unrestricted rotation invariance is not available for first-maximum deletion.

**3. M3 at lemma level**

Let $W$ be the iid walk, $\tau=\inf\{k\ge0:W_k=-1\}$, and $C_N$ its weak-record count through time $N$.

1. **Finite reversal identity — routine/substantial.**  
   Under the finite iid law, for every $k$,

   $$
   \mathbb P(k\text{ is a weak record})=\mathbb P(\tau>k).
   $$

   Reverse the first $k$ coordinates. The record condition becomes nonnegativity of every forward partial sum. Skip-free downward increments identify this with avoiding $-1$ through time $k$. Include $k=0$ separately.

2. **Exploration law — substantial.**  
   The stopped word at $\tau$ decodes to an unconditioned Bienaymé tree, and $\tau$ is its vertex count. Establish this by finite excursion atoms and `walkWeight_increments`; it need not require a general exploration-process construction.

3. **Expected progeny — substantial, with existing input.**  
   I checked:

   ```lean
   BGW.LocallyFinite.lintegral_generationSize
   ```

   gives generation expectation equal to the offspring mean to the generation power. I did not find an exported expected-total-size theorem. Add the identity “total vertices = sum of generation sizes,” use subcritical almost-sure finiteness and Tonelli, obtaining

   $$
   \mathbb E\tau=\sum_{h\ge0}m^h=\frac1{1-m}.
   $$

4. **Record renewal — hard.**  
   Negative drift (`walkAverage_ae_tendsto`) makes the total number $C_\infty$ of positive-time weak records finite almost surely. Restart at the first positive-time visit to $[0,\infty)$; subsequent weak records regenerate. With $r$ the probability of that visit,

   $$
   \mathbb P(C_\infty=j)=(1-r)r^j.
   $$

   Either develop stopped iid independence or prove it by summing over finite stopping words. Do not assume overshoots vanish.

5. **Identify $r=m$ — routine after preceding lemmas.**

   $$
   \mathbb EC_\infty
   =\sum_{k\ge1}\mathbb P(\tau>k)
   =\mathbb E\tau-1
   =\frac m{1-m}
   =\frac r{1-r}.
   $$

6. **Pass to M3 — routine.**  
   Almost-sure stabilization gives the finite-record-count distribution limit. Finite reversal preserves iid laws; `cyclicResidual_tvDist` and the deterministic depth formula transfer it to the frozen event.

**4. Propositions 4.2 and 4.3**

For Proposition 4.2, preserve missing slots:

```lean
def attachedSlots (k : ℕ) (t : PlaneTree) :
    Fin k → Option BGW.LocallyFinite.Tree :=
  fun i => (attachedChild t (i.val + 1)).map
    PlaneTree.toLocallyFinite
```

Proposed source-facing target:

```lean
theorem attachedSlots_tvDist
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1 - (offspringMean μ).toReal) :
    Tendsto (fun n : ℕ =>
      tvDist
        ((finitePlaneLaw μ n).map (attachedSlots ⌊δ * n⌋₊))
        ((forestLaw μ ⌊δ * n⌋₊).map
          (fun F i => some (F i))))
      atTop (𝓝 0)
```

Required steps:

- Decode the finite prefix stopped at $-\lfloor\delta n\rfloor$, with explicit failure output — **substantial**.
- Prove successive iid first-passage blocks have product Bienaymé law — **hard**, sharing stopped-word machinery with M3.
- Prove $\tau_{\lfloor\delta n\rfloor}/n\to\delta/(1-m)<1$ from the strong law and skip-free descent — **substantial**.
- Identify the stopped prefix with the first attached children whenever they exist — **substantial deterministic work**.
- Apply TV contraction; truncation failure vanishes — **routine**. Handle $\delta=0$ directly.

`ForestWalkLaw` supplies conditioned forest-size formulas, not the stopped iid block independence itself.

For Proposition 4.3, use $Q_h=\texttt{survival μ ⌈h⌉₊}$. Export separate statements:

```lean
theorem conditioned_height_below_tendsto_one
    (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hμ : IsMeasurableSubcriticalCauchyOffspring μ)
    (h : ℕ → ℝ) (hh : Tendsto h atTop atTop)
    (hQ : Tendsto (fun n : ℕ =>
      (n : ℝ) * (survival μ ⌈h n⌉₊).toReal) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      conditioned μ n (finiteTreeEvent fun t =>
        (height t : ℝ) < h n)) atTop (𝓝 1)
```

The companion replaces `hQ`’s limit by `atTop` and the event by `h n ≤ (height t : ℝ)`.

The lower bound uses Proposition 4.2 with $\delta=(1-m)/2$, `attachedForestHeight_le_height`, and `forestBelowReal_floor_tendsto_zero`.

The attached-forest upper bound uses two child blocks and child-order reversal at the selected vertex. Prove reversal preserves the selected first maximum and offspring-product weight; the route audit explicitly supports this even with ties. Cover both blocks by prefixes of length $\lfloor2(1-m)n/3\rfloor$ with probability tending to one, using M1. Apply `forestBelowReal_floor_tendsto_one`.

For **full height**, let $N=n-1$, $d=\Delta(t)$, and $\tau_d$ be the first passage of the cyclic residual to $-d$. Then

$$
R(t)=n-|\operatorname{fringe}(u_*)|=N-\tau_d
=\operatorname{lastZero}(\text{reversed residual}).
$$

Negative drift makes the infinite iid last zero finite almost surely. Hence `cyclicResidual_tvDist` makes $R(\mathcal T_n)$ tight. This is **substantial** and controls exterior branches as well as ancestor depth.

On $R\le K$,

$$
H(\mathcal T_n)\le K+1+H_{\mathrm{forest}}.
$$

For fixed $K$, `survival_ratio_tendsto` implies that shifting a diverging threshold downward by $K+1$ preserves $nQ_h\to0$. First fix $K$, take the limit in $n$, then let the tightness error vanish.

**5. M4 and M5**

M4 follows from Proposition 4.3 at $(1\pm\varepsilon)\log n/\log(1/m)$. The checked `survival_log_upper_tendsto_zero`, `survival_log_lower_tendsto_atTop`, and `exists_eta_log_exponent` already provide the analytic inputs. Alternatively, `forest_log_band_tendsto_one` supplies the forest concentration directly, followed by the same full-height transfer.

For M5, write $c_n=\log n/\log(1/m)$.

- **Finite logarithmic moment:** X7 gives $Q_k/m^k\to c>0$. For every $\lambda_n\to\infty$, Proposition 4.3 controls the upper threshold $c_n+\lambda_n$. For the lower tail use the enlarged threshold $\max(c_n-\lambda_n,c_n/2)$, which diverges and still has $nQ_h\to\infty$. This handles nonpositive original thresholds.
- **U4.9:** prove the sequential characterization of uniform tightness by contradiction and diagonal selection of bad indices and increasing tolerances. Absorb finitely many initial sizes using $H(t)\le n-1$ on size-$n$ trees. Null-size conditioned measures cause no difficulty.
- **Infinite logarithmic moment:** X7 gives $Q_k/m^k\to0$. For every fixed $K$, Proposition 4.3 already yields $\mathbb P(H(\mathcal T_n)<c_n-K)\to1$, directly contradicting tightness.
- **U4.10:** to retain the stronger diverging-shift assertion, choose strictly increasing $N_p\ge p$ such that, for all $n\ge N_p$, $c_n\ge2p$ and $nQ_{\lceil c_n-p\rceil}\le1/p$. Set $r_n=\max\{p:N_p\le n\}$, with a harmless initial default. Then $r_n\to\infty$, $c_n-r_n\ge c_n/2\to\infty$, and Proposition 4.3 applies.

**6. Work allocation and risks**

Fix the shared definitions and obtain the required independent interface review before substantial dependent implementation. Then assign disjoint modules:

| Worker | Owned work |
|---|---|
| Coding | Preorder, fringe blocks, records, stopping and exterior-size identities |
| Laws | Joint insertion density, joint TV, cyclic residual TV |
| IID exploration | Stopped forests, independence, hitting-time asymptotics, expected progeny |
| Consumers, after dependencies | M3 renewal; Proposition 4.3; M4–M5 tightness/diagonal lemmas |

The last group can split further once shared APIs stabilize. Keep all helpers outside frozen files; frozen targets receive proof text only.

Principal risks:

- The manuscript’s assertion that tight maximal-vertex depth suffices for full-height transfer is unsupported by that fact alone. The exterior-size argument repairs the proof route.
- Strict records give the wrong M3 statistic, especially with zero increments.
- Ordered-deletion TV alone does not justify an adaptively rotated residual law.
- Do not identify absent children with leaves.
- Real heights require ceilings; shifted-threshold estimates require diverging thresholds.
- The manuscript’s diagonal passage uses undefined `c_n` where its surrounding notation indicates `u_n`; the construction above avoids that notation issue.
- Existing TV uses twice the paper’s normalization; convergence is unaffected.
- `FORMALIZATION_REPORT.md` is stale relative to the checked M1, M2 and Theorem 3.1 proof bodies. I did not independently reverify their axiom closures.

The hardest unproved components are the deterministic record/height bridge and stopped iid exploration machinery. Their signatures above are proposals, not checked library declarations or a passing statement-fidelity verdict.