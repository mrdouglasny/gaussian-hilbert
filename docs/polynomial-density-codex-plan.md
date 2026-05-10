# Codex hand-off plan: discharge `polynomial_dense_L2_of_subGaussian`

**Target axiom**: `polynomial_dense_L2_of_subGaussian` in
`GaussianHilbert/PolynomialDensity.lean:96`.

**Why this matters**: this axiom is the analytic foundation under the
entire Wiener-chaos / Hilbert-sum / OU spectral infrastructure. Live
`#print axioms` confirms it's an upstream dependency of every theorem
in the chain — `hermiteMulti_dense`, `wienerChaos_isHilbertSum`,
`chaosCoordEquiv`, `ouSemigroupAct`, and
`ouSemigroupAct_eq_smul_of_mem_wienerChaos`. Discharging it makes the
chaos pipeline end-to-end axiom-free up to the deferred hypercontractivity.

**After discharge**: gaussian-hilbert axiom count drops from 2 to 1
(`ouSemigroupAct_eLpNorm_hypercontractive` is the only remaining axiom).

**Effort estimate**: ~250-400 lines, ~4-7 active days for codex.

---

## Axiom statement (current)

```lean
axiom polynomial_dense_L2_of_subGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ)
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℝ,
      (∫ x, |f x - MvPolynomial.eval (fun i => x i) p| ^ 2 ∂μ) < ε
```

where `IsSubGaussianMeasure μ := ∃ a > 0, Integrable (fun x => exp(a · ∑ᵢ xᵢ²)) μ`.

**Gemini-vet** (DT-2.5, 2026-05-09): **Standard**. Janson Thm 2.6,
Nualart §1.1.1. Sub-Gaussian ⇒ Carleman's condition ⇒ moment problem
determinate ⇒ polynomial density. Hypothesis is tight.

---

## Mathematical strategy (three-step textbook proof)

For `f ∈ L²(μ)` and `ε > 0`:

1. **`Cc(ℝⁿ)` density in `L²(μ)`**: pick `g ∈ Cc(ℝⁿ)` with
   `‖f − g‖_{L²(μ)} < ε/3`. *Mathlib has this directly.*

2. **Stone-Weierstrass on each ball**: let `R > 0` be such that `g`
   is supported in the closed ball `B_R`. Apply Stone-Weierstrass on
   the compact `B_R` to get a polynomial `p ∈ MvPolynomial (Fin n) ℝ`
   with `‖g − p‖_∞,B_R < ε/(3 · μ(B_R)^{1/2})` (sup norm on `B_R`).
   Then `‖g − p‖_{L²(B_R, μ)} ≤ ε/3`.

3. **Sub-Gaussian tail control on `p`**: For `R` large,
   `‖p‖_{L²(B_R^c, μ)} < ε/3`. This uses sub-Gaussianity: any
   polynomial has finite moments under `μ`, so its `L²`-mass on the
   complement of a large ball is arbitrarily small.

**Combine**:
```
‖f − p‖_{L²(μ)}
  ≤ ‖f − g‖_{L²(μ)} + ‖g − p‖_{L²(B_R, μ)} + ‖p‖_{L²(B_R^c, μ)}
  < ε/3 + ε/3 + ε/3 = ε.
```

(Note `g ≡ 0` outside `B_R`, so the `‖g − p‖_{L²(B_R^c, μ)}` term
is actually `‖p‖_{L²(B_R^c, μ)}`.)

---

## Existing API to consume

### From `GaussianHilbert/PolynomialDensity.lean` itself

* `IsSubGaussianMeasure μ` (line 62) — the hypothesis: `∃ a > 0, Integrable (· ↦ exp(a · ∑ xᵢ²)) μ`.
* `isSubGaussianMeasure_pi_gaussianReal n` (line 113, proved) — the
  standard product Gaussian satisfies it.

### From Mathlib

**Step 1 (Cc density)**:
* `MeasureTheory.Lp.boundedContinuousFunction_dense` (or similar) —
  bounded continuous functions are dense in `Lp` for finite measures.
* `Continuous.exists_lipschitz_*` style: get a compactly-supported
  Lipschitz approximation. Pattern: find compact `K` with
  `μ(Kᶜ) < ε`, then use a partition-of-unity-style cutoff.

  *Better-fit primitive (check current Mathlib API)*:
  `Continuous.exists_compactSupport_continuous_nndist_lt_of_*`
  patterns. There's also `MeasureTheory.Memℒp.exists_compactSupport_*`
  in some Mathlib versions. Search around
  `Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`.

**Step 2 (Stone-Weierstrass)**:
* `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints` —
  abstract Stone-Weierstrass for `*-subalgebras` (overkill here since
  ℝ is self-conjugate).
* `Polynomial.continuousMap_polynomial_dense` (or similar): polynomials
  are dense in `C(K, ℝ)` for compact `K ⊆ ℝ`. **For multivariate**:
  `MvPolynomial`-based versions live in
  `Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean`. Search for
  `MvPolynomial`, `Polynomial.functions`, or `polynomialFunctions`
  with `dense_iff_separatesPoints`.
* The multivariate Stone-Weierstrass primitive: the set of
  `MvPolynomial.eval`s separates points on `B_R`, hence its closure
  is `C(B_R)`. Mathlib's
  `polynomialFunctions_closure_eq_top` is the 1D version;
  search for the multivariate analogue or build it via
  `Continuous.exists_polynomial_uniformly_*`.

**Step 3 (Sub-Gaussian tail)**:
* `IsSubGaussianMeasure μ` ⇒ for every polynomial `p`, `MvPolynomial.eval _ p ∈ L²(μ)`.
  Proof: a monomial `xᵢ^k` is dominated by `exp(δ · xᵢ²)` for any
  `δ > 0` via Young's inequality; finite moments follow.
* For the tail bound, use the inequality
  `‖p · 1_{B_R^c}‖_{L²(μ)}² = ∫_{|x| > R} (p x)² dμ ≤ ‖p‖_{L²(μ)}² · μ(B_R^c)^{?}`
  ...actually the cleanest is:
  `∫_{B_R^c} p² dμ = ∫ p² · 1_{B_R^c} dμ → 0 as R → ∞`
  by **dominated convergence**, with dominant `p²` (integrable since
  `p ∈ L²(μ)`) and pointwise convergence to 0 (since `1_{B_R^c}(x) → 0`
  for any fixed `x`).

---

## Step-by-step Lean implementation

### Step A: Helper lemma — sub-Gaussian ⇒ all polynomials in `L²`

```lean
lemma MvPolynomial_eval_memLp_two_of_subGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ) (p : MvPolynomial (Fin n) ℝ) :
    MemLp (fun x => MvPolynomial.eval (fun i => x i) p) 2 μ := by
  -- Each monomial xᵢ^k satisfies xᵢ^{2k} ≤ (2k/(a·e))^k · exp(a · xᵢ²),
  -- which is bounded times exp(a · ∑ xᵢ²). So xᵢ^{2k} is integrable
  -- under μ. By induction on the polynomial structure (finite linear
  -- combination of monomials), p² is integrable.
  --
  -- Equivalently: use AEStronglyMeasurable (it's continuous + measurable)
  -- + the integrability bound from IsSubGaussianMeasure.
  sorry  -- ~50-80 lines
```

### Step B: Polynomial-tail bound

```lean
lemma MvPolynomial_eval_L2_tail_tendsto {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ) (p : MvPolynomial (Fin n) ℝ) :
    Filter.Tendsto (fun R : ℝ =>
      ∫ x in {x : Fin n → ℝ | R < ‖x‖}, |MvPolynomial.eval (fun i => x i) p| ^ 2 ∂μ)
      Filter.atTop (𝓝 0) := by
  -- DCT: pointwise 1_{R < ‖x‖} → 0 as R → ∞; dominated by p², which is in L¹(μ)
  -- by Step A.
  sorry  -- ~30-50 lines (mostly Mathlib DCT API)
```

(Use `MeasureTheory.tendsto_setIntegral_of_*` if available, or apply
DCT directly via `tendsto_integral_filter_of_dominated_convergence`.)

### Step C: Multivariate Stone-Weierstrass on a ball

This is the part most likely to need new construction if Mathlib
doesn't have it directly. The 1D case is in Mathlib; the multivariate
analogue may require building a `Subalgebra` argument by hand:

```lean
lemma exists_mvPolynomial_uniform_approx
    {n : ℕ} (R : ℝ) (hR : 0 ≤ R)
    (g : (Fin n → ℝ) → ℝ) (hg_cont : Continuous g)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℝ,
      ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) R,
        |g x - MvPolynomial.eval (fun i => x i) p| < ε := by
  -- 1. The set `{ MvPolynomial.eval ∘ coordsApply p : p : MvPolynomial _ ℝ }`
  --    forms a Subalgebra of C(closedBall 0 R, ℝ).
  -- 2. It contains constants (via C-valued polynomials) and the
  --    coordinate projections, hence separates points.
  -- 3. Apply ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
  --    (or the appropriate Stone-Weierstrass primitive).
  -- 4. Density in sup-norm ⇒ existence of uniform-ε polynomial approximant.
  sorry  -- ~80-150 lines depending on Mathlib's primitive shape
```

**Mathlib API hint**: search for `polynomialFunctions` and
`MvPolynomial.aeval` in `Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean`
and `Mathlib/Topology/ContinuousMap/Polynomial.lean`. If the primitive
exists for `MvPolynomial`, this step is ~10 lines. If not, build it
via `Subalgebra` + `separatesPoints` + Stone-Weierstrass.

### Step D: `Cc(ℝⁿ)` density in `L²(μ)`

```lean
lemma exists_continuous_compactSupport_L2_approx {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : (Fin n → ℝ) → ℝ, Continuous g ∧ HasCompactSupport g ∧
      (∫ x, |f x - g x| ^ 2 ∂μ) < ε := by
  -- Use MeasureTheory.Lp.boundedContinuousFunction_dense or equivalent.
  -- Then cutoff to compact support via a smooth bump.
  sorry  -- ~20-40 lines
```

### Step E: The main theorem

```lean
theorem polynomial_dense_L2_of_subGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ)
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℝ,
      (∫ x, |f x - MvPolynomial.eval (fun i => x i) p| ^ 2 ∂μ) < ε := by
  -- Step 1: choose g ∈ Cc with ‖f - g‖_{L²(μ)}² < ε/9.
  obtain ⟨g, hg_cont, hg_supp, hfg⟩ :=
    exists_continuous_compactSupport_L2_approx μ f hf (ε / 9) (by linarith)
  -- Step 2: find R such that supp(g) ⊆ closedBall 0 R.
  --   `HasCompactSupport.exists_pos_le_norm` style.
  obtain ⟨R, hR_pos, hR_supp⟩ : ∃ R > 0,
      ∀ x, R ≤ ‖x‖ → g x = 0 := by
    sorry
  -- Step 3: find polynomial p uniformly approximating g on closedBall 0 R.
  --   Choose uniform-ε to make L²(B_R, μ) contribution < ε/9. Need
  --   ε_unif² · μ(B_R) ≤ ε_unif² · 1 < ε/9, so ε_unif < √(ε/9).
  obtain ⟨p, hp_unif⟩ :=
    exists_mvPolynomial_uniform_approx (n := n) R hR_pos.le
      g hg_cont (Real.sqrt (ε / 9)) (Real.sqrt_pos.mpr (by linarith))
  -- Step 4: bound ‖p‖_{L²(B_R^c, μ)} < ε/9 using sub-Gaussian tail
  --         (Step B applied to p, choosing R large enough — actually
  --         choose R BEFORE step 3 to control the tail, then make
  --         ε_unif small enough for the ball contribution).
  --
  -- (Reorder Steps 2-4: first pick R₁ large for sub-Gaussian tail of any
  -- polynomial candidate, then enlarge to R := max R₁ R_supp(g), then
  -- get the uniform approximant.)
  sorry  -- ~80-150 lines of triangle inequality + bookkeeping
```

**Subtlety**: the proof has a quantifier ordering issue. The polynomial
`p` is chosen to approximate `g` on `B_R`, but `p` itself extends
outside `B_R` and we need its L²-tail to be small. The clean way:

1. Pick `R_g` with `supp(g) ⊆ B_{R_g}`.
2. Pick the polynomial approximant `p` on `B_{R_g}` with uniform error
   `δ`. Now `p` is fixed.
3. `p ∈ L²(μ)` by Step A. By Step B (tail tendsto 0), there's `R_p` such
   that `‖p · 1_{B_{R_p}^c}‖_{L²(μ)} < ε/9`.
4. But we want the tail at `R_g`! If `R_g ≥ R_p`, fine. Otherwise the
   tail beyond `R_g` is not controlled by what Step B gives.

**Better approach**: ε-η dance.
- Fix `f, hf, ε`. Pick `g` approximating `f` to within `ε/9` in L².
- Let `R_g` bound `supp(g)`.
- Note: for *any* polynomial `p`, the tail
  `‖p · 1_{B_{R_g}^c}‖_{L²(μ)}` is some fixed number depending on `p` and `R_g`.
- The uniform Stone-Weierstrass approximant `p` lives in
  `MvPolynomial (Fin n) ℝ`, but with uniform error δ on `B_{R_g}`,
  its **L² norm overall** is at most `‖g‖_∞ + δ · √(μ(B_{R_g}))` — i.e.,
  controlled.
- So `p` has a uniform L²-bound. Combine with sub-Gaussian to get a
  uniform tail bound: there's `R_p ≥ R_g` with the tail below `ε/9`.
- Since `g ≡ 0` outside `B_{R_g}`, on `B_{R_p} \ B_{R_g}` we have
  `|f − p|² ≈ |f − 0|² + |p|² + cross terms`, all controllable.

The textbook approach actually just observes that **any sequence of
polynomials approximating in `Cc` ∪ uniform sense automatically
approximates in `L²(μ)`**, *because* sub-Gaussianity gives a uniform
moment bound. The bookkeeping is fiddly but the math is fine.

---

## Acceptance criteria

* `lake build` succeeds. **Must be verified before reporting**, not
  assumed (per the OUEigenfunctions.lean post-mortem 2026-05-10).
* `grep -nE '^axiom polynomial_dense_L2_of_subGaussian'
    GaussianHilbert/PolynomialDensity.lean` returns nothing.
* `#print axioms GaussianHilbert.hermiteMulti_dense` no longer
  references `polynomial_dense_L2_of_subGaussian` (only `propext`,
  `Classical.choice`, `Quot.sound`).
* Update `AXIOM_AUDIT.md` (top-level): move the row to "Recently
  discharged"; total active drops from 2 to 1.

---

## Notes for codex

* **Lake-build verification is non-negotiable**: the previous Route 1
  codex run claimed success but had build errors. Run `lake build` to
  completion and confirm "Build completed successfully" appears in the
  output before reporting.

* **Mathlib primitive search**: spend the first ~1 hour searching for
  the right `Cc`-density and multivariate Stone-Weierstrass lemmas in
  current Mathlib. Specific search targets:
  - `Mathlib/MeasureTheory/Function/ContinuousMapDense.lean` for Cc
    density.
  - `Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean` and
    `Mathlib/Topology/ContinuousMap/Polynomial.lean` for the
    multivariate Stone-Weierstrass.
  - `MvPolynomial.aeval`, `polynomialFunctions`,
    `Polynomial.functions`.

* **Quantifier-ordering caution**: as noted in Step E, the polynomial
  approximant `p` is fixed first, then the tail beyond `B_{R_g}`
  needs control. Use the uniform L²-bound on the approximant (not just
  the uniform sup-norm) to get a tail bound that depends on the
  *uniform δ* rather than `p` itself.

* **Heartbeat budget**: Step E's combined estimate has multiple
  triangle-inequality steps and may need `set_option maxHeartbeats
  1600000`. Place it directly above the `theorem` declaration.

* **No new axioms**: the entire chain is dischargeable from Mathlib +
  the existing `IsSubGaussianMeasure` definition. If a substep
  doesn't go cleanly, document the missing Mathlib lemma but don't
  axiomatize.

* **Cross-repo**: this plan does *not* touch any other repo.

---

## Downstream impact

Once discharged, `#print axioms` should give the following clean
chains:

```
hermiteMulti_dense  →  [propext, Classical.choice, Quot.sound]
wienerChaos_isHilbertSum  →  [propext, Classical.choice, Quot.sound]
chaosCoordEquiv  →  [propext, Classical.choice, Quot.sound]
ouSemigroupAct  →  [propext, Classical.choice, Quot.sound]
ouSemigroupAct_eq_smul_of_mem_wienerChaos  →  [propext, Classical.choice, Quot.sound]
```

The only remaining axiom in gaussian-hilbert is then
`ouSemigroupAct_eLpNorm_hypercontractive`. The chaos infrastructure
becomes axiom-free up to that final hypercontractivity step. pphi2's
Cluster A still depends on hypercontractivity (and on pin sync), but
the analytic foundation under everything is solid.
