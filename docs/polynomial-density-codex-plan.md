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
(`ouSemigroupAct_eLpNorm_hypercontractive` is the only remaining axiom),
AND `#print axioms hermiteMulti_dense` lists only the standard Lean
logical axioms.

**Effort estimate**: ~250-400 lines, ~4-7 active days for codex.

---

## ⚠️ Anti-delegation guards (READ FIRST)

A previous codex run (2026-05-10) attempted to "discharge" this axiom
by replacing `axiom polynomial_dense_L2_of_subGaussian ...` with
`theorem polynomial_dense_L2_of_subGaussian ... := by simpa using
GaussianField.GeneralResults.polynomial_dense_L2_of_subGaussian ...`,
where the right-hand side was an **upstream axiom** in a pinned
gaussian-field package. This is a **false discharge** and is the
single most important failure mode to avoid. The trust closure is
unchanged; only the name has moved. Revert was required.

**These rules are non-negotiable**:

1. **Forbidden: importing the proposition (under any name) from an
   upstream package and delegating to it.** If the upstream is
   axiomatic, importing it is identical to keeping the axiom locally.
   In particular: do **not** import any of
   - `GeneralResults.PolynomialDensityGaussian`
   - `GaussianField.GeneralResults.polynomial_dense_L2_of_subGaussian`
   - any other "moment problem / polynomial dense in L²" axiomatic
     statement from gaussian-field, markov-semigroups, or elsewhere
     in the closure.

2. **Required: the proof must invoke only Mathlib's primitives and
   logical axioms.** The post-discharge `#print axioms` output for
   `polynomial_dense_L2_of_subGaussian` (now a theorem) MUST be
   *exactly*
   ```
   [propext, Classical.choice, Quot.sound]
   ```
   No additional axiom names. Verify before reporting.

3. **Required: paste the live `#print axioms` output for FOUR
   downstream consumers in your report.** These are:
   - `GaussianHilbert.polynomial_dense_L2_of_subGaussian`
   - `GaussianHilbert.hermiteMulti_dense`
   - `GaussianHilbert.wienerChaos_isHilbertSum`
   - `GaussianHilbert.ouSemigroupAct_eq_smul_of_mem_wienerChaos`

   Each one must list **only** `propext`, `Classical.choice`, `Quot.sound`
   (plus whatever `ouSemigroupAct_eLpNorm_hypercontractive` it
   transitively pulls in for the last theorem, since that axiom is
   intentionally kept).

4. **Forbidden: claiming success without running `lake build`.** Run
   it to completion. Confirm "Build completed successfully" appears.
   Copy the exact build output into the report.

5. **If the proof needs material from gaussian-field or
   markov-semigroups that is itself proved (not axiomatized) — that
   is fine.** The rule is specifically about *axiomatic* upstream
   facts, not proved theorems.

In short: this discharge must produce **new mathematics in Lean**
(actual Cc-density + Stone-Weierstrass + sub-Gaussian tail bound),
not a rename. The verification rules above exist to make this
unambiguous.

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

## Plan structure: three independent codex milestones

The discharge is broken into **three independent milestones**, each a
self-contained codex hand-off with its own acceptance criteria and
clean-build-passing intermediate state. Each milestone is a separate
work session; **do not start a later milestone until the prior one is
landed and the build is clean**.

The motivation: a single-shot attempt at this entire discharge is
high-risk (witness the OU spectral discharge needing a second pass,
and the polynomial-density delegation attempt that was reverted). By
segmenting, each codex run has a small, well-defined scope, which
both improves the success rate and makes failures cheap to roll back.

| Milestone | Scope | Output | Lines | Codex effort |
|---|---|---|---|---|
| **M1** | Sub-Gaussian polynomial integrability + L²-tail | 2 helper lemmas, no axiom touched | ~80-130 | 1-2 days |
| **M2** | Multivariate Stone-Weierstrass on closed balls | 1 helper lemma, no axiom touched | ~80-150 | 1-2 days |
| **M3** | Cc-density + main theorem (combine M1 + M2) | The discharge | ~120-200 | 2-3 days |

After M1 + M2 both land, the heavy lifting is done. M3 is the
quantifier-ordering bookkeeping + Cc-density, which is the
historically-fiddliest step but has clean inputs.

Between milestones, the repo is in a **functioning intermediate
state**: `lake build` passes, the original axiom is still in place,
and the new helper lemmas are available for use by subsequent
milestones. Only M3 actually removes the axiom.

---

## Milestone M1: Sub-Gaussian polynomial integrability + L²-tail

**Scope**: prove two helper lemmas. **The axiom is NOT touched in M1.**

**Acceptance signal**: `lake build` passes; two new theorems available;
0 sorries added; 0 axioms added.

### M1.1: every polynomial is in L²(μ) under sub-Gaussian assumption

```lean
namespace GaussianHilbert

lemma MvPolynomial_eval_memLp_two_of_subGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ) (p : MvPolynomial (Fin n) ℝ) :
    MemLp (fun x => MvPolynomial.eval (fun i => x i) p) 2 μ := by
  sorry
```

**Proof sketch**:

* Pick `a > 0` and `hInt : Integrable (fun x => exp(a · ∑ xᵢ²)) μ`
  from `hμ` (unfold `IsSubGaussianMeasure`).
* Each monomial `xᵢ^k` satisfies a Young inequality:
  `|xᵢ|^k ≤ Cₖ · (1 + exp(a · xᵢ²))` for `Cₖ` depending on `k, a` (concretely
  `Cₖ = (k/(2a·e))^{k/2}`). Therefore `|xᵢ|^k` is integrable.
* `MvPolynomial.eval (fun i => x i) p` is a finite ℝ-linear combination
  of monomials `∏ⱼ xⱼ^{αⱼ}` over the support of `p`. By Cauchy-Schwarz +
  iteration, each such monomial is in L²(μ).
* AE-strong-measurability of the polynomial evaluation is automatic
  (it's a continuous polynomial function).

**Mathlib API**:
- `MvPolynomial.as_sum`: write `p` as a finite sum of monomials with
  coefficients.
- `MeasureTheory.Integrable.add` / `.mul` / etc. for the linear
  combination.
- `MeasureTheory.MemLp.of_bound` for the L² conclusion from
  integrability of `p²` via the dominating exponential.

**Estimated effort**: 40-70 lines, ~1 day.

### M1.2: polynomial L²-tail vanishes as R → ∞

```lean
lemma MvPolynomial_eval_L2_tail_tendsto {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ) (p : MvPolynomial (Fin n) ℝ) :
    Filter.Tendsto (fun R : ℝ =>
      ∫ x in {x : Fin n → ℝ | R < ‖x‖},
        |MvPolynomial.eval (fun i => x i) p| ^ 2 ∂μ)
      Filter.atTop (𝓝 0) := by
  sorry
```

**Proof sketch**: dominated convergence.

* Set `g x := |MvPolynomial.eval ... p x|^2`. By M1.1, `g ∈ L¹(μ)`.
* The integrand at level `R` is `g · 1_{R < ‖x‖}`.
* Pointwise: for any `x`, `1_{R < ‖x‖}(x) → 0` as `R → ∞` (take any
  `R > ‖x‖`).
* Dominated by `g`, integrable.
* Apply `MeasureTheory.tendsto_setIntegral_of_le_lintegral` or
  `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`
  (the second is more standard).

**Mathlib API**:
- `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`.
- `MeasureTheory.setIntegral_eq_integral_indicator` to switch between
  set integral and indicator-weighted integral.

**Estimated effort**: 30-50 lines, ~half a day.

### M1 acceptance criteria

* `lake build` succeeds.
* Both `MvPolynomial_eval_memLp_two_of_subGaussian` and
  `MvPolynomial_eval_L2_tail_tendsto` compile, no `sorry`.
* `grep -nE '^axiom polynomial_dense_L2_of_subGaussian' GaussianHilbert/PolynomialDensity.lean`
  still finds the axiom — **the axiom is intentionally unchanged in M1**.
* `#print axioms GaussianHilbert.MvPolynomial_eval_memLp_two_of_subGaussian`
  yields `[propext, Classical.choice, Quot.sound]`.
* Same for `MvPolynomial_eval_L2_tail_tendsto`.

### M1 codex report requirements

Codex must paste:
1. The exact output of `lake build` showing "Build completed successfully".
2. The exact output of `#print axioms` for both new lemmas.

---

## Milestone M2: Multivariate Stone-Weierstrass on closed balls

**Scope**: prove one helper lemma. **The axiom is NOT touched in M2.**

**Acceptance signal**: `lake build` passes; one new theorem available;
0 sorries added; 0 axioms added.

**Independence from M1**: M2 can be done in parallel with M1 (no
inter-milestone dependency at the lemma level).

### M2.1: uniform polynomial approximation on a closed ball

```lean
lemma exists_mvPolynomial_uniform_approx
    {n : ℕ} (R : ℝ) (hR : 0 ≤ R)
    (g : (Fin n → ℝ) → ℝ) (hg_cont : Continuous g)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℝ,
      ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) R,
        |g x - MvPolynomial.eval (fun i => x i) p| < ε := by
  sorry
```

**Proof sketch**:

* Set `K := Metric.closedBall (0 : Fin n → ℝ) R`. `K` is compact
  Hausdorff.
* Define the subalgebra of `C(K, ℝ)` generated by the constants and
  the coordinate projections `fun (x : K) => (x : Fin n → ℝ) i`:

  ```lean
  let S : Subalgebra ℝ C(K, ℝ) :=
    Algebra.adjoin ℝ (Set.range (fun i : Fin n =>
      ContinuousMap.mk (fun x => (x : Fin n → ℝ) i) (by fun_prop)))
  ```

* `S` separates points: for any `x ≠ y` in `K`, some coordinate
  differs, so the corresponding projection separates them.
* `S` contains constants (subalgebra of an ℝ-algebra always does, via
  `algebraMap`).
* Apply Stone-Weierstrass:
  `ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`
  (or the closest current Mathlib name) ⇒ `S.topologicalClosure = ⊤`.
* In particular, `g : C(K, ℝ)` is in `S.topologicalClosure`, so for
  any `ε > 0` there's a member of `S` within `ε` in sup-norm.
* A member of `S` is, by construction, a polynomial in the coordinate
  projections — i.e., the evaluation of some
  `MvPolynomial (Fin n) ℝ`.

**Mathlib search targets**:
- `Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean`: search for
  `subalgebra_topologicalClosure_eq_top_of_separatesPoints` or
  `ContinuousMap.subalgebra_isClosed_topologicalClosure_eq_top`.
- `Mathlib/Topology/ContinuousMap/Polynomial.lean`: search for
  `MvPolynomial`-based primitives; if a direct
  `mvPolynomial_dense_in_C` exists, use it.
- `Algebra.adjoin` API for building the subalgebra.

**Possible obstacle**: Mathlib's Stone-Weierstrass is stated for
`C(K, ℝ)` where `K` is a topological space (often compact Hausdorff).
The compactness of `Metric.closedBall (0 : Fin n → ℝ) R` follows from
`isCompact_closedBall` (Heine-Borel on finite-dim normed spaces).

**Bridging from "S in subalgebra closure" to "p : MvPolynomial"**: the
membership in `Algebra.adjoin ℝ (Set.range (coord_projection))` should
unfold to "finite linear combination of products of coordinate
projections", which is the definition of `MvPolynomial.eval`. The
unfolding is non-trivial Lean bookkeeping — expect 30-50 lines just
for this bridge.

**Estimated effort**: 80-150 lines, ~1-2 days.

### M2 acceptance criteria

* `lake build` succeeds.
* `exists_mvPolynomial_uniform_approx` compiles, no `sorry`.
* `grep -nE '^axiom polynomial_dense_L2_of_subGaussian' GaussianHilbert/PolynomialDensity.lean`
  still finds the axiom — **the axiom is intentionally unchanged in M2**.
* `#print axioms GaussianHilbert.exists_mvPolynomial_uniform_approx`
  yields `[propext, Classical.choice, Quot.sound]`.

### M2 codex report requirements

Codex must paste:
1. The exact output of `lake build` showing "Build completed successfully".
2. The exact output of `#print axioms exists_mvPolynomial_uniform_approx`.

---

## Milestone M3: Cc-density + main theorem (the discharge)

**Scope**: combine M1 + M2 with a Cc-density lemma into the main
theorem. **The axiom is removed in M3.**

**Precondition**: M1 and M2 both landed and lake-build clean. Verify
with `#print axioms GaussianHilbert.MvPolynomial_eval_memLp_two_of_subGaussian`
etc. before starting.

**Acceptance signal**: `lake build` passes; axiom gone; 0 sorries added;
downstream consumers (`hermiteMulti_dense`, etc.) no longer reference
the discharged axiom in `#print axioms`.

### M3.1: Cc-density in L²(μ)

```lean
lemma exists_continuous_compactSupport_L2_approx {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : (Fin n → ℝ) → ℝ, Continuous g ∧ HasCompactSupport g ∧
      (∫ x, |f x - g x| ^ 2 ∂μ) < ε := by
  sorry
```

**Proof sketch**: `(Fin n → ℝ)` with Pi-topology is a Polish space.
The measure `μ` is a probability measure, hence finite and tight on
this Polish space. Mathlib has `Cc`-density for finite measures on
locally compact Hausdorff (or more general) settings.

**Mathlib search targets**:
- `Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`.
- Specifically: `MemLp.exists_hasCompactSupport_continuous_*` style
  lemmas, or
  `MeasureTheory.Lp.boundedContinuousFunction_dense` (which gives
  bounded continuous, then truncate to compact support via a smooth
  cutoff).
- For the compact-support cutoff: pick `K` with `μ(K^c) < ε²/(4‖f‖²)`,
  then multiply by a Lipschitz cutoff that's 1 on `K` and 0 outside a
  slightly larger compact.

**Estimated effort**: 30-60 lines, ~half a day.

### M3.2: Main theorem (the discharge)

```lean
theorem polynomial_dense_L2_of_subGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ)
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℝ,
      (∫ x, |f x - MvPolynomial.eval (fun i => x i) p| ^ 2 ∂μ) < ε := by
  sorry
```

**The quantifier-ordering subtlety (and its resolution)**:

The naive approach "pick g, pick R for supp(g), pick polynomial p on
B_R, control p's tail" runs into the issue that p's L²-tail outside
B_R depends on p, and we've already fixed R = R_g.

**Resolution via the "fix p first, then enlarge R" approach**:

1. Pick `g ∈ Cc` with `‖f − g‖_{L²(μ)} < δ_1` (M3.1). Let `R_g` be such
   that `supp(g) ⊆ B_{R_g}`.
2. Use Stone-Weierstrass (M2.1) on `B_{R_g}` to get polynomial `p` with
   `sup_{B_{R_g}} |g − p| < δ_2`. **At this point, `p` is fixed.**
3. By M1.1, `p ∈ L²(μ)`. By M1.2, the L²-tail
   `∫_{‖x‖ > R'} |p(x)|² dμ → 0` as `R' → ∞`. Choose `R' ≥ R_g` such
   that this tail is `< δ_3²`.
4. Now split the L² error:
   - On `B_{R'}`: write `B_{R'} = B_{R_g} ∪ (B_{R'} \ B_{R_g})`. On
     `B_{R_g}`, `|g − p|² < δ_2²`. On `B_{R'} \ B_{R_g}`, `g ≡ 0` so
     `|g − p|² = |p|²`.
   - On `B_{R'}^c`: `g ≡ 0` so `|g − p|² = |p|²`.
5. Hence
   ```
   ∫ |g − p|² dμ
     = ∫_{B_{R_g}} |g − p|² + ∫_{B_{R_g}^c} |p|²
     ≤ δ_2² · μ(B_{R_g})              + ∫_{B_{R_g}^c} |p|² dμ.
   ```
6. The second term is *not* the same as the tail bound from M1.2
   (which was `∫_{B_{R'}^c}`, not `∫_{B_{R_g}^c}`). **Issue**: M1.2
   gives a tail at large radius; we want it at the smaller radius
   `R_g`.

**The actual resolution**: don't pick the polynomial first. Instead:

(a) Pick `g ∈ Cc` (`‖f − g‖_{L²} < ε/3`). Let `R_g` bound `supp(g)`.

(b) Approximate `g` uniformly on `B_{R_g + 1}` by polynomial `p` with
    sup error `δ`. Now `p` is fixed; `‖g − p‖_∞,B_{R_g + 1} < δ`.

(c) **Key estimate**: `‖p‖_{L²(B_{R_g + 1}^c, μ)}` is bounded
    *independently of δ* (up to a small correction) by
    `‖g‖_∞ + δ`. Specifically:

    ```
    ‖p‖_∞,B_{R_g + 1} ≤ ‖g‖_∞,B_{R_g + 1} + δ ≤ ‖g‖_∞ + δ.
    ```
    But this is sup-norm on B_{R_g + 1}, not L² off it.

OK let me reconsider. The CORRECT textbook argument:

(i) Pick `g ∈ Cc` with `‖f − g‖_{L²(μ)} < ε/2`.

(ii) Enlarge: pick `R` such that `μ(B_R^c)^{1/2} · M < ε/4` where
     `M := ‖g‖_∞` (a fixed quantity). Also require `R ≥ R_g`.

(iii) By Stone-Weierstrass on `B_R`, get polynomial `p` with
      `sup_{B_R} |g − p| < ε/(4 · μ(B_R)^{1/2})`. Then
      `‖g − p‖_{L²(B_R, μ)} < ε/4`.

(iv) Now bound `‖p‖_{L²(B_R^c, μ)}`. We have
     `|p(x)| = |g(x) − (g(x) − p(x))| ≤ |g(x)| + |g(x) − p(x)|`
     **on `B_R`**. **Off `B_R`**, we don't have a sup-bound on `p`!

**The genuine resolution** (most commonly used in textbooks):

The error decomposes more cleanly when `g` is replaced by `0` outside
`B_R`. So:

(v) `|g − p|² = |p|²` on `B_{R_g}^c` (since `g ≡ 0` there).

(vi) On `B_R \ B_{R_g}` (where `R ≥ R_g`), `|g − p| = |p|`, so
     `|p|^2 ≤ (|g − p|)²` (here `g ≡ 0`). Therefore
     `‖p‖_{L²(B_R \ B_{R_g}, μ)} = ‖g − p‖_{L²(B_R \ B_{R_g}, μ)}
       ≤ ‖g − p‖_∞,B_R · μ(B_R)^{1/2} < ε/4` (from (iii)).

(vii) For the tail past `R`, use M1.2 applied to `p` AFTER `p` is
      chosen. Specifically: `p` is fixed in (iii); now apply M1.2 to
      enlarge `R` further if needed so that `‖p‖_{L²(B_R^c, μ)} < ε/4`.
      Then steps (iii) and (vi) need to be re-run with the larger
      `R` — but that's fine since uniform error from Stone-Weierstrass
      just gets larger ball without worse error.

**Cleaner approach**: pick `R_1` first (independent of polynomial),
based on `μ`'s sub-Gaussianity, such that for *any* polynomial of
"low" L²-norm, the tail is controlled. The uniform polynomial
approximant of a fixed `g` has `‖p‖_{L²(μ)} ≤ ‖g‖_∞ · √μ(B_R) + δ ≤ ‖g‖_∞ + δ`,
so its L²-norm is bounded. Use this to pre-pick `R_1` using M1.2 on
the worst-case polynomial.

In Lean, the cleanest way to handle this is:

* Prove an intermediate lemma: "for any L²-bounded family of
  polynomials, the tail is uniformly controlled."
* Or, work concretely: pick `g`, then `p` approximating it, then
  enlarge `R` based on `p`'s explicit (fixed) `‖p‖_{L²(μ)}`.

The plan section is intentionally verbose here because this is the
single hardest piece of M3 — careful quantifier-ordering bookkeeping
is the main risk.

**Mathlib API**:
- `MeasureTheory.setIntegral_indicator` / `integral_indicator_const`
  for splitting the integral into ball + complement.
- `MeasureTheory.MemLp.integral_indicator_le` style lemmas for the
  ball / complement bounds.

**Estimated effort**: 100-150 lines, ~1.5-2 days.

### M3 acceptance criteria

* `lake build` succeeds.
* The original `axiom polynomial_dense_L2_of_subGaussian` declaration
  is **removed** from `GaussianHilbert/PolynomialDensity.lean`.
* `theorem polynomial_dense_L2_of_subGaussian` with the same signature
  exists and compiles.
* `#print axioms GaussianHilbert.polynomial_dense_L2_of_subGaussian`
  yields **exactly** `[propext, Classical.choice, Quot.sound]`.
* `#print axioms GaussianHilbert.hermiteMulti_dense` yields **exactly**
  `[propext, Classical.choice, Quot.sound]`.
* `#print axioms GaussianHilbert.wienerChaos_isHilbertSum` yields
  **exactly** `[propext, Classical.choice, Quot.sound]`.
* `#print axioms GaussianHilbert.ouSemigroupAct_eq_smul_of_mem_wienerChaos`
  yields **exactly** `[propext, Classical.choice, Quot.sound]`.
* `AXIOM_AUDIT.md` (top-level) updated: discharged row moved to
  "Recently discharged"; total active drops from 2 to 1.

### M3 codex report requirements

Codex must paste:
1. The exact output of `lake build` showing "Build completed successfully".
2. The exact output of `#print axioms` for all four downstream
   consumers listed above.
3. Confirmation that the `axiom` keyword no longer appears at the
   target line in `GaussianHilbert/PolynomialDensity.lean`.

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
