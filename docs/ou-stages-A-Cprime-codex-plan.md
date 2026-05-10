# Codex hand-off plan: discharge OU axioms via Mehler

**Target axioms** (all in `GaussianHilbert/OUEigenfunctions.lean`):

1. `ouSemigroupAct` (line 490) — opaque CLM declaration.
2. `ouSemigroupAct_eq_smul_of_mem_wienerChaos` (line 507) — chaos-eigenvalue equation.

**NOT in scope here**: `ouSemigroupAct_eLpNorm_hypercontractive` (line 528).
That one needs Bonami-Beckner-Nelson hypercontractivity, which depends
on either the full Bakry-Émery instance or LSI tensorization (Stages C
or C-β in the broader plan). This codex plan covers only the Mehler
operator definition and the Hermite-eigenvalue identity.

**Effort estimate**: 2-3 active weeks for codex (~500-800 new lines of
Lean across 2-3 new files). Stages A + C′ + E from the broader
[`ou-mehler-discharge-plan.md`](ou-mehler-discharge-plan.md).

**After discharge**: gaussian-hilbert axiom count drops from 4 to 2
(`polynomial_dense_L2_of_subGaussian` and `ouSemigroupAct_eLpNorm_hypercontractive`
remain).

---

## Existing API to consume

### From `GaussianHilbert/HermitePolynomials.lean`

* `noncomputable def stdGaussianFin (n : ℕ) : Measure (Fin n → ℝ)` (line 73)
  — the standard Gaussian on `Fin n → ℝ` (product of 1D standard
  Gaussians). Probability measure.
* `noncomputable def hermiteEval (k : ℕ) (x : ℝ) : ℝ` (line 62) — the
  k-th probabilist's Hermite polynomial (Mathlib's `Polynomial.hermite`
  evaluated at `x`).

### From `GaussianHilbert/WienerChaos.lean`

* `noncomputable def hermiteMultiLp {n : ℕ} (α : Fin n → ℕ) : Lp ℝ 2 (stdGaussianFin n)`
  (line 106) — multivariate Hermite element: `[fun x => ∏ i, hermiteEval (α i) (x i)]`.
* `def wienerChaos (n k : ℕ) : Submodule ℝ (Lp ℝ 2 (stdGaussianFin n))`
  (line 123) — k-th Wiener chaos: `topologicalClosure of span` of
  `hermiteMultiLp α` for `MultiIndex.totalDegree α = k`.
* `hermiteMulti_dense` (proved theorem) — multivariate Hermite spans
  are dense in `Lp ℝ 2 (stdGaussianFin n)`.

### From Mathlib

* `Probability.gaussianReal 0 1 : Measure ℝ` — 1D standard Gaussian.
* `MeasureTheory.Measure.pi` — product measure.
* `MeasureTheory.MeasurePreserving` — change-of-variables for Bochner
  integration.
* `MeasureTheory.integral_smul_const_left` (and friends) — integration
  through linear maps.
* `MeasureTheory.Lp` API — `Lp.coeFn_*`, `Lp.norm_def`, `Memℓp.toLp`.

---

## Stage A: Mehler operator on `L²(γ_n)`

**File**: new `GaussianHilbert/MehlerKernel.lean`.

### A.1 Function-level Mehler operator

```lean
/-- Function-level Mehler operator:
    `(M_t f)(x) := ∫ f(e^{-t}·x + √(1-e^{-2t})·y) dγ_n(y)`. -/
noncomputable def mehlerFun (n : ℕ) (t : ℝ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x =>
    ∫ y, f (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-2*t)) • y)
      ∂(stdGaussianFin n)
```

### A.2 Measurability

```lean
lemma mehlerFun_measurable (n : ℕ) (t : ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) :
    Measurable (mehlerFun n t f) := by
  -- Apply Measurable.integral_prod_right (or similar Fubini) on the
  -- integrand (x, y) ↦ f(e^{-t} x + √(1-e^{-2t}) y), which is
  -- continuous-then-measurable composition of Measurable f with a
  -- continuous (hence measurable) linear combination.
  sorry
```

### A.3 The key change-of-variables fact

```lean
/-- The linear map `(x, y) ↦ e^{-t}x + √(1-e^{-2t})y` is
    measure-preserving when both arguments are `γ_n`-distributed
    and the output is also `γ_n`. This is the Gaussian rotation /
    sum-of-independent-Gaussians fact in disguise. -/
lemma stdGaussianFin_mehler_pushforward (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    MeasurePreserving
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2*t)) • p.2)
      ((stdGaussianFin n).prod (stdGaussianFin n))
      (stdGaussianFin n) := by
  -- Variance check: e^{-2t} · 1 + (1 - e^{-2t}) · 1 = 1.
  -- Independent-Gaussian-sum lemma in Mathlib:
  -- `gaussianReal_add_gaussianReal_of_indepFun` (already used in
  -- markov-semigroups for the 1D version). Tensor to the n-D version.
  sorry
```

**This is the load-bearing Gaussian fact.** Implementation: tensor the
1D `gaussianReal_add_gaussianReal_of_indepFun` over coordinates via
`Measure.pi` and `MeasurePreserving.prod`. ~50-80 lines.

### A.4 L²-contraction

```lean
/-- Mehler is L²-contractive: `∫ (M_t f)² ≤ ∫ f²`. -/
lemma mehlerFun_integral_sq_le (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 (stdGaussianFin n)) :
    ∫ x, (mehlerFun n t f x)^2 ∂(stdGaussianFin n) ≤
    ∫ x, (f x)^2 ∂(stdGaussianFin n) := by
  -- Jensen on (M_t f)(x) = E_y[f(e^{-t}x + √(1-e^{-2t})y)]:
  -- (M_t f)(x)² ≤ E_y[f²(...)].
  -- Then integrate over x and apply A.3 to identify the joint integral
  -- with ∫ f² dγ_n.
  sorry

/-- Mehler preserves `MemLp 2`. -/
lemma mehlerFun_memLp (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 (stdGaussianFin n)) :
    MemLp (mehlerFun n t f) 2 (stdGaussianFin n) := by
  sorry
```

### A.5 Lp CLM

```lean
/-- The Mehler operator as a CLM on `Lp ℝ 2 (stdGaussianFin n)`. -/
noncomputable def mehlerOp (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Lp ℝ 2 (stdGaussianFin n) →L[ℝ] Lp ℝ 2 (stdGaussianFin n) := by
  -- Build by extending mehlerFun from a dense subspace (e.g. continuous
  -- bounded functions) and using A.4 for boundedness. Operator norm ≤ 1.
  sorry
```

### A.6 Action equation

```lean
/-- `mehlerOp` acts as `mehlerFun` at the underlying-function level. -/
lemma mehlerOp_apply (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (stdGaussianFin n)) :
    (mehlerOp n t ht f : (Fin n → ℝ) → ℝ) =ᵐ[stdGaussianFin n]
      mehlerFun n t f := by
  sorry
```

**Stage A total**: ~250 lines. The hardest piece is A.3 (the Gaussian
sum identity); A.5 (Lp descent) is mechanical but tedious.

---

## Stage C′: Hermite eigenvalues

**File**: new `GaussianHilbert/MehlerHermite.lean` (or extension of
`OUEigenfunctions.lean`).

### C′.1 Mehler-Hermite identity (1D)

```lean
/-- **Mehler-Hermite identity (1D)** — Janson §3.4 formula (3.5),
    Nualart §1.4.

    `∫ He_k(e^{-t}·x + √(1-e^{-2t})·y) dγ(y) = e^{-kt} · He_k(x)`. -/
theorem mehler_hermite_identity_1d (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : ℝ) :
    ∫ y, hermiteEval k (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2*t)) * y)
      ∂(Probability.gaussianReal 0 1) =
    Real.exp (-(k : ℝ) * t) * hermiteEval k x := by
  -- Generating-function proof:
  --   1. Use exp(zx - z²/2) = ∑_n (z^n / n!) · He_n(x) (Hermite GF).
  --   2. Substitute z = e^{-t}·something + √(1-e^{-2t})·something else, etc.
  --   3. Exchange sum and integral on a strip (absolute convergence of GF
  --      in a neighbourhood of z = 0).
  --   4. Perform the Gaussian integral in y:
  --        ∫ exp(z·√(1-e^{-2t})·y) dγ(y) = exp(z²·(1-e^{-2t})/2).
  --   5. Multiply through and read off coefficients of z^k:
  --        LHS coeff = ∫ He_k(...)dγ.
  --        RHS coeff = e^{-kt} · He_k(x) · (1 / k!) · k! = e^{-kt} · He_k(x).
  sorry
```

**Alternative proof routes** (use whichever is most ergonomic in Lean):

* **Induction on k + integration by parts**: longer but elementary;
  uses Hermite's recursion `He_{k+1}(x) = x·He_k(x) - k·He_{k-1}(x)`.
* **Rodrigues formula**: `He_k(x) = (-1)^k e^{x²/2} d^k/dx^k e^{-x²/2}`,
  exchange differentiation and Gaussian integration via DCT.

The generating-function proof is recommended; ~80-150 lines.

### C′.2 Multivariate version

```lean
/-- **Multivariate Mehler-Hermite identity.**
    `M_t hermiteMultiLp α = e^{-|α|·t} · hermiteMultiLp α`. -/
theorem mehlerOp_hermiteMultiLp (n : ℕ) (α : Fin n → ℕ) (t : ℝ) (ht : 0 ≤ t) :
    mehlerOp n t ht (hermiteMultiLp α) =
      Real.exp (-((∑ i, α i : ℕ) : ℝ) * t) • hermiteMultiLp α := by
  -- Tensor over coordinates via Fubini on stdGaussianFin n = Measure.pi (gaussianReal 0 1).
  -- Each coordinate yields one application of mehler_hermite_identity_1d.
  -- The product e^{-α₁t} · ... · e^{-αₙt} = e^{-(∑αᵢ)t}.
  sorry
```

~50 lines via Fubini + product manipulation.

### C′.3 Extension to Wiener chaos closure

```lean
/-- **OU acts as `e^{-kt}` on the k-th Wiener chaos.**
    Combines C′.2 with linearity + density: every f ∈ wienerChaos n k is an
    L² limit of finite linear combinations of hermiteMultiLp α with
    `totalDegree α = k`, and `mehlerOp` is continuous. -/
theorem mehlerOp_smul_of_mem_wienerChaos (n k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (stdGaussianFin n)) (hf : f ∈ wienerChaos n k) :
    mehlerOp n t ht f = Real.exp (-(k : ℝ) * t) • f := by
  -- 1. wienerChaos is defined as topologicalClosure of span S_k where
  --    S_k = {hermiteMultiLp α : totalDegree α = k}.
  -- 2. By C′.2, for each α ∈ S_k, mehlerOp n t ht (hermiteMultiLp α) =
  --    e^{-kt} • hermiteMultiLp α.
  -- 3. By linearity of mehlerOp, this extends to span S_k.
  -- 4. By continuity of mehlerOp, this extends to closure(span S_k).
  -- Mathlib pattern: `Submodule.span_induction` followed by
  --   `Submodule.topologicalClosure_minimal` with the closed equality
  --   predicate.
  sorry
```

~80-100 lines.

**Stage C′ total**: ~250 lines. C′.1 (1D identity) is the bulk;
C′.2-3 are mostly bookkeeping.

---

## Stage E: wire into `OUEigenfunctions.lean`

Replace the two axioms with theorems delegating to the proved versions:

```lean
-- Replace the axiom at line 490
noncomputable def ouSemigroupAct (n : ℕ) (t : ℝ) :
    Lp ℝ 2 (stdGaussianFin n) →L[ℝ] Lp ℝ 2 (stdGaussianFin n) :=
  if h : 0 ≤ t then mehlerOp n t h else 0

-- Replace the axiom at line 507
theorem ouSemigroupAct_eq_smul_of_mem_wienerChaos {n : ℕ} (k : ℕ)
    (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (stdGaussianFin n)) (hf : f ∈ wienerChaos n k) :
    ouSemigroupAct n t f = Real.exp (-(k : ℝ) * t) • f := by
  unfold ouSemigroupAct
  rw [dif_pos ht]
  exact mehlerOp_smul_of_mem_wienerChaos n k t ht f hf
```

The `t < 0` case for `ouSemigroupAct` (mapped to 0) doesn't matter
because all consumers pass `ht : 0 ≤ t`. If desired, define
`ouSemigroupAct n t` via the `Real.toNNReal t` truncation instead, or
remove the conditional entirely if all call sites can be refactored.

**Stage E total**: ~50 lines.

---

## File layout summary

| File | Status | Approximate size |
|---|---|---|
| `GaussianHilbert/MehlerKernel.lean` | new | ~250 lines |
| `GaussianHilbert/MehlerHermite.lean` | new | ~250 lines |
| `GaussianHilbert/OUEigenfunctions.lean` | edit (axioms → theorems) | ~50 lines diff |

Update `GaussianHilbert/Basic.lean` (or wherever the index file is) to
`import` the new files.

---

## Acceptance criteria

* `lake build` succeeds.
* `grep -nE '^axiom (ouSemigroupAct\b|ouSemigroupAct_eq_smul_of_mem_wienerChaos)' GaussianHilbert/OUEigenfunctions.lean` returns nothing.
* The third axiom `ouSemigroupAct_eLpNorm_hypercontractive` continues
  to be an axiom (out of scope for this plan).
* All downstream theorems in `WienerChaos.lean`, `PolynomialChaosConcentration.lean`
  continue to compile unchanged. `polynomial_chaos_concentration` is
  unaffected (it still depends on the hypercontractivity axiom).
* Update `AXIOM_AUDIT.md` (top-level): move 2 rows from "Active" to
  "Recently discharged"; total active drops from 4 to 2.

---

## Notes for codex

* **Start with Stage A.3** (the Gaussian sum identity) — if that
  doesn't go cleanly, the rest stalls. Pin it down first as a
  standalone lemma, then layer A.4-A.6 on top.

* **Stage C′.1**: Mathlib has `Polynomial.hermite_genFun` for the
  generating function, but check Mathlib's exact convention vs. our
  `hermiteEval` (factor of `(-1)^k` and normalization). If the
  generating-function proof gets bogged down in convention juggling,
  fall back to the Rodrigues / induction proof.

* **Heartbeat budget**: A.5 (Lp CLM construction) and C′.3
  (wienerChaos extension) may need `set_option maxHeartbeats 1600000`.

* **Avoid redefining**: don't introduce a new `MehlerOp` typeclass or
  parallel API; just compose with existing `mehlerOp`.

* **No new axioms**: the entire chain is dischargeable from
  Mathlib + the existing gaussian-hilbert API. If you hit a hard
  blocker that suggests a missing Mathlib lemma, document it but
  don't axiomatize without checking with the user.

* **Cross-repo**: this plan does *not* touch markov-semigroups.
  All work is contained in gaussian-hilbert.

---

## Downstream impact

Once both axioms are theorems:

* **gaussian-hilbert**: 4 axioms → 2 axioms.
* **`polynomial_chaos_concentration`** (in
  `GaussianHilbert/PolynomialChaosConcentration.lean`) still depends
  on `ouSemigroupAct_eLpNorm_hypercontractive` (out-of-scope axiom),
  so doesn't become axiom-free yet. But it does become "1 axiom
  away" from being fully proved (vs. 3 axioms today).
* **pphi2 Cluster A** (`polynomial_chaos_exp_moment_bridge` and the
  4 Cluster A consumers) still needs the
  hypercontractivity axiom upstream, so isn't yet dischargeable. But
  the discharge path becomes shorter — only one upstream axiom away
  instead of three.

For the **full pphi2 T² continuum-limit unblock**, this plan must be
followed by **either**:

* Stage C-β (LSI tensorization shortcut, +1 textbook axiom in
  markov-semigroups but discharges
  `ouSemigroupAct_eLpNorm_hypercontractive` immediately), **or**
* Stage C+E (full multivariate BakryEmerySpace, ~3 weeks, no new
  axioms but depends on the markov-semigroups Gross axioms).

See [`ou-mehler-discharge-plan.md`](ou-mehler-discharge-plan.md) for
both alternatives.
