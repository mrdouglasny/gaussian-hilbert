# Codex hand-off plan: discharge OU axioms

**Target axioms** (all in `GaussianHilbert/OUEigenfunctions.lean`):

1. `ouSemigroupAct` (line 490) — opaque CLM declaration.
2. `ouSemigroupAct_eq_smul_of_mem_wienerChaos` (line 507) — chaos-eigenvalue equation.

**NOT in scope here**: `ouSemigroupAct_eLpNorm_hypercontractive` (line 528).
That one needs Bonami-Beckner-Nelson hypercontractivity, which depends
on either the full Bakry-Émery instance or LSI tensorization. Out of scope.

**After discharge**: gaussian-hilbert axiom count drops from 4 to 2
(`polynomial_dense_L2_of_subGaussian` and `ouSemigroupAct_eLpNorm_hypercontractive`
remain).

---

## Two routes — pick ONE

### Route 1 (RECOMMENDED): Spectral-shortcut

Define `ouSemigroupAct` *directly* as the diagonal decay map on the
Wiener-chaos Hilbert sum decomposition. The chaos-eigenvalue equation
becomes structural (true by definition modulo CLM bookkeeping). **No
Mehler integral needed at all.**

* Effort: ~150-300 new lines, ~3-5 days for codex.
* New definitions: `chaosCoordEquiv`, `chaosDecay`, `chaosScale`,
  `chaosDiagCLM`. The `ouSemigroupAct` becomes a one-line definition
  `e.symm ∘ chaosDiagCLM ∘ e` where `e := chaosCoordEquiv n`.
* Trade-off: this `ouSemigroupAct` is the *spectral* OU semigroup. To
  prove it agrees with the *integral-formula* OU semigroup (the Mehler
  operator) one would need Stage A from Route 2. But all downstream
  consumers of these axioms (gaussian-hilbert's
  `polynomial_chaos_concentration`, pphi2's Cluster A) only need the
  chaos-eigenvalue property, which is structurally trivial under this
  definition.

**Read the "Route 1" section below for full implementation guidance.**
This route was attempted by codex on 2026-05-10 with the right
architecture but several Lean pitfalls (Subtype.ext + a.e. equality,
`set_option` placement, `LinearMap` over lp-of-subtypes); the section
calls out each pitfall explicitly so a re-run can land cleanly.

### Route 2 (fallback): Mehler integral

Construct `ouSemigroupAct` as the Lp lifting of the explicit Mehler
integral
`(M_t f)(x) = ∫ f(e^{-t}·x + √(1-e^{-2t})·y) dγ_n(y)`,
then prove the Hermite-eigenvalue identity by induction + Stein's
lemma.

* Effort: ~500-800 new lines, ~2-3 weeks.
* Mathematically heavier but produces a more concretely-grounded
  `ouSemigroupAct` (the integral formula matches the textbook OU
  semigroup directly, which is useful if you ever want to verify
  Markov/positivity/stochastic properties beyond the spectrum).
* Stages A + C′ + E from the broader
  [`ou-mehler-discharge-plan.md`](ou-mehler-discharge-plan.md).

**Read the "Route 2" section below for the full Mehler-integral plan.**

### Why Route 1 is recommended

The pphi2 T² continuum-limit chain (the actual downstream goal) only
consumes the chaos-eigenvalue property. Route 1 delivers it in days
instead of weeks. If a future consumer needs the integral formula,
Route 2 can be done as a separate effort then — the spectral
`ouSemigroupAct` from Route 1 doesn't preclude later refinement.

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

## Route 1: Spectral-shortcut implementation

This is the **recommended path** (vetted by Gemini deep-think
2026-05-10: "mathematically bulletproof, architecturally superior for
this milestone, 100% the correct choice today"). ~150-300 lines, edits
only `GaussianHilbert/OUEigenfunctions.lean` (no new files).

### Mathematical justification (Gemini-vet)

The spectral diagonal `f ↦ ∑_k e^{-kt} P_k f` (where `P_k` is
orthogonal projection onto `wienerChaos n k`) is **the same operator**
as the Mehler integral
`f ↦ ∫ f(e^{-t}·x + √(1-e^{-2t})·y) dγ(y)` on `L²(γ_n)`. Both are
bounded continuous operators on `L²` agreeing on the algebraic direct
sum `⊕_k wienerChaos n k`, which is dense (`wienerChaos_isHilbertSum`).
By continuity + density, equal everywhere. This is **not** "an
operator that happens to act diagonally on chaos" — it's the unique
OU semigroup, in spectral form.

Therefore: the existing axiom `ouSemigroupAct_eLpNorm_hypercontractive`
(asserting Bonami-Beckner-Nelson hypercontractivity), kept in scope,
is correct as a statement about Route 1's `ouSemigroupAct`. Every
property of the Mehler integral is a property of Route 1's operator.

### Architectural debt (mandatory docstring)

Route 1 obscures the *spatial* (pointwise) geometry of the operator.
Pointwise positivity and the Dirichlet-form integration-by-parts
identity — which are what Bakry-Émery / Gross / Nelson proofs of
hypercontractivity *natively* rely on — are practically impossible to
prove from the spectral form alone. To eventually discharge
`ouSemigroupAct_eLpNorm_hypercontractive` natively, we would need to
formalize the Mehler integral (Route 2) and prove an
`ouSemigroupAct_eq_mehler` agreement theorem.

For now, this debt is deferred. **The ouSemigroupAct definition MUST
carry a docstring acknowledging this** (see Step 4 below).

### Architectural idea

`Lp ℝ 2 (stdGaussianFin n)` decomposes as a Hilbert sum
`⊕_k wienerChaos n k` (already proved as `wienerChaos_isHilbertSum n`).
Concretely this gives a linear isometric equivalence

```
chaosCoordEquiv n : Lp ℝ 2 (stdGaussianFin n) ≃ₗᵢ[ℝ]
                    lp (fun k : ℕ => wienerChaos n k) 2
```

Define the OU semigroup as the **diagonal scaling by `e^{-kt}`** on
this `lp` model:

```
ouSemigroupAct n t := chaosCoordEquiv⁻¹ ∘ chaosDiagCLM n t ∘ chaosCoordEquiv
```

where `chaosDiagCLM n t : lp ... →L lp ...` is the per-component
multiplication by `chaosDecay k t = e^{-(k:ℝ)·t}` at index `k`.

The chaos-eigenvalue theorem
`ouSemigroupAct n t f = e^{-kt} • f` for `f ∈ wienerChaos n k`
is then near-definitional: `f ∈ wienerChaos n k` corresponds to
`chaosCoordEquiv f = lp.single 2 k ⟨f, hf⟩`, and `chaosDiagCLM`
applied to `lp.single 2 k x` is `e^{-kt} • lp.single 2 k x` by
construction.

### Step 1: Helper definitions

```lean
/-- The chaos-coordinate isometry. -/
noncomputable def chaosCoordEquiv (n : ℕ) :
    Lp ℝ 2 (stdGaussianFin n) ≃ₗᵢ[ℝ] lp (fun k : ℕ => wienerChaos n k) 2 :=
  (wienerChaos_isHilbertSum n).linearIsometryEquiv

/-- The spectral decay scalar on the k-th chaos. -/
private noncomputable def chaosDecay (k : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-(k : ℝ) * t)

/-- For t ≥ 0, the decay is in [0, 1]. -/
private lemma chaosDecay_norm_le_one (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖chaosDecay k t‖ ≤ 1 := by
  have hkt : 0 ≤ (k : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) ht
  have hnonneg : 0 ≤ chaosDecay k t := Real.exp_nonneg _
  have hle : chaosDecay k t ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rwa [Real.norm_eq_abs, abs_of_nonneg hnonneg]
```

### Step 2: The diagonal CLM (the technical heart — read the pitfall notes!)

The objective is to define
```lean
chaosDiagCLM (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    lp (fun k : ℕ => wienerChaos n k) 2 →L[ℝ]
      lp (fun k : ℕ => wienerChaos n k) 2
```
acting as `(chaosDiagCLM f) k = chaosDecay k t • f k`.

**Pitfall 1: `Subtype.ext` over a.e. equality**

`lp G 2` for `G k = wienerChaos n k` is a subtype of "all functions
ι → α" with the `Memℓp` predicate. To define a function on it, you
provide a function on the underlying coefficient sequence. To prove
`map_add'` and `map_smul'`, you typically use `lp.ext` or
`Subtype.ext` to reduce to coefficient equality — **but the underlying
coefficients live in `wienerChaos n k`, which is itself a subtype of
`Lp ℝ 2 (stdGaussianFin n)`, where equality is a.e.-equivalence**.

This means after `ext k` you may face a goal like
`↑↑↑(... k) =ᵐ[stdGaussianFin n] ↑↑↑(... k)`,
not raw `=`. Codex's first attempt hit this and applied `Subtype.ext`
incorrectly.

**Recommended approach** to avoid this: use `lp.LinearMap.mkContinuous`
**only after** working with the `(· : Lp ...)` coercions explicitly
inside the linear-map fields. Concretely:

```lean
private lemma chaosDiag_memℓp (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (f : lp (fun k : ℕ => wienerChaos n k) 2) :
    Memℓp (fun k : ℕ => chaosScale k t (f k)) 2 :=
  -- Norm-bound + summability of ‖f k‖²:
  -- ‖chaosScale k t (f k)‖² ≤ ‖f k‖²; sum is finite.
  sorry  -- already worked out by codex; ~30 lines

noncomputable def chaosDiagCLM (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    lp (fun k : ℕ => wienerChaos n k) 2 →L[ℝ]
      lp (fun k : ℕ => wienerChaos n k) 2 := by
  refine LinearMap.mkContinuous {
    toFun := fun f => ⟨fun k => chaosScale k t (f k), chaosDiag_memℓp n t ht f⟩
    map_add' := ?_
    map_smul' := ?_
  } 1 ?_
  -- For map_add' / map_smul': use `lp.ext_apply` (or whatever the
  -- coordinate-extensionality lemma is named in current Mathlib),
  -- which gives a per-coordinate goal in `wienerChaos n k`, which is
  -- a `Submodule` of `Lp` — equality there IS raw `=`, NOT `=ᵐ`.
  -- The pitfall codex hit was using `ext k` (which goes one step too
  -- deep into the underlying Lp coeFn). Use `lp.ext` or apply
  -- `Subtype.ext` at the lp level, then reduce to the per-coordinate
  -- subtype, then prove the equality there.
  · -- map_add'
    intros f g
    apply lp.ext  -- target: lp coord-wise equality
    ext k
    -- Now goal: chaosScale k t ((f + g) k) = chaosScale k t (f k) + chaosScale k t (g k)
    -- Both sides are elements of (wienerChaos n k); their underlying Lp
    -- equivalence-class equality is raw `=`. Unfold chaosScale_eq_smul
    -- and use smul_add.
    show chaosScale k t ((f + g) k) = chaosScale k t (f k) + chaosScale k t (g k)
    sorry  -- ~5 lines: unfold + smul_add
  · -- map_smul' — analogous
    sorry
  · -- norm bound: from chaosDecay_norm_le_one + lp norm structure.
    sorry
```

**Pitfall 2: `lp.ext` vs `ext`**

In Lean 4 / Mathlib4, the right idiom for proving `(a b : lp G p), a = b`
is to apply the lp coordinate-extensionality lemma (whatever it's
named — search `lp.ext`, `lp.coeFn_ext`, `Lp.ext_iff_coeFn` in the
current Mathlib). Plain `ext` may unfold too aggressively and reach
the underlying a.e.-equivalence layer.

**Pitfall 3: when the coefficient space is itself a subtype**

`wienerChaos n k` is `Submodule.topologicalClosure ...`, which is a
`Submodule ℝ (Lp ...)`. As a Lean type, it's `↥(wienerChaos n k)`.
Its elements are `⟨f, hf⟩` pairs where `f : Lp ...` and `hf : f ∈ wienerChaos n k`.
**Equality between two such pairs IS raw `=` (Subtype.ext on the carrier
gives raw equality of the underlying `Lp` elements, which IS a.e.
equality, but at the Lp level THAT is just `=` because Lp has already
quotiented).**

The chain: `lp` coords are in `wienerChaos n k` (subtype), whose
underlying elements are in `Lp ℝ 2 (stdGaussianFin n)`. Equality at
each level is `=` (Lp itself is the quotient, not the function space).

### Step 3: chaosDiagCLM_apply_single

```lean
@[simp] lemma chaosDiagCLM_apply_single (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (k : ℕ) (x : wienerChaos n k) :
    chaosDiagCLM n t ht (lp.single 2 k x) =
      chaosDecay k t • lp.single 2 k x := by
  apply lp.ext  -- coord-wise equality
  intro j
  by_cases h : j = k
  · subst h
    -- (lp.single 2 k x) k = x; chaosScale k t x = chaosDecay k t • x
    -- (chaosDecay • lp.single 2 k x) k = chaosDecay k t • x
    -- Both sides equal (chaosDecay k t) • x in wienerChaos n k.
    sorry  -- ~5 lines via lp.single_apply + chaosScale_eq_smul + smul_apply
  · -- (lp.single 2 k x) j = 0 for j ≠ k. Both sides 0.
    sorry  -- ~5 lines
```

### Step 4: ouSemigroupAct definition + chaos-eigenvalue theorem

The `ouSemigroupAct` definition **must** carry the docstring below
acknowledging the architectural debt — this is mandated by Gemini's
review and is essential for any future maintainer who needs to
discharge `ouSemigroupAct_eLpNorm_hypercontractive` natively.

```lean
/-- The Ornstein-Uhlenbeck semigroup acting on `L²(γ_n)`, defined
spectrally via the Wiener-chaos `IsHilbertSum` decomposition.

For `t ≥ 0`, this acts as multiplication by `e^{-kt}` on each Wiener
chaos `wienerChaos n k`. For `t < 0`, the conventional fallback to the
zero map (no consumer in the codebase invokes this branch).

**Mathematical agreement with the Mehler integral.** This operator is
*equal* (not merely "consistent with") to the textbook OU semigroup
defined by the Mehler integral
`(M_t f)(x) = ∫ f(e^{-t}·x + √(1-e^{-2t})·y) dγ_n(y)`, because both
are bounded operators on `L²(γ_n)` agreeing on the algebraic direct
sum `⊕_k wienerChaos n k`, which is dense (`wienerChaos_isHilbertSum`).
By continuity + density, the operators are identical.

**Architectural debt.** While mathematically identical to the spatial
Mehler integral, this spectral definition obscures the pointwise
geometry of the operator. Proving pointwise/Markovian properties
(positivity `f ≥ 0 a.e. ⇒ T_t f ≥ 0 a.e.`, Dirichlet-form integration
by parts `∫ f (-L f) dγ = ∫ |∇f|² dγ`, or any L^p hypercontractivity
result via Bakry-Émery / Gross / Nelson) **cannot** be done from the
spectral form alone. Eventual native discharge of
`ouSemigroupAct_eLpNorm_hypercontractive` will require formalizing
the Mehler integral (Route 2 in
`docs/ou-discharge-codex-plan.md`) and proving an
`ouSemigroupAct_eq_mehler` agreement theorem. -/
noncomputable def ouSemigroupAct (n : ℕ) (t : ℝ) :
    Lp ℝ 2 (stdGaussianFin n) →L[ℝ] Lp ℝ 2 (stdGaussianFin n) :=
  if ht : 0 ≤ t then
    let e := (chaosCoordEquiv n).toContinuousLinearEquiv
    e.symm.toContinuousLinearMap.comp
      ((chaosDiagCLM n t ht).comp e.toContinuousLinearMap)
  else 0

theorem ouSemigroupAct_eq_smul_of_mem_wienerChaos {n : ℕ} (k : ℕ)
    (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (stdGaussianFin n)) (hf : f ∈ wienerChaos n k) :
    ouSemigroupAct n t f = Real.exp (-(k : ℝ) * t) • f := by
  -- Outline:
  --   1. Set fk : wienerChaos n k := ⟨f, hf⟩.
  --   2. Use IsHilbertSum.linearIsometryEquiv_symm_apply_single
  --      to identify e f = lp.single 2 k fk where
  --      e = (chaosCoordEquiv n).toContinuousLinearEquiv.
  --   3. Apply chaosDiagCLM_apply_single (Step 3).
  --   4. e.symm sends the result back to (chaosDecay k t • f).
  --   5. chaosDecay k t = Real.exp (-(k : ℝ) * t).
  -- See "Pitfall 4 — set_option placement" and "Pitfall 5 — dif_pos
  -- unfolding" below.
  sorry  -- ~15 lines
```

**Mandated by Gemini-vet (2026-05-10)**: use
`IsHilbertSum.linearIsometryEquiv_symm_apply_single` to get
`e f = lp.single 2 k fk`. Once that's established, the rest is
straightforward unfolding.

**Pitfall 4: `set_option maxHeartbeats` placement**

The `set_option ... in <theorem>` form must be:
```lean
set_option maxHeartbeats 1600000 in
theorem foo ... := by ...
```
*as its own line directly above the theorem*, not embedded inside a
docstring or after `**Reference:**`. Codex's first attempt put it
inside the trailing docstring text, causing a parse error.

**Pitfall 5: `simpa` lint and `dif_pos` unfolding**

In the calc proof of `ouSemigroupAct_eq_smul_of_mem_wienerChaos`, the
step `simp [ouSemigroupAct, ht, e]` is heavy because it unfolds the
`if dif_pos h then ... else 0`. Prefer an explicit `show` + `dif_pos`
rewrite over `simp` here:

```lean
calc
  e (ouSemigroupAct n t f)
      = chaosDiagCLM n t ht (e f) := by
          show e ((if ht' : 0 ≤ t then ... else 0) f) = chaosDiagCLM n t ht (e f)
          rw [dif_pos ht]
          rfl  -- after definitional unfolding
  ...
```

### Step 5: replace the axioms

In `GaussianHilbert/OUEigenfunctions.lean` lines ~485-512:
1. Replace `axiom ouSemigroupAct ...` with `noncomputable def ouSemigroupAct ...` (Step 4 above).
2. Replace `axiom ouSemigroupAct_eq_smul_of_mem_wienerChaos ...` with the corresponding `theorem ... := by ...` (Step 4).

### Acceptance criteria for Route 1

* `lake build GaussianHilbert.OUEigenfunctions` succeeds — **must be
  verified before reporting**, not assumed.
* `lake build` (full repo) succeeds.
* `grep -nE '^axiom ouSemigroupAct\b|^axiom ouSemigroupAct_eq_smul'
    GaussianHilbert/OUEigenfunctions.lean` returns nothing.
* The third axiom `ouSemigroupAct_eLpNorm_hypercontractive` continues
  to be an axiom (out of scope).
* `AXIOM_AUDIT.md` (top-level): move the two rows from "Active" to
  "Recently discharged".

---

# Route 2: Mehler-integral implementation (fallback)

Original plan, kept for the case where Route 1 hits a Mathlib API
blocker that the spectral approach can't avoid. Stages A + C′ + E from
the broader `ou-mehler-discharge-plan.md`. **Skip this section unless
Route 1 fails.**

---

## Hermite convention check

Mathlib's `Polynomial.hermite` is the **probabilists'** Hermite polynomial
(verified 2026-05-10 against `Mathlib/RingTheory/Polynomial/Hermite/Basic.lean`):

```lean
/-- the probabilists' Hermite polynomials. -/
noncomputable def hermite : ℕ → Polynomial ℤ
  | 0 => 1
  | n + 1 => X * hermite n - derivative (hermite n)
```

Verified values: `He_0 = 1, He_1 = x, He_2 = x² - 1, He_3 = x³ - 3x`
(probabilists' — matches Mehler kernel). The Mehler-Hermite identity in
C′.1 below holds as written. **No rescaling of `hermiteEval` is required.**

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

**Mathlib API hint**: to lift the 1D fact to n-D inside `Measure.pi`,
the input/output types are `(Fin n → ℝ) × (Fin n → ℝ)` and `Fin n → ℝ`.
The pushforward fundamentally needs the rearrangement
`(Fin n → ℝ) × (Fin n → ℝ) ≃ Fin n → ℝ × ℝ`, which is
**`Equiv.arrowProdEquivProdArrow`**. After that swap, the n-D
measure-preserving statement reduces to a `Measure.pi`-of-1D-facts
argument.

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

### A.5 Lp CLM via direct quotient lifting

**Architectural note (added per Gemini review 2026-05-10)**: do **not**
build `mehlerOp` by `LinearMap.extend` from a dense subspace.
Extension produces an abstract topological limit, and proving that
this limit equals the explicit pointwise integral formula (A.6) for an
arbitrary L² equivalence class triggers convergence-tracking pain.

Instead, use **direct L² quotient lifting**: apply `mehlerFun` to a
representative, prove it respects a.e. equality (zero L² norm in,
zero L² norm out), and package via `MemLp.toLp` +
`LinearMap.mkContinuous`.

```lean
/-- The function-level Mehler operator respects a.e. equality. -/
lemma mehlerFun_aeEq_of_aeEq (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    {f g : (Fin n → ℝ) → ℝ}
    (hf : MemLp f 2 (stdGaussianFin n)) (hg : MemLp g 2 (stdGaussianFin n))
    (hfg : f =ᵐ[stdGaussianFin n] g) :
    mehlerFun n t f =ᵐ[stdGaussianFin n] mehlerFun n t g := by
  -- (f - g) =ᵐ 0 ⇒ ‖f - g‖_{L²} = 0 ⇒ by A.4 contraction,
  -- ‖mehlerFun n t (f - g)‖_{L²} = 0 ⇒ mehlerFun n t f =ᵐ mehlerFun n t g
  -- (using linearity of mehlerFun, which is one line by definition).
  sorry

/-- The Mehler operator as a linear map on `Lp ℝ 2 (stdGaussianFin n)`,
    via direct lifting from the function-level operator. -/
noncomputable def mehlerLM (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Lp ℝ 2 (stdGaussianFin n) →ₗ[ℝ] Lp ℝ 2 (stdGaussianFin n) where
  toFun f := (mehlerFun_memLp n t ht f.memLp).toLp _
  map_add' := sorry  -- f.coeFn (f + g) =ᵐ f.coeFn f + f.coeFn g; mehlerFun is linear; use .toLp_add
  map_smul' := sorry  -- analogous

/-- The Mehler operator as a CLM, upgraded from `mehlerLM` via the
    A.4 norm bound `‖M_t f‖_{L²} ≤ 1 · ‖f‖_{L²}`. -/
noncomputable def mehlerOp (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Lp ℝ 2 (stdGaussianFin n) →L[ℝ] Lp ℝ 2 (stdGaussianFin n) :=
  LinearMap.mkContinuous (mehlerLM n t ht) 1 (fun f => by
    -- ‖mehlerLM n t ht f‖_{L²} ≤ 1 * ‖f‖_{L²} from A.4 + Memℓp.toLp norm
    sorry)
```

### A.6 Action equation (now `rfl` after A.5 quotient-lift)

```lean
/-- `mehlerOp` acts as `mehlerFun` at the underlying-function level.
    With the quotient-lift definition in A.5, this is essentially `rfl`
    via `MemLp.coeFn_toLp`. -/
lemma mehlerOp_apply (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (stdGaussianFin n)) :
    (mehlerOp n t ht f : (Fin n → ℝ) → ℝ) =ᵐ[stdGaussianFin n]
      mehlerFun n t (f : (Fin n → ℝ) → ℝ) :=
  MemLp.coeFn_toLp _
```

This makes A.6 trivial (one line) instead of a 50-line convergence
chase.

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
  -- See "Recommended proof: induction + Stein's lemma" below.
  sorry
```

### Recommended proof for C′.1: induction + Stein's lemma

**Architectural note (per Gemini review 2026-05-10)**: do **not**
attempt the generating-function proof. It triggers a Dominated
Convergence / `HasSum` typeclass nightmare on `∫ ∑ = ∑ ∫`. Use the
**100% algebraic** induction route below — it has zero limits, zero
infinite series, and zero analytic content beyond polynomial integration
by parts.

**Setup**: let `a := Real.exp (-t)` and `b := Real.sqrt (1 - Real.exp (-2*t))`.
Note `a² + b² = 1` (one-line algebra).

**Three ingredients** (all already-statable in Mathlib):

1. **Probabilist Hermite recurrence** (from
   `Polynomial.hermite_succ`):
   ```
   He_{k+1}(x) = x · He_k(x) - He_k'(x)
   ```
   Equivalently (using `He_k'(x) = k · He_{k-1}(x)`):
   ```
   He_{k+1}(x) = x · He_k(x) - k · He_{k-1}(x).
   ```
2. **Stein's lemma for polynomials** (a.k.a. Gaussian integration by
   parts):
   ```
   ∫ y · P(y) dγ(y) = ∫ P'(y) dγ(y).
   ```
   Provable from the Gaussian density derivative `(γ)' = -y · γ`.
   Mathlib has `ProbabilityTheory.gaussianReal_integral_mul_id` style
   lemmas; if not in this exact form, derive directly via integration
   by parts on `Polynomial.eval P` against `gaussianPDF 0 1`.

3. **Hermite derivative**:
   ```
   He_k'(x) = k · He_{k-1}(x)
   ```
   Already in Mathlib via `Polynomial.derivative_hermite`.

**Induction step**: assume the identity holds for `k` and `k - 1`.
Prove for `k + 1`. Let `u := a*x + b*y` (so `du/dy = b`).

```
∫ He_{k+1}(u) dγ(y)
  = ∫ [u · He_k(u) - k · He_{k-1}(u)] dγ(y)        -- by recurrence (1)
  = a*x · ∫ He_k(u) dγ(y) + b · ∫ y · He_k(u) dγ(y)
      - k · ∫ He_{k-1}(u) dγ(y)                    -- linearity, expand u
  = a*x · (a^k · He_k(x))                          -- IH at level k
      + b · ∫ y · He_k(u) dγ(y)
      - k · (a^{k-1} · He_{k-1}(x))                -- IH at level (k-1)
  = a^{k+1} · x · He_k(x)
      + b · b · ∫ He_k'(u) dγ(y)                   -- Stein (2):
                                                   -- d/dy He_k(u) = b · He_k'(u),
                                                   -- so ∫ y · He_k(u) dγ = ∫ d/dy[He_k(u)] / 1 dγ
                                                   -- = b · ∫ He_k'(u) dγ
      - k · a^{k-1} · He_{k-1}(x)
  = a^{k+1} · x · He_k(x)
      + b² · k · ∫ He_{k-1}(u) dγ(y)               -- by (3): He_k' = k · He_{k-1}
      - k · a^{k-1} · He_{k-1}(x)
  = a^{k+1} · x · He_k(x)
      + b² · k · a^{k-1} · He_{k-1}(x)             -- IH at level (k-1)
      - k · a^{k-1} · He_{k-1}(x)
  = a^{k+1} · x · He_k(x)
      + (b² - 1) · k · a^{k-1} · He_{k-1}(x)
  = a^{k+1} · x · He_k(x) - a² · k · a^{k-1} · He_{k-1}(x)  -- since b² = 1 - a²
  = a^{k+1} · x · He_k(x) - a^{k+1} · k · He_{k-1}(x)
  = a^{k+1} · [x · He_k(x) - k · He_{k-1}(x)]
  = a^{k+1} · He_{k+1}(x)                          -- by recurrence (1) at x.
```

Substituting `a^{k+1} = Real.exp (-(k+1)·t)` closes the induction.

**Base cases**:
* `k = 0`: `∫ He_0(u) dγ(y) = ∫ 1 dγ(y) = 1 = e^{0} · He_0(x)`. ✓
* `k = 1`: `∫ He_1(u) dγ(y) = ∫ (a*x + b*y) dγ(y) = a*x · 1 + b · 0 = a · He_1(x)`. ✓

This is **purely polynomial algebra** — no DCT, no `HasSum`, no
generating function. Estimated ~80-120 lines (Stein's lemma may need
~30 if not directly in Mathlib).

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
  -- See "Recommended proof using ContinuousLinearMap.eqOn_closure" below.
  sorry
```

### Recommended proof for C′.3: `ContinuousLinearMap.eqOn_closure`

**Architectural note (per Gemini review 2026-05-10)**: state both sides as
**continuous linear maps** equal on a dense submodule, then lift to the
closure in 2-3 lines via `ContinuousLinearMap.eqOn_closure` (or
`ContinuousLinearMap.ext_on`).

```lean
theorem mehlerOp_smul_of_mem_wienerChaos (n k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (stdGaussianFin n)) (hf : f ∈ wienerChaos n k) :
    mehlerOp n t ht f = Real.exp (-(k : ℝ) * t) • f := by
  -- View both sides as CLMs Lp → Lp:
  --   LHS: mehlerOp n t ht
  --   RHS: (Real.exp (-(k : ℝ) * t)) • ContinuousLinearMap.id ℝ _
  set lhs : Lp ℝ 2 (stdGaussianFin n) →L[ℝ] Lp ℝ 2 (stdGaussianFin n) :=
    mehlerOp n t ht
  set rhs : Lp ℝ 2 (stdGaussianFin n) →L[ℝ] Lp ℝ 2 (stdGaussianFin n) :=
    (Real.exp (-(k : ℝ) * t)) • ContinuousLinearMap.id ℝ _
  -- Show they agree on the spanning set S_k = { hermiteMultiLp α : totalDegree α = k }.
  -- C′.2 gives us this for each α with totalDegree α = k:
  have h_basis : ∀ α : Fin n → ℕ, MultiIndex.totalDegree α = k →
      lhs (hermiteMultiLp α) = rhs (hermiteMultiLp α) := by
    intro α hα
    show mehlerOp n t ht (hermiteMultiLp α) =
      Real.exp (-(k : ℝ) * t) • hermiteMultiLp α
    rw [mehlerOp_hermiteMultiLp]
    congr 1
    -- Real.exp (-(totalDegree α : ℝ) * t) = Real.exp (-(k : ℝ) * t)
    rw [hα]
  -- Linearity extends from the spanning set to the span (Submodule.span_induction).
  -- Continuity extends from the span to the closure (Submodule.topologicalClosure)
  -- via ContinuousLinearMap.eqOn_closure / Submodule.topologicalClosure_minimal.
  exact ContinuousLinearMap.eqOn_closure
    (s := Set.range (fun α : { α : Fin n → ℕ // MultiIndex.totalDegree α = k } =>
            hermiteMultiLp α.1))
    (fun _ ⟨⟨α, hα⟩, h⟩ => h ▸ h_basis α hα) hf
  -- (Adjust the argument shape to match wienerChaos's actual definition;
  -- wienerChaos n k = (Submodule.span ℝ S_k).topologicalClosure where
  -- S_k is defined via Set.image of MultiIndex.totalDegree predicate.)
```

`ContinuousLinearMap.eqOn_closure` is the right Mathlib idiom: equality
of two continuous linear maps on a closed set is itself closed, so it
suffices to check on a dense subset (the spanning set, by linearity).
Estimated ~30-50 lines.

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
  standalone lemma, then layer A.4-A.6 on top. Use
  **`Equiv.arrowProdEquivProdArrow`** for the n-D pi-type rearrangement.

* **Stage A.5/A.6 — direct quotient lift, not `LinearMap.extend`**:
  package `mehlerFun` directly into Lp via `MemLp.toLp` +
  `LinearMap.mkContinuous`, with the norm bound coming from A.4.
  This makes A.6 trivial (`MemLp.coeFn_toLp`). **Do not** use
  `LinearMap.extend` from a dense subspace — it triggers convergence
  tracking that's painful to manage.

* **Stage C′.1 — induction + Stein's lemma, not generating function**:
  the recommended proof uses (1) Hermite recurrence
  `He_{k+1} = X · He_k - He_k'`, (2) Stein's lemma
  `∫ y · P(y) dγ = ∫ P'(y) dγ`, (3) `He_k' = k · He_{k-1}`, plus the
  collapse `b² = 1 - a²` with `a := e^{-t}`, `b := √(1 - e^{-2t})`.
  Pure polynomial algebra, no DCT, no infinite series, no `HasSum`.

* **Stage C′.3 — `ContinuousLinearMap.eqOn_closure`**: state both sides
  as CLMs equal on the spanning set `{hermiteMultiLp α : totalDegree α = k}`,
  then lift via `eqOn_closure`. Avoid hand-rolling
  `Submodule.span_induction` + closure tracking.

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

* **Hermite convention** (verified 2026-05-10): Mathlib's
  `Polynomial.hermite` IS the probabilists' convention. No rescaling
  is needed; the Mehler-Hermite identity holds as stated.

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
