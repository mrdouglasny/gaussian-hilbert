# Codex hand-off — Stage N3: discharge `ouSemigroupAct_eLpNorm_hypercontractive`

**Mission**: convert the last remaining gaussian-hilbert axiom

```lean
axiom ouSemigroupAct_eLpNorm_hypercontractive {n : ℕ}
    (p : ℝ) (hp : 2 ≤ p)
    (t : ℝ) (_ht : 0 ≤ t)
    (_h_nelson : p - 1 ≤ Real.exp (2 * t))
    (f : MeasureTheory.Lp ℝ 2 (stdGaussianFin n)) :
    MeasureTheory.eLpNorm
        ((ouSemigroupAct n t f : (Fin n → ℝ) → ℝ))
        (ENNReal.ofReal p) (stdGaussianFin n) ≤
      MeasureTheory.eLpNorm
        ((f : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n)
```

(in `GaussianHilbert/OUEigenfunctions.lean:1559`) into a **theorem**, by
routing through:

1. The proved multivariate LSI(1):
   `BakryEmerySpace.satisfiesLogSobolev (be := stdGaussianFin.bakryEmerySpace n)`
   (`stdGaussianFin_LSI` in `GaussianHilbert/HypercontractivityFromBE.lean`).
2. The bundled Gross axiom
   `MarkovSemigroup.gross_lsi_implies_hypercontractive`
   (in `MarkovSemigroups/Abstract/Hypercontractivity.lean:215`,
   takes a `DirichletMarkovSemigroup` and yields `IsHypercontractive`).
3. A bridge from the abstract `IsHypercontractive` on functions to the
   concrete `eLpNorm` on `Lp` elements.

No new axioms.

---

## Repository setup

- **Repo**: `~/Documents/GitHub/gaussian-hilbert`
- **Base branch**: `main` (currently has `HypercontractivityFromBE.lean`
  with the multivariate LSI as a working theorem and a sketch of N3 as
  a schema; `OUEigenfunctions.lean` has the axiom at line 1559).
- **Working branch**: `feat/stage-n3-hypercontractivity-wire-in` (create
  from main).
- **Worktree**: please run with `isolation: "worktree"`.
- **Sister repo (read-only for this hand-off)**:
  `~/Documents/GitHub/markov-semigroups` at commit `8ed9e52` (head of
  main). The `stdGaussianFin.bakryEmerySpace` instance lives in
  `MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean:2814`.

---

## Reading list

1. **`GaussianHilbert/OUEigenfunctions.lean`** — the file containing the
   target axiom. Read lines 1390-1570 (definitions of `ouSemigroupAct`,
   `chaosCoordEquiv`, `mehlerOp`, the `mehlerOp = ouSemigroupAct`
   agreement theorem, and the axiom). The agreement theorem
   `mehlerOp_eq_ouSemigroupAct` (line ~1462) gives you
   `ouSemigroupAct n t = mehlerOp n t ht` for `0 ≤ t`; use this to
   reduce the spectral form to the pointwise Mehler form.
2. **`GaussianHilbert/HypercontractivityFromBE.lean`** — the LSI input
   is already proved here as `stdGaussianFin_LSI`. Use this directly.
3. **`MarkovSemigroups/Abstract/Hypercontractivity.lean`** — read the
   `MarkovSemigroup` structure (line 76), `DirichletMarkovSemigroup`
   structure (line 137), `IsHypercontractive` definition (line 114), and
   the axiom `gross_lsi_implies_hypercontractive` (line 215). Note that
   `MarkovSemigroup`'s fields are *unconditional* (no `IsCore`
   hypotheses), unlike the BE class's `semigroup_*` fields which assume
   `IsCore`.
4. **`MarkovSemigroups/Instances/WorkInProgress/EuclideanFin.lean`** —
   the multivariate BE-instance `stdGaussianFin.bakryEmerySpace n`
   (line 2814) and the underlying proved theorems
   `ouSemigroupFin_zero/mean/contraction/selfAdjoint/compose/...`,
   most of which have `IsCoreFin` hypotheses. The `ouSemigroupFin`
   semigroup itself is at line 43 (just the Mehler integral, defined
   unconditionally for any function `f`).
5. **`MarkovSemigroups/Instances/WorkInProgress/EuclideanEntropyDecay.lean`** —
   the 1D `Gaussian1D.bakryEmerySpace` for any cross-reference needs.
6. **`~/.claude/AXIOM_AUDIT_FORMAT.md`** — audit-doc conventions
   (you'll update `gaussian-hilbert/AXIOM_AUDIT.md`).

After reading, write a one-paragraph summary of the work scope and
**pause for confirmation** before writing code.

---

## Anti-delegation guards (non-negotiable)

The same guards from the Stage N1 brief apply:

- **No `:= by simpa using upstreamAxiom` delegations.**
- **No new `axiom` declarations** without explicit notification.
- **No `sorry` in committed code.** Pause and report blockers.
- **Do not modify existing axioms** anywhere (gaussian-hilbert,
  markov-semigroups, gaussian-field, Mathlib).
- **Do not modify existing BE / Gross / Stroock-Varopoulos facts**.

---

## Deliverables

### 1. Modify `GaussianHilbert/OUEigenfunctions.lean`

Replace the `axiom ouSemigroupAct_eLpNorm_hypercontractive` declaration
at line 1559 with a `theorem` of the same signature. Keep the
docstring; update the vetting/discharge note to reflect the discharge.

### 2. Likely new file or new section: `GaussianHilbert/OUDirichletMarkovBridge.lean` (or similar)

A clean bridge layer. The bridge has three parts:

**Part A — `DirichletMarkovSemigroup` for the multivariate Gaussian OU**:
construct
```lean
noncomputable def stdGaussianDMS (n : ℕ) :
    DirichletMarkovSemigroup (Fin n → ℝ)
```
from `stdGaussianFin.bakryEmerySpace n`. The structure has ~20 fields;
many can be inherited from the BE-instance, but some need real
mathematical work because the bundled `MarkovSemigroup` requires
*unconditional* semigroup laws (no `IsCore` hypotheses):

- `P := GaussianFin.ouSemigroupFin` (direct).
- `P_zero` follows from `GaussianFin.ouSemigroupFin_zero` (unconditional).
- `P_semigroup` needs an unconditional version — codex proved
  `GaussianFin.ouSemigroupFin_compose` with `IsCoreFin` hypothesis;
  here you need the version for all measurable `f`. **The Mehler-integral
  formulation makes this direct**: both sides equal `∫∫ f(...) dγ dγ`
  by Fubini, regardless of IsCoreFin status. Likely a new helper
  lemma `ouSemigroupFin_compose_general` proving it for any measurable
  `f` (or even any `f`, with junk value if not integrable). **No new
  axiom**.
- `P_conservation : P_t (fun _ => 1) = fun _ => 1` — proves directly
  from `∫ 1 dγ_n = 1` (γ is a probability measure).
- `P_positivity : 0 ≤ f → 0 ≤ P_t f` — direct from integral of
  nonneg integrand is nonneg.
- `P_symmetric` — unconditional version of
  `ouSemigroupFin_selfAdjoint` (same Fubini story).
- `P_l2_contraction` — needs upgrading
  `ouSemigroupFin_contraction` (which is in raw-integral form on
  IsCoreFin) to an `eLpNorm`-form on `MemLp f 2 γ_n` functions.
  Probably the cleanest route: prove `eLpNorm (P_t f) 2 ≤ eLpNorm f 2`
  directly via Jensen + Fubini; the IsCoreFin-restricted version is a
  corollary.
- Dirichlet-form fields (`energy`, `IsCore`, `energy_symm`, etc.):
  inherit from the BE-instance.
- `energy_eq_deriv`: the crucial compatibility. For the OU case,
  `E(f, g) = ∫ Σᵢ ∂ᵢf · ∂ᵢg dγ_n`, and
  `-(d/dt)|_{t=0+} ∫ f · P_t g dγ_n = ∫ Σᵢ ∂ᵢf · ∂ᵢg dγ_n`. This is
  the integrated Gaussian Stein identity / Dirichlet-form identity.
  The 1D analogue is `gaussian_dirichlet_form_identity` in
  `EuclideanStein.lean`; the multivariate version follows from it via
  Fubini per coordinate, but you may need a new helper or to prove it
  inline. **No new axiom expected** — this is a Fubini lift.

**Part B — invoking Gross**:
```lean
theorem stdGaussianDMS_isHypercontractive (n : ℕ) :
    (stdGaussianDMS n).IsHypercontractive 1 :=
  MarkovSemigroup.gross_lsi_implies_hypercontractive
    (stdGaussianDMS n) 1 (...)
```
where the LSI input is `stdGaussianFin_LSI n` (already proved in
`HypercontractivityFromBE.lean`) — likely needs a tiny adapter to match
the `D.SatisfiesLogSobolev 1` form (`DirichletMarkovSemigroup`-bundled
vs `DirichletSpace`-bundled). Should be a one-line `id`-style
unfolding.

**Part C — eLpNorm-form bridge for `ouSemigroupAct`**:
```lean
theorem ouSemigroupAct_eLpNorm_hypercontractive (n : ℕ) (p : ℝ)
    (hp : 2 ≤ p) (t : ℝ) (ht : 0 ≤ t)
    (h_nelson : p - 1 ≤ Real.exp (2 * t))
    (f : MeasureTheory.Lp ℝ 2 (stdGaussianFin n)) :
    eLpNorm ((ouSemigroupAct n t f : (Fin n → ℝ) → ℝ))
            (ENNReal.ofReal p) (stdGaussianFin n) ≤
      eLpNorm ((f : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) := by
  -- Step 1: ouSemigroupAct n t = mehlerOp n t ht (Stage Ag, proved).
  -- Step 2: mehlerOp's pointwise action coincides a.e. with ouSemigroupFin.
  -- Step 3: Apply stdGaussianDMS_isHypercontractive with q := ENNReal.ofReal p, p := 2.
  --         Check Nelson bound h_nelson maps to q ≤ 1 + (p − 1)·e^{2t} in the form
  --         the abstract IsHypercontractive demands.
  -- Step 4: Translate the abstract `eLpNorm (P_t f) q ≤ eLpNorm f p` (functions)
  --         to the concrete `eLpNorm ((ouSemigroupAct n t f : Lp) : function) q ≤ ...`.
  sorry  -- replace this once steps 1-4 are filled
```

The most delicate piece is **Step 4**: bridging the coercion of `Lp` to
its underlying function with the `(Fin n → ℝ) → ℝ` function the
`IsHypercontractive` predicate uses. `(ouSemigroupAct n t f : (Fin n → ℝ) → ℝ)`
is the coercion of an `Lp` element; `(mehlerFun n t ht f₀)` where
`f₀ := (f : (Fin n → ℝ) → ℝ)` is the pointwise version. They agree
a.e., which is enough for `eLpNorm` equality.

### 3. Update audit doc: `gaussian-hilbert/AXIOM_AUDIT.md`

After the theorem lands, gaussian-hilbert has **0** local axioms (down
from 1). The transitive markov-semigroups axiom load becomes 4
(Gross + 3 GaussianFin BGL textbook axioms). Update the audit doc
accordingly.

---

## Verification at the end

- **`lake build`** of the full gaussian-hilbert project succeeds.
- **`#print axioms ouSemigroupAct_eLpNorm_hypercontractive`** shows exactly:
  ```
  axioms it depends on:
    [propext, Classical.choice, Quot.sound,
     MarkovSemigroup.gross_lsi_implies_hypercontractive,
     GaussianFin.ouSemigroupFin_l2_sq_hasDerivWithinAt,
     GaussianFin.ouSemigroupFin_preserves_IsCore,
     GaussianFin.ouSemigroupFin_entropy_sq_decay_bound]
  ```
  Anything else (especially new local axioms in gaussian-hilbert)
  is unexpected.
- All downstream consumers (`bonami_nelson_chaos`,
  `bonami_nelson_chaosLE`, `polynomial_chaos_concentration`) rebuild.

---

## Risks and exit ramps

### Risk 1: `energy_eq_deriv` is harder than expected

This compatibility condition links the Dirichlet form to the
right-derivative of `∫ f · P_t g dμ` at `t = 0`. For Gaussian OU, the
1D version `gaussian_dirichlet_form_identity` is proved (via Stein +
IBP) in `EuclideanStein.lean`; the multivariate version is a Fubini
lift over coordinates. If this stalls past ~3 hours, factor it as a
clearly-named helper lemma and report — but DO NOT add it as an axiom.

### Risk 2: `P_l2_contraction` in eLpNorm-form

The BE-instance gives `∫ (P_t f)² ∂μ ≤ ∫ f² ∂μ` on `IsCore` only. The
abstract MarkovSemigroup wants `eLpNorm (P t f) 2 μ ≤ eLpNorm f 2 μ`
on `MemLp f 2 μ`. The cleanest path is a direct Jensen+Fubini proof on
the Mehler integral. If you find yourself extending from IsCore by
density, that's also fine.

### Risk 3: representative bridge

`Lp.coeFn` returns an a.e.-equivalence class. The agreement
"`(ouSemigroupAct n t f : function) =ᵐ ouSemigroupFin t (f : function)`"
needs to hold a.e. Both are constructed from the Mehler integral
(directly for `mehlerFun`, spectrally for `ouSemigroupAct`). The
existing `mehlerOp_apply` lemma in `OUEigenfunctions.lean` gives the
pointwise representative for `mehlerOp`; combined with
`mehlerOp_eq_ouSemigroupAct`, we get the bridge.

---

## Final reporting

When you finish (or hit a blocker), report:

1. Final commit hash on `feat/stage-n3-hypercontractivity-wire-in`.
2. Worktree path.
3. `#print axioms GaussianHilbert.ouSemigroupAct_eLpNorm_hypercontractive`
   output. Expected closure listed above.
4. `lake build` status.
5. Total lines added (target ~150-250 lines).
6. Any helper lemmas added in markov-semigroups (should be 0;
   everything stays in gaussian-hilbert).
7. Any deviations from the plan.

If you hit a true blocker that requires a new axiom in
markov-semigroups (the only place fundamental new axioms could
plausibly go), **stop and report** rather than adding it. We'll
consult on whether to vet + add or find another route.
