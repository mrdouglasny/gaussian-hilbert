/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
-/
import MarkovSemigroups.Diffusion.CarreDuChamp
import MarkovSemigroups.Abstract.Hypercontractivity
import MarkovSemigroups.Instances.WorkInProgress.EuclideanEntropyDecay
import MarkovSemigroups.Instances.WorkInProgress.EuclideanFin
import MarkovSemigroups.Instances.WorkInProgress.EuclideanFinLp
import GaussianHilbert.OUEigenfunctions

/-! # Intended transitive use of markov-semigroups for hypercontractivity

This file documents and exercises the dependency chain that
`GaussianHilbert.ouSemigroupAct_eLpNorm_hypercontractive` will route
through after Stage N completes. The goal is to make explicit which
markov-semigroups axioms gaussian-hilbert (and therefore pphi2) will
transitively depend on, and to ship a working 1D end-to-end example
of the composition.

## Axiom inventory (1 transitive axiom)

As of 2026-05-13, the 1D Gaussian Bakry-Émery instance
`Gaussian1D.bakryEmerySpace : BakryEmerySpace ℝ` is **axiom-free**
(its `#print axioms` shows only the Mathlib core
`propext, Classical.choice, Quot.sound`). All four of the historical
1D BE textbook axioms — `ouSemigroup_preserves_IsCore`,
`ouSemigroup_gradient_decay`, `ouSemigroup_l2_sq_hasDerivWithinAt`,
`ouSemigroup_entropy_sq_decay_bound` — have been discharged into
proved theorems in the markov-semigroups A1/A2 work
(commits `1b3f797`, `6a89298`, `00cd52b`, `ab36ab0`).

Consequently the **only** markov-semigroups axiom that pphi2 will
inherit transitively through the post-Stage-N gaussian-hilbert chain
is the (bundled) Gross theorem:

| Axiom | File:Line | Signature | Citation |
|---|---|---|---|
| `MarkovSemigroup.gross_lsi_implies_hypercontractive` | `Abstract/Hypercontractivity.lean:215` | `(D : DirichletMarkovSemigroup X) (ρ : ℝ) (h_lsi : D.SatisfiesLogSobolev ρ) : D.IsHypercontractive ρ` | Gross 1975, Thm 1; BGL Thm 5.2.3 |

This is a single well-cited textbook fact — substantially better than
the 5-axiom inventory the original Stage N plan assumed.

The Gross-API bundle refactor (commits `6e4ad85`, `371780b`) replaced
the previous loose form (`MarkovSemigroup` + `h_compatible : ds.μ = S.μ` +
`SemigroupGeneratesDirichletForm`) with a single bundled structure
`DirichletMarkovSemigroup`. The new `MarkovSemigroup` field of the
bundle carries four structural Markov properties the old version
omitted: conservation (P_t 1 = 1), positivity (f ≥ 0 ⇒ P_t f ≥ 0),
symmetry, and an `eLpNorm`-based contraction that avoids the Bochner
junk-value trap on non-`L²` functions.

## Chain structure (post-Stage N)

```
       Gaussian1D.bakryEmerySpace        (BakryEmerySpace ℝ, axiom-free)
                       │
            multivariate Gaussian BE-instance construction      (Stage N1)
                       │
                       ▼
        stdGaussianFin.bakryEmerySpace n   (BakryEmerySpace (Fin n → ℝ))
                       │
            BakryEmerySpace.satisfiesLogSobolev                 (proved theorem
                       │                                         in CarreDuChamp.lean)
                       ▼
            LSI(1) on (Fin n → ℝ, γ_n) as a DirichletSpace fact
                       │
            adapt to DirichletMarkovSemigroup bundle            (Stage N3)
              ├─ inherit semigroup, semigroup laws, t≥0 guards
              ├─ prove conservation (P_t 1 = 1)
              ├─ prove positivity (f ≥ 0 ⇒ P_t f ≥ 0)
              ├─ prove symmetry (transfer from BE.semigroup_selfAdjoint)
              ├─ prove eLpNorm contraction (upgrade BE.semigroup_contraction)
              └─ certify energy_eq_deriv (link BE.energy with the OU generator)
                       │
                       ▼
          DirichletMarkovSemigroup (Fin n → ℝ)
                       │     ┌─── gross_lsi_implies_hypercontractive
                       └─────┤    (the only axiom in the chain)
                             ▼
        D.IsHypercontractive 1     (eLpNorm-form Nelson bound)
                       │
            translate to concrete `ouSemigroupAct` CLM action   (Stage N3)
                       │
                       ▼
       GaussianHilbert.ouSemigroupAct_eLpNorm_hypercontractive
                  (currently axiom in gaussian-hilbert;
                   theorem after Stage N3, transitively
                   depending only on `gross_lsi_implies_hypercontractive`
                   plus Mathlib core)
```

## What this file ships

A working 1D end-to-end demonstration of the chain. Specifically:

- `oneDimGaussianLSI` — the 1D Gaussian log-Sobolev inequality with
  constant ρ = 1, obtained by applying `BakryEmerySpace.satisfiesLogSobolev`
  to `Gaussian1D.bakryEmerySpace`. Compiles with no `sorry` and
  `#print axioms` shows only the Mathlib core — confirming the 1D
  chain into LSI is now genuinely axiom-free.

The multivariate analogue (`stdGaussianFin_LSI_schema`) and the
Gross-HC application (`stdGaussianFin_hypercontractive_schema`) are
sketched here as a schema with `sorry` placeholders for the work
Stage N1 + N3 will complete. Once Stage N lands, these schemas turn
into one-line theorems mirroring `oneDimGaussianLSI`.
-/

namespace GaussianHilbert

open MarkovSemigroup

/-! ### 1D end-to-end (works today, axiom-free into LSI) -/

/-- **1D Gaussian log-Sobolev inequality (LSI(1)).**

The standard 1D Gaussian measure satisfies the log-Sobolev inequality
with constant 1. This is the foundational input for Gross's
hypercontractivity theorem (and ultimately for the multivariate
Nelson bound after Stage N).

`#print axioms oneDimGaussianLSI` shows only `propext, Classical.choice,
Quot.sound` — the 1D BE chain is fully discharged. -/
theorem oneDimGaussianLSI :
    DirichletSpace.SatisfiesLogSobolev
      (ds := Gaussian1D.bakryEmerySpace.toDirichletSpace)
      Gaussian1D.bakryEmerySpace.ρ :=
  BakryEmerySpace.satisfiesLogSobolev (be := Gaussian1D.bakryEmerySpace)

/-! ### Multivariate target schema (Stage N1 + Stage N3 will fill in) -/

/-- **Multivariate Gaussian LSI(1).**

The standard `n`-dimensional Gaussian measure
`Measure.pi (fun _ : Fin n => gaussianReal 0 1)` satisfies the
log-Sobolev inequality with constant 1.

After Stage N1 (markov-semigroups commit `b97f7d9` →
`8ed9e52` on main), `stdGaussianFin.bakryEmerySpace n` is available
as a complete `BakryEmerySpace (Fin n → ℝ)` instance, with three
GaussianFin axioms transitively in its closure. Applying
`BakryEmerySpace.satisfiesLogSobolev` gives the LSI directly. -/
theorem stdGaussianFin_LSI (n : ℕ) :
    DirichletSpace.SatisfiesLogSobolev
      (ds := (stdGaussianFin.bakryEmerySpace n).toDirichletSpace)
      (stdGaussianFin.bakryEmerySpace n).ρ :=
  BakryEmerySpace.satisfiesLogSobolev (be := stdGaussianFin.bakryEmerySpace n)

/-- **The bundled Gross HC target — schema (Stage N3 fills in).**

Given the multivariate LSI from `stdGaussianFin_LSI_schema`,
`gross_lsi_implies_hypercontractive` (the only transitive axiom in
the chain) produces the bundled `IsHypercontractive` predicate on a
`DirichletMarkovSemigroup (Fin n → ℝ)` constructed from the BE
instance plus four extra Markov-semigroup properties.

The bridge `BakryEmerySpace → DirichletMarkovSemigroup` is part of N3.
The BE instance gives us the semigroup, the carré du champ Γ, the
energy form, and the `IsCore`-restricted semigroup laws. The bundled
`MarkovSemigroup` additionally requires `t ≥ 0`-guarded semigroup
laws, conservation (`P_t 1 = 1`), positivity (`f ≥ 0 ⇒ P_t f ≥ 0`),
symmetry (transferred from `BE.semigroup_selfAdjoint`), and an
`eLpNorm`-form contraction (upgraded from `BE.semigroup_contraction`).
The bundle further requires `energy_eq_deriv` linking the energy form
to the generator's quadratic form. -/
theorem stdGaussianFin_hypercontractive_schema (_n : ℕ) : True := by
  -- Original Stage N3 sketch retained as design intent. The Phase 2 bundle
  -- below now provides the `DirichletMarkovSemigroup (Fin n → ℝ)` slot directly,
  -- so the schema collapses to the two-line Phase 2 wire-in next door.
  trivial

/-! ## Phase 3 smoke test (2026-05-15)

Confirms that Phase 2's `GaussianFin.stdGaussianFin_dirichletMarkovSemigroup`
(landed in markov-semigroups commit 6782dc7 on
`feat/lp-carrier-stdGaussianFin-dirichletmarkov`) is reachable from
gaussian-hilbert and slots correctly into
`gross_lsi_implies_hypercontractive`. Once Stage W (LSI tensorization) or
Stage N (full BE instance) lands, `h_lsi` becomes a real theorem and these
examples upgrade to the actual discharge of
`ouSemigroupAct_eLpNorm_hypercontractive`. -/

/-- The Phase 2 bundle is reachable and well-typed as a
`DirichletMarkovSemigroup` on `(Fin n → ℝ)`. -/
noncomputable example (n : ℕ) : DirichletMarkovSemigroup (Fin n → ℝ) :=
  GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n

/-- The Phase 2 bundle slots into `gross_lsi_implies_hypercontractive`:
given an LSI hypothesis, the bundle yields hypercontractivity of the
underlying semigroup. This is the schema that Stage W/N will close. -/
example (n : ℕ)
    (h_lsi : DirichletMarkovSemigroup.SatisfiesLogSobolev
      (GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n) 1) :
    MarkovSemigroup.IsHypercontractive
      (GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n).toMarkovSemigroup 1 :=
  gross_lsi_implies_hypercontractive
    (GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n) 1 one_pos h_lsi

/-! ## Stage E.1 — `h_lsi` adapter (2026-05-15)

Promotes the smoke-test hypothesis above into a real theorem by
transferring `BakryEmerySpace.satisfiesLogSobolev` for
`stdGaussianFin.bakryEmerySpace n` (proved upstream, ρ = 1) through
the Phase 2 `DirichletMarkovSemigroup` bundle. Both sides reduce to
`DirichletSpace.SatisfiesLogSobolev (ds := dirichletSpaceFin n) 1`
because the bundle's auto-derived `toDirichletSpace` takes its fields
from `(dirichletSpaceFin n).field_name`, so the two `ds` instances are
definitionally equal. -/

/-- The Phase 2 `DirichletMarkovSemigroup` bundle for the multivariate
standard Gaussian satisfies the log-Sobolev inequality with constant 1
(`SatisfiesLogSobolev D 1`), inherited from
`stdGaussianFin.bakryEmerySpace n`. -/
theorem stdGaussianFin_dirichletMarkovSemigroup_satisfiesLogSobolev (n : ℕ) :
    DirichletMarkovSemigroup.SatisfiesLogSobolev
      (GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n) 1 :=
  stdGaussianFin_LSI n

/-- The Phase 2 `DirichletMarkovSemigroup` bundle's underlying
`MarkovSemigroup` is hypercontractive at ρ = 1. Combines the E.1 LSI
adapter with `gross_lsi_implies_hypercontractive`. -/
theorem stdGaussianFin_dirichletMarkovSemigroup_isHypercontractive (n : ℕ) :
    MarkovSemigroup.IsHypercontractive
      (GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n).toMarkovSemigroup 1 :=
  gross_lsi_implies_hypercontractive
    (GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n) 1 one_pos
    (stdGaussianFin_dirichletMarkovSemigroup_satisfiesLogSobolev n)

/-! ## Stage E.2 — concrete `ouSemigroupAct_eLpNorm_hypercontractive`
discharge (2026-05-15)

Bridges the abstract `IsHypercontractive` (via the Phase 2 bundle's
underlying `MarkovSemigroup`) to the concrete `eLpNorm`-based statement
that gaussian-hilbert exposes. The key observation is that all the
moving pieces agree **definitionally**:

* `γFin n = stdGaussianFin n` is `rfl` (both reduce to
  `Measure.pi (fun _ => gaussianReal 0 1)`).
* `ouSemigroupFin t f = mehlerFun n t f` is `rfl` (both are the same
  Mehler integral with `ouShiftFin = ouAffine` reducibly).
* `(stdGaussianFin_dirichletMarkovSemigroup n).toMarkovSemigroup.P t =
  ouSemigroupFinLp (n := n) t` definitionally from the bundle.

The remaining work is:

1. `t = 0` case: `h_nelson : p - 1 ≤ exp(0) = 1` ⇒ `p ≤ 2`, combined
   with `hp : 2 ≤ p` ⇒ `p = 2`; `ouSemigroupAct n 0 = id`; bound is
   reflexive equality.
2. `t > 0` case: apply `IsHypercontractive` with abstract `p := 2`,
   abstract `q := target_p`, abstract `ρ := 1`. The chained `ae_eq`s
   produce equal `eLpNorm`s on both sides.
-/

open MeasureTheory ENNReal GaussianFin

private lemma γFin_eq_stdGaussianFin (n : ℕ) :
    GaussianFin.γFin n = stdGaussianFin n := rfl

private lemma ouSemigroupFin_eq_mehlerFun (n : ℕ) (t : ℝ) (f : (Fin n → ℝ) → ℝ) :
    GaussianFin.ouSemigroupFin t f = mehlerFun n t f := rfl

/-- The Phase 2 bundle's underlying semigroup action `(P t f)` agrees
a.e. with gaussian-hilbert's spectral OU action `ouSemigroupAct n t f`. -/
private lemma bundle_P_ae_eq_ouSemigroupAct (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (f : Lp ℝ 2 (stdGaussianFin n)) :
    (((GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n).toMarkovSemigroup.P t f
        : (Fin n → ℝ) → ℝ))
      =ᵐ[stdGaussianFin n]
      ((ouSemigroupAct n t f : (Fin n → ℝ) → ℝ)) := by
  -- (bundle.P t f) is (ouSemigroupFinLp t f) by definition, whose underlying
  -- function is a.e. ouSemigroupFin t (⇑f) = mehlerFun n t (⇑f) (rfl).
  have hLp : (((GaussianFin.ouSemigroupFinLp (n := n) t f) : (Fin n → ℝ) → ℝ))
      =ᵐ[GaussianFin.γFin n] GaussianFin.ouSemigroupFin t ((⇑f) : (Fin n → ℝ) → ℝ) :=
    GaussianFin.ouSemigroupFinLp_coeFn_ae (n := n) t ht f
  -- (mehlerOp n t ht f) is a.e. mehlerFun n t (⇑f).
  have hMehler : ((mehlerOp n t ht f : (Fin n → ℝ) → ℝ))
      =ᵐ[stdGaussianFin n] mehlerFun n t ((⇑f) : (Fin n → ℝ) → ℝ) :=
    mehlerOp_apply n t ht f
  -- Stage Ag: mehlerOp = ouSemigroupAct as CLMs.
  have hAg : mehlerOp n t ht = ouSemigroupAct n t :=
    mehlerOp_eq_ouSemigroupAct n t ht
  -- bundle.P t f = ouSemigroupFinLp t f definitionally.
  have hP_def :
      (GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n).toMarkovSemigroup.P t f
        = GaussianFin.ouSemigroupFinLp (n := n) t f := rfl
  rw [hP_def]
  -- Chain: ouSemigroupFinLp = ouSemigroupFin = mehlerFun =ᵐ mehlerOp = ouSemigroupAct.
  refine hLp.trans ?_
  rw [← hAg]
  exact hMehler.symm

/-- **Concrete Bonami-Beckner-Nelson hypercontractivity for the
multivariate standard Gaussian OU semigroup** (Stage E.2, 2026-05-15).

For `p ≥ 2`, `t ≥ 0`, and `p - 1 ≤ exp(2t)` (the Nelson threshold),
the OU semigroup `ouSemigroupAct n t` maps `L²(γ_n)` to `L^p(γ_n)` with
operator norm ≤ 1.

This is the discharge of the previously-axiomatised
`ouSemigroupAct_eLpNorm_hypercontractive`. The proof routes through
the abstract Phase 2 `DirichletMarkovSemigroup` bundle and
`gross_lsi_implies_hypercontractive`, then identifies the abstract
semigroup action with `ouSemigroupAct` via the chain
`bundle.P t = ouSemigroupFinLp t =ᵐ ouSemigroupFin t = mehlerFun n t
=ᵐ mehlerOp n t ht = ouSemigroupAct n t`. -/
theorem ouSemigroupAct_eLpNorm_hypercontractive {n : ℕ}
    (p : ℝ) (hp : 2 ≤ p)
    (t : ℝ) (ht : 0 ≤ t)
    (h_nelson : p - 1 ≤ Real.exp (2 * t))
    (f : Lp ℝ 2 (stdGaussianFin n)) :
    eLpNorm
        ((ouSemigroupAct n t f : (Fin n → ℝ) → ℝ))
        (ENNReal.ofReal p) (stdGaussianFin n) ≤
      eLpNorm
        ((f : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) := by
  rcases eq_or_lt_of_le ht with ht0 | ht_pos
  · -- t = 0 case: h_nelson forces p ≤ 2, combined with hp gives p = 2.
    subst ht0
    have hp_le : p ≤ 2 := by
      have h := h_nelson
      simp at h
      linarith
    have hp_eq : p = 2 := le_antisymm hp_le hp
    subst hp_eq
    -- Now goal: eLpNorm (ouSemigroupAct n 0 f) (ENNReal.ofReal 2) ≤ eLpNorm f 2.
    -- Use the agreement: ouSemigroupAct n 0 f =ᵐ bundle.P 0 f = ouSemigroupFinLp 0 f = f.
    have hae := bundle_P_ae_eq_ouSemigroupAct n 0 le_rfl f
    -- bundle.P 0 = ouSemigroupFinLp_zero = id, so bundle.P 0 f = f.
    have hP0 : (GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n).toMarkovSemigroup.P 0 f
        = f := by
      change GaussianFin.ouSemigroupFinLp (n := n) 0 f = f
      rw [GaussianFin.ouSemigroupFinLp_zero]
      rfl
    rw [hP0] at hae
    -- hae : (f : ...) =ᵐ (ouSemigroupAct n 0 f : ...)
    -- Need: eLpNorm (ouSemigroupAct n 0 f) (ofReal 2) ≤ eLpNorm f 2.
    have hofReal2 : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, ENNReal.ofReal_natCast]
      rfl
    rw [hofReal2, eLpNorm_congr_ae hae.symm]
    exact le_refl _
  · -- t > 0 case: apply IsHypercontractive with abstract p := 2, q := target_p.
    have hHC := stdGaussianFin_dirichletMarkovSemigroup_isHypercontractive n
    obtain ⟨_, hHC⟩ := hHC
    -- Apply with abstract_p := 2, abstract_q := p (target).
    -- Need: 1 < 2, 2 ≤ p, 0 < t, p ≤ 1 + (2 - 1) * exp(2 * 1 * t) = 1 + exp(2t).
    have h_q_bound : p ≤ 1 + (2 - 1) * Real.exp (2 * 1 * t) := by
      have : Real.exp (2 * 1 * t) = Real.exp (2 * t) := by ring_nf
      rw [this]
      linarith
    have hf_memLp2 :
        MemLp ((⇑f) : (Fin n → ℝ) → ℝ) (ENNReal.ofReal 2)
          (GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n).toMarkovSemigroup.μ := by
      have hμ_eq :
          (GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n).toMarkovSemigroup.μ
            = stdGaussianFin n := rfl
      rw [hμ_eq]
      have hofReal2 : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, ENNReal.ofReal_natCast]
        rfl
      rw [hofReal2]
      exact Lp.memLp f
    have hbound := hHC 2 p t (by norm_num : (1:ℝ) < 2) hp ht_pos h_q_bound f hf_memLp2
    -- hbound : eLpNorm ((bundle.P t f) : ...) (ofReal p) bundle.μ ≤
    --          eLpNorm ((⇑f) : ...) (ofReal 2) bundle.μ.
    -- bundle.μ = stdGaussianFin n is rfl (definitionally γFin n = stdGaussianFin n);
    -- (bundle.P t f) =ᵐ (ouSemigroupAct n t f) by bundle_P_ae_eq_ouSemigroupAct;
    -- ENNReal.ofReal 2 = (2 : ℝ≥0∞).
    have hae := bundle_P_ae_eq_ouSemigroupAct n t ht_pos.le f
    have hofReal2 : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, ENNReal.ofReal_natCast]
      rfl
    -- Massage hbound's RHS to use 2 instead of ENNReal.ofReal 2.
    have hbound' :
        eLpNorm
          (((GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n).toMarkovSemigroup.P t f
            : (Fin n → ℝ) → ℝ))
          (ENNReal.ofReal p) (stdGaussianFin n) ≤
            eLpNorm ((f : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) := by
      have := hbound
      rw [hofReal2] at this
      -- bundle.μ = stdGaussianFin n is rfl; the goal type matches.
      exact this
    -- Swap (bundle.P t f) for (ouSemigroupAct n t f) on the LHS via ae_eq.
    rw [show (((GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n).toMarkovSemigroup.P t f
        : (Fin n → ℝ) → ℝ)) = _ from rfl] at hbound'
    exact (eLpNorm_congr_ae hae).symm.le.trans hbound'

end GaussianHilbert
