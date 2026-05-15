/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hermite Polynomials Are OU Eigenfunctions

The Ornstein-Uhlenbeck generator on $L^2(\gamma_n)$ (with $\gamma_n$
the standard multivariate Gaussian on $\mathbb R^n$) is
$$
L f(x) \;=\; \Delta f(x) - x \cdot \nabla f(x).
$$

The key spectral fact: $L H_\alpha = -|\alpha| H_\alpha$ for every
multi-index $\alpha$, so the $k$-th Wiener chaos is the eigenspace
of $L$ with eigenvalue $-k$. The OU semigroup $T_t$ acts on
$\mathcal H_k$ by $e^{-kt}$.

The proof is direct algebra:
1. The 1D recurrence gives $L_1 H_k = -k \, H_k$ where
   $L_1 = \partial_x^2 - x \partial_x$.
2. The multi-dim $L$ is a sum of single-coordinate operators
   $L_i = \partial_{x_i}^2 - x_i \partial_{x_i}$.
3. $H_\alpha = \prod_i H_{\alpha_i}(x_i)$, and each $L_i$ acts only
   on its own coordinate, contributing $-\alpha_i$. Sum gives
   $-|\alpha|$.

This bypasses any infinite-dimensional spectral theory: the
eigenfunction relation is a polynomial identity.

## Main definitions

- `ouGenerator n` — the operator $L = \Delta - x \cdot \nabla$ on
  smooth functions $\mathbb R^n \to \mathbb R$.

## Main theorems

- `ouGenerator_hermiteMulti_1d` — `L₁ H_k = -k · H_k` (1D base case).
- `ouGenerator_hermiteMulti` — `L H_α = -|α| · H_α` (multi-index).
- `ouSemigroup_act_wienerChaos` — `T_t f = exp(-k t) · f` for
  `f ∈ wienerChaos γ k`. This is the semigroup-level reformulation.

## References

- S. Janson, *Gaussian Hilbert Spaces*, Cambridge (1997), §2.4
  (the OU semigroup) and Theorem 4.4 (eigenvalues of `L`).
- D. Bakry, I. Gentil, M. Ledoux, *Analysis and Geometry of Markov
  Diffusion Operators*, Springer (2014), §2.7.

## Status

API + axiom skeleton (2026-05-08). The 1D and multivariate
eigenfunction identities are stated as axioms with explicit
proof-strategy docstrings citing the polynomial recurrence; the
semigroup-level reformulation depends on the
`Diffusion/OrnsteinUhlenbeck.lean` skeleton being filled in.
-/

import GaussianHilbert.WienerChaos
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

noncomputable section

namespace GaussianHilbert

/-- The 1D Ornstein-Uhlenbeck generator
$L_1 f(x) = f''(x) - x \, f'(x)$ acting on smooth real functions. -/
noncomputable def ouGenerator1D (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => deriv (deriv f) x - x * deriv f x

/-- The $n$-dim Ornstein-Uhlenbeck generator
$L f(x) = \Delta f(x) - x \cdot \nabla f(x)$. -/
noncomputable def ouGenerator (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x =>
    (∑ i, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single i 1)) -
    (∑ i, x i * fderiv ℝ f x (Pi.single i 1))

/-- The 1D Hermite polynomial as an `ℝ[X]` polynomial. Wrapper around
`(Polynomial.hermite k).map (Int.castRingHom ℝ)` matching gaussian-field's
`hermiteR k` so we can reuse `Polynomial.deriv_aeval` and the
`hermite_derivative` recurrence. -/
private noncomputable abbrev hermitePolyR (k : ℕ) : Polynomial ℝ :=
  (Polynomial.hermite k).map (Int.castRingHom ℝ)

private lemma hermitePolyR_eval_eq_hermiteEval (k : ℕ) (x : ℝ) :
    (hermitePolyR k).eval x = hermiteEval k x := rfl

private lemma derivative_hermitePolyR (k : ℕ) :
    Polynomial.derivative (hermitePolyR (k + 1)) =
      ((k + 1 : ℕ) : Polynomial ℝ) * hermitePolyR k := by
  simp only [hermitePolyR]
  rw [Polynomial.derivative_map, hermite_derivative,
      Polynomial.map_mul, Polynomial.map_natCast]

/-- Derivative of `hermiteEval (k+1)` is `(k+1) · hermiteEval k`. -/
private lemma deriv_hermiteEval_succ (k : ℕ) (x : ℝ) :
    deriv (hermiteEval (k + 1)) x = (k + 1 : ℝ) * hermiteEval k x := by
  -- deriv (eval (hermite (k+1))) = eval (derivative (hermite (k+1)))
  -- = eval ((k+1) * hermite k) = (k+1) * hermiteEval k
  have h_aeval : deriv (fun u : ℝ => (hermitePolyR (k + 1)).eval u) x =
      (Polynomial.derivative (hermitePolyR (k + 1))).eval x := by
    have h1 : (fun u : ℝ => (hermitePolyR (k + 1)).eval u) =
        fun u : ℝ => Polynomial.aeval u (hermitePolyR (k + 1)) := by
      ext u
      simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id]
    rw [h1, Polynomial.deriv_aeval]
    simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id]
  show deriv (fun u : ℝ => (hermitePolyR (k + 1)).eval u) x = _
  rw [h_aeval, derivative_hermitePolyR, Polynomial.eval_mul, Polynomial.eval_natCast]
  push_cast
  rfl

/-- Hermite three-term recurrence at the value level:
`hermiteEval (k + 2) x = x · hermiteEval (k + 1) x − (k + 1) · hermiteEval k x`. -/
private lemma hermiteEval_recurrence (k : ℕ) (x : ℝ) :
    hermiteEval (k + 2) x =
      x * hermiteEval (k + 1) x - ((k + 1 : ℕ) : ℝ) * hermiteEval k x := by
  -- `hermite (k+2) = X * hermite (k+1) - derivative (hermite (k+1))`
  -- and `derivative (hermite (k+1)) = (k+1) * hermite k`.
  show (hermitePolyR (k + 2)).eval x =
    x * (hermitePolyR (k + 1)).eval x - ((k + 1 : ℕ) : ℝ) * (hermitePolyR k).eval x
  have h1 : hermitePolyR (k + 2) =
      Polynomial.X * hermitePolyR (k + 1) -
        Polynomial.derivative (hermitePolyR (k + 1)) := by
    simp only [hermitePolyR]
    rw [Polynomial.hermite_succ, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.derivative_map]
  rw [h1, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
      derivative_hermitePolyR, Polynomial.eval_mul, Polynomial.eval_natCast]

/-- `hermiteEval` is differentiable on ℝ (as a polynomial evaluation). -/
private lemma hermiteEval_differentiable (k : ℕ) :
    Differentiable ℝ (hermiteEval k) := by
  show Differentiable ℝ (fun u : ℝ => (hermitePolyR k).eval u)
  exact (hermitePolyR k).differentiable

/-- **1D Hermite polynomials are OU eigenfunctions:** `L₁ H_k = −k · H_k`.

**Proof:** From `H_k'(x) = k · H_{k-1}(x)` (`deriv_hermiteEval_succ`) and the
three-term recurrence `H_{k+2}(x) = x H_{k+1}(x) − (k+1) H_k(x)`
(`hermiteEval_recurrence`), expand `L₁ H_k = H_k'' - x · H_k'`
and collapse via the recurrence.

**Reference:** Janson, *Gaussian Hilbert Spaces*, Theorem 4.4. -/
theorem ouGenerator1D_hermiteEval (k : ℕ) (x : ℝ) :
    ouGenerator1D (hermiteEval k) x = -(k : ℝ) * hermiteEval k x := by
  unfold ouGenerator1D
  match k with
  | 0 =>
    -- hermiteEval 0 = (fun _ => 1), so all derivatives vanish.
    have h_const : hermiteEval 0 = fun _ : ℝ => (1 : ℝ) := by
      funext y
      show (hermitePolyR 0).eval y = 1
      simp [hermitePolyR, Polynomial.hermite_zero]
    rw [h_const]
    simp
  | 0 + 1 =>
    -- hermiteEval 1 = id, deriv = 1, deriv² = 0; goal: 0 - x · 1 = -1 · x
    have h_id : hermiteEval 1 = fun y : ℝ => y := by
      funext y
      show (hermitePolyR 1).eval y = y
      simp [hermitePolyR, Polynomial.hermite_succ, Polynomial.hermite_zero]
    rw [h_id]
    simp
  | m + 1 + 1 =>
    -- f' = (m+2) · hermiteEval (m+1)
    have h_d1 : deriv (hermiteEval (m + 2)) = fun y => ((m + 2 : ℕ) : ℝ) * hermiteEval (m + 1) y := by
      funext y
      have := deriv_hermiteEval_succ (m + 1) y
      convert this using 1
      push_cast; ring
    rw [h_d1]
    -- f'' = (m+2) · deriv (hermiteEval (m+1)) = (m+2)(m+1) hermiteEval m
    have h_d2 : deriv (fun y => ((m + 2 : ℕ) : ℝ) * hermiteEval (m + 1) y) x =
        ((m + 2 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * hermiteEval m x) := by
      rw [deriv_const_mul _ ((hermiteEval_differentiable (m + 1)).differentiableAt)]
      rw [deriv_hermiteEval_succ]
      push_cast; ring
    rw [h_d2]
    -- Goal: (m+2)(m+1) H_m x − x · (m+2) · H_{m+1} x = -(m+2) · H_{m+2} x
    -- Use H_{m+2} x = x · H_{m+1} x − (m+1) · H_m x.
    have h_rec := hermiteEval_recurrence m x
    -- Normalise `m+1+1` to `m+2` and push casts.
    show ((m + 2 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * hermiteEval m x) -
        x * (((m + 2 : ℕ) : ℝ) * hermiteEval (m + 1) x) =
      -((m + 2 : ℕ) : ℝ) * hermiteEval (m + 2) x
    push_cast at h_rec ⊢
    linear_combination ((m : ℝ) + 2) * h_rec

/-! ## Multivariate slicing helpers (toward `ouGenerator_hermiteMultiEval`)

The OU generator definition uses `fderiv` on `(Fin n → ℝ) → ℝ`. To
reduce to the 1D case, slice along each coordinate: for fixed `x` and
`i`, the slice `s ↦ hermiteMultiEval α (Function.update x i s)` equals
`(∏_{j ≠ i} H_{α_j}(x_j)) · hermiteEval (α i) s`, and its
1D `ouGenerator1D` is computed by `ouGenerator1D_hermiteEval` times the
constant `∏_{j ≠ i} H_{α_j}(x_j)`. -/

/-- The "co-product" excluding coordinate `i`. -/
private noncomputable def hermiteMultiCoprod {n : ℕ} (α : Fin n → ℕ)
    (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∏ j ∈ (Finset.univ.erase i), hermiteEval (α j) (x j)

/-- The slice `s ↦ hermiteMultiEval α (update x i s)` equals
`(∏_{j ≠ i} H_{α_j}(x_j)) · hermiteEval (α i) s`. -/
private lemma hermiteMultiEval_update {n : ℕ} (α : Fin n → ℕ)
    (x : Fin n → ℝ) (i : Fin n) (s : ℝ) :
    hermiteMultiEval α (Function.update x i s) =
      hermiteMultiCoprod α i x * hermiteEval (α i) s := by
  unfold hermiteMultiEval hermiteMultiCoprod
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
        (fun j => hermiteEval (α j) ((Function.update x i s) j)) (Finset.mem_univ i)]
  rw [Function.update_self]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro j hj
  have hj' : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [Function.update_of_ne hj']

/-- Slice has a 1D derivative. -/
private lemma hermiteMultiEval_slice_HasDerivAt {n : ℕ} (α : Fin n → ℕ)
    (x : Fin n → ℝ) (i : Fin n) (s : ℝ) :
    HasDerivAt (fun t : ℝ => hermiteMultiEval α (Function.update x i t))
      (hermiteMultiCoprod α i x * deriv (hermiteEval (α i)) s) s := by
  -- Slice equals const · hermiteEval (α i) (·).
  have h_eq : (fun t : ℝ => hermiteMultiEval α (Function.update x i t)) =
      fun t => hermiteMultiCoprod α i x * hermiteEval (α i) t := by
    funext t
    exact hermiteMultiEval_update α x i t
  rw [h_eq]
  exact (hermiteEval_differentiable (α i)).differentiableAt.hasDerivAt.const_mul
    (hermiteMultiCoprod α i x)

/-- Helper: a Finset-product of `C^∞` functions of the form
`x ↦ p_j (x j)` is `C^∞`. -/
private lemma hermiteMultiProd_contDiff {n : ℕ} (α : Fin n → ℕ)
    (t : Finset (Fin n)) :
    ContDiff ℝ ⊤ (fun x : Fin n → ℝ => ∏ j ∈ t, hermiteEval (α j) (x j)) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact contDiff_const
  | insert k s hk ih =>
    have h_eq : (fun x : Fin n → ℝ => ∏ j ∈ insert k s, hermiteEval (α j) (x j)) =
        fun x => hermiteEval (α k) (x k) * ∏ j ∈ s, hermiteEval (α j) (x j) := by
      funext x
      exact Finset.prod_insert hk
    rw [h_eq]
    refine ContDiff.mul ?_ ih
    -- hermiteEval (α k) (x k) = (hermitePolyR (α k)).eval (x k) = aeval (x k) (hermitePolyR (α k))
    -- composed with the projection x ↦ x k
    have h_one : ContDiff ℝ ⊤ (fun y : ℝ => (hermitePolyR (α k)).eval y) := by
      have : (fun y : ℝ => (hermitePolyR (α k)).eval y) =
          fun y : ℝ => Polynomial.aeval y (hermitePolyR (α k)) := by
        funext y
        simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id]
      rw [this]
      exact Polynomial.contDiff_aeval (hermitePolyR (α k)) ⊤
    exact h_one.comp (contDiff_apply ℝ ℝ k)

/-- `hermiteMultiEval α` is `C^∞`, hence smooth. -/
private lemma hermiteMultiEval_contDiff {n : ℕ} (α : Fin n → ℕ) :
    ContDiff ℝ ⊤ (hermiteMultiEval α) := by
  unfold hermiteMultiEval
  exact hermiteMultiProd_contDiff α Finset.univ

/-- `hermiteMultiEval α` is differentiable at every point. -/
private lemma hermiteMultiEval_differentiable {n : ℕ} (α : Fin n → ℕ) :
    Differentiable ℝ (hermiteMultiEval α) :=
  (hermiteMultiEval_contDiff α).differentiable (by norm_num)

private lemma hermiteMultiEval_differentiableAt {n : ℕ} (α : Fin n → ℕ)
    (x : Fin n → ℝ) :
    DifferentiableAt ℝ (hermiteMultiEval α) x :=
  (hermiteMultiEval_differentiable α).differentiableAt

/-- Connect the slice derivative to the partial derivative `fderiv … (Pi.single i 1)`. -/
private lemma fderiv_hermiteMultiEval_apply_single {n : ℕ}
    (α : Fin n → ℕ) (x : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (hermiteMultiEval α) x (Pi.single i 1) =
      hermiteMultiCoprod α i x * deriv (hermiteEval (α i)) (x i) := by
  -- The slice `s ↦ f (update x i s)` has derivative
  -- `fderiv f (update x i s) (Pi.single i 1)` by chain rule, then equals
  -- the slice's 1D derivative by `hermiteMultiEval_slice_HasDerivAt`.
  have h_slice := hermiteMultiEval_slice_HasDerivAt α x i (x i)
  have h_chain : HasDerivAt
      (fun s : ℝ => hermiteMultiEval α (Function.update x i s))
      (fderiv ℝ (hermiteMultiEval α) x (Pi.single i 1)) (x i) := by
    have h_update := hasDerivAt_update x i (x i)
    have h_f : HasFDerivAt (hermiteMultiEval α)
        (fderiv ℝ (hermiteMultiEval α) x) x :=
      (hermiteMultiEval_differentiableAt α x).hasFDerivAt
    have h_eq : x = Function.update x i (x i) := (Function.update_eq_self i x).symm
    exact HasFDerivAt.comp_hasDerivAt_of_eq (x := x i) (l := hermiteMultiEval α)
      (l' := fderiv ℝ (hermiteMultiEval α) x) (y := x)
      (f := Function.update x i) (f' := Pi.single i 1)
      h_f h_update h_eq
  exact h_chain.unique h_slice

/-- The function `y ↦ fderiv f y (Pi.single i 1)` (the i-th partial derivative
as a function of the base point) coincides on the i-line through x with
`s ↦ c · deriv (hermiteEval (α i)) s` where `c = hermiteMultiCoprod α i x`. -/
private lemma fderiv_apply_single_update {n : ℕ}
    (α : Fin n → ℕ) (x : Fin n → ℝ) (i : Fin n) (s : ℝ) :
    fderiv ℝ (hermiteMultiEval α) (Function.update x i s) (Pi.single i 1) =
      hermiteMultiCoprod α i x * deriv (hermiteEval (α i)) s := by
  rw [fderiv_hermiteMultiEval_apply_single α (Function.update x i s) i]
  -- Need: `hermiteMultiCoprod α i (update x i s) = hermiteMultiCoprod α i x`
  -- and `(update x i s) i = s`.
  congr 1
  · unfold hermiteMultiCoprod
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hj' : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [Function.update_of_ne hj']
  · rw [Function.update_self]

/-- `deriv` of `hermiteEval k` is differentiable. (Used for the second slice
derivative.) -/
private lemma deriv_hermiteEval_differentiable (k : ℕ) :
    Differentiable ℝ (deriv (hermiteEval k)) := by
  match k with
  | 0 =>
    have h : deriv (hermiteEval 0) = fun _ : ℝ => (0 : ℝ) := by
      have h_const : hermiteEval 0 = fun _ : ℝ => (1 : ℝ) := by
        funext y; show (hermitePolyR 0).eval y = 1
        simp [hermitePolyR, Polynomial.hermite_zero]
      funext y
      rw [h_const]; exact deriv_const y 1
    rw [h]; exact differentiable_const 0
  | k + 1 =>
    have h : deriv (hermiteEval (k + 1)) = fun y => ((k + 1 : ℕ) : ℝ) * hermiteEval k y := by
      funext y
      simpa using deriv_hermiteEval_succ k y
    rw [h]; exact (hermiteEval_differentiable k).const_mul _

/-- Second slice derivative: the slice `s ↦ fderiv f (update x i s) (Pi.single i 1)`
has 1D derivative `c · deriv²(hermiteEval (α i)) (x i)` at `s = x i`. -/
private lemma fderiv_apply_single_slice_HasDerivAt {n : ℕ}
    (α : Fin n → ℕ) (x : Fin n → ℝ) (i : Fin n) :
    HasDerivAt
      (fun s : ℝ => fderiv ℝ (hermiteMultiEval α) (Function.update x i s)
        (Pi.single i 1))
      (hermiteMultiCoprod α i x * deriv (deriv (hermiteEval (α i))) (x i))
      (x i) := by
  have h_eq : (fun s : ℝ => fderiv ℝ (hermiteMultiEval α) (Function.update x i s)
        (Pi.single i 1)) =
      fun s => hermiteMultiCoprod α i x * deriv (hermiteEval (α i)) s := by
    funext s
    exact fderiv_apply_single_update α x i s
  rw [h_eq]
  exact (deriv_hermiteEval_differentiable (α i)).differentiableAt.hasDerivAt.const_mul
    (hermiteMultiCoprod α i x)

-- (`hermiteMultiEval_contDiff` defined above.)

/-- Connect the second slice derivative to `fderiv (fderiv f) x v w`. -/
private lemma fderiv_fderiv_apply_single_single {n : ℕ}
    (α : Fin n → ℕ) (x : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (fderiv ℝ (hermiteMultiEval α)) x (Pi.single i 1) (Pi.single i 1) =
      hermiteMultiCoprod α i x * deriv (deriv (hermiteEval (α i))) (x i) := by
  -- Strategy: T = (· at Pi.single i 1) is a CLM. Apply chain rule:
  -- `g(y) := fderiv f y (Pi.single i 1) = T (fderiv f y)`. So
  -- `fderiv g x v = T (fderiv (fderiv f) x v)`.
  -- The slice 1D derivative of g at x_i along Function.update equals `fderiv g x (Pi.single i 1)`.
  -- And the slice equals the explicit derivative by `fderiv_apply_single_slice_HasDerivAt`.
  set T : ((Fin n → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ))
  set g : (Fin n → ℝ) → ℝ := fun y => fderiv ℝ (hermiteMultiEval α) y (Pi.single i 1)
  -- g = T ∘ fderiv (hermiteMultiEval α)
  have h_g : g = fun y => T (fderiv ℝ (hermiteMultiEval α) y) := by
    funext y
    rfl
  -- f is C^2
  have h_f_top : ContDiff ℝ ⊤ (hermiteMultiEval α) := hermiteMultiEval_contDiff α
  have h_fderiv_c1 : ContDiff ℝ 1 (fderiv ℝ (hermiteMultiEval α)) :=
    h_f_top.fderiv_right (le_top)
  have h_fderiv_diff : DifferentiableAt ℝ (fderiv ℝ (hermiteMultiEval α)) x :=
    (h_fderiv_c1.differentiable (by norm_num)).differentiableAt
  -- fderiv g x = T ∘ fderiv (fderiv f) x.
  have h_fderiv_g : fderiv ℝ g x = T.comp (fderiv ℝ (fderiv ℝ (hermiteMultiEval α)) x) := by
    rw [h_g]
    exact (T.hasFDerivAt.comp x h_fderiv_diff.hasFDerivAt).fderiv
  -- Apply at Pi.single i 1
  have h_eval :
      fderiv ℝ g x (Pi.single i 1) =
      fderiv ℝ (fderiv ℝ (hermiteMultiEval α)) x (Pi.single i 1) (Pi.single i 1) := by
    rw [h_fderiv_g]
    rfl
  -- And `fderiv g x (Pi.single i 1) = c · deriv²(hermiteEval (α i)) (x i)`
  -- via the slice + chain rule:
  have h_g_diff : DifferentiableAt ℝ g x := by
    rw [h_g]
    exact T.differentiableAt.comp x h_fderiv_diff
  have h_chain : HasDerivAt (fun s => g (Function.update x i s))
      (fderiv ℝ g x (Pi.single i 1)) (x i) := by
    have h_update := hasDerivAt_update x i (x i)
    have h_g_fderiv : HasFDerivAt g (fderiv ℝ g x) x := h_g_diff.hasFDerivAt
    have h_eq2 : x = Function.update x i (x i) := (Function.update_eq_self i x).symm
    exact HasFDerivAt.comp_hasDerivAt_of_eq (x := x i) (l := g)
      (l' := fderiv ℝ g x) (y := x)
      (f := Function.update x i) (f' := Pi.single i 1)
      h_g_fderiv h_update h_eq2
  have h_slice := fderiv_apply_single_slice_HasDerivAt α x i
  rw [← h_eval]
  exact h_chain.unique h_slice

/-- **Multivariate Hermite polynomials are OU eigenfunctions:**
`L H_α = -|α| · H_α`.

**Proof:** Slice each coordinate:
`hermiteMultiEval α (update x i s) = c_i(x) · hermiteEval (α i) s`
where `c_i(x) := ∏_{j ≠ i} hermiteEval (α j) (x j)`. The 1D and 2D
partial derivatives factor through `c_i(x)`, so the i-th term of
`ouGenerator n` is `c_i(x) · ouGenerator1D (hermiteEval (α i)) (x i)`.
By `ouGenerator1D_hermiteEval` this equals
`c_i(x) · (-α_i) · hermiteEval (α i) (x i) = -α_i · hermiteMultiEval α x`.
Summing over i gives `-(∑_i α_i) · hermiteMultiEval α x =
-(MultiIndex.totalDegree α) · hermiteMultiEval α x`. -/
theorem ouGenerator_hermiteMultiEval {n : ℕ} (α : Fin n → ℕ)
    (x : Fin n → ℝ) :
    ouGenerator n (hermiteMultiEval α) x =
      -(MultiIndex.totalDegree α : ℝ) * hermiteMultiEval α x := by
  classical
  unfold ouGenerator MultiIndex.totalDegree
  -- Rewrite each fderiv term using the slicing lemmas.
  have h_partial : ∀ i : Fin n,
      fderiv ℝ (hermiteMultiEval α) x (Pi.single i 1) =
        hermiteMultiCoprod α i x * deriv (hermiteEval (α i)) (x i) := by
    intro i; exact fderiv_hermiteMultiEval_apply_single α x i
  have h_partial2 : ∀ i : Fin n,
      fderiv ℝ (fderiv ℝ (hermiteMultiEval α)) x (Pi.single i 1) (Pi.single i 1) =
        hermiteMultiCoprod α i x * deriv (deriv (hermiteEval (α i))) (x i) := by
    intro i; exact fderiv_fderiv_apply_single_single α x i
  simp_rw [h_partial, h_partial2]
  -- Now: ∑_i c_i · (deriv²(hermiteEval (α i)) (x i)) - ∑_i x i · (c_i · deriv(hermiteEval (α i)) (x i))
  --   = ∑_i c_i · ouGenerator1D(hermiteEval (α i))(x i)
  --   = ∑_i c_i · (-α_i) · hermiteEval (α i) (x i)
  --   = -∑_i α_i · hermiteMultiEval α x
  rw [← Finset.sum_sub_distrib]
  rw [show (fun i : Fin n =>
      hermiteMultiCoprod α i x * deriv (deriv (hermiteEval (α i))) (x i) -
      x i * (hermiteMultiCoprod α i x * deriv (hermiteEval (α i)) (x i))) =
      (fun i => hermiteMultiCoprod α i x *
        (deriv (deriv (hermiteEval (α i))) (x i) -
         x i * deriv (hermiteEval (α i)) (x i))) from by
    funext i; ring]
  -- The bracket is `ouGenerator1D (hermiteEval (α i)) (x i)`
  rw [show (fun i : Fin n =>
        hermiteMultiCoprod α i x *
        (deriv (deriv (hermiteEval (α i))) (x i) -
         x i * deriv (hermiteEval (α i)) (x i))) =
      (fun i => hermiteMultiCoprod α i x * ouGenerator1D (hermiteEval (α i)) (x i)) from by
    funext i; rfl]
  -- Apply 1D OU theorem
  simp_rw [ouGenerator1D_hermiteEval]
  -- ∑_i c_i · (-α_i · hermiteEval (α i) (x i)) = ∑_i (-α_i · ∏_j hermiteEval (α j) (x j))
  -- and the latter = -(∑_i α_i) · hermiteMultiEval α x.
  rw [show (fun i : Fin n =>
        hermiteMultiCoprod α i x * (-((α i : ℝ)) * hermiteEval (α i) (x i))) =
      (fun i => -((α i : ℝ)) * hermiteMultiEval α x) from by
    funext i
    unfold hermiteMultiEval hermiteMultiCoprod
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
        (fun j => hermiteEval (α j) (x j)) (Finset.mem_univ i)]
    ring]
  rw [← Finset.sum_mul, Finset.sum_neg_distrib]
  push_cast
  ring

/-! ## Mehler-kernel scaffolding

This is the function-level side of the OU semigroup. The actual `L²`
operator still enters below through the spectral definition
`ouSemigroupAct`; the purpose of the Mehler definitions here is to build
the pointwise/integral API needed for the eventual hypercontractivity
discharge and for the agreement theorem between the two models. -/

/-- The deterministic OU scaling factor `e^{-t}`. -/
noncomputable def ouScale (t : ℝ) : ℝ :=
  Real.exp (-t)

/-- The Gaussian noise factor `sqrt(1 - e^{-2t})` appearing in the Mehler formula. -/
noncomputable def ouNoise (t : ℝ) : ℝ :=
  Real.sqrt (1 - Real.exp (-2 * t))

lemma one_sub_exp_neg_two_nonneg (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ 1 - Real.exp (-2 * t) := by
  have hle : Real.exp (-2 * t) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by linarith)
  linarith

lemma ouNoise_nonneg (t : ℝ) : 0 ≤ ouNoise t := by
  simp [ouNoise]

lemma ouNoise_sq (t : ℝ) (ht : 0 ≤ t) :
    ouNoise t ^ 2 = 1 - Real.exp (-2 * t) := by
  simpa [ouNoise] using Real.sq_sqrt (one_sub_exp_neg_two_nonneg t ht)

lemma ouScale_sq (t : ℝ) :
    ouScale t ^ 2 = Real.exp (-2 * t) := by
  unfold ouScale
  rw [show (-2 * t : ℝ) = -t + -t by ring, Real.exp_add]
  ring

lemma ouScale_sq_add_ouNoise_sq (t : ℝ) (ht : 0 ≤ t) :
    ouScale t ^ 2 + ouNoise t ^ 2 = 1 := by
  rw [ouScale_sq, ouNoise_sq t ht]
  ring

/-- The affine mixing map `(x, y) ↦ e^{-t} x + sqrt(1 - e^{-2t}) y`. -/
noncomputable def ouAffine {n : ℕ} (t : ℝ) (x y : Fin n → ℝ) : Fin n → ℝ :=
  ouScale t • x + ouNoise t • y

@[simp] lemma ouAffine_apply {n : ℕ} (t : ℝ) (x y : Fin n → ℝ) (i : Fin n) :
    ouAffine t x y i = ouScale t * x i + ouNoise t * y i := by
  simp [ouAffine]

private lemma measurable_ouAffine_prod {n : ℕ} (t : ℝ) :
    Measurable fun z : (Fin n → ℝ) × (Fin n → ℝ) => ouAffine t z.1 z.2 := by
  unfold ouAffine
  fun_prop

private lemma measurable_ouAffine_right {n : ℕ} (t : ℝ) (x : Fin n → ℝ) :
    Measurable fun y : Fin n → ℝ => ouAffine t x y := by
  unfold ouAffine
  fun_prop

/-- The raw Mehler operator on functions:
`(M_t f)(x) = ∫ f(e^{-t} • x + sqrt(1 - e^{-2t}) • y) dγ_n(y)`. -/
noncomputable def mehlerFun (n : ℕ) (t : ℝ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x => ∫ y, f (ouAffine t x y) ∂(stdGaussianFin n)

@[simp] lemma mehlerFun_apply (n : ℕ) (t : ℝ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    mehlerFun n t f x = ∫ y, f (ouAffine t x y) ∂(stdGaussianFin n) :=
  rfl

/-- If `f` is measurable, then its Mehler average is measurable in the base point. -/
lemma mehlerFun_measurable (n : ℕ) (t : ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) :
    Measurable (mehlerFun n t f) := by
  haveI : MeasureTheory.SFinite (stdGaussianFin n) := by
    unfold stdGaussianFin
    infer_instance
  let g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun z => f (ouAffine t z.1 z.2)
  have hg : MeasureTheory.StronglyMeasurable g := by
    exact hf.stronglyMeasurable.comp_measurable (measurable_ouAffine_prod t)
  exact (by
    simpa [mehlerFun, g] using
      (MeasureTheory.StronglyMeasurable.integral_prod_right'
        (ν := stdGaussianFin n) hg).measurable)

@[simp] lemma mehlerFun_zero (n : ℕ) (t : ℝ) :
    mehlerFun n t (0 : (Fin n → ℝ) → ℝ) = 0 := by
  funext x
  simp [mehlerFun]

@[simp] lemma mehlerFun_const (n : ℕ) (t c : ℝ) :
    mehlerFun n t (fun _ : Fin n → ℝ => c) = fun _ : Fin n → ℝ => c := by
  haveI : MeasureTheory.IsProbabilityMeasure (stdGaussianFin n) := by
    unfold stdGaussianFin
    infer_instance
  funext x
  simp [mehlerFun]

private lemma ou_kernel_map_real (t : ℝ) (ht : 0 ≤ t) :
    ((ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1)).map
        (fun p : ℝ × ℝ => ouScale t * p.1 + ouNoise t * p.2) =
      ProbabilityTheory.gaussianReal 0 1 := by
  let γ : MeasureTheory.Measure ℝ := ProbabilityTheory.gaussianReal 0 1
  set a : ℝ := ouScale t with ha
  set b : ℝ := ouNoise t with hb
  have hX : ProbabilityTheory.HasLaw (fun p : ℝ × ℝ => p.1) γ (γ.prod γ) :=
    ⟨measurable_fst.aemeasurable, by rw [MeasureTheory.Measure.map_fst_prod]; simp [γ]⟩
  have hY : ProbabilityTheory.HasLaw (fun p : ℝ × ℝ => p.2) γ (γ.prod γ) :=
    ⟨measurable_snd.aemeasurable, by rw [MeasureTheory.Measure.map_snd_prod]; simp [γ]⟩
  have hXscaled := ProbabilityTheory.gaussianReal_const_mul hX a
  have hYscaled := ProbabilityTheory.gaussianReal_const_mul hY b
  have hindep0 : ProbabilityTheory.IndepFun
      (fun p : ℝ × ℝ => p.1)
      (fun p : ℝ × ℝ => p.2)
      (γ.prod γ) :=
    ProbabilityTheory.indepFun_prod (μ := γ) (ν := γ) (X := id) (Y := id)
      measurable_id measurable_id
  have hindep : ProbabilityTheory.IndepFun
      (fun p : ℝ × ℝ => a * p.1)
      (fun p : ℝ × ℝ => b * p.2)
      (γ.prod γ) :=
    hindep0.comp (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
  have hmap := ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun
    hindep hXscaled.map_eq hYscaled.map_eq
  have hab_real : a ^ 2 + b ^ 2 = 1 := by
    rw [ha, hb, ouScale_sq, ouNoise_sq t ht]
    ring
  let va : NNReal := ⟨a ^ 2, sq_nonneg a⟩
  let vb : NNReal := ⟨b ^ 2, sq_nonneg b⟩
  have hgoal :
      ProbabilityTheory.gaussianReal (a * (0 : ℝ) + b * (0 : ℝ))
        (va * (1 : NNReal) + vb * (1 : NNReal)) = γ := by
    change ProbabilityTheory.gaussianReal (a * (0 : ℝ) + b * (0 : ℝ))
      (va * (1 : NNReal) + vb * (1 : NNReal)) =
      ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)
    congr 1
    · simp
    · simp only [mul_one]
      exact NNReal.eq (by
        simp [va, vb, NNReal.coe_add, NNReal.coe_mk, hab_real])
  simpa [γ] using hmap.trans hgoal

private lemma stdGaussianFin_prod_map_ouAffine (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ((stdGaussianFin n).prod (stdGaussianFin n)).map (fun z => ouAffine t z.1 z.2) =
      stdGaussianFin n := by
  let γ : MeasureTheory.Measure ℝ := ProbabilityTheory.gaussianReal 0 1
  let e : (Fin n → ℝ × ℝ) ≃ᵐ ((Fin n → ℝ) × (Fin n → ℝ)) :=
    MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
  let g : (Fin n → ℝ × ℝ) → (Fin n → ℝ) :=
    fun z i => ouScale t * (z i).1 + ouNoise t * (z i).2
  have hprod :
      (MeasureTheory.Measure.pi (fun _ : Fin n => γ.prod γ)).map e =
        (stdGaussianFin n).prod (stdGaussianFin n) := by
    simpa [stdGaussianFin, γ] using
      (MeasureTheory.measurePreserving_arrowProdEquivProdArrow
        ℝ ℝ (Fin n) (fun _ => γ) (fun _ => γ)).map_eq
  have hcoord : ∀ i : Fin n,
      (γ.prod γ).map (fun p : ℝ × ℝ => ouScale t * p.1 + ouNoise t * p.2) = γ := by
    intro i
    simpa [γ] using ou_kernel_map_real t ht
  haveI : ∀ i : Fin n, MeasureTheory.SigmaFinite
      ((γ.prod γ).map (fun p : ℝ × ℝ => ouScale t * p.1 + ouNoise t * p.2)) := by
    intro i
    rw [hcoord i]
    infer_instance
  have hpi :
      (MeasureTheory.Measure.pi (fun _ : Fin n => γ.prod γ)).map g =
        MeasureTheory.Measure.pi (fun _ : Fin n => γ) := by
    calc
      (MeasureTheory.Measure.pi (fun _ : Fin n => γ.prod γ)).map g
          = MeasureTheory.Measure.pi (fun i : Fin n =>
              (γ.prod γ).map (fun p : ℝ × ℝ => ouScale t * p.1 + ouNoise t * p.2)) := by
              simpa [g] using
                (MeasureTheory.Measure.pi_map_pi
                  (μ := fun _ : Fin n => γ.prod γ)
                  (f := fun _ : Fin n => fun p : ℝ × ℝ => ouScale t * p.1 + ouNoise t * p.2)
                  (hf := fun _ =>
                    (by
                      fun_prop : Measurable
                        (fun p : ℝ × ℝ => ouScale t * p.1 + ouNoise t * p.2)).aemeasurable))
      _ = MeasureTheory.Measure.pi (fun _ : Fin n => γ) := by
        congr 1
        funext i
        exact hcoord i
  have hcomp : g = (fun z => ouAffine t z.1 z.2) ∘ e := by
    funext z
    ext i
    simp [g, e, MeasurableEquiv.arrowProdEquivProdArrow, ouAffine]
  calc
    ((stdGaussianFin n).prod (stdGaussianFin n)).map (fun z => ouAffine t z.1 z.2)
        = (((MeasureTheory.Measure.pi (fun _ : Fin n => γ.prod γ)).map e).map
            (fun z => ouAffine t z.1 z.2)) := by rw [hprod]
    _ = (MeasureTheory.Measure.pi (fun _ : Fin n => γ.prod γ)).map g := by
      rw [MeasureTheory.Measure.map_map
          (measurable_ouAffine_prod t)
          e.measurable]
      simpa [Function.comp, hcomp]
    _ = stdGaussianFin n := by simpa [stdGaussianFin, γ] using hpi

private lemma integral_comp_ouAffine_eq (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf : MeasureTheory.Integrable f (stdGaussianFin n)) :
    ∫ z, f (ouAffine t z.1 z.2) ∂((stdGaussianFin n).prod (stdGaussianFin n)) =
      ∫ x, f x ∂(stdGaussianFin n) := by
  have hf_map :
      MeasureTheory.AEStronglyMeasurable f
        (((stdGaussianFin n).prod (stdGaussianFin n)).map (fun z => ouAffine t z.1 z.2)) := by
    rw [stdGaussianFin_prod_map_ouAffine n t ht]
    exact hf.aestronglyMeasurable
  calc
    ∫ z, f (ouAffine t z.1 z.2) ∂((stdGaussianFin n).prod (stdGaussianFin n))
        = ∫ x, f x ∂(((stdGaussianFin n).prod (stdGaussianFin n)).map
            (fun z => ouAffine t z.1 z.2)) := by
              rw [MeasureTheory.integral_map (measurable_ouAffine_prod t).aemeasurable hf_map]
    _ = ∫ x, f x ∂(stdGaussianFin n) := by
      rw [stdGaussianFin_prod_map_ouAffine n t ht]

private lemma mehlerFun_sq_le_ae {n : ℕ} {t : ℝ} (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf_meas : Measurable f)
    (hf : MeasureTheory.MemLp f 2 (stdGaussianFin n)) :
    ∀ᵐ x ∂(stdGaussianFin n),
      (mehlerFun n t f x) ^ 2 ≤
        ∫ y, (f (ouAffine t x y)) ^ 2 ∂(stdGaussianFin n) := by
  haveI : MeasureTheory.SFinite (stdGaussianFin n) := by
    unfold stdGaussianFin
    infer_instance
  haveI : MeasureTheory.IsProbabilityMeasure (stdGaussianFin n) := by
    unfold stdGaussianFin
    infer_instance
  have hsq :
      MeasureTheory.Integrable
        (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (f (ouAffine t z.1 z.2)) ^ 2)
        ((stdGaussianFin n).prod (stdGaussianFin n)) := by
    have hf_sq : MeasureTheory.Integrable (fun x : Fin n → ℝ => f x ^ 2) (stdGaussianFin n) :=
      hf.integrable_sq
    rw [← stdGaussianFin_prod_map_ouAffine n t ht] at hf_sq
    exact hf_sq.comp_measurable (measurable_ouAffine_prod t)
  filter_upwards [hsq.prod_right_ae] with x hx
  let g : (Fin n → ℝ) → ℝ := fun y => f (ouAffine t x y)
  have hg_sq : MeasureTheory.Integrable (fun y : Fin n → ℝ => g y ^ 2) (stdGaussianFin n) := by
    simpa [g] using hx
  have hg_int : MeasureTheory.Integrable g (stdGaussianFin n) := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq ?_).2 hg_sq |>.integrable (by norm_num)
    exact (hf_meas.comp (measurable_ouAffine_right t x)).aestronglyMeasurable
  simpa [mehlerFun, g] using
    (ConvexOn.map_integral_le (μ := stdGaussianFin n)
      (s := Set.univ) (g := fun r : ℝ => r ^ 2) (f := g)
      (hg := Even.convexOn_pow (𝕜 := ℝ) (n := 2) even_two)
      (hgc := continuousOn_pow 2) (hsc := isClosed_univ)
      (hfs := by simp) (hfi := hg_int) (hgi := hg_sq))

private lemma mehlerFun_sq_integrable {n : ℕ} {t : ℝ} (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf_meas : Measurable f)
    (hf : MeasureTheory.MemLp f 2 (stdGaussianFin n)) :
    MeasureTheory.Integrable (fun x : Fin n → ℝ => (mehlerFun n t f x) ^ 2)
      (stdGaussianFin n) := by
  haveI : MeasureTheory.SFinite (stdGaussianFin n) := by
    unfold stdGaussianFin
    infer_instance
  have hsq :
      MeasureTheory.Integrable
        (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (f (ouAffine t z.1 z.2)) ^ 2)
        ((stdGaussianFin n).prod (stdGaussianFin n)) := by
    have hf_sq : MeasureTheory.Integrable (fun x : Fin n → ℝ => f x ^ 2) (stdGaussianFin n) :=
      hf.integrable_sq
    rw [← stdGaussianFin_prod_map_ouAffine n t ht] at hf_sq
    exact hf_sq.comp_measurable (measurable_ouAffine_prod t)
  have hright :
      MeasureTheory.Integrable
        (fun x : Fin n → ℝ =>
          ∫ y, (f (ouAffine t x y)) ^ 2 ∂(stdGaussianFin n))
        (stdGaussianFin n) :=
    hsq.integral_prod_left
  have hmehler_ae : MeasureTheory.AEStronglyMeasurable (mehlerFun n t f) (stdGaussianFin n) :=
    (mehlerFun_measurable n t hf_meas).aestronglyMeasurable
  have hleft_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun x : Fin n → ℝ => (mehlerFun n t f x) ^ 2)
        (stdGaussianFin n) := (AEMeasurable.pow_const hmehler_ae.aemeasurable 2).aestronglyMeasurable
  refine MeasureTheory.Integrable.mono' hright hleft_meas ?_
  filter_upwards [mehlerFun_sq_le_ae ht hf_meas hf] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact hx

/-- The Mehler averaging operator is an `L²` contraction on `stdGaussianFin n`. -/
lemma mehlerFun_integral_sq_le {n : ℕ} {t : ℝ} (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf_meas : Measurable f)
    (hf : MeasureTheory.MemLp f 2 (stdGaussianFin n)) :
    ∫ x, (mehlerFun n t f x) ^ 2 ∂(stdGaussianFin n) ≤
      ∫ x, f x ^ 2 ∂(stdGaussianFin n) := by
  haveI : MeasureTheory.SFinite (stdGaussianFin n) := by
    unfold stdGaussianFin
    infer_instance
  have hleft :
      MeasureTheory.Integrable (fun x : Fin n → ℝ => (mehlerFun n t f x) ^ 2)
        (stdGaussianFin n) :=
    mehlerFun_sq_integrable ht hf_meas hf
  have hsq :
      MeasureTheory.Integrable
        (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (f (ouAffine t z.1 z.2)) ^ 2)
        ((stdGaussianFin n).prod (stdGaussianFin n)) := by
    have hf_sq : MeasureTheory.Integrable (fun x : Fin n → ℝ => f x ^ 2) (stdGaussianFin n) :=
      hf.integrable_sq
    rw [← stdGaussianFin_prod_map_ouAffine n t ht] at hf_sq
    exact hf_sq.comp_measurable (measurable_ouAffine_prod t)
  have hright :
      MeasureTheory.Integrable
        (fun x : Fin n → ℝ =>
          ∫ y, (f (ouAffine t x y)) ^ 2 ∂(stdGaussianFin n))
        (stdGaussianFin n) :=
    hsq.integral_prod_left
  calc
    ∫ x, (mehlerFun n t f x) ^ 2 ∂(stdGaussianFin n)
        ≤ ∫ x, ∫ y, (f (ouAffine t x y)) ^ 2 ∂(stdGaussianFin n) ∂(stdGaussianFin n) := by
          exact MeasureTheory.integral_mono_ae hleft hright (mehlerFun_sq_le_ae ht hf_meas hf)
    _ = ∫ z, (f (ouAffine t z.1 z.2)) ^ 2 ∂((stdGaussianFin n).prod (stdGaussianFin n)) := by
      symm
      exact MeasureTheory.integral_prod _ hsq
    _ = ∫ x, f x ^ 2 ∂(stdGaussianFin n) := by
      exact integral_comp_ouAffine_eq n t ht hf.integrable_sq

/-- `mehlerFun` preserves `L²` membership and is contractive there. -/
lemma mehlerFun_memLp {n : ℕ} {t : ℝ} (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf_meas : Measurable f)
    (hf : MeasureTheory.MemLp f 2 (stdGaussianFin n)) :
    MeasureTheory.MemLp (mehlerFun n t f) 2 (stdGaussianFin n) := by
  haveI : MeasureTheory.SFinite (stdGaussianFin n) := by
    unfold stdGaussianFin
    infer_instance
  have hmehler_ae : MeasureTheory.AEStronglyMeasurable (mehlerFun n t f) (stdGaussianFin n) :=
    (mehlerFun_measurable n t hf_meas).aestronglyMeasurable
  refine (MeasureTheory.memLp_two_iff_integrable_sq
    hmehler_ae).2 ?_
  exact mehlerFun_sq_integrable ht hf_meas hf

private lemma integrable_comp_ouAffine {n : ℕ} {t : ℝ} (ht : 0 ≤ t)
    {f : (Fin n → ℝ) → ℝ} (hf : MeasureTheory.Integrable f (stdGaussianFin n)) :
    MeasureTheory.Integrable
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) => f (ouAffine t z.1 z.2))
      ((stdGaussianFin n).prod (stdGaussianFin n)) := by
  rw [← stdGaussianFin_prod_map_ouAffine n t ht] at hf
  exact hf.comp_measurable (measurable_ouAffine_prod t)

private lemma mehlerFun_add_ae {n : ℕ} {t : ℝ} (ht : 0 ≤ t)
    {f g : (Fin n → ℝ) → ℝ}
    (_hf_meas : Measurable f) (_hg_meas : Measurable g)
    (hf : MeasureTheory.MemLp f 2 (stdGaussianFin n))
    (hg : MeasureTheory.MemLp g 2 (stdGaussianFin n)) :
    mehlerFun n t (f + g) =ᵐ[stdGaussianFin n]
      fun x => mehlerFun n t f x + mehlerFun n t g x := by
  haveI : MeasureTheory.SFinite (stdGaussianFin n) := by
    unfold stdGaussianFin
    infer_instance
  haveI : MeasureTheory.IsFiniteMeasure (stdGaussianFin n) := by
    unfold stdGaussianFin
    infer_instance
  have hcomp_add :
      MeasureTheory.Integrable
        (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (f + g) (ouAffine t z.1 z.2))
        ((stdGaussianFin n).prod (stdGaussianFin n)) :=
    integrable_comp_ouAffine ht ((hf.add hg).integrable (by norm_num))
  have hcomp_f :
      MeasureTheory.Integrable
        (fun z : (Fin n → ℝ) × (Fin n → ℝ) => f (ouAffine t z.1 z.2))
        ((stdGaussianFin n).prod (stdGaussianFin n)) :=
    integrable_comp_ouAffine ht (hf.integrable (by norm_num))
  have hcomp_g :
      MeasureTheory.Integrable
        (fun z : (Fin n → ℝ) × (Fin n → ℝ) => g (ouAffine t z.1 z.2))
        ((stdGaussianFin n).prod (stdGaussianFin n)) :=
    integrable_comp_ouAffine ht (hg.integrable (by norm_num))
  filter_upwards [hcomp_add.prod_right_ae, hcomp_f.prod_right_ae, hcomp_g.prod_right_ae] with
    x hx_add hx_f hx_g
  simpa [Pi.add_apply] using (MeasureTheory.integral_add hx_f hx_g)

private lemma mehlerFun_smul_ae {n : ℕ} {t : ℝ} (ht : 0 ≤ t) (c : ℝ)
    {f : (Fin n → ℝ) → ℝ}
    (_hf_meas : Measurable f)
    (hf : MeasureTheory.MemLp f 2 (stdGaussianFin n)) :
    mehlerFun n t (c • f) =ᵐ[stdGaussianFin n]
      c • mehlerFun n t f := by
  haveI : MeasureTheory.SFinite (stdGaussianFin n) := by
    unfold stdGaussianFin
    infer_instance
  haveI : MeasureTheory.IsFiniteMeasure (stdGaussianFin n) := by
    unfold stdGaussianFin
    infer_instance
  have hcomp_smul :
      MeasureTheory.Integrable
        (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (c • f) (ouAffine t z.1 z.2))
        ((stdGaussianFin n).prod (stdGaussianFin n)) := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      (integrable_comp_ouAffine ht (hf.integrable (by norm_num))).const_mul c
  have hcomp_f :
      MeasureTheory.Integrable
        (fun z : (Fin n → ℝ) × (Fin n → ℝ) => f (ouAffine t z.1 z.2))
        ((stdGaussianFin n).prod (stdGaussianFin n)) :=
    integrable_comp_ouAffine ht (hf.integrable (by norm_num))
  filter_upwards [hcomp_smul.prod_right_ae, hcomp_f.prod_right_ae] with x hx_smul hx_f
  simpa [Pi.smul_apply, smul_eq_mul] using
    (MeasureTheory.integral_const_mul c (fun y : Fin n → ℝ => f (ouAffine t x y)))

private lemma mehlerFun_aeEq_of_aeEq {n : ℕ} {t : ℝ} (ht : 0 ≤ t)
    {f g : (Fin n → ℝ) → ℝ}
    (_hf_meas : Measurable f) (_hg_meas : Measurable g)
    (_hf : MeasureTheory.MemLp f 2 (stdGaussianFin n))
    (_hg : MeasureTheory.MemLp g 2 (stdGaussianFin n))
    (hfg : f =ᵐ[stdGaussianFin n] g) :
    mehlerFun n t f =ᵐ[stdGaussianFin n] mehlerFun n t g := by
  haveI : MeasureTheory.SFinite (stdGaussianFin n) := by
    unfold stdGaussianFin
    infer_instance
  let φ : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) := fun z => ouAffine t z.1 z.2
  have hfg_map :
      f =ᵐ[((stdGaussianFin n).prod (stdGaussianFin n)).map φ] g := by
    rw [stdGaussianFin_prod_map_ouAffine n t ht]
    exact hfg
  have hcomp :
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) => f (ouAffine t z.1 z.2)) =ᵐ[
        (stdGaussianFin n).prod (stdGaussianFin n)]
      (fun z : (Fin n → ℝ) × (Fin n → ℝ) => g (ouAffine t z.1 z.2)) := by
    simpa [φ, Function.comp] using
      (MeasureTheory.ae_eq_comp (measurable_ouAffine_prod t).aemeasurable hfg_map)
  filter_upwards [MeasureTheory.Measure.ae_ae_of_ae_prod hcomp] with x hx
  exact MeasureTheory.integral_congr_ae hx

private lemma lp_norm_sq_eq_integral_sq {n : ℕ}
    (f : MeasureTheory.Lp ℝ 2 (stdGaussianFin n)) :
    ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂(stdGaussianFin n) := by
  have h := norm_sq_eq_re_inner (𝕜 := ℝ) f
  rw [MeasureTheory.L2.inner_def (𝕜 := ℝ)] at h
  simpa [pow_two] using h

/-- The Mehler operator as a linear map on `L²(γ_n)`, built from the function-level Mehler
formula using the canonical measurable representative of an `Lp` element. -/
noncomputable def mehlerLM (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    MeasureTheory.Lp ℝ 2 (stdGaussianFin n) →ₗ[ℝ]
      MeasureTheory.Lp ℝ 2 (stdGaussianFin n) where
  toFun f :=
    (mehlerFun_memLp ht (MeasureTheory.Lp.stronglyMeasurable f).measurable
      (MeasureTheory.Lp.memLp f)).toLp (mehlerFun n t f)
  map_add' f g := by
    let hf : MeasureTheory.MemLp (mehlerFun n t f) 2 (stdGaussianFin n) :=
      mehlerFun_memLp ht (MeasureTheory.Lp.stronglyMeasurable f).measurable
        (MeasureTheory.Lp.memLp f)
    let hg : MeasureTheory.MemLp (mehlerFun n t g) 2 (stdGaussianFin n) :=
      mehlerFun_memLp ht (MeasureTheory.Lp.stronglyMeasurable g).measurable
        (MeasureTheory.Lp.memLp g)
    let hsum : MeasureTheory.MemLp
        (mehlerFun n t (fun x => f x + g x)) 2 (stdGaussianFin n) :=
      mehlerFun_memLp ht
        ((MeasureTheory.Lp.stronglyMeasurable f).measurable.add
          (MeasureTheory.Lp.stronglyMeasurable g).measurable)
        ((MeasureTheory.Lp.memLp f).add (MeasureTheory.Lp.memLp g))
    let hfg : MeasureTheory.MemLp (mehlerFun n t (⇑(f + g))) 2 (stdGaussianFin n) :=
      mehlerFun_memLp ht (MeasureTheory.Lp.stronglyMeasurable (f + g)).measurable
        (MeasureTheory.Lp.memLp (f + g))
    change MeasureTheory.MemLp.toLp (mehlerFun n t (⇑(f + g))) hfg =
      MeasureTheory.MemLp.toLp (mehlerFun n t f) hf +
        MeasureTheory.MemLp.toLp (mehlerFun n t g) hg
    calc
      MeasureTheory.MemLp.toLp (mehlerFun n t (⇑(f + g))) hfg
          = MeasureTheory.MemLp.toLp (mehlerFun n t (fun x => f x + g x)) hsum := by
            exact MeasureTheory.MemLp.toLp_congr hfg hsum
              (mehlerFun_aeEq_of_aeEq ht
                (MeasureTheory.Lp.stronglyMeasurable (f + g)).measurable
                (((MeasureTheory.Lp.stronglyMeasurable f).measurable).add
                  (MeasureTheory.Lp.stronglyMeasurable g).measurable)
                (MeasureTheory.Lp.memLp (f + g))
                ((MeasureTheory.Lp.memLp f).add (MeasureTheory.Lp.memLp g))
                (MeasureTheory.Lp.coeFn_add f g))
      _ = MeasureTheory.MemLp.toLp (fun x => mehlerFun n t f x + mehlerFun n t g x) (hf.add hg) := by
            exact MeasureTheory.MemLp.toLp_congr hsum (hf.add hg)
              (mehlerFun_add_ae ht (MeasureTheory.Lp.stronglyMeasurable f).measurable
                (MeasureTheory.Lp.stronglyMeasurable g).measurable
                (MeasureTheory.Lp.memLp f) (MeasureTheory.Lp.memLp g))
      _ = MeasureTheory.MemLp.toLp (mehlerFun n t f) hf +
          MeasureTheory.MemLp.toLp (mehlerFun n t g) hg := by
            simpa using (MeasureTheory.MemLp.toLp_add hf hg)
  map_smul' c f := by
    let hf : MeasureTheory.MemLp (mehlerFun n t f) 2 (stdGaussianFin n) :=
      mehlerFun_memLp ht (MeasureTheory.Lp.stronglyMeasurable f).measurable
        (MeasureTheory.Lp.memLp f)
    let hsmul : MeasureTheory.MemLp
        (mehlerFun n t (fun x => c • f x)) 2 (stdGaussianFin n) :=
      mehlerFun_memLp ht
        (((MeasureTheory.Lp.stronglyMeasurable f).measurable).const_smul c)
        ((MeasureTheory.Lp.memLp f).const_smul c)
    let hcf : MeasureTheory.MemLp (mehlerFun n t (⇑(c • f))) 2 (stdGaussianFin n) :=
      mehlerFun_memLp ht (MeasureTheory.Lp.stronglyMeasurable (c • f)).measurable
        (MeasureTheory.Lp.memLp (c • f))
    change MeasureTheory.MemLp.toLp (mehlerFun n t (⇑(c • f))) hcf =
      c • MeasureTheory.MemLp.toLp (mehlerFun n t f) hf
    calc
      MeasureTheory.MemLp.toLp (mehlerFun n t (⇑(c • f))) hcf
          = MeasureTheory.MemLp.toLp (mehlerFun n t (fun x => c • f x)) hsmul := by
            exact MeasureTheory.MemLp.toLp_congr hcf hsmul
              (mehlerFun_aeEq_of_aeEq ht
                (MeasureTheory.Lp.stronglyMeasurable (c • f)).measurable
                (((MeasureTheory.Lp.stronglyMeasurable f).measurable).const_smul c)
                (MeasureTheory.Lp.memLp (c • f))
                ((MeasureTheory.Lp.memLp f).const_smul c)
                (MeasureTheory.Lp.coeFn_smul c f))
      _ = MeasureTheory.MemLp.toLp (c • mehlerFun n t f) (hf.const_smul c) := by
            exact MeasureTheory.MemLp.toLp_congr hsmul (hf.const_smul c)
              (mehlerFun_smul_ae ht c (MeasureTheory.Lp.stronglyMeasurable f).measurable
                (MeasureTheory.Lp.memLp f))
      _ = c • MeasureTheory.MemLp.toLp (mehlerFun n t f) hf := by
            simpa using (MeasureTheory.MemLp.toLp_const_smul c hf)

private lemma mehlerLM_norm_le (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (f : MeasureTheory.Lp ℝ 2 (stdGaussianFin n)) :
    ‖mehlerLM n t ht f‖ ≤ ‖f‖ := by
  let hf : MeasureTheory.MemLp (mehlerFun n t f) 2 (stdGaussianFin n) :=
    mehlerFun_memLp ht (MeasureTheory.Lp.stronglyMeasurable f).measurable
      (MeasureTheory.Lp.memLp f)
  have hsq : ‖mehlerLM n t ht f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [lp_norm_sq_eq_integral_sq]
    calc
      ∫ x, (mehlerLM n t ht f x) ^ 2 ∂(stdGaussianFin n)
          = ∫ x, (mehlerFun n t f x) ^ 2 ∂(stdGaussianFin n) := by
            change ∫ x, ((MeasureTheory.MemLp.toLp (mehlerFun n t f) hf : MeasureTheory.Lp ℝ 2
              (stdGaussianFin n)) x) ^ 2 ∂(stdGaussianFin n) =
              ∫ x, (mehlerFun n t f x) ^ 2 ∂(stdGaussianFin n)
            apply MeasureTheory.integral_congr_ae
            filter_upwards [MeasureTheory.MemLp.coeFn_toLp hf] with a ha
            rw [ha]
      _ ≤ ∫ x, (f x) ^ 2 ∂(stdGaussianFin n) := by
        exact mehlerFun_integral_sq_le ht (MeasureTheory.Lp.stronglyMeasurable f).measurable
          (MeasureTheory.Lp.memLp f)
      _ = ‖f‖ ^ 2 := by rw [← lp_norm_sq_eq_integral_sq]
  exact le_of_sq_le_sq hsq (norm_nonneg _)

/-- The Mehler operator as a continuous linear map on `L²(γ_n)`. -/
noncomputable def mehlerOp (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    MeasureTheory.Lp ℝ 2 (stdGaussianFin n) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (stdGaussianFin n) :=
  LinearMap.mkContinuous (mehlerLM n t ht) 1 (fun f => by
    simpa using mehlerLM_norm_le n t ht f)

/-- `mehlerOp` acts as `mehlerFun` on the underlying representative of an `L²` class. -/
lemma mehlerOp_apply (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (f : MeasureTheory.Lp ℝ 2 (stdGaussianFin n)) :
    (mehlerOp n t ht f : (Fin n → ℝ) → ℝ) =ᵐ[stdGaussianFin n]
      mehlerFun n t f := by
  exact MeasureTheory.MemLp.coeFn_toLp
    (mehlerFun_memLp ht (MeasureTheory.Lp.stronglyMeasurable f).measurable
      (MeasureTheory.Lp.memLp f))

private lemma hermiteEval_eq_wickMonomial_one (k : ℕ) (x : ℝ) :
    hermiteEval k x = wickMonomial k 1 x := by
  unfold hermiteEval
  rw [wick_eq_hermiteR k 1 (by norm_num : (0 : ℝ) < 1)]
  show _ = Real.sqrt 1 ^ k * _
  rw [Real.sqrt_one, one_pow, one_mul, div_one]

private lemma ouScale_pow (k : ℕ) (t : ℝ) :
    ouScale t ^ k = Real.exp (-(k : ℝ) * t) := by
  induction k with
  | zero =>
      simp [ouScale]
  | succ k ih =>
      rw [pow_succ, ih, ouScale]
      have hexp : Real.exp (-(k : ℝ) * t) * Real.exp (-t) =
          Real.exp (-(k : ℝ) * t + -t) := by
        rw [← Real.exp_add]
      rw [hexp]
      congr 1
      norm_num
      ring

private lemma integral_wickMonomial_one_gaussianReal (k : ℕ) :
    ∫ y : ℝ, wickMonomial k 1 y ∂(ProbabilityTheory.gaussianReal 0 1) =
      if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simpa [hk, wickMonomial_zero] using
      (GaussianField.wickMonomial_inner_gaussianReal_one k 0)
  · simpa [hk, wickMonomial_zero] using
      (GaussianField.wickMonomial_inner_gaussianReal_one k 0)

private lemma wickMonomial_one_memLp_two (k : ℕ) :
    MeasureTheory.MemLp (wickMonomial k 1) 2 (ProbabilityTheory.gaussianReal 0 1) := by
  have hsm :
      MeasureTheory.AEStronglyMeasurable (wickMonomial k 1)
        (ProbabilityTheory.gaussianReal 0 1) := by
    refine ((hermiteEval_differentiable k).continuous.aestronglyMeasurable).congr ?_
    filter_upwards with x
    exact hermiteEval_eq_wickMonomial_one k x
  refine (MeasureTheory.memLp_two_iff_integrable_sq hsm).2 ?_
  apply MeasureTheory.Integrable.of_integral_ne_zero
  rw [show (fun x : ℝ => wickMonomial k 1 x ^ 2) =
      (fun x : ℝ => wickMonomial k 1 x * wickMonomial k 1 x) from by
    funext x
    ring]
  rw [GaussianField.wickMonomial_inner_gaussianReal_one k k, if_pos rfl]
  exact_mod_cast Nat.factorial_ne_zero k

/-- The 1D Mehler action on the probabilists' Hermite polynomial. -/
private lemma mehler_hermiteEval_1d (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : ℝ) :
    ∫ y : ℝ, hermiteEval k (ouScale t * x + ouNoise t * y)
        ∂(ProbabilityTheory.gaussianReal 0 1) =
      Real.exp (-(k : ℝ) * t) * hermiteEval k x := by
  have h_expand :
      ∀ y : ℝ,
        wickMonomial k 1 (ouScale t * x + ouNoise t * y) =
          ∑ m ∈ Finset.range (k + 1),
            ((k.choose m : ℝ) * ouScale t ^ m * wickMonomial m 1 x *
              ouNoise t ^ (k - m)) * wickMonomial (k - m) 1 y := by
    intro y
    have h := wickMonomial_add_add k (ouScale t ^ 2) (ouNoise t ^ 2)
      (ouScale t * x) (ouNoise t * y)
    rw [ouScale_sq_add_ouNoise_sq t ht] at h
    refine h.trans ?_
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hscale :
        wickMonomial m (ouScale t ^ 2) (ouScale t * x) =
          ouScale t ^ m * wickMonomial m 1 x := by
      simpa [one_mul] using wickMonomial_homogeneity m (ouScale t) 1 x
    have hnoise :
        wickMonomial (k - m) (ouNoise t ^ 2) (ouNoise t * y) =
          ouNoise t ^ (k - m) * wickMonomial (k - m) 1 y := by
      simpa [one_mul] using wickMonomial_homogeneity (k - m) (ouNoise t) 1 y
    rw [hscale, hnoise]
    ring
  calc
    ∫ y : ℝ, hermiteEval k (ouScale t * x + ouNoise t * y)
        ∂(ProbabilityTheory.gaussianReal 0 1)
      = ∫ y : ℝ, wickMonomial k 1 (ouScale t * x + ouNoise t * y)
          ∂(ProbabilityTheory.gaussianReal 0 1) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with y
            rw [hermiteEval_eq_wickMonomial_one]
    _ = ∫ y : ℝ,
          ∑ m ∈ Finset.range (k + 1),
            ((k.choose m : ℝ) * ouScale t ^ m * wickMonomial m 1 x *
              ouNoise t ^ (k - m)) * wickMonomial (k - m) 1 y
          ∂(ProbabilityTheory.gaussianReal 0 1) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with y
            exact h_expand y
    _ = ∑ m ∈ Finset.range (k + 1),
          ((k.choose m : ℝ) * ouScale t ^ m * wickMonomial m 1 x *
            ouNoise t ^ (k - m)) *
            ∫ y : ℝ, wickMonomial (k - m) 1 y ∂(ProbabilityTheory.gaussianReal 0 1) := by
            rw [MeasureTheory.integral_finset_sum]
            · refine Finset.sum_congr rfl ?_
              intro m hm
              rw [MeasureTheory.integral_const_mul]
            · intro i hi
              exact ((wickMonomial_one_memLp_two (k - i)).integrable (by norm_num)).const_mul _
    _ = (k.choose k : ℝ) * ouScale t ^ k * wickMonomial k 1 x *
          ∫ y : ℝ, wickMonomial (k - k) 1 y ∂(ProbabilityTheory.gaussianReal 0 1) := by
            rw [Finset.sum_eq_single k]
            · simp
            · intro m hm hmk
              have hm_le : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
              have hkmp : 0 < k - m := Nat.sub_pos_of_lt (lt_of_le_of_ne hm_le hmk)
              rw [integral_wickMonomial_one_gaussianReal]
              simp [Nat.ne_of_gt hkmp]
            · simp
    _ = Real.exp (-(k : ℝ) * t) * hermiteEval k x := by
          simp [integral_wickMonomial_one_gaussianReal, hermiteEval_eq_wickMonomial_one,
            ouScale_pow]

/-- The multivariate Mehler action on a multivariate Hermite polynomial. -/
private lemma mehlerFun_hermiteMultiEval {n : ℕ} (α : Fin n → ℕ)
    (t : ℝ) (ht : 0 ≤ t) (x : Fin n → ℝ) :
    mehlerFun n t (hermiteMultiEval α) x =
      Real.exp (-(MultiIndex.totalDegree α : ℝ) * t) * hermiteMultiEval α x := by
  rw [mehlerFun]
  unfold hermiteMultiEval stdGaussianFin ouAffine
  simp_rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (f := fun i (y : ℝ) => hermiteEval (α i) (ouScale t * x i + ouNoise t * y))]
  have h1d :
      (fun i : Fin n =>
        ∫ y : ℝ, hermiteEval (α i) (ouScale t * x i + ouNoise t * y)
          ∂(ProbabilityTheory.gaussianReal 0 1)) =
        fun i => Real.exp (-(α i : ℝ) * t) * hermiteEval (α i) (x i) := by
    funext i
    exact mehler_hermiteEval_1d (α i) t ht (x i)
  rw [h1d]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  unfold MultiIndex.totalDegree
  calc
    ∑ x, -↑(α x) * t = (∑ x, -((α x : ℝ))) * t := by
      rw [Finset.sum_mul]
    _ = -↑(∑ i, α i) * t := by
      congr 1
      rw [Finset.sum_neg_distrib]
      push_cast
      rfl

/-- `mehlerOp` acts on `hermiteMultiLp α` by the expected eigenvalue. -/
private theorem mehlerOp_hermiteMultiLp {n : ℕ} (α : Fin n → ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    mehlerOp n t ht (hermiteMultiLp α) =
      Real.exp (-(MultiIndex.totalDegree α : ℝ) * t) • hermiteMultiLp α := by
  rw [MeasureTheory.Lp.ext_iff]
  calc
    (mehlerOp n t ht (hermiteMultiLp α) : (Fin n → ℝ) → ℝ)
        =ᵐ[stdGaussianFin n] mehlerFun n t (hermiteMultiLp α) :=
          mehlerOp_apply n t ht (hermiteMultiLp α)
    _ =ᵐ[stdGaussianFin n] mehlerFun n t (hermiteMultiEval α) := by
          exact mehlerFun_aeEq_of_aeEq ht
            (MeasureTheory.Lp.stronglyMeasurable (hermiteMultiLp α)).measurable
            (hermiteMultiEval_continuous α).measurable
            (MeasureTheory.Lp.memLp (hermiteMultiLp α))
            (hermiteMultiEval_memLp α)
            (hermiteMultiLp_coeFn α)
    _ =ᵐ[stdGaussianFin n]
          fun x => Real.exp (-(MultiIndex.totalDegree α : ℝ) * t) * hermiteMultiEval α x := by
            filter_upwards with x
            exact mehlerFun_hermiteMultiEval α t ht x
    _ =ᵐ[stdGaussianFin n]
          fun x => (Real.exp (-(MultiIndex.totalDegree α : ℝ) * t) • hermiteMultiLp α) x := by
            filter_upwards [MeasureTheory.Lp.coeFn_smul
              (Real.exp (-(MultiIndex.totalDegree α : ℝ) * t)) (hermiteMultiLp α),
              hermiteMultiLp_coeFn α] with x hs hx
            rw [hs, Pi.smul_apply, hx]
            simp [smul_eq_mul]

/-- The Mehler operator acts on the `k`-th Wiener chaos by `e^{-kt}`. -/
theorem mehlerOp_eq_smul_of_mem_wienerChaos {n : ℕ} (k : ℕ)
    (t : ℝ) (ht : 0 ≤ t)
    (f : MeasureTheory.Lp ℝ 2 (stdGaussianFin n))
    (hf : f ∈ wienerChaos n k) :
    mehlerOp n t ht f = Real.exp (-(k : ℝ) * t) • f := by
  let c : ℝ := Real.exp (-(k : ℝ) * t)
  let A : MeasureTheory.Lp ℝ 2 (stdGaussianFin n) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (stdGaussianFin n) :=
    mehlerOp n t ht - c • ContinuousLinearMap.id ℝ (MeasureTheory.Lp ℝ 2 (stdGaussianFin n))
  have h_span_le :
      Submodule.span ℝ
        {g | ∃ α : Fin n → ℕ, MultiIndex.totalDegree α = k ∧ g = hermiteMultiLp α}
      ≤ A.ker := by
    rw [Submodule.span_le]
    intro g hg
    rcases hg with ⟨α, hα, rfl⟩
    change A (hermiteMultiLp α) = 0
    simp [A, c, mehlerOp_hermiteMultiLp, hα]
  have h_closed_le : wienerChaos n k ≤ A.ker :=
    Submodule.topologicalClosure_minimal _ h_span_le A.isClosed_ker
  have hAf : A f = 0 := h_closed_le hf
  change mehlerOp n t ht f - c • f = 0 at hAf
  exact sub_eq_zero.mp hAf

/-- The chaos-coordinate isometry coming from the Wiener-chaos Hilbert-sum
decomposition. -/
noncomputable def chaosCoordEquiv (n : ℕ) :
    MeasureTheory.Lp ℝ 2 (stdGaussianFin n) ≃ₗᵢ[ℝ]
      lp (fun k : ℕ => wienerChaos n k) 2 :=
  (wienerChaos_isHilbertSum n).linearIsometryEquiv

/-- The spectral decay factor on the `k`-th Wiener chaos. -/
private noncomputable def chaosDecay (k : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-(k : ℝ) * t)

/-- The chaos-coordinate scaling on the `k`-th Wiener chaos. -/
private noncomputable def chaosScale {n : ℕ} (k : ℕ) (t : ℝ)
    (x : wienerChaos n k) : wienerChaos n k :=
  ⟨chaosDecay k t • (x : MeasureTheory.Lp ℝ 2 (stdGaussianFin n)),
    Submodule.smul_mem (wienerChaos n k) _ x.2⟩

@[simp] private lemma chaosScale_coe {n : ℕ} (k : ℕ) (t : ℝ)
    (x : wienerChaos n k) :
    ((chaosScale k t x : wienerChaos n k) :
      MeasureTheory.Lp ℝ 2 (stdGaussianFin n)) =
      chaosDecay k t • (x : MeasureTheory.Lp ℝ 2 (stdGaussianFin n)) :=
  rfl

private lemma chaosDecay_norm_le_one (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖chaosDecay k t‖ ≤ 1 := by
  have hkt : 0 ≤ (k : ℝ) * t := mul_nonneg (by exact_mod_cast Nat.zero_le k) ht
  have hnonneg : 0 ≤ chaosDecay k t := by
    unfold chaosDecay
    positivity
  have hle : chaosDecay k t ≤ 1 := by
    unfold chaosDecay
    exact Real.exp_le_one_iff.mpr (by linarith)
  rwa [Real.norm_eq_abs, abs_of_nonneg hnonneg]

private lemma chaosDiag_memℓp (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (f : lp (fun k : ℕ => wienerChaos n k) 2) :
    Memℓp (fun k : ℕ => chaosScale k t (f k)) 2 := by
  apply memℓp_gen
  have hf : Summable (fun k : ℕ => ‖f k‖ ^ (2 : ℝ)) :=
    (lp.memℓp f).summable (by norm_num)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) ?_ hf
  intro k
  have hnorm : ‖chaosScale k t (f k)‖ ≤ ‖f k‖ := by
    change ‖((chaosScale k t (f k) : wienerChaos n k) :
        MeasureTheory.Lp ℝ 2 (stdGaussianFin n))‖ ≤
      ‖((f k : wienerChaos n k) : MeasureTheory.Lp ℝ 2 (stdGaussianFin n))‖
    rw [chaosScale_coe]
    calc
      ‖chaosDecay k t • (((f k : wienerChaos n k) :
          MeasureTheory.Lp ℝ 2 (stdGaussianFin n)))‖
          ≤ ‖chaosDecay k t‖ *
            ‖(((f k : wienerChaos n k) :
              MeasureTheory.Lp ℝ 2 (stdGaussianFin n)))‖ := norm_smul_le _ _
      _ ≤ 1 * ‖(((f k : wienerChaos n k) :
          MeasureTheory.Lp ℝ 2 (stdGaussianFin n)))‖ := by
        gcongr
        exact chaosDecay_norm_le_one k t ht
      _ = ‖((f k : wienerChaos n k) : MeasureTheory.Lp ℝ 2 (stdGaussianFin n))‖ := by ring
  have hleft : 0 ≤ ‖chaosScale k t (f k)‖ := norm_nonneg _
  change ‖chaosScale k t (f k)‖ ^ (2 : ℝ) ≤ ‖f k‖ ^ (2 : ℝ)
  simpa using Real.rpow_le_rpow hleft hnorm (by norm_num : 0 ≤ (2 : ℝ))

private noncomputable def chaosDiagLM (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    lp (fun k : ℕ => wienerChaos n k) 2 →ₗ[ℝ]
      lp (fun k : ℕ => wienerChaos n k) 2 where
  toFun f := ⟨fun k : ℕ => chaosScale k t (f k), chaosDiag_memℓp n t ht f⟩
  map_add' f g := by
    apply lp.ext
    funext k
    apply Subtype.ext
    show ((chaosScale k t ((f + g) k) : wienerChaos n k) :
        MeasureTheory.Lp ℝ 2 (stdGaussianFin n)) =
      ((chaosScale k t (f k) + chaosScale k t (g k) : wienerChaos n k) :
        MeasureTheory.Lp ℝ 2 (stdGaussianFin n))
    change chaosDecay k t • ((((f + g) k : wienerChaos n k) :
        MeasureTheory.Lp ℝ 2 (stdGaussianFin n))) =
      chaosDecay k t • (((f k : wienerChaos n k) :
        MeasureTheory.Lp ℝ 2 (stdGaussianFin n))) +
      chaosDecay k t • (((g k : wienerChaos n k) :
        MeasureTheory.Lp ℝ 2 (stdGaussianFin n)))
    rw [show ((((f + g) k : wienerChaos n k) :
        MeasureTheory.Lp ℝ 2 (stdGaussianFin n))) =
        (((f k : wienerChaos n k) : MeasureTheory.Lp ℝ 2 (stdGaussianFin n))) +
        (((g k : wienerChaos n k) : MeasureTheory.Lp ℝ 2 (stdGaussianFin n))) from rfl]
    rw [smul_add]
  map_smul' c f := by
    apply lp.ext
    funext k
    apply Subtype.ext
    show ((chaosScale k t ((c • f) k) : wienerChaos n k) :
        MeasureTheory.Lp ℝ 2 (stdGaussianFin n)) =
      ((c • chaosScale k t (f k) : wienerChaos n k) :
        MeasureTheory.Lp ℝ 2 (stdGaussianFin n))
    change chaosDecay k t • (((c • f) k : wienerChaos n k) :
        MeasureTheory.Lp ℝ 2 (stdGaussianFin n)) =
      c • (chaosDecay k t • (((f k : wienerChaos n k) :
        MeasureTheory.Lp ℝ 2 (stdGaussianFin n))))
    rw [show (((c • f) k : wienerChaos n k) : MeasureTheory.Lp ℝ 2 (stdGaussianFin n)) =
        c • (((f k : wienerChaos n k) : MeasureTheory.Lp ℝ 2 (stdGaussianFin n))) from rfl]
    simpa [smul_smul, mul_comm]

private lemma chaosDiagLM_norm_le (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (f : lp (fun k : ℕ => wienerChaos n k) 2) :
    ‖chaosDiagLM n t ht f‖ ≤ ‖f‖ := by
  have hp : 0 < ((2 : ENNReal).toReal) := by norm_num
  have hsum : ∀ s : Finset ℕ,
      ∑ k ∈ s, ‖chaosDiagLM n t ht f k‖ ^ (2 : ℝ) ≤ ‖f‖ ^ (2 : ℝ) := by
    intro s
    refine le_trans ?_ (lp.sum_rpow_le_norm_rpow (p := (2 : ENNReal)) hp f s)
    refine Finset.sum_le_sum ?_
    intro k hk
    have hnorm : ‖chaosDiagLM n t ht f k‖ ≤ ‖f k‖ := by
      change ‖((chaosScale k t (f k) : wienerChaos n k) :
          MeasureTheory.Lp ℝ 2 (stdGaussianFin n))‖ ≤
        ‖((f k : wienerChaos n k) : MeasureTheory.Lp ℝ 2 (stdGaussianFin n))‖
      rw [chaosScale_coe]
      calc
        ‖chaosDecay k t • (((f k : wienerChaos n k) :
            MeasureTheory.Lp ℝ 2 (stdGaussianFin n)))‖
            ≤ ‖chaosDecay k t‖ *
              ‖(((f k : wienerChaos n k) :
                MeasureTheory.Lp ℝ 2 (stdGaussianFin n)))‖ := norm_smul_le _ _
        _ ≤ 1 * ‖(((f k : wienerChaos n k) :
            MeasureTheory.Lp ℝ 2 (stdGaussianFin n)))‖ := by
          gcongr
          exact chaosDecay_norm_le_one k t ht
        _ = ‖((f k : wienerChaos n k) : MeasureTheory.Lp ℝ 2 (stdGaussianFin n))‖ := by ring
    have hleft : 0 ≤ ‖chaosDiagLM n t ht f k‖ := norm_nonneg _
    simpa using Real.rpow_le_rpow hleft hnorm
      (by norm_num : 0 ≤ ENNReal.toReal (2 : ENNReal))
  exact lp.norm_le_of_forall_sum_le
    (p := (2 : ENNReal)) hp (norm_nonneg _) (f := chaosDiagLM n t ht f) hsum

/-- The diagonal scaling map on chaos coordinates. -/
noncomputable def chaosDiagCLM (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    lp (fun k : ℕ => wienerChaos n k) 2 →L[ℝ]
      lp (fun k : ℕ => wienerChaos n k) 2 :=
  LinearMap.mkContinuous (chaosDiagLM n t ht) 1 (by
    intro f
    simpa using chaosDiagLM_norm_le n t ht f)

@[simp] lemma chaosDiagCLM_apply_single (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (k : ℕ) (x : wienerChaos n k) :
    chaosDiagCLM n t ht (lp.single 2 k x) =
      chaosDecay k t • lp.single 2 k x := by
  change chaosDiagLM n t ht (lp.single 2 k x) = chaosDecay k t • lp.single 2 k x
  apply lp.ext
  funext j
  by_cases h : j = k
  · subst h
    apply Subtype.ext
    simp [chaosDiagLM, chaosScale]
  · simp [chaosDiagLM, chaosScale, h]

/-- The Ornstein-Uhlenbeck semigroup acting on `L²(γ_n)`, defined
spectrally via the Wiener-chaos `IsHilbertSum` decomposition.

For `t ≥ 0`, this acts as multiplication by `e^{-kt}` on each Wiener
chaos `wienerChaos n k`. For `t < 0`, the conventional fallback is the
zero map; no consumer in this codebase uses that branch.

**Mathematical agreement with the Mehler integral.** This operator is
equal to the textbook OU semigroup defined by the Mehler integral
`(M_t f)(x) = ∫ f(e^{-t}·x + √(1-e^{-2t})·y) dγ_n(y)`, because both
are bounded operators on `L²(γ_n)` agreeing on the algebraic direct
sum `⊕_k wienerChaos n k`, which is dense by
`wienerChaos_isHilbertSum`. By continuity plus density, the operators
coincide.

**Architectural debt.** While mathematically identical to the spatial
Mehler integral, this spectral definition obscures the pointwise
geometry of the operator. Proving positivity, Dirichlet-form identities,
or native hypercontractivity from this form alone is impractical. A
future discharge of `ouSemigroupAct_eLpNorm_hypercontractive` will
require formalizing the Mehler integral and proving agreement with the
present spectral definition. -/
noncomputable def ouSemigroupAct (n : ℕ) (t : ℝ) :
    MeasureTheory.Lp ℝ 2 (stdGaussianFin n) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (stdGaussianFin n) :=
  if ht : 0 ≤ t then
    let coord := (chaosCoordEquiv n).toContinuousLinearEquiv
    coord.symm.toContinuousLinearMap.comp
      ((chaosDiagCLM n t ht).comp coord.toContinuousLinearMap)
  else 0

set_option maxHeartbeats 1600000
/-- **The OU semigroup acts on $\mathcal H_k$ by $e^{-kt}$.**

The OU semigroup $T_t$ on $L^2(\gamma_n)$ commutes with the spectral
decomposition into Wiener chaos: each chaos $\mathcal H_k$ is
$T_t$-invariant, and $T_t$ restricts to multiplication by $e^{-kt}$
on it.

This is the semigroup-level reformulation of the eigenfunction
identity above. The connection: $T_t = e^{tL}$, so on the eigenspace
of $L$ with eigenvalue $-k$, $T_t$ is multiplication by $e^{-kt}$.

**Reference:** Janson, *Gaussian Hilbert Spaces*, Theorem 4.4 +
the OU semigroup's L²-spectral-resolution. Bakry-Gentil-Ledoux §2.7. -/
theorem ouSemigroupAct_eq_smul_of_mem_wienerChaos {n : ℕ} (k : ℕ)
    (t : ℝ) (_ht : 0 ≤ t)
    (f : MeasureTheory.Lp ℝ 2 (stdGaussianFin n))
    (_hf : f ∈ wienerChaos n k) :
    ouSemigroupAct n t f = Real.exp (-(k : ℝ) * t) • f := by
  let coord : MeasureTheory.Lp ℝ 2 (stdGaussianFin n) ≃L[ℝ]
      lp (fun j : ℕ => wienerChaos n j) 2 :=
    (chaosCoordEquiv n).toContinuousLinearEquiv
  let fk : wienerChaos n k := ⟨f, _hf⟩
  have hsymm : coord.symm (lp.single 2 k fk) = f := by
    change ((chaosCoordEquiv n).symm (lp.single 2 k fk) :
      MeasureTheory.Lp ℝ 2 (stdGaussianFin n)) = f
    simpa [chaosCoordEquiv, fk] using
      (wienerChaos_isHilbertSum n).linearIsometryEquiv_symm_apply_single (i := k) fk
  have hcoords : coord f = lp.single 2 k fk := by
    have h := congrArg coord hsymm
    simpa using h.symm
  have hact : coord (ouSemigroupAct n t f) = chaosDiagCLM n t _ht (coord f) := by
    rw [ouSemigroupAct, dif_pos _ht]
    change coord (coord.symm (chaosDiagCLM n t _ht (coord f))) =
      chaosDiagCLM n t _ht (coord f)
    simp
  apply coord.injective
  calc
    coord (ouSemigroupAct n t f) = chaosDiagCLM n t _ht (coord f) := hact
    _ = chaosDiagCLM n t _ht (lp.single 2 k fk) := by rw [hcoords]
    _ = chaosDecay k t • lp.single 2 k fk := chaosDiagCLM_apply_single n t _ht k fk
    _ = coord (chaosDecay k t • f) := by rw [coord.map_smul, hcoords]

/-- **Agreement: the spectral OU semigroup equals the Mehler integral operator.**

For every $t \ge 0$, the operator `ouSemigroupAct n t` defined spectrally
via the Wiener-chaos `IsHilbertSum` decomposition coincides with the
Mehler integral operator `mehlerOp n t ht` on $L^2(\gamma_n)$.

**Proof.** Both operators are bounded linear (CLMs) and act as
multiplication by $e^{-kt}$ on each Wiener chaos $\mathcal H_k =$
`wienerChaos n k` (by `mehlerOp_eq_smul_of_mem_wienerChaos` and
`ouSemigroupAct_eq_smul_of_mem_wienerChaos`). Their difference $A$ is
therefore a CLM vanishing on every $\mathcal H_k$, hence on
$\bigsqcup_k \mathcal H_k = \bigvee_k \mathcal H_k$, hence on its closure.
By `wienerChaos_isHilbertSum`, that closure is the whole space, so $A=0$. -/
theorem mehlerOp_eq_ouSemigroupAct (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    mehlerOp n t ht = ouSemigroupAct n t := by
  -- Coord isometry as a continuous linear equiv.
  let coord : MeasureTheory.Lp ℝ 2 (stdGaussianFin n) ≃L[ℝ]
      lp (fun k : ℕ => wienerChaos n k) 2 :=
    (chaosCoordEquiv n).toContinuousLinearEquiv
  let coordCLM : MeasureTheory.Lp ℝ 2 (stdGaussianFin n) →L[ℝ]
      lp (fun k : ℕ => wienerChaos n k) 2 :=
    coord.toContinuousLinearMap
  -- A := coord ∘ mehlerOp - chaosDiagCLM ∘ coord; we will show A = 0.
  set A : MeasureTheory.Lp ℝ 2 (stdGaussianFin n) →L[ℝ]
      lp (fun k : ℕ => wienerChaos n k) 2 :=
    coordCLM.comp (mehlerOp n t ht) - (chaosDiagCLM n t ht).comp coordCLM with hA_def
  -- Step 1: A vanishes on every Wiener chaos.
  have h_van : ∀ k : ℕ, wienerChaos n k ≤ A.ker := by
    intro k f hf
    -- Goal: A f = 0.
    show coordCLM (mehlerOp n t ht f) - chaosDiagCLM n t ht (coordCLM f) = 0
    rw [mehlerOp_eq_smul_of_mem_wienerChaos k t ht f hf]
    let fk : wienerChaos n k := ⟨f, hf⟩
    have hsymm : coord.symm (lp.single 2 k fk) = f := by
      change ((chaosCoordEquiv n).symm (lp.single 2 k fk) :
        MeasureTheory.Lp ℝ 2 (stdGaussianFin n)) = f
      simpa [chaosCoordEquiv, fk] using
        (wienerChaos_isHilbertSum n).linearIsometryEquiv_symm_apply_single (i := k) fk
    have hcoords : coordCLM f = lp.single 2 k fk := by
      have h := congrArg coord hsymm
      simpa [coordCLM, coord] using h.symm
    rw [coordCLM.map_smul, hcoords, chaosDiagCLM_apply_single]
    unfold chaosDecay
    simp [sub_self]
  -- Step 2: ⨆ k wienerChaos n k ≤ A.ker.
  have h_sup_le : (⨆ k : ℕ, wienerChaos n k) ≤ A.ker := iSup_le h_van
  -- Step 3: A.ker is closed; pass to the closure.
  have h_closure_le :
      (⨆ k : ℕ, wienerChaos n k).topologicalClosure ≤ A.ker :=
    Submodule.topologicalClosure_minimal _ h_sup_le A.isClosed_ker
  -- Step 4: (⨆ k wienerChaos n k).topologicalClosure = ⊤ (totality witness).
  have h_top : (⨆ k : ℕ, wienerChaos n k).topologicalClosure = ⊤ :=
    wienerChaos_iSup_topologicalClosure_eq_top n
  -- Step 5: A.ker = ⊤ ⇒ A = 0.
  have hA_ker_top : (A.ker : Submodule ℝ _) = ⊤ := by
    apply le_antisymm le_top
    calc (⊤ : Submodule ℝ _)
        = (⨆ k : ℕ, wienerChaos n k).topologicalClosure := h_top.symm
      _ ≤ A.ker := h_closure_le
  have hA0 : A = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    have hf : f ∈ A.ker := by rw [hA_ker_top]; trivial
    exact hf
  -- Step 6: Extract coordCLM ∘ mehlerOp = chaosDiagCLM ∘ coordCLM, conclude.
  have h_eq : coordCLM.comp (mehlerOp n t ht) =
      (chaosDiagCLM n t ht).comp coordCLM := sub_eq_zero.mp hA0
  apply ContinuousLinearMap.ext
  intro f
  -- Goal: mehlerOp n t ht f = ouSemigroupAct n t f.
  apply coord.injective
  show coordCLM (mehlerOp n t ht f) =
    coord.toLinearEquiv (ouSemigroupAct n t f)
  -- Unfold the spectral definition (0 ≤ t branch).
  have hrhs : coord.toLinearEquiv (ouSemigroupAct n t f) =
      chaosDiagCLM n t ht (coordCLM f) := by
    simp [ouSemigroupAct, dif_pos ht, coord, coordCLM]
  rw [hrhs]
  exact DFunLike.congr_fun h_eq f

/- **Nelson's hypercontractive bound for the OU semigroup**
(`ouSemigroupAct_eLpNorm_hypercontractive`).

For any $p \ge 2$ and $t \ge 0$ with $e^{2t} \ge p - 1$, the OU
semigroup $T_t$ maps $L^2(\gamma_n)$ to $L^p(\gamma_n)$ with operator
norm $\le 1$.

**Discharged 2026-05-15** as
`GaussianHilbert.ouSemigroupAct_eLpNorm_hypercontractive` in
`GaussianHilbert/HypercontractivityFromBE.lean` via the Phase 2
markov-semigroups Lp-carrier `DirichletMarkovSemigroup` bundle plus
`gross_lsi_implies_hypercontractive`. Consumers (e.g.
`PolynomialChaosConcentration.lean`) import the proved theorem from
that file.

**Reference:** E. Nelson, *The free Markoff field*, J. Funct. Anal.
12 (1973), §3. Bakry-Gentil-Ledoux Thm 5.2.3. -/

end GaussianHilbert
