/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Polynomial Density in L²(μ) for Sub-Gaussian Probability Measures

A general analysis result: for any probability measure on `Fin n → ℝ` with
sub-Gaussian tails, multivariate polynomials are dense in `L²(μ)`. This is the
natural setting for the moment problem on `ℝⁿ` and the foundation for
orthogonal-polynomial completeness theorems (Hermite, Hermite functions on
`L²(γ)`, Wiener chaos in finite dim).

## Main definitions

- `IsSubGaussianMeasure μ` — `μ` has sub-Gaussian tails:
  `Integrable (fun x => exp(a * ∑ᵢ xᵢ²)) μ` for some `a > 0`. Equivalently,
  `x ↦ exp(a‖x‖²)` is in `L¹(μ)`. All polynomials lie in `L²(μ)` and the
  Gaussian-style tail decay controls polynomial L²-mass on tail balls.

## Main results

- `polynomial_dense_L2_of_subGaussian` — multivariate polynomials are
  dense in `L²(μ)` for any sub-Gaussian probability measure `μ` on `Fin n → ℝ`.
- `isSubGaussianMeasure_pi_gaussianReal` — the standard product Gaussian
  `Measure.pi (fun _ : Fin n => gaussianReal 0 1)` has sub-Gaussian tails. Proved
  by transporting **Fernique's theorem** (Mathlib's
  `IsGaussian.exists_integrable_exp_sq`) along
  `WithLp.toLp 2 : (Fin n → ℝ) ≃ EuclideanSpace ℝ (Fin n)`.

## References

- S. Janson, *Gaussian Hilbert Spaces*, Cambridge (1997), Theorem 2.6.
- D. Nualart, *The Malliavin Calculus and Related Topics*, Springer (2006),
  §1.1.1.
- C. Berg, *The multidimensional moment problem and semigroups*, in
  *Probability Measures on Groups VIII*, Lecture Notes in Math. 1210,
  Springer (1986), 110–124.
-/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Analytic.Order
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Algebra.MvPolynomial

noncomputable section

open MeasureTheory ProbabilityTheory Real WithLp Filter
open scoped Topology

namespace GaussianHilbert

/-- A measure `μ` on `Fin n → ℝ` has sub-Gaussian tails if there exists `a > 0`
with `Integrable (fun x => exp(a · ∑ᵢ xᵢ²)) μ`.

Equivalently, identifying `Fin n → ℝ` with `EuclideanSpace ℝ (Fin n)`, the function
`x ↦ exp(a‖x‖²)` lies in `L¹(μ)`. This condition makes all polynomial functions
square-integrable under `μ` and is the standard hypothesis for polynomial-density
theorems via the moment-problem circle of ideas. -/
def IsSubGaussianMeasure {n : ℕ} (μ : Measure (Fin n → ℝ)) : Prop :=
  ∃ a > (0 : ℝ), Integrable (fun x : Fin n → ℝ => Real.exp (a * ∑ i, x i ^ 2)) μ

/- **Polynomial density in L²(μ) for sub-Gaussian probability measures.**

For any probability measure `μ` on `Fin n → ℝ` with sub-Gaussian tails, the
multivariate polynomials `MvPolynomial (Fin n) ℝ` evaluated at coordinates are
dense in `L²(μ)`.

This is the multivariate version of the classical density theorem for the
Hamburger moment problem on determinate measures. The standard product Gaussian,
the Ornstein-Uhlenbeck stationary distribution, and any sub-Gaussian
distribution on `ℝⁿ` (Beta distributions trivially via Stone-Weierstrass on a
compact, Gamma distributions, etc.) all satisfy the hypothesis.

**Reference:** Janson, *Gaussian Hilbert Spaces*, Theorem 2.6.

**Proof strategy** (textbook):
1. `Cc(ℝⁿ)` is dense in `L²(μ)` (general measure-theoretic fact, Mathlib has it).
2. Given `g ∈ Cc(ℝⁿ)` supported in a closed ball `B_R`, Stone-Weierstrass on the
   compact `B_R` gives a polynomial `p` with `‖g - p‖_{∞,B_R} < ε`.
3. The sub-Gaussian tail bound `μ(B_R^c) ≤ C exp(-aR²)` controls
   `‖p‖_{L²(B_R^c, μ)}` — polynomial growth on the tail is dominated by Gaussian
   decay of the measure.
4. Combine: `‖f - p‖_{L²(μ)} ≤ ‖f - g‖_{L²(μ)} + ‖g - p‖_{L²(B_R, μ)}
   + ‖p‖_{L²(B_R^c, μ)}`, each term `< ε/3` for suitable choices.

**Vetting:** Gemini deep-think DT-2.5 (2026-05-09): **Standard.** The
sub-Gaussian hypothesis implies Carleman's condition, hence the moment
problem is determinate, hence polynomials are dense in `L²(μ)`. The
hypothesis is sufficient (and weaker hypotheses like a second moment
alone do *not* suffice — Stieltjes-style indeterminate examples exist).
Lean signature is correct. Full record:
[pphi2/docs/gaussian-field-axiom-vet-2026-05-09.md](https://github.com/mrdouglasny/pphi2/blob/main/docs/gaussian-field-axiom-vet-2026-05-09.md). -/
/- The proof of `polynomial_dense_L2_of_subGaussian` appears below, after the
supporting moment and `L²` lemmas used in the orthogonal-complement argument. -/

/-- Under a sub-Gaussian tail hypothesis, every coordinate has exponential moments of all orders. -/
lemma integrable_exp_coord_of_subGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ) (i : Fin n) (t : ℝ) :
    Integrable (fun x : Fin n → ℝ => Real.exp (t * x i)) μ := by
  rcases hμ with ⟨a, ha, hInt⟩
  refine Integrable.mono_nonneg (hInt.const_mul (Real.exp (t ^ 2 / (4 * a))))
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_apply i))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _) ?_
  · filter_upwards with x
    have h_quad : t * x i ≤ t ^ 2 / (4 * a) + a * x i ^ 2 := by
      have hmul : (4 * a) * (t * x i) ≤ t ^ 2 + 4 * a * (a * x i ^ 2) := by
        nlinarith [sq_nonneg (2 * a * x i - t)]
      have hdiv : t * x i ≤ (t ^ 2 + 4 * a * (a * x i ^ 2)) / (4 * a) := by
        refine (_root_.le_div_iff₀ (by positivity : 0 < 4 * a)).2 ?_
        simpa [mul_add, mul_assoc, mul_left_comm, mul_comm, ha.ne'] using hmul
      calc
        t * x i ≤ (t ^ 2 + 4 * a * (a * x i ^ 2)) / (4 * a) := hdiv
        _ = t ^ 2 / (4 * a) + a * x i ^ 2 := by
          field_simp [ha.ne']
    calc
      Real.exp (t * x i) ≤ Real.exp (t ^ 2 / (4 * a) + a * x i ^ 2) := Real.exp_le_exp.mpr h_quad
      _ = Real.exp (t ^ 2 / (4 * a)) * Real.exp (a * x i ^ 2) := by
        rw [Real.exp_add]
      _ ≤ Real.exp (t ^ 2 / (4 * a)) * Real.exp (a * ∑ j, x j ^ 2) := by
        have hsq : x i ^ 2 ≤ ∑ j, x j ^ 2 := by
          exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (by simp)
        have hsum : a * x i ^ 2 ≤ a * ∑ j, x j ^ 2 :=
          mul_le_mul_of_nonneg_left hsq ha.le
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum) (Real.exp_nonneg _)

/-- Under a sub-Gaussian tail hypothesis, each coordinate belongs to every finite `Lᵖ(μ)`. -/
lemma zero_mem_interior_integrableExpSet_coord_of_subGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ) (i : Fin n) :
    0 ∈ interior (ProbabilityTheory.integrableExpSet (fun x : Fin n → ℝ => x i) μ) := by
  have h_univ :
      ProbabilityTheory.integrableExpSet (fun x : Fin n → ℝ => x i) μ = Set.univ := by
    ext t
    simp [ProbabilityTheory.integrableExpSet, integrable_exp_coord_of_subGaussian, hμ]
  simp [h_univ]

/-- Under a sub-Gaussian tail hypothesis, each coordinate belongs to every finite `Lᵖ(μ)`. -/
lemma memLp_coord_of_subGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ) (i : Fin n) (p : NNReal) :
    MemLp (fun x : Fin n → ℝ => x i) p μ := by
  exact ProbabilityTheory.memLp_of_mem_interior_integrableExpSet
    (X := fun x : Fin n → ℝ => x i) (μ := μ)
    (zero_mem_interior_integrableExpSet_coord_of_subGaussian μ hμ i) p

/-- Under a sub-Gaussian tail hypothesis, every coordinate has finite moments of all orders. -/
lemma integrable_pow_coord_of_subGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ) (i : Fin n) (k : ℕ) :
    Integrable (fun x : Fin n → ℝ => x i ^ k) μ := by
  exact ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet
    (X := fun x : Fin n → ℝ => x i) (μ := μ)
    (zero_mem_interior_integrableExpSet_coord_of_subGaussian μ hμ i) k

/-- Under a sub-Gaussian tail hypothesis, the quadratic weight `∑ i, x i^2` has an exponential
interval around `0` inside its `integrableExpSet`. -/
lemma zero_mem_interior_integrableExpSet_sum_sq_of_subGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ) :
    0 ∈ interior (ProbabilityTheory.integrableExpSet (fun x : Fin n → ℝ => ∑ i, x i ^ 2) μ) := by
  rcases hμ with ⟨a, ha, hInt⟩
  have h_cont_sum_sq : Continuous (fun x : Fin n → ℝ => ∑ i, x i ^ 2) := by
    refine continuous_finset_sum Finset.univ fun i _ => ?_
    exact (continuous_apply i).pow 2
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset]
  refine ⟨-1, a, by constructor <;> linarith [ha], ?_⟩
  intro t ht
  have hneg : Integrable (fun x : Fin n → ℝ => Real.exp (-1 * ∑ i, x i ^ 2)) μ := by
    refine Integrable.mono_nonneg (integrable_const 1)
      ((Real.continuous_exp.comp (continuous_const.mul h_cont_sum_sq)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _) ?_
    · filter_upwards with x
      have hs_nonneg : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (x i)
      exact Real.exp_le_one_iff.mpr (by nlinarith)
  exact ProbabilityTheory.integrable_exp_mul_of_le_of_le
    (X := fun x : Fin n → ℝ => ∑ i, x i ^ 2) (μ := μ) hneg hInt ht.1.le ht.2.le

/-- Under a sub-Gaussian tail hypothesis, all powers of the quadratic weight are integrable. -/
lemma integrable_pow_sum_sq_of_subGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ) (k : ℕ) :
    Integrable (fun x : Fin n → ℝ => (∑ i, x i ^ 2) ^ k) μ := by
  exact ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet
    (X := fun x : Fin n → ℝ => ∑ i, x i ^ 2) (μ := μ)
    (zero_mem_interior_integrableExpSet_sum_sq_of_subGaussian μ hμ) k

/-- Under a sub-Gaussian tail hypothesis, each multivariate monomial belongs to `L²(μ)`. -/
lemma memLp_monomial_eval_two_of_subGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ) (d : Fin n →₀ ℕ) :
    MemLp (fun x : Fin n → ℝ => ∏ i, x i ^ d i) 2 μ := by
  have h_cont_monomial : Continuous (fun x : Fin n → ℝ => ∏ i, x i ^ d i) := by
    refine continuous_finset_prod Finset.univ fun i _ => ?_
    exact (continuous_apply i).pow (d i)
  have h_meas : AEStronglyMeasurable (fun x : Fin n → ℝ => ∏ i, x i ^ d i) μ := by
    exact h_cont_monomial.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq h_meas]
  refine Integrable.mono_nonneg
    (integrable_pow_sum_sq_of_subGaussian μ hμ (∑ i, d i))
    (h_cont_monomial.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => sq_nonneg _) ?_
  · filter_upwards with x
    let s : ℝ := ∑ i, x i ^ 2
    have hs_nonneg : 0 ≤ s := by
      exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)
    calc
      (∏ i, x i ^ d i) ^ 2 = ∏ i, (x i ^ 2) ^ d i := by
        rw [pow_two, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl ?_
        intro i hi
        rw [← pow_add, ← two_mul, pow_mul]
      _ ≤ ∏ i, s ^ d i := by
        refine Finset.prod_le_prod (fun i _ => by positivity) ?_
        intro i hi
        have hi_le : x i ^ 2 ≤ s := by
          exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
        exact pow_le_pow_left₀ (by positivity : 0 ≤ x i ^ 2) hi_le _
      _ = s ^ ∑ i, d i := by
        rw [Finset.prod_pow_eq_pow_sum]

/-- Under a sub-Gaussian tail hypothesis, every multivariate polynomial evaluation belongs to
`L²(μ)`. -/
lemma MvPolynomial_eval_memLp_two_of_subGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ) (p : MvPolynomial (Fin n) ℝ) :
    MemLp (fun x : Fin n → ℝ => MvPolynomial.eval (fun i => x i) p) 2 μ := by
  have h_eval :
      (fun x : Fin n → ℝ => MvPolynomial.eval (fun i => x i) p) =
        fun x => ∑ d ∈ p.support, p.coeff d * ∏ i, x i ^ d i := by
    funext x
    simpa using (MvPolynomial.eval_eq' (X := fun i => x i) (f := p))
  rw [h_eval]
  exact memLp_finset_sum _ fun d hd =>
    (memLp_monomial_eval_two_of_subGaussian μ hμ d).const_mul (p.coeff d)

/-- For an integrable function on `Fin n → ℝ`, the integral over quadratic tails
`{x | N ≤ ∑ i, x i^2}` tends to zero. -/
lemma tendsto_integral_indicator_ge_sum_sq_to_zero_of_integrable {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    {g : (Fin n → ℝ) → ℝ} (hg : Integrable g μ) :
    Tendsto
      (fun N : ℕ => ∫ x, ({x | (N : ℝ) ≤ ∑ i, x i ^ 2}.indicator g) x ∂μ)
      atTop (𝓝 0) := by
  have h_tail_meas :
      ∀ N : ℕ, MeasurableSet {x : Fin n → ℝ | (N : ℝ) ≤ ∑ i, x i ^ 2} := by
    intro N
    have h_cont_sum_sq : Continuous (fun x : Fin n → ℝ => ∑ i, x i ^ 2) := by
      refine continuous_finset_sum Finset.univ fun i _ => ?_
      exact (continuous_apply i).pow 2
    exact measurableSet_le continuous_const.measurable h_cont_sum_sq.measurable
  let F : ℕ → (Fin n → ℝ) → ℝ :=
    fun N x => ({x | (N : ℝ) ≤ ∑ i, x i ^ 2}.indicator g) x
  have h_tendsto :
      Tendsto (fun N : ℕ => ∫ x, F N x ∂μ) atTop (𝓝 (∫ x, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (G := ℝ) (F := F) (f := fun _ => (0 : ℝ))
      (fun x => ‖g x‖) ?_ hg.norm ?_ ?_
    · intro N
      exact hg.aestronglyMeasurable.indicator (h_tail_meas N)
    · intro N
      exact ae_of_all _ fun x => norm_indicator_le_norm_self _ _
    · filter_upwards with x
      refine tendsto_atTop_of_eventually_const (i₀ := Nat.ceil (∑ i, x i ^ 2) + 1) ?_
      intro N hN
      dsimp [F]
      have hnot : x ∉ {x : Fin n → ℝ | (N : ℝ) ≤ ∑ i, x i ^ 2} := by
        simp only [Set.mem_setOf_eq, not_le]
        have hceil_lt : ((Nat.ceil (∑ i, x i ^ 2)) : ℝ) < N := by
          exact_mod_cast lt_of_lt_of_le (Nat.lt_succ_self _) hN
        exact lt_of_le_of_lt (Nat.le_ceil _) hceil_lt
      rw [Set.indicator_of_notMem hnot]
  simpa [F] using h_tendsto

/-- In particular, the `L²` mass of a polynomial evaluation on quadratic tails tends to zero. -/
lemma tendsto_integral_indicator_ge_sum_sq_eval_sq_to_zero_of_subGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ) (p : MvPolynomial (Fin n) ℝ) :
    Tendsto
      (fun N : ℕ =>
        ∫ x, ({x | (N : ℝ) ≤ ∑ i, x i ^ 2}.indicator
          (fun x : Fin n → ℝ => (MvPolynomial.eval (fun i => x i) p) ^ 2)) x ∂μ)
      atTop (𝓝 0) := by
  exact tendsto_integral_indicator_ge_sum_sq_to_zero_of_integrable μ
    (MvPolynomial_eval_memLp_two_of_subGaussian μ hμ p).integrable_sq

/-- On any compact set in `Fin n → ℝ`, continuous functions can be uniformly approximated by
multivariate polynomials. -/
lemma exists_polynomial_near_continuous_on_isCompact {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℝ,
      ∀ x ∈ K, |f x - MvPolynomial.eval (fun i => x i) p| < ε := by
  let coord : Fin n → C(Fin n → ℝ, ℝ) := fun i => ⟨fun x => x i, continuous_apply i⟩
  let A : Subalgebra ℝ C(Fin n → ℝ, ℝ) := Algebra.adjoin ℝ (Set.range coord)
  have hA_sep : A.SeparatesPoints := by
    intro x y hxy
    classical
    have hne : ∃ i : Fin n, x i ≠ y i := by
      by_contra h
      apply hxy
      ext i
      by_contra hi
      exact h ⟨i, hi⟩
    rcases hne with ⟨i, hi⟩
    refine ⟨fun z => z i, ?_, hi⟩
    exact ⟨coord i, Algebra.subset_adjoin ⟨i, rfl⟩, rfl⟩
  obtain ⟨g, hgA, hg_close⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (A := A) hA_sep ⟨f, hf⟩ hK hε
  have hgA' : (g : C(Fin n → ℝ, ℝ)) ∈ Algebra.adjoin ℝ (Set.range coord) := hgA
  rw [Algebra.adjoin_range_eq_range_aeval ℝ coord] at hgA'
  rcases hgA' with ⟨p, rfl⟩
  refine ⟨p, ?_⟩
  intro x hx
  have h_eval :
      (MvPolynomial.aeval coord p : C(Fin n → ℝ, ℝ)) x =
        MvPolynomial.eval (fun i => x i) p := by
    simpa using (MvPolynomial.comp_aeval_apply
      (R := ℝ) (σ := Fin n) (S₁ := C(Fin n → ℝ, ℝ)) (B := ℝ)
      (f := coord) (φ := ContinuousMap.evalAlgHom ℝ ℝ x) p)
  have := hg_close x hx
  simpa [Real.norm_eq_abs, h_eval, abs_sub_comm] using this

/-- In `L²(μ)`, every function can be approximated by continuous compactly supported functions on
`Fin n → ℝ`. This is the compact-support half of the polynomial-density strategy. -/
lemma MemLp.exists_hasCompactSupport_integral_sq_sub_le {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : (Fin n → ℝ) → ℝ,
      HasCompactSupport g ∧
      (∫ x, |f x - g x| ^ 2 ∂μ) ≤ ε ∧
      Continuous g ∧
      MemLp g 2 μ := by
  have hf' : MemLp f (ENNReal.ofReal 2) μ := by
    simpa using hf
  simpa [Real.norm_eq_abs] using
    (hf'.exists_hasCompactSupport_integral_rpow_sub_le (μ := μ) (p := 2) zero_lt_two hε)

/-- The `L²(μ)` class of a polynomial evaluation, viewed as an element of `Lp ℝ 2 μ`. -/
noncomputable def polynomialToL2 {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ) :
    MvPolynomial (Fin n) ℝ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun p := (MvPolynomial_eval_memLp_two_of_subGaussian μ hμ p).toLp _
  map_add' p q := by
    simpa [Pi.add_def, MvPolynomial.eval_add] using
      (MemLp.toLp_add
        (MvPolynomial_eval_memLp_two_of_subGaussian μ hμ p)
        (MvPolynomial_eval_memLp_two_of_subGaussian μ hμ q))
  map_smul' c p := by
    simpa [Pi.smul_apply, MvPolynomial.smul_eval, smul_eq_mul, mul_comm] using
      (MemLp.toLp_const_smul c
        (MvPolynomial_eval_memLp_two_of_subGaussian μ hμ p))

/-- The linear polynomial corresponding to a continuous linear functional on `Fin n → ℝ`. -/
noncomputable def linearFunctionalPolynomial {n : ℕ}
    (L : StrongDual ℝ (Fin n → ℝ)) :
    MvPolynomial (Fin n) ℝ :=
  ∑ i : Fin n, MvPolynomial.C (L (fun j => if i = j then 1 else 0)) * MvPolynomial.X i

/-- Evaluating `linearFunctionalPolynomial L` recovers the functional `L`. -/
lemma linearFunctionalPolynomial_eval {n : ℕ}
    (L : StrongDual ℝ (Fin n → ℝ)) (x : Fin n → ℝ) :
    MvPolynomial.eval (fun i => x i) (linearFunctionalPolynomial L) = L x := by
  simp [linearFunctionalPolynomial]
  simpa [smul_eq_mul, mul_comm] using
    (LinearMap.pi_apply_eq_sum_univ (f := (L : (Fin n → ℝ) →ₗ[ℝ] ℝ)) x).symm

/-- A linear functional grows at most quadratically relative to `∑ i, x i^2`. -/
lemma linearFunctional_mul_le_subGaussian_weight {n : ℕ}
    (a : ℝ) (ha : 0 < a) (L : StrongDual ℝ (Fin n → ℝ))
    (t : ℝ) (x : Fin n → ℝ) :
    t * L x ≤
      t ^ 2 * max (∑ i, (L (fun j => if i = j then 1 else 0)) ^ 2) 1 / (4 * a)
        + a * ∑ i, x i ^ 2 := by
  let C : ℝ := max (∑ i, (L (fun j => if i = j then 1 else 0)) ^ 2) 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hformula : L x = ∑ i, x i * L (fun j => if i = j then 1 else 0) := by
    simpa [smul_eq_mul] using
      LinearMap.pi_apply_eq_sum_univ (f := (L : (Fin n → ℝ) →ₗ[ℝ] ℝ)) x
  have hsq1 :
      (∑ i, x i * L (fun j => if i = j then 1 else 0)) ^ 2 ≤
        (∑ i, x i ^ 2) * (∑ i, (L (fun j => if i = j then 1 else 0)) ^ 2) := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
      (Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) (f := fun i => x i)
        (g := fun i => L (fun j => if i = j then 1 else 0)))
  have hsq : (L x) ^ 2 ≤ (∑ i, x i ^ 2) * C := by
    rw [hformula]
    exact le_trans hsq1 (by gcongr; exact le_max_left _ _)
  have hmain :
      4 * a * C * (t * L x) ≤ t ^ 2 * C ^ 2 + 4 * a ^ 2 * ((∑ i, x i ^ 2) * C) := by
    nlinarith [hsq, sq_nonneg (2 * a * L x - t * C)]
  have hdiv :
      t * L x ≤
        (t ^ 2 * C ^ 2 + 4 * a ^ 2 * ((∑ i, x i ^ 2) * C)) / (4 * a * C) := by
    refine (_root_.le_div_iff₀ (by positivity : 0 < 4 * a * C)).2 ?_
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
  calc
    t * L x ≤
        (t ^ 2 * C ^ 2 + 4 * a ^ 2 * ((∑ i, x i ^ 2) * C)) / (4 * a * C) := hdiv
    _ = t ^ 2 * C / (4 * a) + a * ∑ i, x i ^ 2 := by
      field_simp [C, hC.ne', ha.ne']
    _ = t ^ 2 * max (∑ i, (L (fun j => if i = j then 1 else 0)) ^ 2) 1 / (4 * a)
          + a * ∑ i, x i ^ 2 := by
      rfl

/-- Under the sub-Gaussian hypothesis, every continuous linear functional has exponential moments
of all orders. -/
lemma integrable_exp_linear_of_subGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ) (L : StrongDual ℝ (Fin n → ℝ)) (t : ℝ) :
    Integrable (fun x : Fin n → ℝ => Real.exp (t * L x)) μ := by
  rcases hμ with ⟨a, ha, hInt⟩
  let C : ℝ := t ^ 2 * max (∑ i, (L (fun j => if i = j then 1 else 0)) ^ 2) 1 / (4 * a)
  refine Integrable.mono_nonneg (hInt.const_mul (Real.exp C))
    ((Real.continuous_exp.comp (continuous_const.mul L.continuous)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _) ?_
  filter_upwards with x
  have hbound : t * L x ≤ C + a * ∑ i, x i ^ 2 := by
    simpa [C] using linearFunctional_mul_le_subGaussian_weight a ha L t x
  calc
    Real.exp (t * L x) ≤ Real.exp (C + a * ∑ i, x i ^ 2) := Real.exp_le_exp.mpr hbound
    _ = Real.exp C * Real.exp (a * ∑ i, x i ^ 2) := by rw [Real.exp_add]

/-- The exponential of a continuous linear functional belongs to `L²(μ)` under the
sub-Gaussian hypothesis. -/
lemma memLp_exp_linear_two_of_subGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ) (L : StrongDual ℝ (Fin n → ℝ)) (t : ℝ) :
    MemLp (fun x : Fin n → ℝ => Real.exp (t * L x)) 2 μ := by
  have h_cont : Continuous (fun x : Fin n → ℝ => Real.exp (t * L x)) := by
    exact Real.continuous_exp.comp (continuous_const.mul L.continuous)
  rw [memLp_two_iff_integrable_sq h_cont.aestronglyMeasurable]
  convert integrable_exp_linear_of_subGaussian μ hμ L (2 * t) using 1
  ext x
  rw [pow_two, ← Real.exp_add, ← two_mul, mul_assoc]

/-- If two finite measures on `ℝ` have all moments and all exponential moments in common, then
their complex moment-generating functions agree everywhere. -/
lemma complexMGF_eq_of_moments
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsetμ : ProbabilityTheory.integrableExpSet id μ = Set.univ)
    (hsetν : ProbabilityTheory.integrableExpSet id ν = Set.univ)
    (hmom : ∀ n : ℕ, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) :
    ProbabilityTheory.complexMGF id μ = ProbabilityTheory.complexMGF id ν := by
  let F : ℂ → ℂ := fun z => ProbabilityTheory.complexMGF id μ z - ProbabilityTheory.complexMGF id ν z
  have hanalyticμ : ∀ z, AnalyticAt ℂ (ProbabilityTheory.complexMGF id μ) z := by
    intro z
    have hz : z.re ∈ interior (ProbabilityTheory.integrableExpSet id μ) := by
      simp [hsetμ]
    exact ProbabilityTheory.analyticAt_complexMGF hz
  have hanalyticν : ∀ z, AnalyticAt ℂ (ProbabilityTheory.complexMGF id ν) z := by
    intro z
    have hz : z.re ∈ interior (ProbabilityTheory.integrableExpSet id ν) := by
      simp [hsetν]
    exact ProbabilityTheory.analyticAt_complexMGF hz
  have hderiv : ∀ n : ℕ, iteratedDeriv n F 0 = 0 := by
    intro n
    have hzμ : (0 : ℂ).re ∈ interior (ProbabilityTheory.integrableExpSet id μ) := by
      simp [hsetμ]
    have hzν : (0 : ℂ).re ∈ interior (ProbabilityTheory.integrableExpSet id ν) := by
      simp [hsetν]
    rw [show F =
        fun z => ProbabilityTheory.complexMGF id μ z - ProbabilityTheory.complexMGF id ν z by rfl]
    rw [iteratedDeriv_fun_sub (AnalyticAt.contDiffAt <| hanalyticμ 0)
      (AnalyticAt.contDiffAt <| hanalyticν 0)]
    rw [ProbabilityTheory.iteratedDeriv_complexMGF hzμ, ProbabilityTheory.iteratedDeriv_complexMGF hzν]
    rw [sub_eq_zero]
    simpa using (show (∫ x, (x ^ n : ℂ) ∂μ) = ∫ x, (x ^ n : ℂ) ∂ν by
      exact_mod_cast hmom n)
  have htop : analyticOrderAt F 0 = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      ((hanalyticμ 0).sub (hanalyticν 0))).2 (fun i _ => hderiv i)
  have hzero : F = 0 :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (z := (0 : ℂ)) (f := F) (hf := by
      intro z
      exact (hanalyticμ z).sub (hanalyticν z))).1 htop
  ext z
  exact sub_eq_zero.mp <| by simpa [F] using congrFun hzero z

/-- An `L²` function orthogonal to all polynomial evaluations has trivial positive and negative
parts as weighted measures. -/
lemma withDensity_pos_eq_neg_of_mem_orthogonal_polynomialToL2 {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ) {u : Lp ℝ 2 μ}
    (hu : u ∈ ((polynomialToL2 μ hμ).range)ᗮ) :
    let g : (Fin n → ℝ) → ℝ := u
    let μpos : Measure (Fin n → ℝ) := μ.withDensity fun x => ENNReal.ofReal (g x)
    let μneg : Measure (Fin n → ℝ) := μ.withDensity fun x => ENNReal.ofReal (-g x)
    μpos = μneg := by
  dsimp
  let g : (Fin n → ℝ) → ℝ := u
  have hg_memLp : MemLp g 2 μ := Lp.memLp u
  have hpos_memLp : MemLp (fun x => max (g x) 0) 2 μ := hg_memLp.pos_part
  have hneg_memLp : MemLp (fun x => max (-g x) 0) 2 μ := hg_memLp.neg_part
  have hg_int : Integrable g μ := MemLp.integrable (by norm_num) hg_memLp
  have hneg_int : Integrable (-g) μ := MemLp.integrable (by norm_num) hg_memLp.neg
  let μpos : Measure (Fin n → ℝ) := μ.withDensity fun x => ENNReal.ofReal (g x)
  let μneg : Measure (Fin n → ℝ) := μ.withDensity fun x => ENNReal.ofReal (-g x)
  haveI : IsFiniteMeasure μpos := isFiniteMeasure_withDensity_ofReal hg_int.hasFiniteIntegral
  haveI : IsFiniteMeasure μneg := isFiniteMeasure_withDensity_ofReal hneg_int.hasFiniteIntegral
  have hmom_zero : ∀ (L : StrongDual ℝ (Fin n → ℝ)) (k : ℕ),
      ∫ x, g x * (L x) ^ k ∂μ = 0 := by
    intro L k
    let p : MvPolynomial (Fin n) ℝ := (linearFunctionalPolynomial L) ^ k
    have hp_mem : polynomialToL2 μ hμ p ∈ (polynomialToL2 μ hμ).range := by
      exact ⟨p, rfl⟩
    have hinner := (Submodule.mem_orthogonal' (polynomialToL2 μ hμ).range u).1 hu _ hp_mem
    rw [MeasureTheory.L2.inner_def] at hinner
    have hp_eval_mem : MemLp (fun x : Fin n → ℝ => MvPolynomial.eval (fun i => x i) p) 2 μ :=
      MvPolynomial_eval_memLp_two_of_subGaussian μ hμ p
    have hrewrite :
        (∫ a, inner ℝ (u a) ((polynomialToL2 μ hμ p) a) ∂μ)
          = ∫ a, inner ℝ (u a) (MvPolynomial.eval (fun i => a i) p) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp hp_eval_mem] with x hx
      simp [polynomialToL2, hx]
    rw [hrewrite] at hinner
    convert hinner using 1
    congr with x
    simp [p, linearFunctionalPolynomial_eval]
    change u x * L x ^ k = L x ^ k * u x
    ring
  have hchar : ∀ L : StrongDual ℝ (Fin n → ℝ), charFunDual μpos L = charFunDual μneg L := by
    intro L
    have hL_aemeas_pos : AEMeasurable L μpos := Measurable.aemeasurable (by fun_prop)
    have hL_aemeas_neg : AEMeasurable L μneg := Measurable.aemeasurable (by fun_prop)
    have hset_pos : ProbabilityTheory.integrableExpSet id (μpos.map L) = Set.univ := by
      ext t
      constructor
      · intro _
        simp
      · intro _
        refine (integrable_map_measure
          ((Real.continuous_exp.comp (continuous_const.mul continuous_id')).aestronglyMeasurable)
          hL_aemeas_pos).2 ?_
        rw [integrable_withDensity_iff (by fun_prop) (by simp)]
        simpa [μpos, g, mul_comm] using
          hpos_memLp.integrable_mul (memLp_exp_linear_two_of_subGaussian μ hμ L t)
    have hset_neg : ProbabilityTheory.integrableExpSet id (μneg.map L) = Set.univ := by
      ext t
      constructor
      · intro _
        simp
      · intro _
        refine (integrable_map_measure
          ((Real.continuous_exp.comp (continuous_const.mul continuous_id')).aestronglyMeasurable)
          hL_aemeas_neg).2 ?_
        rw [integrable_withDensity_iff (by fun_prop) (by simp)]
        simpa [μneg, g, mul_comm] using
          hneg_memLp.integrable_mul (memLp_exp_linear_two_of_subGaussian μ hμ L t)
    have hmom : ∀ k : ℕ, ∫ x, x ^ k ∂(μpos.map L) = ∫ x, x ^ k ∂(μneg.map L) := by
      intro k
      rw [integral_map (μ := μpos) hL_aemeas_pos ((continuous_id'.pow k).aestronglyMeasurable),
        integral_map (μ := μneg) hL_aemeas_neg ((continuous_id'.pow k).aestronglyMeasurable)]
      rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
      rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
      simp only [smul_eq_mul]
      have hLpow_mem : MemLp (fun x : Fin n → ℝ => (L x) ^ k) 2 μ := by
        convert MvPolynomial_eval_memLp_two_of_subGaussian μ hμ
          ((linearFunctionalPolynomial L) ^ k) using 1
        ext x
        simp [linearFunctionalPolynomial_eval]
      have hsub :
          ∫ x, (ENNReal.ofReal (g x)).toReal * (L x) ^ k ∂μ
            - ∫ x, (ENNReal.ofReal (-g x)).toReal * (L x) ^ k ∂μ = 0 := by
        change ∫ x, max (g x) 0 * (L x) ^ k ∂μ - ∫ x, max (-g x) 0 * (L x) ^ k ∂μ = 0
        calc
          ∫ x, max (g x) 0 * (L x) ^ k ∂μ - ∫ x, max (-g x) 0 * (L x) ^ k ∂μ
              = ∫ x, (max (g x) 0 * (L x) ^ k - max (-g x) 0 * (L x) ^ k) ∂μ := by
                  symm
                  exact integral_sub' (hpos_memLp.integrable_mul hLpow_mem)
                    (hneg_memLp.integrable_mul hLpow_mem)
          _ = 0 := by
            convert hmom_zero L k using 1
            congr with x
            rw [← sub_mul, max_zero_sub_eq_self]
      exact sub_eq_zero.mp hsub
    have hmgf := complexMGF_eq_of_moments (μpos.map L) (μneg.map L) hset_pos hset_neg hmom
    rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
    rw [← ProbabilityTheory.complexMGF_id_mul_I (μ := μpos.map L) 1,
      ← ProbabilityTheory.complexMGF_id_mul_I (μ := μneg.map L) 1]
    exact congrFun hmgf (1 * Complex.I)
  exact Measure.ext_of_charFunDual (funext hchar)

/-- **Polynomial density in `L²(μ)` for sub-Gaussian probability measures.** -/
theorem polynomial_dense_L2_of_subGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ)
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℝ,
      (∫ x, |f x - MvPolynomial.eval (fun i => x i) p| ^ 2 ∂μ) < ε := by
  let K : Submodule ℝ (Lp ℝ 2 μ) := (polynomialToL2 μ hμ).range
  have hKbot : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    let g : (Fin n → ℝ) → ℝ := u
    let μpos : Measure (Fin n → ℝ) := μ.withDensity fun x => ENNReal.ofReal (g x)
    let μneg : Measure (Fin n → ℝ) := μ.withDensity fun x => ENNReal.ofReal (-g x)
    have hmeas_eq : μpos = μneg := withDensity_pos_eq_neg_of_mem_orthogonal_polynomialToL2 μ hμ hu
    have hdens_eq : (fun x => ENNReal.ofReal (g x)) =ᵐ[μ] fun x => ENNReal.ofReal (-g x) := by
      exact (withDensity_eq_iff_of_sigmaFinite (μ := μ) (by fun_prop) (by fun_prop)).1 hmeas_eq
    have hzero_ae : g =ᵐ[μ] 0 := by
      filter_upwards [hdens_eq] with x hx
      have hmax : max (g x) 0 = max (-g x) 0 := by
        simpa using congrArg ENNReal.toReal hx
      calc
        g x = max (g x) 0 - max (-g x) 0 := by
          symm
          exact max_zero_sub_eq_self (g x)
        _ = 0 := by rw [hmax, sub_self]
    have hu_zero0 : (u : (Fin n → ℝ) → ℝ) =ᵐ[μ] 0 := by
      simpa [g] using hzero_ae
    have hu_zero : (u : (Fin n → ℝ) → ℝ) =ᵐ[μ] ((0 : Lp ℝ 2 μ) : (Fin n → ℝ) → ℝ) :=
      hu_zero0.trans (Lp.coeFn_zero ℝ 2 μ).symm
    exact Lp.ext hu_zero
  have hclosure : K.topologicalClosure = ⊤ :=
    (Submodule.topologicalClosure_eq_top_iff (K := K)).2 hKbot
  have hx : hf.toLp f ∈ K.topologicalClosure := by
    simp [hclosure]
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hx
  obtain ⟨y, hyK, hy⟩ := hx (Real.sqrt ε) (Real.sqrt_pos.2 hε)
  rcases hyK with ⟨p, rfl⟩
  have hp_mem : MemLp (fun x : Fin n → ℝ => MvPolynomial.eval (fun i => x i) p) 2 μ :=
    MvPolynomial_eval_memLp_two_of_subGaussian μ hμ p
  refine ⟨p, ?_⟩
  have hy_norm : ‖hf.toLp f - hp_mem.toLp (fun x : Fin n → ℝ => MvPolynomial.eval (fun i => x i) p)‖
      < Real.sqrt ε := by
    simpa [dist_eq_norm, polynomialToL2] using hy
  have hsub_mem : MemLp (fun x : Fin n → ℝ => f x - MvPolynomial.eval (fun i => x i) p) 2 μ :=
    hf.sub hp_mem
  have hy_sub : ‖hsub_mem.toLp (fun x : Fin n → ℝ => f x - MvPolynomial.eval (fun i => x i) p)‖
      < Real.sqrt ε := by
    have hsub_eq :
        hsub_mem.toLp (fun x : Fin n → ℝ => f x - MvPolynomial.eval (fun i => x i) p)
          = hf.toLp f - hp_mem.toLp (fun x : Fin n → ℝ => MvPolynomial.eval (fun i => x i) p) := by
      simpa using (MemLp.toLp_sub hf hp_mem)
    rw [hsub_eq]
    exact hy_norm
  have hsq :
      ‖hsub_mem.toLp (fun x : Fin n → ℝ => f x - MvPolynomial.eval (fun i => x i) p)‖ ^ 2
        = ∫ x, |f x - MvPolynomial.eval (fun i => x i) p| ^ 2 ∂μ := by
    calc
      ‖hsub_mem.toLp (fun x : Fin n → ℝ => f x - MvPolynomial.eval (fun i => x i) p)‖ ^ 2
          = inner ℝ (hsub_mem.toLp (fun x : Fin n → ℝ => f x - MvPolynomial.eval (fun i => x i) p))
              (hsub_mem.toLp (fun x : Fin n → ℝ => f x - MvPolynomial.eval (fun i => x i) p)) := by
            simp
      _ = ∫ x, inner ℝ
            ((hsub_mem.toLp (fun x : Fin n → ℝ => f x - MvPolynomial.eval (fun i => x i) p)) x)
            ((hsub_mem.toLp (fun x : Fin n → ℝ => f x - MvPolynomial.eval (fun i => x i) p)) x) ∂μ := by
            rw [MeasureTheory.L2.inner_def]
      _ = ∫ x, |f x - MvPolynomial.eval (fun i => x i) p| ^ 2 ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [MemLp.coeFn_toLp hsub_mem] with x hx
            simp [hx]
  have hy_sq :
      ‖hsub_mem.toLp (fun x : Fin n → ℝ => f x - MvPolynomial.eval (fun i => x i) p)‖ ^ 2 < ε := by
    have : ‖hsub_mem.toLp (fun x : Fin n → ℝ => f x - MvPolynomial.eval (fun i => x i) p)‖ ^ 2
        < (Real.sqrt ε) ^ 2 := by
      gcongr
    simpa [Real.sq_sqrt (le_of_lt hε)] using this
  rw [← hsq]
  exact hy_sq

/-- The standard product Gaussian on `Fin n → ℝ` has sub-Gaussian tails.

The proof transports **Fernique's theorem** for the standard Gaussian on
`EuclideanSpace ℝ (Fin n)` (Mathlib's `IsGaussian.exists_integrable_exp_sq`) back
through the measurable equivalence `WithLp.toLp 2 : (Fin n → ℝ) ≃ EuclideanSpace ℝ (Fin n)`,
under which `Measure.pi (fun _ => gaussianReal 0 1)` pushes forward to
`stdGaussian (EuclideanSpace ℝ (Fin n))` (Mathlib's `map_pi_eq_stdGaussian`).
The Euclidean norm satisfies `‖toLp 2 x‖² = ∑ᵢ xᵢ²`
(`EuclideanSpace.real_norm_sq_eq`). -/
lemma isSubGaussianMeasure_pi_gaussianReal (n : ℕ) :
    IsSubGaussianMeasure
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  -- Fernique: ∃ C > 0, Integrable (fun y => exp(C‖y‖²)) (stdGaussian (EuclideanSpace ℝ (Fin n)))
  obtain ⟨C, hC, hI⟩ :=
    IsGaussian.exists_integrable_exp_sq (μ := stdGaussian (EuclideanSpace ℝ (Fin n)))
  refine ⟨C, hC, ?_⟩
  -- Replace stdGaussian by the pushforward of Measure.pi via toLp 2
  rw [← map_pi_eq_stdGaussian (ι := Fin n)] at hI
  -- Pull the integrability back through toLp 2
  rw [integrable_map_measure ?_ ?_] at hI
  · -- hI : Integrable ((fun y => exp(C * ‖y‖²)) ∘ toLp 2) (Measure.pi ...)
    -- Goal:  Integrable (fun x => exp(C * ∑ i, x i ^ 2))   (Measure.pi ...)
    convert hI using 2 with x
    show Real.exp (C * ∑ i, x i ^ 2) = Real.exp (C * ‖(toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2)
    rw [EuclideanSpace.real_norm_sq_eq]
  · -- AEStronglyMeasurable of the integrand on EuclideanSpace
    exact (Real.continuous_exp.comp
      ((continuous_const.mul (continuous_norm.pow 2)))).aestronglyMeasurable
  · -- AEMeasurable of toLp 2
    exact (Measurable.aemeasurable (by fun_prop))

end GaussianHilbert
