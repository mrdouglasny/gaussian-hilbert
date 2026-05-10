# gaussian-hilbert

## Topic

A *Gaussian Hilbert space* is a closed linear subspace `H ⊆ L²(Ω, μ)`
of a probability space's L² such that **every element of `H` is a
centered Gaussian random variable**. The structural fact that drives the
theory is that for jointly Gaussian variables, "orthogonal in L²" is
equivalent to "independent" — a property of Gaussians and only
Gaussians. Orthogonal subspaces correspond to independent algebras, and
the *Wiener chaos* decomposition into orthogonal pieces `H^{:k:}` is a
decomposition into independent levels of polynomial complexity.

This repository formalizes the finite-dimensional Gaussian Hilbert
space theory in Lean 4, following the standard textbook treatment in
Svante Janson's *Gaussian Hilbert Spaces* (Cambridge University Press,
1997). The finite-dim restriction (working with the standard product
Gaussian `γ_n` on `ℝⁿ`) suffices for many concrete applications —
lattice approximations of Euclidean QFT, random-matrix concentration,
finite-particle Stein's method — and avoids the heavier infinite-dim
Malliavin calculus while preserving all the algebraic and spectral
content.

## Initial contents

Four library files and one shared foundational axiom:

| File | Source | Content |
|---|---|---|
| `GaussianHilbert/HermitePolynomials.lean` | imported from `markov-semigroups/MarkovSemigroups/Gaussian/` | Multivariate (probabilist's) Hermite polynomials `H_α(x) = ∏ᵢ He_{αᵢ}(xᵢ)`, orthogonality `∫ H_α H_β dγ_n = δ_{αβ} ∏ᵢ αᵢ!` (proved via Fubini + 1D Wick orthogonality), and L²-density `hermiteMulti_dense` (proved via `MvPolynomial.induction_on` + Hermite three-term recurrence + `Submodule.span` change-of-basis). |
| `GaussianHilbert/WienerChaos.lean` | imported from `markov-semigroups/MarkovSemigroups/Gaussian/` | The `k`-th Wiener chaos `wienerChaos n k` as a closed L² submodule, orthogonal projection `chaosProjection n k`, distinct-chaos orthogonality, full chaos decomposition `wienerChaos_isHilbertSum : IsHilbertSum ℝ (wienerChaos n) ...` (proved from `hermiteMulti_dense`). |
| `GaussianHilbert/OUEigenfunctions.lean` | imported from `markov-semigroups/MarkovSemigroups/Gaussian/` | The Ornstein-Uhlenbeck generator `L = Δ - x·∇` and the eigenfunction theorem `ouGenerator_hermiteMultiEval : L H_α = -|α| H_α` (proved). Three placeholder axioms for the OU semigroup operator `ouSemigroupAct` and its action on chaos pieces (gated on the Mehler-kernel discharge plan; see `docs/`). |
| `GaussianHilbert/PolynomialChaosConcentration.lean` | imported from `markov-semigroups/MarkovSemigroups/Gaussian/` | Bonami-Beckner-Nelson hypercontractive bound `‖f‖_{L^p} ≤ (p-1)^{k/2} ‖f‖_{L²}` on the `k`-th chaos, the analogous bound on `⊕_{k ≤ d} H_k`, and **Janson Theorem 5.10** polynomial-chaos concentration `ℙ(|F| > λ ‖F‖_{L²}) ≤ 2 exp(-c_d λ^{2/d})`. |
| `GaussianHilbert/PolynomialDensity.lean` | imported from `gaussian-field/GeneralResults/PolynomialDensityGaussian.lean` | The textbook density axiom `polynomial_dense_L2_of_subGaussian` (Janson Thm 2.6) plus the proved instance `isSubGaussianMeasure_pi_gaussianReal` (transported from Mathlib's Fernique theorem). |

All four library files are sorry-free as imported. Three OU-action
placeholder axioms remain in `OUEigenfunctions.lean`; a discharge plan
(via Mehler kernel + Bakry-Émery + Gross's hypercontractivity duality)
is committed at `docs/ou-mehler-discharge-plan.md`. Companion roadmap at
`docs/polynomial-chaos-roadmap.md`.

## Sources

**Primary:**
- S. Janson, *Gaussian Hilbert Spaces*, Cambridge Tracts in Mathematics 129, Cambridge University Press (1997).

**Secondary:**
- D. Nualart, *The Malliavin Calculus and Related Topics*, 2nd ed., Springer (2006). §1.1 (Wiener chaos), §1.4 (multiple stochastic integrals on finite-dim Gaussian).
- V.I. Bogachev, *Gaussian Measures*, Mathematical Surveys and Monographs 62, AMS (1998). Ch. 1-2 (Gaussian measure infrastructure), Ch. 5 (Hermite polynomials and Wick algebra).
- D. Bakry, I. Gentil, M. Ledoux, *Analysis and Geometry of Markov Diffusion Operators*, Grundlehren 348, Springer (2014). Ch. 2 (OU semigroup as a Markov diffusion), Ch. 5 (hypercontractivity, Gross's theorem, Bonami-Beckner-Nelson).
- I. Nourdin, G. Peccati, *Normal Approximations with Malliavin Calculus*, Cambridge Tracts in Mathematics 192 (2012). Ch. 2 (Wiener chaos refresher), Ch. 5 (Stein-Malliavin method, fourth-moment theorem).

**Original references for individual results:**
- E. Nelson, "The free Markoff field", *J. Funct. Anal.* 12 (1973), 211-227. (Hypercontractivity for OU.)
- L. Gross, "Logarithmic Sobolev inequalities", *Amer. J. Math.* 97 (1975), 1061-1083. (LSI ↔ hypercontractivity duality.)
- A. Bonami, "Étude des coefficients de Fourier des fonctions de `L^p(G)`", *Ann. Inst. Fourier* 20 (1970), 335-402. (Two-point Bonami inequality, the discrete predecessor.)
- W. Beckner, "Inequalities in Fourier analysis", *Ann. Math.* 102 (1975), 159-182.
- S. Janson, "On hypercontractivity for multipliers on orthogonal polynomials", *Arkiv för matematik* 21 (1983), 97-110. (Theorem 5.10's polynomial-chaos concentration form.)

## Dependencies

```
       Mathlib
          │
   ┌──────┴──────┐
   ▼             ▼
gaussian-field  markov-semigroups
   │             │
   └──────┬──────┘
          ▼
   gaussian-hilbert
          │
          ▼
   pphi2 / pphi2N / future
```

`gaussian-field` provides the foundational Gaussian-measure
infrastructure (Wick algebra, characteristic functional, Schwartz
nuclear structure, the polynomial L²-density axiom).
`markov-semigroups` provides the abstract Bakry-Émery / Dirichlet-form
framework and Gross's LSI ↔ hypercontractivity duality. `gaussian-hilbert`
consumes both: the chaos algebra is built on gaussian-field's Wick
infrastructure; the hypercontractivity discharge plan goes through
markov-semigroups' abstract Gross theorem applied to the OU semigroup
on `(ℝⁿ, γ_n)`.

Neither `gaussian-field` nor `markov-semigroups` depends on the other
or on `gaussian-hilbert`. This three-way separation is deliberate:
downstream consumers of `gaussian-field` (e.g., `OSforGFF`) don't pay
the markov-semigroups build cost; downstream consumers of
`markov-semigroups` (e.g., `lgt` for the Yang-Mills mass gap via
Dobrushin uniqueness) don't pay the gaussian-field build cost; only
projects that genuinely need the chaos / OU concentration material
import `gaussian-hilbert`.

## Status

Repository skeleton + initial seed planned. See [`TODO.md`](TODO.md)
for further development directions motivated by Janson's textbook.
