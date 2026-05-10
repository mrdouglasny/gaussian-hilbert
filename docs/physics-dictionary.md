# Physics ↔ Math dictionary: Feynman diagrams and Gaussian Hilbert spaces

*A translation guide between the physics methodology of Feynman diagrams
and the Janson "Gaussian Hilbert space" framework formalized in this
repository. Last refreshed 2026-05-10.*

## TL;DR

The Janson "Gaussian Hilbert space" framework is the **measure-theoretic
/ Hilbert-space version of free-field Feynman diagrams**. Almost every
physical concept has a one-to-one mathematical counterpart. The two
dialects differ in *what extra structure each emphasizes*, not in the
underlying content. Numerically, every free-field Feynman-diagram
calculation can be done as an Isserlis-pairing computation in this
framework, and vice-versa — they are the same theorem in different
notations.

This document spells out the correspondence and notes where each side
develops machinery the other does not.

## Setting

Both sides organize calculations of moments and correlation functions
of polynomials in Gaussian random variables.

- **Physics:** correlation functions `⟨φ(x₁) φ(x₂) … φ(xₙ)⟩` in a free
  scalar field theory; "interacting" extensions via the Dyson series
  `e^{-V}` and perturbative expansion.
- **Math:** integrals `∫ p(X) dγ(X)` for polynomial `p` against a
  Gaussian measure `γ` (typically `γ_n` on `Fin n → ℝ` in
  `gaussian-hilbert`'s finite-dim setting).

The free field `φ(x)` becomes the random variable `⟨φ, f⟩` for a test
function `f` (a Gaussian RV with covariance `⟨f, G f⟩` where `G` is the
free propagator). Polynomials in field values become polynomials in
finitely many such Gaussian RVs — exactly the setting of the chaos
decomposition.

## The dictionary

| Physics (Feynman / QFT) | Math (Janson / `gaussian-hilbert`) | Where in the repo |
|---|---|---|
| Wick's theorem: `⟨φ(x₁)·…·φ(x_{2n})⟩ = ∑_{pairings} ∏ ⟨φ(x_i)φ(x_j)⟩` | **Isserlis's theorem** (same identity, no pictures) | follows from `hermiteMulti_orthogonality` + chaos algebra; explicit Isserlis statement is a planned Mathlib upstream (TODO Cluster VI) |
| Normal-ordering `:φ(x)ⁿ:` | **Wick monomial** = scaled probabilist's Hermite polynomial | `wick_eq_hermiteR` (gaussian-field's `SchwartzNuclear/HermiteWick.lean`); `hermiteMultiEval` (this repo, `HermitePolynomials.lean`) |
| Free propagator `G(x,y) = ⟨φ(x)φ(y)⟩` | Covariance kernel of the Gaussian measure (the "lines" of a Feynman graph) | gaussian-field's `IsGaussian` infrastructure |
| `n`-particle Fock subspace `Hₙ` | The `n`-th **Wiener chaos** `H^{:n:}` | `wienerChaos n k` (`WienerChaos.lean`) |
| Fock-space orthogonal decomposition `F = ⊕ Hₙ` | `wienerChaos_isHilbertSum : L²(γ) = ⊕̂ₙ Hₙ` | `wienerChaos_isHilbertSum` (`WienerChaos.lean`, **proved**) |
| Free Hamiltonian `H_free`, eigenstate `\|α⟩` of energy `\|α\|` | OU generator `L = Δ - x·∇`, eigenfunction `H_α` of eigenvalue `−\|α\|` | `ouGenerator_hermiteMultiEval` (`OUEigenfunctions.lean`, **proved**) |
| Heisenberg evolution `e^{−tH_free}\|α⟩ = e^{−\|α\|t}\|α⟩` | OU semigroup `T_t H_α = e^{−\|α\|t} H_α` | `ouSemigroupAct_eq_smul_of_mem_wienerChaos` (`OUEigenfunctions.lean`, currently **placeholder axiom**) |
| Feynman diagram with `n` external legs / various loop topologies | An element of `⊕_{k ≤ d} Hₖ` — a polynomial in the field of total degree ≤ `d` | `wienerChaosLE n d` |
| Sum over Feynman diagrams for `⟨A·B⟩` | Inner product `⟨A, B⟩_{L²(γ)}` of two chaos elements | the pairings drop out because L² inner product is computed directly via chaos orthogonality + Isserlis |
| Dyson expansion `e^{−V} = ∑ (−V)ⁿ/n!`, then Wick contract each term | Multivariate polynomial expansion + Isserlis | **same calculation**; physics draws diagrams, math evaluates `MvPolynomial.eval` and uses Hermite orthogonality |
| "Tadpole / vacuum diagrams vanish for normal-ordered `:V:`" | Wick subtraction projects to chaos pieces of degree `≥ 1`, killing the constant (vacuum) contribution | follows from chaos orthogonality + `hermiteMultiEval (0 : Fin n → ℕ) = 1` |
| Bonami-Beckner-Nelson hypercontractive bound on the OU semigroup | `‖T_t f‖_{L^p} ≤ ‖f‖_{L^q}` for `e^{2t}(p−1) ≥ q−1` | `ouSemigroupAct_eLpNorm_hypercontractive` (currently **placeholder axiom**); the discharge plan derives it from markov-semigroups `gross_lsi_implies_hypercontractive` + Bakry-Émery curvature 1 |
| "Polynomial-degree-`d` observable has at most `(\|F\|_2)^{2/d}` characteristic deviations" | Janson Theorem 5.10 polynomial-chaos concentration: `P(\|F\| > λ‖F‖₂) ≤ 2 exp(−c_d λ^{2/d})` | `polynomial_chaos_concentration` (`PolynomialChaosConcentration.lean`, **proved**) |

## Where each side develops machinery the other doesn't

### Physics has, this repo doesn't (yet)

- **Connected / 1PI / amputated diagrams.** Combinatorial sub-classes
  of Feynman graphs that organize perturbation theory by topology
  (cumulants, vertex functions, effective action). The math has all
  the algebraic tools to define these (logarithm of the generating
  functional ⇒ connected; Legendre transform ⇒ 1PI), but they're
  rarely the focus in measure-theoretic textbooks.
- **Renormalization** (BPHZ, Hopf algebra of graphs, Kreimer-Connes).
  The math equivalent is careful handling of UV-divergent operator
  products via higher-order Wick subtractions; this exists in
  constructive QFT (Glimm-Jaffe, Fröhlich-Spencer, Brydges-Federbush)
  but is not in the Janson core.
- **Diagrammatic intuition** for setting up calculations and spotting
  cancellations (gauge invariance, Ward identities, BRST, etc.).

### This repo has, physics doesn't develop systematically

- **Hypercontractivity** as an L^p ↔ L^q norm inequality.
  Physicists use the consequences (Nelson's bound on integrability of
  `e^{−V}` for `P(φ)₂`) but rarely state the inequality in this form.
- **Sharp polynomial-chaos concentration** (Janson Thm 5.10): tail
  bounds of the form `P(\|F\| > λ‖F‖₂) ≤ 2 exp(−c_d λ^{2/d})`. The
  math here is much sharper than the typical physics estimate of "the
  relevant integral is bounded by the diagrammatic estimate".
- **Moment-problem determinacy.** When does knowing all moments
  determine the measure? Sub-Gaussian + Carleman's condition is
  sufficient; weaker hypotheses (second moment alone) don't suffice
  (Stieltjes-style indeterminate examples). Physicists implicitly
  assume "reconstruction from moments" works; the math states the
  precise hypothesis. Captured here in
  `polynomial_dense_L2_of_subGaussian`.
- **Functional-analytic spectral structure** of OU as an unbounded
  self-adjoint generator on `L²(γ)`. Physicists know the spectrum is
  `ℕ` but rarely care about the operator-theoretic packaging.

## The fundamental agreement

> Every Feynman-diagram calculation for a free-field correlation
> function can be done as an Isserlis-pairing computation in
> `gaussian-hilbert`-style notation, and vice-versa. They produce the
> same numbers because they are the same theorem.

The differences are *about which extra structure each side organizes
around*:

- A physicist would say "draw the diagram, apply Feynman rules,
  integrate" — graph-theoretic bookkeeping.
- A mathematician working in Janson's framework would say "expand in
  chaos, use orthogonality, apply hypercontractivity if needed" —
  Hilbert-space bookkeeping.

For *interacting* QFT (Dyson series, renormalization), the physics
methodology is more developed; the math methodology has rigorous
functional-inequality bounds that the physics methodology often
assumes implicitly. In rigorous constructive QFT, both methodologies
are used together — exactly because they're the same content viewed
from complementary angles.

## What `gaussian-hilbert` provides for the physics user

Right now this repository captures:

- **Free-field "Wick algebra" in finite dimensions** — full content of
  physics's free-field perturbation theory, except the diagrammatic
  combinatorics aren't drawn out.
- **Free-field "Fock space spectral decomposition"** —
  `wienerChaos_isHilbertSum` (proved).
- **Free-field "OU dynamics"** = imaginary-time Schrödinger evolution
  with `H_free` — `ouGenerator_hermiteMultiEval` (proved) +
  `ouSemigroupAct` (currently placeholder, see
  [`ou-mehler-discharge-plan.md`](ou-mehler-discharge-plan.md)).
- **Hypercontractive bound** — exactly Nelson's bound used in the
  Glimm-Jaffe proof of `P(φ)₂` existence (currently placeholder; same
  discharge plan).
- **Polynomial-chaos concentration** (Janson Thm 5.10) — used in the
  lattice-side Nelson estimate that pphi2's `FieldDecomposition`
  consumes.

What is **not** here (and physics relies on for actual interacting
computations) is in [`TODO.md`](../TODO.md) clusters II–V:

- Explicit multiple Wiener integrals `I_k(f)` and the Wick / Isserlis
  diagram formulae for products `I_{k₁}(f₁) · I_{k₂}(f₂)` (Cluster
  II).
- Connected-diagram / cumulant generating functional `log Z` (Cluster
  II is the natural place; not yet started).
- Renormalized perturbation theory; BPHZ; the Hopf algebra of graphs
  (out of scope for Janson, would require a separate library).
- Stein-Malliavin and the fourth-moment theorem (Cluster III) — the
  modern probabilistic refinement of "Wick's theorem ⇒ CLT".

## References

- S. Janson, *Gaussian Hilbert Spaces*, Cambridge Tracts in
  Mathematics 129, Cambridge University Press (1997). The canonical
  math-side reference; chapter contents map directly onto this repo's
  files.
- L. Isserlis, "On a formula for the product-moment coefficient of any
  order of a normal frequency distribution in any number of
  variables", *Biometrika* 12 (1918), 134–139. (Wick's theorem before
  Wick.)
- G.C. Wick, "The evaluation of the collision matrix", *Phys. Rev.* 80
  (1950), 268–272.
- J. Glimm, A. Jaffe, *Quantum Physics: A Functional Integral Point of
  View*, Springer (1987). Bridges the two perspectives in constructive
  QFT.
- D. Bakry, I. Gentil, M. Ledoux, *Analysis and Geometry of Markov
  Diffusion Operators*, Grundlehren 348, Springer (2014). The
  functional-inequality / OU-semigroup side.
- I. Nourdin, G. Peccati, *Normal Approximations with Malliavin
  Calculus*, Cambridge Tracts in Mathematics 192 (2012). The
  Stein-Malliavin refinement of Wick / Isserlis.
- P. Cvitanović, *Field Theory*, Nordita Lecture Notes (1983); D.
  Kreimer, "On the Hopf algebra structure of perturbative quantum
  field theories", *Adv. Theor. Math. Phys.* 2 (1998), 303–334. The
  diagrammatic / combinatorial physics side.
