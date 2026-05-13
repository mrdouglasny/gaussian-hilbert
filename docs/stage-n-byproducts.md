# Stage N byproducts — what a full `BakryEmerySpace (Fin n → ℝ)` instance buys

*Companion to [`hypercontractivity-discharge-plan.md`](hypercontractivity-discharge-plan.md).*

> **Status note (2026-05-12)**: the byproducts listed below assume the
> *generic* `BakryEmerySpace.pi` tensorization lemma. As of the Stage N
> pivot (see `markov-semigroups/docs/stage-n-detailed-plan.md`), we are
> shipping only the **concrete** `stdGaussianFin.bakryEmerySpace n`
> instance for now, because building the generic version requires first
> refactoring the `BakryEmerySpace` class to expose either a kernel
> mixin or a tensor-product structure (~2-3 weeks of class refactor,
> separate project). The concrete instance still gives the LSI / HC /
> Gaussian-concentration byproducts at the n-Gaussian level; the
> "generic across all BE spaces" reusability is deferred until the
> abstraction refactor lands.
>
> When that refactor happens, gaussian-field's existing
> `NuclearTensorProduct` infrastructure
> (`~/Documents/GitHub/gaussian-field/GaussianField/Nuclear/`) is the
> natural design starting point for the tensor-product flavor of the
> redesign.

Stage N is the alternative to Stage W's LSI-tensorization shortcut: instead
of postulating tensorization + 1D Gaussian LSI as textbook axioms and
deriving `stdGaussianFin_satisfiesLogSobolev` algebraically, Stage N
builds a full `BakryEmerySpace (Fin n → ℝ)` instance with curvature
ρ = 1 from the multivariate Ornstein-Uhlenbeck semigroup. Both routes
produce the same immediate hypercontractivity result. This doc is about
what *else* falls out of Stage N — the byproducts that justify (or
don't) its extra ~1 week of work.

---

## The instance itself

```
instance stdGaussianFin.bakryEmerySpace (n : ℕ) :
    BakryEmerySpace (Fin n → ℝ) 1 :=
  ⟨ /- 16 fields -/ ⟩
```

A `BakryEmerySpace X ρ` instance bundles a Markov diffusion semigroup
`P_t` on `X` with a `carré du champ` operator `Γ` and an `iterated
carré` `Γ₂`, satisfying the **curvature-dimension condition**
`CD(ρ, ∞)`: `Γ₂(f) ≥ ρ · Γ(f)` pointwise. For Gaussian measures with
the OU semigroup, ρ = 1.

The 16 fields decompose into four clusters:

1. **Semigroup data** (4 fields): `P_t`, semigroup law, strong continuity,
   `P_0 = id`. These come directly from `ouSemigroupAct` after the
   Mehler-spectral agreement (Stage Ag, ✅ done).
2. **Generator data** (4 fields): infinitesimal generator `L`, domain,
   `(P_t f - f)/t → L f` in `L²`, self-adjointness of `L` on a core.
   For the multivariate OU generator `L = Δ − x · ∇`, these follow from
   `ouSemigroupAct_eq_smul_of_mem_wienerChaos` plus standard spectral
   calculus.
3. **Carré du champ** (4 fields): `Γ(f, g) = ½(L(fg) − f·Lg − g·Lf)`,
   bilinearity, positivity, integration-by-parts. For OU on Gaussians,
   `Γ(f, g) = ∇f · ∇g`, which is essentially `MeasureTheory.LineDeriv`
   pulled into the multivariate inner product.
4. **Curvature-dimension** (4 fields): the `CD(1, ∞)` inequality, plus
   `Γ`-derivative-commutation along `P_t`, plus the gradient-decay
   estimate `Γ(P_t f) ≤ e^{-2t} P_t(Γ f)`, plus integrability of
   `Γ(P_t f)` under stationary measure. The load-bearing piece is the
   **Mehler-derivative commutation lemma** (see below).

---

## The Mehler-derivative commutation lemma

The technical core of Stage N:

```
∂_i (M_t f)(x) = e^{-t} · M_t (∂_i f)(x)
```

where `M_t` is the Mehler operator on `L²(γ_n)` and `∂_i` is partial
derivative in coordinate `i`. Proof: differentiate

```
(M_t f)(x) = ∫ f(e^{-t} x + √(1−e^{-2t}) y) dγ_n(y)
```

under the Gaussian integral via DCT, using polynomial growth of `f` and
the Gaussian tail of `γ_n`. The factor `e^{-t}` comes from the chain
rule on the `e^{-t} x` term; the integral against the shifted argument
re-assembles as `M_t (∂_i f)`.

This lemma is independently reusable:

- **OU gradient-decay**: combined with Cauchy-Schwarz,
  `|∇(M_t f)|² ≤ e^{-2t} M_t(|∇f|²)`, which is the `Γ`-decay field of
  the BE instance. This is also the *direct* hypercontractivity input
  in Bakry-Émery's original proof (BGL §5.5).
- **Spectral resolution**: re-derives `ouSemigroupAct_eq_smul_of_mem_wienerChaos`
  pointwise rather than spectrally, useful when needing the explicit
  Mehler integrand.
- **Multivariate Stein identity**: `∫ x_i f dγ_n = ∫ ∂_i f dγ_n` falls
  out by `M_t`-asymptotics, giving Stein's method on `γ_n`.

---

## The tensor-lift machinery (Fubini)

To get the multivariate BE instance from 1D, Stage N builds a generic
"BE tensorizes over independent products" lemma:

```
theorem BakryEmerySpace.pi {ι : Type*} [Fintype ι]
    {X : ι → Type*} (μ : ∀ i, Measure (X i))
    [∀ i, BakryEmerySpace (X i) ρ] :
    BakryEmerySpace (∀ i, X i) ρ
```

The proof is field-by-field Fubini: the product semigroup is
`(P_t f)(x) = ∫ ... ∫ f(P_t^{(1)} x_1, ..., P_t^{(n)} x_n) ∏ dμ_i`, and
each BE field tensorizes with the same ρ because `Γ`, `Γ₂`, and
curvature are all coordinate-additive.

This lemma is independently reusable — once it lands, **any** product
of BE spaces gets a BE instance with the minimum ρ, automatically.
Examples we'd use it for:

- **Lattice Gaussian fields**: `Configuration` types in the
  pphi2/gaussian-field stack are `Fin N → Fin N → ℝ`-shaped products
  of Gaussian factors; a BE instance descends from `BakryEmerySpace.pi`.
- **Multi-time OU processes**: needed if pphi2's path-space
  formulation evolves to use BE.

---

## Direct corollaries of the BE instance

Once `stdGaussianFin.bakryEmerySpace n` exists, these follow without
further axioms via existing `BakryEmerySpace` theorems in
markov-semigroups (or via their Mathlib analogues if upstreamed):

### 1. Log-Sobolev inequality (the immediate goal)

```
theorem stdGaussianFin_logSobolev (n : ℕ) (f : Lp ℝ 2 (stdGaussianFin n)) :
    ent_{γ_n}(f²) ≤ 2 · ∫ |∇f|² dγ_n
```

Direct from `BakryEmerySpace.satisfiesLogSobolev` with ρ = 1.

### 2. Hypercontractivity (Stage E wire-in)

```
theorem stdGaussian_hypercontractive (n : ℕ) (p : ℝ) (hp : 2 ≤ p)
    (t : ℝ) (ht : 0 ≤ t) (h_nelson : p − 1 ≤ exp(2t))
    (f : Lp ℝ 2 (stdGaussianFin n)) :
    ‖M_t f‖_{L^p(γ_n)} ≤ ‖f‖_{L^2(γ_n)}
```

Via `gross_lsi_implies_hypercontractive` applied to the OU semigroup
with LSI constant 1. This is the discharge of
`ouSemigroupAct_eLpNorm_hypercontractive`.

### 3. Poincaré inequality (spectral gap)

```
theorem stdGaussianFin_poincare (n : ℕ) (f : Lp ℝ 2 (stdGaussianFin n)) :
    Var_{γ_n}(f) ≤ ∫ |∇f|² dγ_n
```

A weaker consequence of LSI (Rothaus 1985; BGL Prop 4.2.5), but
sometimes cleaner to use directly. Optimal constant 1 reflects the
spectral gap of OU.

### 4. Transport-entropy inequality T_2 (Talagrand 1996)

```
theorem stdGaussianFin_T2 (n : ℕ) (ν : Measure (Fin n → ℝ))
    [IsProbabilityMeasure ν] (hν : ν ≪ γ_n) :
    W_2(ν, γ_n)² ≤ 2 · KL(ν ∥ γ_n)
```

Otto-Villani 2000 / Bobkov-Götze 1999: LSI(1) implies T_2 with
constant 2. The Wasserstein distance bounds Gaussian concentration of
Lipschitz functions.

### 5. Gaussian concentration

```
theorem stdGaussianFin_gaussianConcentration (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hf : LipschitzWith K f) (t : ℝ) (ht : 0 ≤ t) :
    γ_n {x | f x − E[f] ≥ t} ≤ exp(−t² / (2 K²))
```

Herbst's argument from LSI(1). The same dimension-free constant 2 that
gives T_2 also gives this concentration — *uniformly in n*, which is
the foundational ingredient for the polynomial-chaos concentration we
already have in the form
`polynomial_chaos_concentration` (currently axiom-load-bearing via
`ouSemigroupAct_eLpNorm_hypercontractive`).

### 6. Isoperimetric inequality (Bobkov 1997)

```
theorem stdGaussianFin_isoperimetric (n : ℕ) (A : Set (Fin n → ℝ)) :
    I(γ_n(A)) ≤ ∫ I(1_A) dγ_n
```

where `I` is the Gaussian isoperimetric profile. Half-spaces are
extremal. Stage N gives this via the BE-implication of the Bobkov
inequality (BGL §8.5.2), which in turn implies LSI but is strictly
stronger.

### 7. Brascamp-Lieb inequality

```
theorem stdGaussianFin_BL (n : ℕ) (f : (Fin n → ℝ) → ℝ) (hf : LogConcave f) :
    Var_γ(f) ≤ E_γ[⟨∇f, H_V^{-1} ∇f⟩]
```

The variance bound under log-concave perturbations of `γ_n`. Used in
gaussian-field's FKG and second-moment analyses; currently
established via FKG inequalities, but Brascamp-Lieb is more general
and cleaner for log-concave perturbations of the free field.

### 8. Sobolev embedding via Gross-Beckner

```
theorem stdGaussianFin_sobolev_2_p (n : ℕ) (p : ℝ) (hp : 2 ≤ p)
    (f : Lp ℝ 2 (stdGaussianFin n)) :
    ‖f − E[f]‖_{L^p} ≤ C(p) · ‖∇f‖_{L^2}
```

Beckner's logarithmic Sobolev with p > 2 (Beckner 1989): tighter than
the trivial `L²` bound, with `C(p) = √(p − 1)`. Stage N gives this for
free via `BakryEmerySpace.beckner` (if upstreamed) or via the standard
BE → Gross-Beckner derivation.

---

## What Stage W *cannot* give without further work

| Result | Stage W | Stage N |
|---|---|---|
| Hypercontractivity (LSI → HC) | ✓ via `gross_lsi_implies_hypercontractive` | ✓ direct |
| Poincaré inequality | ✗ — would need a separate axiom | ✓ direct from CD(1, ∞) |
| T_2 transport-entropy | ✗ — needs Otto-Villani 2000 separately | ✓ from LSI but also via curvature |
| Gaussian concentration (Herbst) | ✓ from LSI | ✓ direct |
| Isoperimetric (Bobkov) | ✗ — Bobkov inequality is strictly stronger than LSI | ✓ accessible from CD(1, ∞) via Bobkov |
| Brascamp-Lieb | ✗ — independent of LSI | ✓ via BE generator analysis |
| Mehler-derivative lemma | not built | ✓ explicit |
| Tensor-lift `BakryEmerySpace.pi` | not built | ✓ generic, reusable |

In other words: Stage W *closes* the immediate hypercontractivity hole
but produces nothing reusable beyond `lsi_tensorize` and the 1D Gaussian
LSI as standalone axioms. Stage N produces a **toolkit** — the BE
instance itself, the Mehler-derivative lemma, and the generic
tensorization machinery — each of which has 3+ downstream consumers
in our existing or planned codebase.

---

## Concrete downstream consumers (across our projects)

For each Stage N byproduct, where else in our stack it would be used:

### `stdGaussianFin.bakryEmerySpace` directly

- **gaussian-field**: any LSI / Poincaré / concentration argument
  about the lattice GFF restricts to BE on the coordinate marginals.
  Currently those uses go through ad-hoc Gaussian-specific lemmas;
  Stage N would replace them with one uniform structure.
- **pphi2**: continuum-limit tightness arguments use Gaussian
  concentration on intermediate lattice configurations. Currently
  handled via `gaussian_continuum_concentration` axiom-style; Stage N
  derives it.
- **markov-semigroups** itself: the BE instance is the canonical
  example expected by the abstract `BakryEmerySpace` theory. Having
  it in the library improves documentation and testing.

### Mehler-derivative commutation `∂(M_t f) = e^{-t} M_t(∂f)`

- **gaussian-hilbert**: alternate route to `mehlerOp_eq_smul_of_mem_wienerChaos`
  via direct spatial-derivative computation rather than spectral.
- **markov-semigroups**: the prototype of the abstract `Γ`-decay
  field. Useful for stating and proving the *abstract* gradient
  contraction.
- **OS3 (RP) analyses**: reflection positivity arguments sometimes
  invoke commutation between the time-reflection map and the OU
  semigroup; Stage N's commutation makes this rigorous.

### `BakryEmerySpace.pi` (tensorization lemma)

- **gaussian-field**: lattice configurations are products; this lemma
  is the right way to lift 1D properties.
- **pphi2 lattice action**: any time we approximate the interacting
  measure by a product Gaussian, we need product-level BE properties
  with explicit constants.
- **markov-semigroups**: standard library lemma that should exist
  generically anyway.

### LSI → T_2 → Gaussian concentration chain

- **OS reconstruction**: future arguments about regularity of the
  reconstructed Wightman functional could use T_2.
- **Continuum-limit pphi2**: concentration of the lattice partition
  function around its mean is a Gaussian concentration application,
  currently bounded only by Markov's inequality.

### Brascamp-Lieb

- **gaussian-field FKG cluster**: Brascamp-Lieb generalises FKG to
  log-concave perturbations and is the cleaner stament for second-moment
  estimates of `e^{−V} dγ` with `V` convex.
- **pphi2 interacting measure**: the `e^{−λ φ⁴}` perturbation of the
  GFF is *not* log-concave on `φ`, so Brascamp-Lieb doesn't apply
  directly there, but it *does* apply to the relevant quadratic-Gaussian
  decompositions used in cluster expansions.

---

## Caveats

- **Currently zero direct consumers**. As of 2026-05-11, the only
  *load-bearing* use of any of these byproducts is hypercontractivity
  (via `ouSemigroupAct_eLpNorm_hypercontractive`). Everything in the
  table above is potential future use. If pphi2 closes its current OS
  axioms via other routes, the BE instance sits unused.
- **Markov-semigroups axiom layer is shared**. Whether we go Stage W
  or Stage N, the 2 Gross axioms (`gross_lsi_implies_hypercontractive`
  + the LSI → HC implication) in markov-semigroups stay. Stage N adds
  no new axioms but doesn't retire existing ones.
- **Effort-to-payoff is asymmetric**. Stage N's ~1 extra week
  produces ~8 reusable byproducts; if 2-3 of them get used, it pays
  off. If none get used in the next 6 months, Stage W was the right
  call.
- **The Mehler-derivative lemma alone is independently valuable**
  (~150-200 lines). It could be extracted from Stage N's 600-line
  total and proved as a standalone helper even under Stage W.

---

## Recommendation framing

**Stage N pays off if:**
- We expect to use Gaussian concentration / Poincaré / Brascamp-Lieb /
  T_2 in pphi2 continuum-limit work within the next 3-6 months.
- We want markov-semigroups to be a usable, well-stocked library for
  future projects (e.g. lattice gauge theory, OS reconstruction).
- We value 0-new-axioms over ~1 week of saved time.

**Stage W is the right call if:**
- Hypercontractivity is purely a means to discharge the existing
  `polynomial_chaos_concentration` chain, with no further BE
  consumers planned.
- We're optimizing for closing the gaussian-hilbert axiom list
  quickly to free up bandwidth for other repos.
- We can re-do Stage N later, in isolation, if the byproducts turn
  out to be needed.

The decision boils down to **how confidently we project further BE
consumers**. Without a concrete plan to use 2-3 of the byproducts
above, Stage W is the rational shortcut.
