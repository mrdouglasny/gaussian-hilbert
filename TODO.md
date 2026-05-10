# gaussian-hilbert TODO

Forward-looking development directions, organised roughly along the
chapter structure of Janson's *Gaussian Hilbert Spaces*. Initial seed
covers Ch. 2-3 + Ch. 5 (Theorem 5.10); the items below extend that
coverage chapter by chapter and outline several adjacent applications.

Status legend: ☐ not started · ◐ partially seeded · ✓ done.

## Cluster I — finishing the initial seed

### ☐ Discharge the OU/Mehler placeholder axioms

The three `ouSemigroupAct*` axioms in `OUEigenfunctions.lean` are
load-bearing for `polynomial_chaos_concentration`. Discharge plan
([`docs/ou-mehler-discharge-plan.md`](docs/ou-mehler-discharge-plan.md))
sketches a five-stage Mehler-kernel + Bakry-Émery + Gross route:

- **Stage A:** define `mehlerOp n t` as a CLM on `Lp ℝ 2 (stdGaussianFin n)`
  via the explicit Mehler integral. ~250 lines.
- **Stage B:** semigroup identity `M_s ∘ M_t = M_{s+t}`. ~200 lines.
- **Stage C′:** 1D Mehler-Hermite identity `∫ He_k(e^{-t}x + √(1-e^{-2t})y) dγ(y) = e^{-kt} He_k(x)` via the Hermite generating function;
  multivariate version by tensor product. ~250 lines.
- **Stage C:** multivariate `BakryEmerySpace` instance lifting
  markov-semigroups' 1D Gaussian instance. ~600 lines.
- **Stage E:** wire hypercontractivity through `gross_lsi_implies_hypercontractive`.
  ~50 lines.

After Stages A+B+C′ alone, two of the three OU placeholder axioms are
discharged. Stage C/E (which gives the third) requires the abstract
Bakry-Émery framework from markov-semigroups.

Total: ~3-4 weeks. After this, the polynomial-chaos pipeline rests only
on the gaussian-field analytic axiom + the four 1D BGL axioms in
markov-semigroups + Gross 1975 (also currently axiomatized in
markov-semigroups).

### ☐ Vet `polynomial_dense_L2_of_subGaussian` with Gemini deep-think

Currently marked `(NOT VERIFIED)` in source. Get the DT pass on (a)
hypothesis sufficiency, (b) `Cc`-density vs Schwartz-density choice,
(c) measurability prerequisites. ~1 hour, closes the most load-bearing
external-axiom loop.

## Cluster II — Janson Ch. 4-7 (deeper OU + chaos calculus)

### ☐ Cameron-Martin theory (Ch. 8)

The unitary `T : L²(γ) → L²(dx)` defined by `Tf := f · √ρ` (where `ρ`
is the Gaussian density) carries Hermite polynomials into Hermite
*functions*. Provides the bridge between the "polynomial" Gaussian
Hilbert space picture and the "Schwartz / spectral" Hermite-function
picture (the latter already in
[gaussian-field](https://github.com/mrdouglasny/gaussian-field)'s
`SchwartzNuclear/HermiteHilbertBasis.lean`). Useful for several
follow-on directions (Mehler kernel as integral operator on `L²(dx)`,
density theorems via the Hermite-function HilbertBasis).

Estimated effort: ~1-2 weeks.

### ☐ Multiple Wiener integrals on a finite-dim Gaussian space (Ch. 7)

`I_k(f)` for symmetric `f : (ℝⁿ)^k → ℝ` square-integrable. On the
finite-dim Gaussian Hilbert space, `I_k` is just a polynomial functional
of degree `k`; the construction makes the chaos decomposition
`L²(γ_n) = ⊕_k 𝓗_k` more explicit and gives the contraction-based
formulae for products of multiple integrals (`I_k(f) · I_m(g)` as a sum
of `I_{k+m-2r}` terms). Foundational for Cluster III (Stein-Malliavin).

Estimated effort: ~2 weeks.

### ☐ Diagram formulae for products of Wiener chaos elements (Ch. 7)

The combinatorial Wick / Feynman-diagram expansion for
`E[I_{k₁}(f₁) · I_{k₂}(f₂) · … · I_{k_n}(f_n)]` as a sum over complete
pairings (the *Wick* / *Isserlis* theorem). Gives the random-matrix
`GUE` second-moment formulae as a corollary.

Estimated effort: ~1-2 weeks.

### ☐ Hilbert-space-valued (vector) Wiener chaos (Ch. 11)

Generalize `wienerChaos n k` to take values in an arbitrary separable
Hilbert space `E`. Needed for Stein's method on Hilbert-valued
functionals and for some random-matrix applications.

Estimated effort: ~1 week.

## Cluster III — Stein-Malliavin / fourth-moment theorem

### ☐ Stein's method on a Gaussian Hilbert space (Nourdin-Peccati Ch. 5)

The Stein equation `f' - x f = h - E_γ h` on a 1D Gaussian, lifted to
multivariate / chaos-element settings via the Malliavin operators
(divergence `δ`, Malliavin derivative `D`). On a finite-dim Gaussian
Hilbert space, both are concrete polynomial operators on the chaos
decomposition. Goal: the **Stein bound**
`d_{TV}(I_k(f), N(0, k! ‖f‖²)) ≤ √( (E[I_k(f)⁴] / (3 (E[I_k(f)²])²)) - 1 )`.

Estimated effort: ~2-3 weeks (after Cluster II's multiple integrals).

### ☐ Fourth-moment theorem (Nualart-Peccati 2005)

A normalised sequence in the `k`-th Wiener chaos converges in
distribution to `N(0, 1)` iff its fourth moments converge to `3`. One
of the cleanest CLT-type results in modern probability. Builds on
Stein-Malliavin.

Estimated effort: ~1-2 weeks (after the Stein bound).

## Cluster IV — concentration-of-measure refinements

### ☐ Sharp constants in Bonami-Beckner (Ch. 5)

Replace the `(d+1) · (p-1)^{d/2}` factor in `bonami_nelson_chaosLE`
with the sharp `√(d+1) · (p-1)^{d/2}`. Janson Thm 5.10 is sharp; the
weaker constant in our seed is for tactical convenience.

Estimated effort: 3-5 days.

### ☐ Latala-style polynomial concentration

Latala's refinement of Janson 5.10 gives optimal tail constants in
terms of mixed `L^p`-norms of the polynomial's coefficient tensors.
Sharp at every chaos level for symmetric tensors.

References: R. Latala, *Estimates of moments and tails of Gaussian
chaoses*, Ann. Probab. 34 (2006), 2315-2331.

Estimated effort: ~3 weeks.

### ☐ Adamczak-Latala two-sided bounds for chaos

Two-sided sharp bounds (matching `c_d λ^{2/d}` upper *and* lower) for
fixed-order chaos elements. The current pipeline only proves the upper
bound.

Estimated effort: ~2 weeks (substantial new material).

## Cluster V — applications and connections

### ☐ Random-matrix applications

The GUE second-moment / Wick algebra connection. `Tr(M^k)` for a `GUE`
matrix `M` is a polynomial in the matrix entries, hence a chaos
element; the moment formulae fall out of Cluster II's diagram
expansion. Combined with Cluster IV's hypercontractivity, gives
concentration of `Tr(M^k)` around its mean.

Estimated effort: ~1-2 weeks (after Cluster II).

### ☐ Connection to `markov-semigroups`' Bakry-Émery framework

Construct the OU `BakryEmerySpace (Fin n → ℝ)` instance from this
side, exporting it back to markov-semigroups (or as a separate
`gaussian-hilbert/BakryEmery.lean` module). Lets markov-semigroups'
abstract concentration / variance theorems specialize to the standard
Gaussian without needing the Mehler kernel re-derivation.

Estimated effort: 1-2 weeks (after the OU/Mehler discharge in
Cluster I).

### ☐ Free probability deformation (q-Wick algebra)

The `q`-Wick / `q`-Hermite polynomials interpolate between bosonic
(`q = 1`, ours), fermionic (`q = -1`), and free probability (`q = 0`).
Janson Ch. 16 covers the `q = 1` case fully; the `q = 0` (free
probability) case is the natural Lean follow-on. Gets you free
hypercontractivity (Biane), the free CLT, etc.

Estimated effort: ~2-3 months (a full deformation programme).

### ☐ Brownian functionals

Bridge to [brownian-motion](https://github.com/mrdouglasny/brownian-motion):
expand a Brownian functional in the multiple-integral chaos basis
(Wiener-Itô expansion). The infinite-dim case is the heaviest item on
this list; the finite-dim restriction (functionals of `B_{t₁}, …, B_{t_n}`
for fixed times) reduces to multivariate Hermite expansion and is
already covered by our seed.

Full infinite-dim Wiener-Itô integral: ~6+ months.

## Cluster VI — Mathlib upstreaming

The cleaner pieces of this library should eventually go to Mathlib:

### ☐ `Polynomial.hermite_orthogonality` (1D version)

Mathlib has `Polynomial.hermite n` (probabilist's Hermite) and the
Rodrigues-formula interplay (`hermite_eq_deriv_gaussian`) but **no
direct Hermite orthogonality theorem** `∫ He_n He_m dγ = δ_{nm} · n!`.
This is one of the most basic consequences of the Rodrigues formula
(`n`-fold integration by parts on `He_n · He_m · ρ`). Currently we
route through gaussian-field's `wickMonomial_inner_gaussianReal_one`;
upstreaming the direct theorem to Mathlib would simplify the gaussian-field
side too.

### ☐ Multivariate Hermite product orthogonality

Once 1D is upstreamed, the multivariate version
`∫ H_α H_β dγ_n = δ_{αβ} · ∏ αᵢ!` is a 5-line Fubini consequence.

### ☐ Polynomial L²-density for sub-Gaussian probability measures

Currently the `polynomial_dense_L2_of_subGaussian` axiom (Janson Thm 2.6).
The textbook proof is `Cc` density + Stone-Weierstrass on each ball +
sub-Gaussian tail control of polynomial growth — all standard, ~250 lines.
A natural Mathlib contribution that benefits the moment-problem and
characteristic-function communities.

### ☐ Multivariate Wick polynomials

The Wick / normal-ordering construction and the multinomial expansion
`:(∑ γⱼ ξⱼ)^k:_c` already proved generically in
[gaussian-field](https://github.com/mrdouglasny/gaussian-field)'s
`SchwartzNuclear/HermiteWick.lean` over arbitrary `Fintype` index sets.
Could be upstreamed to Mathlib's polynomial / measure-theory libraries.
