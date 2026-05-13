# Stage N3 blocker analysis (2026-05-13)

**Status**: codex rescue agent attempted Stage N3 (discharging
`ouSemigroupAct_eLpNorm_hypercontractive`) and bailed at a real
structural blocker without making any code changes. Anti-delegation
guards were honored — no silent axioms, no `sorry`, no false delegation.

## The blocker

The brief asks codex to build a `DirichletMarkovSemigroup (Fin n → ℝ)`
from `stdGaussianFin.bakryEmerySpace n`. The two structures disagree
on the *domain of the semigroup laws*:

- **`BakryEmerySpace`** (in `Diffusion/CarreDuChamp.lean`) states the
  semigroup laws under an explicit `IsCore f` hypothesis, e.g.:

  ```lean
  semigroup_add : ∀ s t f, 0 ≤ s → 0 ≤ t → IsCore f →
      semigroup (s + t) f = semigroup s (semigroup t f)
  semigroup_contraction : ∀ f t, 0 ≤ t → IsCore f →
      ∫ x, (semigroup t f x) ^ 2 ∂μ ≤ ∫ x, (f x) ^ 2 ∂μ
  ```

  The comment at `CarreDuChamp.lean:104` notes that *without* `IsCore`,
  "Lean's `integral`-returns-0 default desyncs the two sides" — i.e.
  for `f` not integrable along the relevant Mehler shifts, both sides
  collapse to the Bochner junk value `0`, and the equation becomes
  vacuous rather than informative.

- **`MarkovSemigroup`** (in `Abstract/Hypercontractivity.lean:76`,
  post-2026-05-13 bundle refactor) states the same laws
  **unconditionally**, with no `IsCore` hypothesis. The `P_l2_contraction`
  uses `eLpNorm` (which returns `⊤` for non-`L²` functions, avoiding
  the Bochner junk-value trap) — but `P_semigroup`, `P_conservation`,
  `P_positivity`, `P_symmetric` are stated for *all* `f : X → ℝ`.

The bridge gap: the upstream multivariate OU semigroup proofs
(`ouSemigroupFin_compose`, `ouSemigroupFin_contraction`,
`ouSemigroupFin_selfAdjoint`) all carry the `IsCoreFin f` hypothesis,
matching the BE-instance discipline. They do NOT cover the
unconditional case the `MarkovSemigroup` structure demands.

Codex confirmed via the Lean LSP that `MeasureTheory.integral_prod`
(the obvious tool for unconditional Fubini upgrades) requires an
`Integrable` hypothesis, so the existing proof path does not admit a
small "drop the IsCore hypothesis" patch. The gap is structural, not
a small lemma.

## What codex did not do (correctly)

- Did **not** modify any files in either repo.
- Did **not** add new axioms.
- Did **not** introduce sorries.
- Did **not** silently work around the gap.
- Reported the gap with file:line evidence and three viable
  resolution paths.

## Resolution options (codex's + one of mine)

**Option 1 (codex, "change the carrier")**: change `MarkovSemigroup`'s
semigroup carrier from `(X → ℝ) → (X → ℝ)` to a space where the
unconditional laws are actually sound (e.g. `Lp ℝ 2 μ → Lp ℝ 2 μ`,
or a quotient by a.e.-equivalence). Substantial upstream refactor;
re-vets the Gross axioms.

**Option 2 (codex, "BE→DMS bridge")**: add an upstream constructor
`DirichletMarkovSemigroup.ofBakryEmerySpace` that bakes in the
measurable/integrable representative semantics. Substantial new
infrastructure in `Abstract/`.

**Option 3 (codex, "relax the bundle")**: relax `MarkovSemigroup` to
carry IsCore-restricted laws like BE does. Smallest refactor in
absolute LOC; requires re-vetting the Gross axioms on the new
weaker statements (and may invalidate the 2026-05-13 Gemini-3.1-pro
vetting that motivated the bundle in the first place — the bundle
was specifically created to be IsCore-free).

**Option 4 (mine, "extra textbook axioms")** — **REJECTED after 3.1-pro
vetting (2026-05-13)**.

I proposed introducing 3-4 unconditional textbook axioms for the
multivariate Gaussian OU semigroup laws. Vetted with gemini-3.1-pro-preview:
verdict was that **the unconditional versions of `P_semigroup` and
`P_symmetric` are mathematically false in Lean** due to Bochner
junk-value behavior with oscillatory signed functions. Specifically:

> "If $f$ is a highly oscillatory signed function that is not
> absolutely integrable under the Mehler measure for $s+t$, then
> $P_{s+t} f$ evaluates exactly to `0` (junk value). However, the
> inner integral for $P_t f(z)$ might conditionally converge to a
> well-defined, rapidly decaying finite value for every $z$ due to
> cancellation. If that resulting function $P_t f$ is absolutely
> integrable under $P_s$, the iterated integral $P_s (P_t f)$ will
> evaluate to a non-zero value. Thus $P_{s+t} f = 0 \ne P_s(P_t f)$,
> and the 'reduces to 0 = 0' Fubini discharge plan mathematically
> collapses."

You also can't "fix" this by artificially truncating $P_t f$ to `0`
for $f \notin L^2$, because that immediately violates `P_zero : ∀ f, P 0 f = f`.

**Implication**: the 2026-05-13 bundle refactor of `Abstract/Hypercontractivity.lean`
that put `MarkovSemigroup` into unconditional-pointwise-functions
shape was itself mathematically flawed. The previous gemini-3.1-pro
vetting that approved it was wrong about Lean integration semantics.

3.1-pro vetted axioms C and D individually (the two with `MemLp` /
`IsCoreFin` hypotheses, which avoid the junk-value trap):

- **Axiom C** (`ouSemigroupFin_eLpNorm_contraction`, with `MemLp f 2`
  hypothesis, using `eLpNorm` not raw integral): **Likely correct**.
- **Axiom D** (`ouSemigroupFin_energy_eq_deriv`, with both
  `IsCoreFin` hypotheses): **Likely correct**.

But these alone aren't enough — we'd still need the unconditional
`P_semigroup` and `P_symmetric` somewhere, and those don't admit
the textbook-axiom treatment.

## Recommendation (revised 2026-05-13 post-3.1-pro)

3.1-pro recommends **Alternative 2** (Lp quotient carrier) or
**Alternative 1** (relax MarkovSemigroup fields back to IsCore /
MemLp hypotheses) as the *only* mathematically sound paths.

Quoting 3.1-pro:

> "The gold standard in mathlib (e.g., `MeasureTheory.Lp`) is to
> formulate `P` as a monoid homomorphism to bounded linear operators:
> `ℝ≥0 → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)`. On this space, composition
> `P(s+t) = P s ∘ P t`, symmetry `⟪P t f, g⟫ = ⟪f, P t g⟫`, and
> `P 0 f = f` hold flawlessly and unconditionally because all elements
> are μ-almost-everywhere equivalence classes of L² functions, entirely
> side-stepping Bochner junk values."

This means Stage N3 actually requires an **upstream refactor of
`Abstract/Hypercontractivity.lean`**, not an additional textbook
axiom in `EuclideanFin.lean`. The choice is between:

- **Option 1**: relax `MarkovSemigroup` to carry `MemLp` / `IsCore`
  hypotheses on its laws (and re-vet Gross on the new weaker
  statements with gemini-3.1-pro — should pass since BGL Gross is
  routinely stated on a core algebra).
- **Option 2**: refactor `MarkovSemigroup` to carry an `Lp →L Lp`
  operator-valued semigroup. More substantial, but produces a much
  cleaner abstract framework. Mathlib-aligned.

Either is a real upstream project (~1 week each, with Gross re-vetting).
The user's call which to pursue.

## Pre-existing axiom-count counts (no changes since codex bailed)

- markov-semigroups main: **11 axioms** (head `ed88be1`, all post-N1
  documentation pushed and synced).
- gaussian-hilbert main: **1 axiom** (`ouSemigroupAct_eLpNorm_hypercontractive`,
  unchanged; the post-N1 multivariate LSI was added but the discharge
  bridge couldn't be completed).
- pphi2 (`phase-b-discharge`): **21 axioms, 2 sorries** (uncommitted
  AXIOM_AUDIT.md refresh waiting for your review).

## Suggested next action

Pick **Option 1** (relax MarkovSemigroup to IsCore/MemLp hypotheses,
re-vet Gross axioms) or **Option 2** (refactor MarkovSemigroup to
operator-valued `Lp →L Lp` semigroup). Both are upstream refactors of
`Abstract/Hypercontractivity.lean`. Option 1 is the smaller refactor;
Option 2 is the cleaner long-term framework.

If picking Option 1: dispatch a codex rescue with a brief covering
(a) the structure rewrite of `MarkovSemigroup`/`DirichletMarkovSemigroup`
to carry `MemLp` / `IsCore` hypotheses, (b) re-vetting the
`gross_lsi_implies_hypercontractive` axiom on the new weaker
statement with gemini-3.1-pro-preview, (c) updating the gaussian-hilbert
wire-in N3 to use the relaxed bundle. Estimated ~5-7 days.

If picking Option 2: same but with the `Lp →L Lp` operator-valued
formulation. Estimated ~7-14 days, with the upside that the resulting
abstract framework is much closer to mathlib conventions and may help
future Markov-semigroup projects.

Either way: **the 2026-05-13 bundle refactor needs to be partially
reverted/redone**. The motivation for the unconditional shape (the
original gemini-3.1-pro vet) turned out to be flawed about Lean
integration semantics.
