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

**Option 4 (mine, "extra textbook axioms")**: introduce ~3-5 new
*vetted textbook axioms* in markov-semigroups stating the
unconditional versions of the Markov-semigroup laws for the
multivariate Gaussian OU semigroup. Specifically:

```lean
-- Each would carry full BGL citation + gemini-3.1-pro-preview vetting
-- + a clean tensor-lift discharge plan.

axiom ouSemigroupFin_compose_general {n : ℕ} (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (f : (Fin n → ℝ) → ℝ) :
    ouSemigroupFin (s + t) f = ouSemigroupFin s (ouSemigroupFin t f)

axiom ouSemigroupFin_eLpNorm_contraction {n : ℕ} (t : ℝ) (ht : 0 ≤ t)
    (f : (Fin n → ℝ) → ℝ) (hf : MeasureTheory.MemLp f 2 (γFin n)) :
    eLpNorm (ouSemigroupFin t f) 2 (γFin n) ≤ eLpNorm f 2 (γFin n)

-- Plus possibly: P_symmetric_general, energy_eq_deriv_general
```

Each axiom is a standard fact in the BGL framework (the Gaussian OU
semigroup is a Markov semigroup in the literature — the unconditional
laws hold by construction); each has a Fubini-style discharge plan;
each adds to markov-semigroups' textbook-axiom load.

**Tradeoff for Option 4**: 3-5 more textbook axioms in markov-semigroups
(brings total from 11 to ~14-16). pphi2's transitive axiom load grows
from the expected 4 (Gross + 3 GaussianFin) to ~7-9. Each new axiom is
narrow and citable.

## Recommendation

**Option 4** is the lowest-friction path consistent with our axiom
philosophy ("vetted provable textbook theorem with discharge plan").
It treats the unconditional Markov-semigroup laws on the Gaussian OU
as additional standard facts, which is mathematically correct, and
postpones the broader question of "should the abstract
`MarkovSemigroup` structure require IsCore-restricted laws?" to a
later cleanup.

**Option 3** is also defensible if you prefer to keep the axiom count
low and accept that the bundle refactor's "all-functions" framing was
overly ambitious. The trade is re-vetting Gross on the new weaker
statements.

**Options 1 and 2** are bigger upstream projects; both buy a cleaner
final structure but cost ~1-2 more weeks of work each.

## Pre-existing axiom-count counts (no changes since codex bailed)

- markov-semigroups main: **11 axioms** (head `ed88be1`, all post-N1
  documentation pushed and synced).
- gaussian-hilbert main: **1 axiom** (`ouSemigroupAct_eLpNorm_hypercontractive`,
  unchanged; the post-N1 multivariate LSI was added but the discharge
  bridge couldn't be completed).
- pphi2 (`phase-b-discharge`): **21 axioms, 2 sorries** (uncommitted
  AXIOM_AUDIT.md refresh waiting for your review).

## Suggested next action

Pick option 3 or 4, vet the new statements with gemini-3.1-pro, then
re-dispatch codex with a revised brief that includes the new axiom
statements as inputs (rather than asking codex to derive them).
