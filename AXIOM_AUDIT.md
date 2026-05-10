# Axiom audit — gaussian-hilbert

*Last updated 2026-05-10.*

## Purpose

In this project, an **axiom** is a *vetted provable theorem with a vetted
discharge plan* — not a fundamental unprovable assumption. Each axiom
listed below is:

1. A standard textbook fact, with explicit literature citation.
2. Reviewed for type correctness, hypothesis sufficiency, and
   non-vacuity (typically by a Gemini deep-think pass and/or a
   literature cross-check).
3. Accompanied by a concrete plan to discharge it into a Lean theorem
   (inline in the row, or linked to a dedicated discharge-plan doc).

We use the `axiom` keyword as a *staging point* — it lets the project
proceed to use a result before its full Lean proof is assembled, while
keeping the trust boundary explicit and discharge progress trackable.
The goal is for every entry below to eventually become a proved
theorem.

Format and conventions for this audit doc:
`~/.claude/AXIOM_AUDIT_FORMAT.md`.

---

*Per-axiom registry for `gaussian-hilbert`. Each row records the axiom's
statement (line ref), literature reference, vetting verdict, discharge
plan, and downstream consumers.*

## Conventions

**Vetting source codes** (per
[research-dev `AXIOM_MANAGEMENT.md`](https://github.com/mrdouglasny/research-dev/blob/main/library/lean/AXIOM_MANAGEMENT.md)):
- **DT** — Gemini deep-think (slow, high-reasoning vet pass; suffix `-2.5` / `-3.1` for the model)
- **GR** — Gemini chat review (`gemini-3-pro-preview`)
- **CX** — Codex (independent re-derivation / cross-check)
- **LP** — literature proof with explicit page reference
- **SA** — self-audit (author cross-checked against textbook by hand)
- **PR** — peer review (external mathematician)

**Rating scale:**
- **Standard** — well-established textbook fact with multiple independent references
- **Likely correct** — checked, consistent with textbook(s) but not externally vetted
- **Needs review** — placeholder; statement plausible but not yet vetted
- **Placeholder** — known to need replacement; statement may be approximate (infrastructure-stub)
- **Flagged** — concern raised; do not consume downstream until resolved

## Summary

**2 axioms total** (`grep ^axiom` on `GaussianHilbert/`):
- 1 in `GaussianHilbert/PolynomialDensity.lean` — analytic axiom feeding the algebraic discharge of `hermiteMulti_dense`
- 1 in `GaussianHilbert/OUEigenfunctions.lean` — the remaining OU hypercontractive placeholder

The polynomial-chaos pipeline (proved theorems `hermiteMulti_dense`,
`wienerChaos_isHilbertSum`, `bonami_nelson_chaos`,
`bonami_nelson_chaosLE`, `polynomial_chaos_concentration`) transitively
rests on these 2 + Lean built-ins (`propext`, `Classical.choice`,
`Quot.sound`).

## Audit table

### Analytic foundation

| Axiom | File:Line | Reference | Rating | Vetting | Strategy / Plan | Consumers |
|---|---|---|---|---|---|---|
| `polynomial_dense_L2_of_subGaussian` | [`GaussianHilbert/PolynomialDensity.lean:90`](../GaussianHilbert/PolynomialDensity.lean#L90) | S. Janson, *Gaussian Hilbert Spaces*, Cambridge (1997), Theorem 2.6; D. Nualart, *Malliavin Calculus* §1.1.1; C. Berg, *Multidimensional moment problem*, LNM 1210 (1986) | **Standard** | DT-2.5 (2026-05-09; verdict and detailed entry recorded in [`pphi2/docs/gaussian-field-axiom-vet-2026-05-09.md`](https://github.com/mrdouglasny/pphi2/blob/main/docs/gaussian-field-axiom-vet-2026-05-09.md)) | Multivariate polynomials are dense in `L²(μ)` for any sub-Gaussian probability measure on `Fin n → ℝ`. Textbook proof: (1) `Cc(ℝⁿ)` dense in `L²(μ)` (Mathlib has it); (2) Stone-Weierstrass on each ball; (3) sub-Gaussian tail controls polynomial L²-mass on tail. Lean discharge: ~250 lines, ~4-7 days; the analytic content is the tail-control step. **The DT-2.5 verdict noted that the hypothesis is tight: weaker (e.g. second moment alone) doesn't suffice — Stieltjes-style indeterminate counterexamples exist.** | `hermiteMulti_dense` (proved theorem, `HermitePolynomials.lean`, via `Submodule.span` change-of-basis between multivariate monomials and multivariate Hermite polynomials); transitively `wienerChaos_isHilbertSum` (`WienerChaos.lean`). Not used by the chaos-concentration consumers (which depend only on the OU placeholders below). |

The `IsSubGaussianMeasure` predicate in the same file is a `def` (not an
axiom), and the lemma `isSubGaussianMeasure_pi_gaussianReal` is fully
**proved** (transports Mathlib's `IsGaussian.exists_integrable_exp_sq`
through the `WithLp.toLp 2` measurable equivalence; depends only on
Lean built-ins).

### Previously axiomatized but now proved

These two former OU placeholders were discharged on 2026-05-10 by a
spectral construction using `wienerChaos_isHilbertSum`: `ouSemigroupAct`
is now defined by diagonal decay on chaos coordinates, and
`ouSemigroupAct_eq_smul_of_mem_wienerChaos` is proved from that
definition. This is mathematically equivalent to the Mehler operator on
`L²(γ_n)`, but the pointwise Mehler identification is still deferred.

| Former axiom | File:Line | Reference | Discharge status | Notes | Consumers |
|---|---|---|---|---|---|
| `ouSemigroupAct` | [`GaussianHilbert/OUEigenfunctions.lean:657`](../GaussianHilbert/OUEigenfunctions.lean#L657) | BGL §2.7.4 (OU semigroup definition) | **Proved** | Defined spectrally as the continuous diagonal map `f_k ↦ e^{-kt} f_k` on the `ℓ²` sum of Wiener-chaos coordinates, transported back along `wienerChaos_isHilbertSum`. This is sufficient for all existing chaos-eigenvalue consumers. | `ouSemigroupAct_eq_smul_of_mem_wienerChaos`, `ouSemigroupAct_eLpNorm_hypercontractive`, `bonami_nelson_chaos`, `bonami_nelson_chaosLE`, `polynomial_chaos_concentration` |
| `ouSemigroupAct_eq_smul_of_mem_wienerChaos` | [`GaussianHilbert/OUEigenfunctions.lean:680`](../GaussianHilbert/OUEigenfunctions.lean#L680) | BGL §2.7.4 (OU eigenvalues on chaos: `T_t H_k = e^{-kt} H_k`); Janson §3.4; Nualart §1.4 | **Proved** | Reduced to the single-coordinate computation for the spectral diagonal operator under the chaos-coordinate equivalence. | `bonami_nelson_chaos`, `bonami_nelson_chaosLE`, `polynomial_chaos_concentration` |

### Remaining OU placeholder

The only OU axiom left is the hypercontractive bound. It remains
load-bearing for `polynomial_chaos_concentration` (Janson Thm 5.10) and
the Bonami-Nelson `L^p` bounds.

The full Mehler-kernel discharge plan at
[`docs/ou-mehler-discharge-plan.md`](ou-mehler-discharge-plan.md)
remains relevant if we later want a pointwise Markov realization of the
OU semigroup or a native proof of hypercontractivity. For the current
repo milestone, only the last hypercontractive step is still axiomatic.

| Axiom | File:Line | Reference | Rating | Vetting | Strategy / Plan | Consumers |
|---|---|---|---|---|---|---|
| `ouSemigroupAct_eLpNorm_hypercontractive` | [`GaussianHilbert/OUEigenfunctions.lean:724`](../GaussianHilbert/OUEigenfunctions.lean#L724) | E. Nelson, *J. Funct. Anal.* 12 §3 (1973); BGL Theorem 5.2.3 | **Placeholder** | LP | Bonami-Beckner-Nelson hypercontractive bound `‖T_t f‖_{L^p} ≤ ‖f‖_{L^q}` for `e^{2t} ≥ p-1`, `q = 2`. Discharge: Bakry-Émery curvature 1 on `(Fin n → ℝ, γ_n)` → LSI(1) → markov-semigroups `gross_lsi_implies_hypercontractive`. See [Stages C+E](ou-mehler-discharge-plan.md#stage-c--multivariate-bakryemeryspace-600-lines-10-14-days-no-new-axioms) (~650 lines / ~2-3 weeks; cross-repo dep on markov-semigroups for the Gross axiom — see the plan's "cross-repo dependency note"). Shortcut available via [LSI tensorization (Stage C-β)](ou-mehler-discharge-plan.md#optional-shortcut-stage-c--no-full-be-instance-1-axiom): adds 1 textbook axiom but cuts ~1 week. | `bonami_nelson_chaos`, `bonami_nelson_chaosLE`, `polynomial_chaos_concentration` (the load-bearing Bonami-Beckner-Nelson step in the polynomial-chaos concentration argument) |

## Open vetting items

1. **`ouSemigroupAct_eLpNorm_hypercontractive`** — flagged as
   `Placeholder` on the strength of literature reference alone; a DT
   pass when Mehler-kernel infrastructure lands would confirm the
   constant `e^{2t} ≥ p-1` matches the strongest published version
   (Janson §5.1 has minor variations in exponent thresholds across
   sub-versions).
2. **The spectral discharge avoids the Mehler kernel for now** — this
   is acceptable for the current downstream uses, but a future native
   proof of hypercontractivity or positivity/Markov properties should
   still identify `ouSemigroupAct` with the textbook Mehler operator.

## Related discharge plans (in this repo)

- [`docs/polynomial-chaos-roadmap.md`](polynomial-chaos-roadmap.md) —
  current-state status report for the four chaos-cluster files. All
  four are sorry-free; the only outstanding work is the remaining OU
  hypercontractive
  discharge.
- [`docs/ou-mehler-discharge-plan.md`](ou-mehler-discharge-plan.md) —
  detailed five-stage plan for the full Mehler-kernel route. Two former
  OU placeholders have already been discharged spectrally; the
  hypercontractive placeholder remains.

## Maintenance protocol

When adding or removing an axiom:
1. Update this file (the audit table row).
2. Update [`README.md`](../README.md)'s axiom count + Status section in sync.
3. If the discharge plan changes, update the `docs/<plan>.md` entry and
   re-link from the row's "Strategy / Plan" column.
4. After any new vetting pass, update the row's `Vetting` column AND
   the `Vetting:` line in the source-file docstring.

When *discharging* an axiom (turning it into a proved theorem):
1. Move the row to a "Previously axiomatized but now proved" section
   (create one when first needed).
2. Update README's axiom count + Status section.
3. Note consumers' `#print axioms` change in the commit message so the
   audit trail is visible.
