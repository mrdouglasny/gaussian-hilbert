# Axiom Audit

*Per-axiom registry for `gaussian-hilbert`. Each row records the axiom's
statement (line ref), literature reference, vetting verdict, discharge
plan, and downstream consumers. Last refreshed: 2026-05-10.*

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

**4 axioms total** (`grep ^axiom` on `GaussianHilbert/`):
- 1 in `GaussianHilbert/PolynomialDensity.lean` — analytic axiom feeding the algebraic discharge of `hermiteMulti_dense`
- 3 in `GaussianHilbert/OUEigenfunctions.lean` — placeholder OU-action axioms gated on the Mehler-kernel discharge plan

The polynomial-chaos pipeline (proved theorems `hermiteMulti_dense`,
`wienerChaos_isHilbertSum`, `bonami_nelson_chaos`,
`bonami_nelson_chaosLE`, `polynomial_chaos_concentration`) transitively
rests on these 4 + Lean built-ins (`propext`, `Classical.choice`,
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

### OU semigroup action (placeholder cluster)

These three axioms are infrastructure stubs: they declare an `ouSemigroupAct`
operator and its expected behaviour on Wiener-chaos pieces, without
specifying the operator. They are load-bearing for `polynomial_chaos_concentration`
(Janson Thm 5.10) and the Bonami-Nelson L^p bounds.

A full discharge plan exists at
[`docs/ou-mehler-discharge-plan.md`](ou-mehler-discharge-plan.md) — five
stages, ~3-4 weeks of focused work, no further Mathlib gaps. After
those discharges, the polynomial-chaos pipeline rests only on
`polynomial_dense_L2_of_subGaussian` (above) +
`gross_lsi_implies_hypercontractive` (markov-semigroups) + the 4 1D
Mehler-kernel BGL axioms (markov-semigroups).

| Axiom | File:Line | Reference | Rating | Vetting | Strategy / Plan | Consumers |
|---|---|---|---|---|---|---|
| `ouSemigroupAct` | [`GaussianHilbert/OUEigenfunctions.lean:490`](../GaussianHilbert/OUEigenfunctions.lean#L490) | BGL §2.7.4 (OU semigroup definition) | **Placeholder** | LP | Defines the OU semigroup as a CLM `Lp ℝ 2 (stdGaussianFin n) →L[ℝ] Lp ℝ 2 (stdGaussianFin n)` without specifying the operator. Discharge: define explicitly as the Mehler integral `(M_t f)(x) = ∫ f(e^{-t}x + √(1-e^{-2t})y) dγ_n(y)`. See [Stage A](ou-mehler-discharge-plan.md#stage-a--mehler-operator-on-l-250-lines-5-7-days-no-new-axioms) (~250 lines / ~1 week). | `ouSemigroupAct_eq_smul_of_mem_wienerChaos`, `ouSemigroupAct_eLpNorm_hypercontractive` (same file); `bonami_nelson_chaos`, `bonami_nelson_chaosLE`, `polynomial_chaos_concentration` (`PolynomialChaosConcentration.lean`). pphi2's `Pphi2.NelsonEstimate.{ChaosTailBridge, PolynomialChaosBridge}` consume the last via `polynomial_chaos_concentration`. |
| `ouSemigroupAct_eq_smul_of_mem_wienerChaos` | [`GaussianHilbert/OUEigenfunctions.lean:507`](../GaussianHilbert/OUEigenfunctions.lean#L507) | BGL §2.7.4 (OU eigenvalues on chaos: `T_t H_k = e^{-kt} H_k`); Janson §3.4 (Mehler-Hermite identity); Nualart §1.4 | **Placeholder** | LP | OU semigroup multiplies each Hermite chaos `H_k` by `e^{-kt}`. Direct discharge: prove the 1D Mehler-Hermite identity `∫ He_k(e^{-t}x + √(1-e^{-2t})y) dγ(y) = e^{-kt} He_k(x)` via Hermite generating function; tensor product to multivariate; extend to closure by linearity + density. See [Stage C′](ou-mehler-discharge-plan.md#stage-c--hermite-eigenvalues-via-1d-mehler-hermite-identity-250-lines-parallel-to-ab) (~250 lines / ~1 week). | `bonami_nelson_chaos`, `bonami_nelson_chaosLE`, `polynomial_chaos_concentration` |
| `ouSemigroupAct_eLpNorm_hypercontractive` | [`GaussianHilbert/OUEigenfunctions.lean:528`](../GaussianHilbert/OUEigenfunctions.lean#L528) | E. Nelson, *J. Funct. Anal.* 12 §3 (1973); BGL Theorem 5.2.3 | **Placeholder** | LP | Bonami-Beckner-Nelson hypercontractive bound `‖T_t f‖_{L^p} ≤ ‖f‖_{L^q}` for `e^{2t} ≥ p-1`, `q = 2`. Discharge: Bakry-Émery curvature 1 on `(Fin n → ℝ, γ_n)` → LSI(1) → markov-semigroups `gross_lsi_implies_hypercontractive`. See [Stages C+E](ou-mehler-discharge-plan.md#stage-c--multivariate-bakryemeryspace-600-lines-10-14-days-no-new-axioms) (~650 lines / ~2-3 weeks; cross-repo dep on markov-semigroups for the Gross axiom — see the plan's "cross-repo dependency note"). Shortcut available via [LSI tensorization (Stage C-β)](ou-mehler-discharge-plan.md#optional-shortcut-stage-c--no-full-be-instance-1-axiom): adds 1 textbook axiom but cuts ~1 week. | `bonami_nelson_chaos`, `bonami_nelson_chaosLE`, `polynomial_chaos_concentration` (the load-bearing Bonami-Beckner-Nelson step in the polynomial-chaos concentration argument) |

## Open vetting items

1. **`ouSemigroupAct_eLpNorm_hypercontractive`** — flagged as
   `Placeholder` on the strength of literature reference alone; a DT
   pass when Mehler-kernel infrastructure lands would confirm the
   constant `e^{2t} ≥ p-1` matches the strongest published version
   (Janson §5.1 has minor variations in exponent thresholds across
   sub-versions).
2. **None of the OU placeholders have been DT-vetted yet** — this is
   acceptable while they remain pure placeholder axioms (the statements
   are simple eigenvalue and norm bounds, well-cited), but a DT pass
   would be valuable before the discharge plan is executed in case the
   discharge surfaces a hypothesis-strength issue not visible from the
   axiom statement alone.

## Related discharge plans (in this repo)

- [`docs/polynomial-chaos-roadmap.md`](polynomial-chaos-roadmap.md) —
  current-state status report for the four chaos-cluster files. All
  four are sorry-free; the only outstanding work is the OU placeholder
  discharge.
- [`docs/ou-mehler-discharge-plan.md`](ou-mehler-discharge-plan.md) —
  detailed five-stage plan for discharging the 3 OU placeholder axioms
  via the Mehler kernel + Bakry-Émery + Gross route.

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
