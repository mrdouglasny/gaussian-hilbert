# Status

*Snapshot of the repository's current development state. Last
refreshed: 2026-05-10. For axiom-by-axiom detail see
[`docs/AXIOM_AUDIT.md`](docs/AXIOM_AUDIT.md); for forward-looking
development directions see [`TODO.md`](TODO.md).*

## At a glance

| | Count |
|---|---|
| Library files | 5 (`HermitePolynomials`, `WienerChaos`, `OUEigenfunctions`, `PolynomialChaosConcentration`, `PolynomialDensity`) |
| Lean source | ~1,950 lines |
| Sorries | **0** |
| Axioms | **4** (1 analytic foundation + 3 OU placeholders) |
| `lake build` | clean (3023 jobs as of last full build, 2026-05-10) |
| Total dependencies | Mathlib v4.29.0 + gaussian-field (`9c66a40`) + markov-semigroups (`3cb482d`) |

## Files

| File | Lines | Status |
|---|---|---|
| [`GaussianHilbert/PolynomialDensity.lean`](GaussianHilbert/PolynomialDensity.lean) | ~130 | **Proved**: `IsSubGaussianMeasure` def, `isSubGaussianMeasure_pi_gaussianReal` (Fernique-based, no axioms beyond Lean built-ins). **1 axiom**: `polynomial_dense_L2_of_subGaussian` (Janson Thm 2.6, DT-2.5 vetted). |
| [`GaussianHilbert/HermitePolynomials.lean`](GaussianHilbert/HermitePolynomials.lean) | ~460 | **Proved**: `hermiteMulti_orthogonality` (`∫ H_α H_β dγ_n = δ_{αβ} ∏ αᵢ!`), `hermiteMulti_l2_pos`, `hermiteMulti_dense`. The density theorem uses the polynomial-density axiom above + a `Submodule.span` change-of-basis between multivariate monomials and multivariate Hermite polynomials. **0 axioms.** |
| [`GaussianHilbert/WienerChaos.lean`](GaussianHilbert/WienerChaos.lean) | ~530 | **Proved**: `wienerChaos n k` (closed L² subspace) and `wienerChaosLE n d`, distinct-chaos orthogonality `wienerChaos_orthogonal`, `chaosProjection`, the chaos sum `chaosProjection_sum_eq_of_mem_wienerChaosLE`, and `wienerChaos_isHilbertSum` (the full orthogonal Hilbert-sum decomposition `L²(γ_n) = ⊕̂ₖ 𝓗_k`, derived from `hermiteMulti_dense` via `IsHilbertSum.mkInternal`). **0 axioms.** |
| [`GaussianHilbert/OUEigenfunctions.lean`](GaussianHilbert/OUEigenfunctions.lean) | ~540 | **Proved**: `ouGenerator` (`L = Δ - x·∇`), 1D + multivariate `ouGenerator_hermiteMultiEval` eigenfunction theorem (`L H_α = -|α| H_α`). **3 placeholder axioms** for the OU semigroup operator and its action on chaos pieces (gated on Mehler-kernel discharge plan; see [`docs/ou-mehler-discharge-plan.md`](docs/ou-mehler-discharge-plan.md)). |
| [`GaussianHilbert/PolynomialChaosConcentration.lean`](GaussianHilbert/PolynomialChaosConcentration.lean) | ~630 | **Proved**: `bonami_nelson_chaos`, `bonami_nelson_chaosLE`, `polynomial_chaos_concentration` (Janson Theorem 5.10). **0 new axioms** (consumes the 3 OU placeholders from `OUEigenfunctions.lean`). |

## Axiom dependencies (verified `#print axioms`)

| Theorem | Depends on |
|---|---|
| `hermiteMulti_orthogonality` | Lean built-ins only |
| `hermiteMulti_dense` | Lean built-ins + `polynomial_dense_L2_of_subGaussian` |
| `wienerChaos_isHilbertSum` | Lean built-ins + `polynomial_dense_L2_of_subGaussian` |
| `ouGenerator_hermiteMultiEval` | Lean built-ins only |
| `polynomial_chaos_concentration` | Lean built-ins + 3 OU placeholders |
| `bonami_nelson_chaos` / `_chaosLE` | Lean built-ins + 3 OU placeholders |

The `polynomial_dense_L2_of_subGaussian` axiom does *not* propagate up
to `polynomial_chaos_concentration` — that theorem rests only on the OU
placeholders and Lean built-ins. The `polynomial_dense_L2_of_subGaussian`
dep is confined to `hermiteMulti_dense` and the subsequent
`wienerChaos_isHilbertSum`.

## Active downstream consumers

- [pphi2](https://github.com/mrdouglasny/pphi2) (Cluster A: Nelson
  dynamical-cutoff concentration) — imports
  `GaussianHilbert.PolynomialChaosConcentration` in
  `Pphi2/NelsonEstimate/{ChaosTailBridge, PolynomialChaosBridge}.lean`.
  Pin currently floats on `main`.
- pphi2's audit at
  [`pphi2/docs/axiom_audit.md`](https://github.com/mrdouglasny/pphi2/blob/main/docs/axiom_audit.md)
  records `gaussian-hilbert` as a Lake dependency with 4 active axioms.

No other consumers yet. Future natural consumers (per [`TODO.md`](TODO.md)):
- pphi2N (O(N) sigma model, vector-valued chaos)
- Stein's method / Nourdin-Peccati fourth-moment theorem
- Stochastic-PDE polynomial-coefficient expansions
- Random-matrix concentration via `Tr(M^k)` chaos bounds

## Discharge horizon

The Mehler-kernel + Bakry-Émery + Gross discharge plan in
[`docs/ou-mehler-discharge-plan.md`](docs/ou-mehler-discharge-plan.md)
estimates ~3-4 weeks of focused work to discharge all 3 OU placeholder
axioms. After that, the polynomial-chaos pipeline rests only on:

- **`polynomial_dense_L2_of_subGaussian`** (this repo, DT-2.5 vetted, well-cited)
- **`gross_lsi_implies_hypercontractive`** (markov-semigroups, well-cited Gross 1975)
- **4 Gaussian1D Mehler-kernel facts** (markov-semigroups, GR-vetted)

All five are textbook items. Full axiom-free downstream consumption
is plausible on a multi-month timescale if the Mehler discharge +
Gaussian1D BGL discharges + Gross discharge are all executed (the
Gross discharge alone is the deepest piece, ~3-6 weeks).

## Recent history

- **2026-05-10:** Repository created. Initial seed of 5 files migrated
  from `markov-semigroups/MarkovSemigroups/Gaussian/*` and
  `gaussian-field/GeneralResults/PolynomialDensityGaussian.lean`.
  Namespace renamed `MarkovSemigroups.Gaussian` /
  `GaussianField.GeneralResults` → `GaussianHilbert`. The two plan docs
  (`polynomial-chaos-roadmap.md`, `ou-mehler-discharge-plan.md`) followed.
  See README for architectural context.
