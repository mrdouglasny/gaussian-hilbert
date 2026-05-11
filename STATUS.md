# Status

*Snapshot of the repository's current development state. Last
refreshed: 2026-05-11. For axiom-by-axiom detail see
[`AXIOM_AUDIT.md`](AXIOM_AUDIT.md); for forward-looking
development directions see [`TODO.md`](TODO.md).*

## At a glance

| | Count |
|---|---|
| Library files | 5 (`HermitePolynomials`, `WienerChaos`, `OUEigenfunctions`, `PolynomialChaosConcentration`, `PolynomialDensity`) |
| Lean source | ~2,540 lines |
| Sorries | **0** |
| Axioms | **1** (Bonami-Beckner-Nelson hypercontractivity, intentionally deferred) |
| `lake build` | clean (3213 jobs as of 2026-05-11) |
| Total dependencies | Mathlib v4.29.0 + gaussian-field + markov-semigroups |

## Files

| File | Lines | Status |
|---|---|---|
| [`GaussianHilbert/PolynomialDensity.lean`](GaussianHilbert/PolynomialDensity.lean) | ~720 | **Proved**: `IsSubGaussianMeasure` def, `isSubGaussianMeasure_pi_gaussianReal` (Fernique-based), and `polynomial_dense_L2_of_subGaussian` (Janson Thm 2.6, discharged 2026-05-11 via L²-orthogonal-complement / Carleman moment-determinacy route). **0 axioms.** |
| [`GaussianHilbert/HermitePolynomials.lean`](GaussianHilbert/HermitePolynomials.lean) | ~460 | **Proved**: `hermiteMulti_orthogonality` (`∫ H_α H_β dγ_n = δ_{αβ} ∏ αᵢ!`), `hermiteMulti_l2_pos`, `hermiteMulti_dense`. **0 axioms.** |
| [`GaussianHilbert/WienerChaos.lean`](GaussianHilbert/WienerChaos.lean) | ~530 | **Proved**: `wienerChaos n k` (closed L² subspace), `wienerChaosLE n d`, `wienerChaos_orthogonal`, `chaosProjection`, `chaosProjection_sum_eq_of_mem_wienerChaosLE`, and `wienerChaos_isHilbertSum` (the full orthogonal Hilbert-sum decomposition `L²(γ_n) = ⊕̂ₖ 𝓗_k`). **0 axioms.** |
| [`GaussianHilbert/OUEigenfunctions.lean`](GaussianHilbert/OUEigenfunctions.lean) | ~720 | **Proved**: `ouGenerator` (`L = Δ - x·∇`), 1D + multivariate `ouGenerator_hermiteMultiEval` eigenfunction theorem, `ouSemigroupAct` (spectral construction via `wienerChaos_isHilbertSum`), and `ouSemigroupAct_eq_smul_of_mem_wienerChaos` (both discharged 2026-05-10). **1 placeholder axiom**: `ouSemigroupAct_eLpNorm_hypercontractive` (Bonami-Beckner-Nelson; needs Mehler integral + LSI tensorization / Bakry-Émery for native proof). |
| [`GaussianHilbert/PolynomialChaosConcentration.lean`](GaussianHilbert/PolynomialChaosConcentration.lean) | ~630 | **Proved**: `bonami_nelson_chaos`, `bonami_nelson_chaosLE`, `polynomial_chaos_concentration` (Janson Theorem 5.10). **0 new axioms** (consumes the single OU hypercontractivity placeholder). |

## Axiom dependencies (verified `#print axioms` on 2026-05-11)

| Theorem | Depends on |
|---|---|
| `polynomial_dense_L2_of_subGaussian` | Lean built-ins only |
| `hermiteMulti_orthogonality` | Lean built-ins only |
| `hermiteMulti_dense` | Lean built-ins only |
| `wienerChaos_isHilbertSum` | Lean built-ins only |
| `ouSemigroupAct` | Lean built-ins only |
| `ouSemigroupAct_eq_smul_of_mem_wienerChaos` | Lean built-ins only |
| `ouGenerator_hermiteMultiEval` | Lean built-ins only |
| `polynomial_chaos_concentration` | Lean built-ins + `ouSemigroupAct_eLpNorm_hypercontractive` |
| `bonami_nelson_chaos` / `_chaosLE` | Lean built-ins + `ouSemigroupAct_eLpNorm_hypercontractive` |

"Lean built-ins" means `propext`, `Classical.choice`, `Quot.sound`.

**Only one real axiom** in the closure of all gaussian-hilbert
theorems: `ouSemigroupAct_eLpNorm_hypercontractive`. Everything else
is end-to-end axiom-free.

## Active downstream consumers

- [pphi2](https://github.com/mrdouglasny/pphi2) (Cluster A: Nelson
  dynamical-cutoff concentration) — imports
  `GaussianHilbert.PolynomialChaosConcentration` in
  `Pphi2/NelsonEstimate/{ChaosTailBridge, PolynomialChaosBridge}.lean`.
- pphi2's audit at [`pphi2/docs/axiom_audit.md`](https://github.com/mrdouglasny/pphi2/blob/main/docs/axiom_audit.md)
  records `gaussian-hilbert` as a Lake dependency.

No other consumers yet. Future natural consumers:
- pphi2N (O(N) sigma model, vector-valued chaos)
- Stein's method / Nourdin-Peccati fourth-moment theorem
- Stochastic-PDE polynomial-coefficient expansions
- Random-matrix concentration via `Tr(M^k)` chaos bounds

## Discharge horizon

The remaining `ouSemigroupAct_eLpNorm_hypercontractive` axiom requires
the Mehler integral + LSI tensorization / Bakry-Émery for a native
proof. The discharge plans are documented in:

- [`docs/ou-discharge-codex-plan.md`](docs/ou-discharge-codex-plan.md)
  Route 2 (Mehler integral, ~2-3 weeks).
- [`docs/ou-mehler-discharge-plan.md`](docs/ou-mehler-discharge-plan.md)
  (the broader Stages A-E with C-β as the LSI-tensorization shortcut,
  ~3-4 weeks total).

The full discharge depends transitively on either the markov-semigroups
Gross axioms (~3-6 weeks of further work) or accepts the LSI
tensorization fact as a single textbook axiom in markov-semigroups
(~1 additional week).

For the pphi2 T² continuum-limit chain (the immediate downstream goal),
the gaussian-hilbert side is now as clean as possible without crossing
into the multi-month Mehler/hypercontractivity discharge effort.

## Recent history

- **2026-05-11:** Discharged `polynomial_dense_L2_of_subGaussian` via
  the L²-orthogonal-complement / Carleman moment-determinacy route
  (~590 new lines in `PolynomialDensity.lean`). All downstream
  consumers (`hermiteMulti_dense`, `wienerChaos_isHilbertSum`,
  `chaosCoordEquiv`, `ouSemigroupAct`,
  `ouSemigroupAct_eq_smul_of_mem_wienerChaos`) verified clean against
  `[propext, Classical.choice, Quot.sound]`.

- **2026-05-10:** Discharged the two OU semigroup axioms (`ouSemigroupAct`
  and `ouSemigroupAct_eq_smul_of_mem_wienerChaos`) via spectral
  construction on the Wiener-chaos Hilbert sum (Gemini-vetted Route 1
  from the OU discharge plan). The codex hand-off needed two passes;
  see `docs/ou-discharge-codex-plan.md` for the pitfall guidance that
  made the second pass succeed.

- **2026-05-10:** Repository migrated to top-level `AXIOM_AUDIT.md`
  per the new global convention in `~/.claude/AXIOM_AUDIT_FORMAT.md`.

- **2026-05-10:** Repository created. Initial seed of 5 files migrated
  from `markov-semigroups/MarkovSemigroups/Gaussian/*` and
  `gaussian-field/GeneralResults/PolynomialDensityGaussian.lean`.
