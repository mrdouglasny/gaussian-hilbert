# Status

*Snapshot of the repository's current development state. Last
refreshed: 2026-05-15 (later — after Stage E.2 + axiom retirement).
For axiom-by-axiom detail see [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md); for
forward-looking development directions see [`TODO.md`](TODO.md).*

## At a glance

| | Count |
|---|---|
| Library files | 6 (`HermitePolynomials`, `WienerChaos`, `OUEigenfunctions`, `PolynomialChaosConcentration`, `PolynomialDensity`, `HypercontractivityFromBE`) |
| Lean source | ~2,890 lines |
| Sorries | **0** |
| **Local axioms** | **0** *(gaussian-hilbert is now zero-axiom; the Bonami-Beckner-Nelson hypercontractivity placeholder was discharged 2026-05-15)* |
| Inherited axioms (transitive on `polynomial_chaos_concentration`) | 4: `gross_lsi_implies_hypercontractive` (markov-semigroups; Gross 1975) + 3 markov-semigroups GaussianFin BE axioms |
| `lake build` | clean (3241 jobs as of 2026-05-15) |
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

**Discharged 2026-05-15.** gaussian-hilbert is now zero local axioms.
The `ouSemigroupAct_eLpNorm_hypercontractive` placeholder is a real
theorem (Stages E.1 + E.2, branch `phase-3-smoke-test`). Remaining
upstream axiom hygiene (in markov-semigroups, not this repo):
- Phase 2.5 fresh-Fubini cleanup of
  `ouSemigroupFin_l2_sq_hasDerivWithinAt` (~1.5 days, would drop one
  inherited axiom).
- The 3 GaussianFin BE axioms + the Gross axiom are textbook
  (BGL Ch. 2 + Gross 1975) and live in the markov-semigroups
  axiom-discharge backlog.

(Section retained below for the historical pre-discharge snapshot.)

After the upstream Lp-carrier refactor + Phase 2 + Phase 3 wire-in
(2026-05-13 to 2026-05-15), the remaining
`ouSemigroupAct_eLpNorm_hypercontractive` discharge has collapsed to
**~1-2 active days** of adapter work. Concretely:

* **N1 BE instance** (multivariate `BakryEmerySpace (Fin n → ℝ)`):
  ✅ already on markov-semigroups main since commit `e1e2011`.
* **Lp-carrier Phase 1** (abstract `MarkovSemigroup` /
  `DirichletMarkovSemigroup`): ✅ on markov-semigroups main.
* **Lp-carrier Phase 2** (concrete
  `GaussianFin.stdGaussianFin_dirichletMarkovSemigroup n`): ✅ on
  markov-semigroups branch
  `feat/lp-carrier-stdGaussianFin-dirichletmarkov` at commit `6782dc7`
  (the BE → DirichletMarkovSemigroup bridge that the discharge plan
  used to call N3).
* **Phase 3 wire-in (smoke test)**: ✅ this repo, branch
  `phase-3-smoke-test` at commit `0f0c5eb`. `HypercontractivityFromBE.lean`
  contains two compiling `example`s: bundle reachable from gaussian-hilbert,
  and `gross_lsi_implies_hypercontractive` accepts it.

What remains:

1. **`h_lsi` adapter** (~50-100 lines): construct
   `DirichletMarkovSemigroup.SatisfiesLogSobolev (stdGaussianFin_dirichletMarkovSemigroup n) 1`
   from `BakryEmerySpace.satisfiesLogSobolev (be := stdGaussianFin.bakryEmerySpace n)`.
2. **Predicate adapter** (~50 lines): bridge the abstract
   `MarkovSemigroup.IsHypercontractive` from
   `gross_lsi_implies_hypercontractive` to the concrete `eLpNorm`-form
   statement of `ouSemigroupAct_eLpNorm_hypercontractive`. Uses the
   already-proved `mehlerOp_eq_ouSemigroupAct` (Stage Ag, 2026-05-11).

Updated estimate at `docs/hypercontractivity-discharge-plan.md`. The
old plan listed ~10-14 days for "Stage N" and ~5-7 days for "Stage W"
(LSI tensorization shortcut), but most of that effort was actually
delivered by the Lp-carrier Phase 1+2 + the prior N1 BE instance.

For the pphi2 T² continuum-limit chain (the immediate downstream goal),
this means the upstream gaussian-hilbert side is essentially closed:
once the two adapters land, `polynomial_chaos_concentration` and the
downstream OU placeholder are end-to-end axiom-free for the standard
trio + the inherited Gross axioms in markov-semigroups.

## Recent history

- **2026-05-15 (later):** **`ouSemigroupAct_eLpNorm_hypercontractive`
  discharged — gaussian-hilbert is now zero-axiom.** Three commits on
  `phase-3-smoke-test`:
  - Stage E.1 (`fbb6701`): the Phase 2 bundle satisfies LSI(1) by
    direct transfer from `BakryEmerySpace.satisfiesLogSobolev`.
    Defeq through `@[reducible] DirichletMarkovSemigroup.toDirichletSpace`.
  - Stage E.2 (`e1bde62`): `ouSemigroupAct_eLpNorm_hypercontractive_proved`
    composing abstract `IsHypercontractive` (via `gross_lsi_implies_hypercontractive`)
    with the agreement chain
    `bundle.P t = ouSemigroupFinLp t =ᵐ ouSemigroupFin t = mehlerFun n t
    =ᵐ mehlerOp n t ht = ouSemigroupAct n t`. The `ouSemigroupFin = mehlerFun`
    and `γFin n = stdGaussianFin n` agreements are both `rfl`.
  - Axiom retirement (`029156d`): deletes the placeholder axiom from
    `OUEigenfunctions.lean`, renames `_proved` to drop the suffix, adds
    `import GaussianHilbert.HypercontractivityFromBE` to
    `PolynomialChaosConcentration.lean`. `grep ^axiom GaussianHilbert/`
    is now empty.
  - Net effect: `#print axioms polynomial_chaos_concentration` now
    shows `[propext, Classical.choice, Quot.sound,
    gross_lsi_implies_hypercontractive,
    GaussianFin.ouSemigroupFin_entropy_sq_decay_bound,
    GaussianFin.ouSemigroupFin_l2_sq_hasDerivWithinAt,
    GaussianFin.ouSemigroupFin_preserves_IsCore]` — the standard trio
    + 1 Gross axiom + 3 inherited markov-semigroups GaussianFin BE
    axioms. **No local gaussian-hilbert axioms.**

- **2026-05-15:** Phase 3 wire-in smoke test landed on
  `phase-3-smoke-test` (commit `0f0c5eb`).
  `HypercontractivityFromBE.lean` exercised the new
  `GaussianFin.stdGaussianFin_dirichletMarkovSemigroup` bundle from
  markov-semigroups Phase 2, with two passing `example` checks
  confirming the bundle types correctly and slots into
  `gross_lsi_implies_hypercontractive`. MarkovSemigroups pin bumped to
  `feat/lp-carrier-stdGaussianFin-dirichletmarkov` (`6782dc7`).
  Stage N status revised: now ~1-2 days from full
  `ouSemigroupAct_eLpNorm_hypercontractive` discharge — and that
  discharge landed the same day (see entry above).

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
