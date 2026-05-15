# Discharge plan: `ouSemigroupAct_eLpNorm_hypercontractive`

*Created 2026-05-11. Significantly revised 2026-05-11 after
discovering that Stage A is already complete.*

**Target axiom**: `ouSemigroupAct_eLpNorm_hypercontractive` in
[`GaussianHilbert/OUEigenfunctions.lean:724`](../GaussianHilbert/OUEigenfunctions.lean#L724).
Bonami-Beckner-Nelson hypercontractive bound
`‖T_t f‖_{L^p} ≤ ‖f‖_{L²}` for `e^{2t} ≥ p − 1`.

**Why this is the only remaining gaussian-hilbert axiom**: the chaos
infrastructure has been fully discharged
(`polynomial_dense_L2_of_subGaussian` 2026-05-11; `ouSemigroupAct`
and `ouSemigroupAct_eq_smul_of_mem_wienerChaos` 2026-05-10). The OU
pair was discharged via a **spectral shortcut** (defining
`ouSemigroupAct` as the diagonal `e^{-kt}` on the Wiener-chaos Hilbert
sum). Per Gemini's vet, this shortcut *cannot* deliver the
hypercontractivity bound — that property requires the **pointwise**
geometry of the operator (positivity, Dirichlet-form integration by
parts), which the spectral form obscures.

To discharge this last axiom natively, the Mehler integral must be
constructed and identified with the existing spectral `ouSemigroupAct`,
then hypercontractivity follows from Bakry-Émery curvature 1 + LSI(1)
+ Gross's LSI ⇔ HC duality.

> ## 🟢 MAJOR LEVERAGE: Stage A is already done
>
> An end-of-session audit on 2026-05-11 revealed that codex, while
> implementing the OU spectral discharge on 2026-05-10, *already
> built the entire Mehler-integral L²-CLM scaffold* in
> [`GaussianHilbert/OUEigenfunctions.lean`](../GaussianHilbert/OUEigenfunctions.lean)
> (lines 528-1233, ~700 lines). The following are all proved, with
> `#print axioms` showing only `[propext, Classical.choice, Quot.sound]`:
>
> | Decl | Line | What it is |
> |---|---|---|
> | `ouAffine`, `mehlerFun`, `mehlerFun_measurable` | 528-556 | Function-level Mehler operator |
> | `stdGaussianFin_prod_map_ouAffine` | 627 | Measure-preservation (the load-bearing Gaussian fact) |
> | `mehlerFun_integral_sq_le`, `mehlerFun_memLp` | 769, 806 | L²-contraction via Jensen |
> | `mehlerLM`, `mehlerLM_norm_le` | 919, 994 | LinearMap intermediate |
> | **`mehlerOp`** | **1018** | **The L²-CLM (Stage A target)** |
> | `mehler_hermiteEval_1d` | 1082 | 1D Mehler-Hermite identity |
> | `mehlerOp_hermiteMultiLp` | 1182 | n-D Mehler-Hermite identity |
> | **`mehlerOp_eq_smul_of_mem_wienerChaos`** | **1211** | **Mehler eigenvalue on chaos (Stage Ag pre-req)** |
>
> This collapses the discharge cost dramatically:
> * **Stage A**: DONE.
> * **Stage Ag**: now near-trivial (both `mehlerOp` and `ouSemigroupAct`
>   satisfy the same eigenvalue equation on every Wiener chaos; by
>   `wienerChaos_isHilbertSum` density + `ContinuousLinearMap.ext_on`,
>   they're equal). **~30-60 lines, ~1 day.**
> * **Stages W/N and E**: unchanged.
>
> The revised totals are in the "Total effort" section below.

**Estimate**: **~1.5-2 weeks** (recommended Route W) or **~2.5-3 weeks**
(no-new-axioms Route N). See route trade-off below.

---

## Architecture (post-spectral-discharge)

```
┌──────────────────────────────────────────────────────────────────────────────┐
│ ALREADY DISCHARGED (2026-05-10) — spectral shortcut on wienerChaos_isHilbertSum:│
│   - ouSemigroupAct (def via chaosDiagCLM)                                    │
│   - ouSemigroupAct_eq_smul_of_mem_wienerChaos (theorem)                      │
└──────────────────────────────────────────────────────────────────────────────┘
                                       │
                                       │ spectral OU acts as e^{-kt} on chaos H_k
                                       ▼
┌──────────────────┐                  ┌─────────────────────────────────────┐
│  Stage A         │                  │  ou-discharge-codex-plan.md         │
│  Mehler operator │                  │  Route 2 (formerly the "full"       │
│  on L²(γ_n)      │                  │  Mehler route; now downscoped to    │
│                  │                  │  just Stage A for the agreement)    │
└────────┬─────────┘                  └─────────────────────────────────────┘
         │
         │ both definitions act as e^{-kt} on H_k
         ▼
┌─────────────────────────────────────┐
│  Agreement theorem:                 │
│  mehlerOp = ouSemigroupAct          │
│  (~50-100 lines)                    │
└────────┬────────────────────────────┘
         │
         ▼
┌─────────────────────────────────────┐          ┌──────────────────────────────────┐
│  Route W (recommended):             │   OR     │  Route N (no new axioms):        │
│  Stage C-β LSI tensorization        │          │  Stage C full BE instance        │
│  shortcut. +1 markov-semigroups     │          │  on (Fin n → ℝ, γ_n) with        │
│  axiom (lsi_tensorize), but cuts    │          │  curvature ρ = 1. ~600 lines.    │
│  ~1 week. ~250 lines.               │          │  Depends transitively on:        │
│                                     │          │   - 4 BGL Ch. 2 axioms           │
│                                     │          │   - 2 Gross axioms               │
└────────┬────────────────────────────┘          │  (all already in                 │
         │                                       │   markov-semigroups)             │
         │                                       └────────┬─────────────────────────┘
         │                                                │
         ├───────────┬────────────────────────────────────┘
                     ▼
                ┌────────────────────────────────────────────────────────────┐
                │  Stage E: wire ouSemigroupAct_eLpNorm_hypercontractive     │
                │  from Gross's gross_lsi_implies_hypercontractive applied   │
                │  to the (Mehler = spectral) OU semigroup. ~50 lines.       │
                └────────────────────────────────────────────────────────────┘
```

---

## Stages (4 substeps)

### Stage A — Mehler operator on `L²(γ_n)`

**Status**: ✅ **DONE.** The Mehler operator
`mehlerOp n t ht : Lp ℝ 2 (stdGaussianFin n) →L[ℝ] Lp ℝ 2 (stdGaussianFin n)`
is defined at `GaussianHilbert/OUEigenfunctions.lean:1018` as the
L²-CLM lifting of the Mehler integral
`(M_t f)(x) = ∫ f(e^{-t}·x + √(1 − e^{-2t})·y) dγ_n(y)`.

Codex built this during the 2026-05-10 OU spectral discharge work
(commit `e6235e9` and follow-ups) but didn't surface it in the
prior version of this plan. Verified with `#print axioms`: only
`[propext, Classical.choice, Quot.sound]`.

Components built:

- `ouAffine`, `mehlerFun`, `mehlerFun_measurable` (lines 528-556).
- `stdGaussianFin_prod_map_ouAffine` (line 627) — the measure-preservation
  Gaussian fact `(x, y) ↦ e^{-t}x + √(1−e^{-2t})y` pushforward.
- `mehlerFun_integral_sq_le`, `mehlerFun_memLp` (lines 769, 806) —
  L²-contraction via Jensen.
- `mehlerLM`, `mehlerLM_norm_le` (lines 919, 994) — LinearMap intermediate.
- **`mehlerOp` (line 1018)** — the Lp CLM.

Also built (a head start on Stage Ag):

- `mehler_hermiteEval_1d` (line 1082) — 1D Mehler-Hermite identity
  `∫ He_k(e^{-t}·x + √(1−e^{-2t})·y) dγ(y) = e^{-kt} · He_k(x)`.
- `mehlerOp_hermiteMultiLp` (line 1182) — multivariate version via
  Fubini.
- **`mehlerOp_eq_smul_of_mem_wienerChaos` (line 1211)** — Mehler's
  chaos-eigenvalue equation, proved via `ContinuousLinearMap.ext_on`
  on the dense span. **Eigenvalue identity for `mehlerOp` is DONE.**

### Stage Ag — Agreement theorem: `mehlerOp = ouSemigroupAct` ✓ DONE

**Status**: discharged 2026-05-11. Theorem
`mehlerOp_eq_ouSemigroupAct` lives in
`GaussianHilbert/OUEigenfunctions.lean` (after
`ouSemigroupAct_eq_smul_of_mem_wienerChaos`), proved with only the
standard Mathlib axioms.

**Proof** (~70 lines): set
`A := coord ∘ mehlerOp − chaosDiagCLM ∘ coord` and show `A = 0`.
For each Wiener chaos `f ∈ wienerChaos n k`, both
`mehlerOp_eq_smul_of_mem_wienerChaos` and
`chaosDiagCLM_apply_single` collapse `A f` to `0`; hence
`wienerChaos n k ≤ A.ker` for every `k`. The closed kernel `A.ker` then
contains `(⨆ k, wienerChaos n k).topologicalClosure = ⊤` (totality
witness, see below), so `A = 0`. Reading off
`coord ∘ mehlerOp = chaosDiagCLM ∘ coord` and applying
`coord.symm` gives the operator identity.

**Companion refactor**: extracted the dense-iSup witness as a public
lemma `wienerChaos_iSup_topologicalClosure_eq_top` in
`GaussianHilbert/WienerChaos.lean`. This avoids triggering the
`∀ i, CompleteSpace (wienerChaos n i)` Pi-instance synthesis that
`OrthogonalFamily.linearIsometry` would force. The original
`wienerChaos_isHilbertSum` is now a two-line wrapper combining
orthogonality and the new totality lemma.

### Stage W (recommended) — LSI tensorization shortcut

**Goal**: prove that `stdGaussianFin n` satisfies the log-Sobolev
inequality LSI(1).

**Approach**: postulate **LSI tensorizes** with the same constant as
a single textbook axiom in markov-semigroups
(`Abstract/LogSobolev/Tensorization.lean` or similar). Then:

```lean
axiom lsi_tensorize {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] {μ : ∀ i, Measure (α i)}
    [∀ i, IsProbabilityMeasure (μ i)] {c : ℝ}
    (h : ∀ i, SatisfiesLogSobolev (μ i) c) :
    SatisfiesLogSobolev (Measure.pi μ) c

theorem stdGaussianFin_satisfiesLogSobolev (n : ℕ) :
    SatisfiesLogSobolev (stdGaussianFin n) 1 :=
  lsi_tensorize (fun _ => Gaussian1D.bakryEmerySpace.satisfiesLogSobolev)
```

**Trade-off**:
- **+1 well-cited textbook axiom** in markov-semigroups (Gross 1975;
  BGL §5.2.4 Proposition 5.2.7; this is a *standard* fact and Mathlib
  doesn't currently have it).
- **−1 week of work** vs the full BE instance.
- **No transitive dependency** on the markov-semigroups Gross axioms
  for *this* discharge (the Gross axioms ARE still needed downstream
  via `gross_lsi_implies_hypercontractive`, but that's a separate
  effort).

**Effort**: ~250 lines, ~5-7 days.

### Stage N (alternative) — full multivariate Bakry-Émery instance

**Goal**: build `stdGaussianFin.bakryEmerySpace n : BakryEmerySpace (Fin n → ℝ)`
with curvature ρ = 1, then `stdGaussianFin_satisfiesLogSobolev` follows
from `BakryEmerySpace.satisfiesLogSobolev`.

**Approach**: 16-field BE instance construction. Most fields are
routine; the load-bearing piece is the **Mehler-derivative
commutation lemma**

```
∂_i (M_t f)(x) = e^{-t} · M_t (∂_i f)(x)
```

(chain rule under the Gaussian integral via DCT) plus L²-contraction
per coordinate. Tensor-lift of the 4 BGL Ch. 2 axioms via Fubini
gives the entropy / L²-decay / `hasDerivWithinAt` fields.

**Trade-off**:
- **No new axioms** (transitively depends on the 4 BGL Ch. 2 axioms +
  2 Gross axioms in markov-semigroups, but those are already there).
- **+1 week of work** vs Route W.
- **Reusable**: a multivariate BE instance is useful for other
  downstream applications (Stein's method, Brascamp-Lieb, etc.).

**Effort**: ~600 lines, ~10-14 days.

### Stage E — wire-in

**Goal**: replace `axiom ouSemigroupAct_eLpNorm_hypercontractive` with
a theorem.

```lean
theorem ouSemigroupAct_eLpNorm_hypercontractive {n : ℕ}
    (p : ℝ) (hp : 2 ≤ p) (t : ℝ) (ht : 0 ≤ t)
    (h_nelson : p − 1 ≤ Real.exp (2 * t))
    (f : Lp ℝ 2 (stdGaussianFin n)) :
    eLpNorm ((ouSemigroupAct n t f : (Fin n → ℝ) → ℝ))
            (ENNReal.ofReal p) (stdGaussianFin n) ≤
      eLpNorm ((f : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) := by
  -- Translate gross_lsi_implies_hypercontractive applied to the
  -- (Mehler = spectral) semigroup with LSI constant 1.
  -- Nelson bound e^{2t} ≥ p − 1 with q = 2 reads off as the abstract
  -- HC predicate.
  sorry
```

The translation involves bridging the abstract `IsHypercontractive`
predicate from `markov-semigroups/Abstract/Hypercontractivity.lean` to
the concrete `ouSemigroupAct`-based statement. Typically a small
`simp`-able adapter.

**Effort**: ~50 lines, ~1-2 days.

---

## Total effort (revised 2026-05-15 after Lp-carrier Phase 1+2 + Phase 3 smoke test)

The 2026-05-13 → 2026-05-15 work in markov-semigroups (Lp-carrier
Phase 1 + 2) collapsed most of Stage N's "build BE → DirichletMarkovSemigroup
bridge" work into a delivered bundle. Stage N route is now strictly
preferable to Stage W — same time-to-completion, no new axioms, more
infrastructure preserved.

| Stage | Status | Remaining lines | Remaining days | New axioms |
|---|---|---|---|---|
| A — Mehler operator | ✅ **DONE** (~700 lines in OUEigenfunctions.lean) | 0 | 0 | 0 |
| Ag — Agreement theorem | ✅ **DONE** (~70-line proof, 2026-05-11) | 0 | 0 | 0 |
| N1 — multivariate BE instance (`stdGaussianFin.bakryEmerySpace`) | ✅ **DONE** (markov-semigroups main, commit `e1e2011`, before 2026-05-13) | 0 | 0 | 0 |
| Lp-carrier Phase 1 (abstract `MarkovSemigroup`/`DirichletMarkovSemigroup`) | ✅ **DONE** (markov-semigroups main, `e1e2011`) | 0 | 0 | 0 |
| Lp-carrier Phase 2 (`stdGaussianFin_dirichletMarkovSemigroup` bundle = the old N3 bridge) | ✅ **DONE** (markov-semigroups branch, commit `6782dc7`, 2026-05-15) | 0 | 0 | 0 (but introduces transitive `ouSemigroupFin_l2_sq_hasDerivWithinAt` via polarization — see Phase 2.5 below) |
| Phase 3 smoke test (gaussian-hilbert wire-in) | ✅ **DONE** (`phase-3-smoke-test`, commit `0f0c5eb`, 2026-05-15) | 0 | 0 | 0 |
| **E.1** — `h_lsi` adapter (transfer `BakryEmerySpace.satisfiesLogSobolev` through the new bundle) | not started | ~50-100 | 0.5-1 | 0 |
| **E.2** — predicate adapter (abstract `IsHypercontractive` → concrete `eLpNorm` form via `mehlerOp_eq_ouSemigroupAct`) | not started | ~50 | 0.5-1 | 0 |
| **Route N total (remaining)** | | **~100-150** | **~1-2 days** | **0** |

For reference: pre-Lp-carrier estimate had Route N at ~600 lines / 10-14
days because the BE → DirichletMarkovSemigroup bridge was assumed to be a
~16-field hand build. Phase 2 delivered that bridge as a usable bundle.

### Phase 2.5 follow-up (post-discharge cleanup, optional)

The Phase 2 bundle's `energy_eq_deriv` field was proved by polarization
from the existing markov-semigroups axiom
`ouSemigroupFin_l2_sq_hasDerivWithinAt` rather than the brief's preferred
fresh Fubini lift. This makes that axiom load-bearing at the public
DirichletMarkovSemigroup boundary (and therefore at gaussian-hilbert's
`stdGaussianFin_dirichletMarkovSemigroup` consumer site). The axiom is
already on the markov-semigroups discharge path with a dual-vetted
plan (Fubini lift through `ouSemigroupFin_insertNth_eq` and
`integral_γFin_succAbove`, ~1.5 active days). Discharging it eliminates
the polarization-introduced public-boundary axiom and drops the
markov-semigroups GaussianFin axiom count 11 → 10.

---

## Recommendation

**Route N (the only remaining path).** Stage W (LSI tensorization
shortcut) was the recommendation in the 2026-05-11 plan because Route N
was estimated at ~600 lines / 10-14 days. With Phase 2 delivered, Route N
is now ~100-150 lines / 1-2 days — strictly faster than Stage W
(~250 lines / 5-7 days) and avoids the +1 markov-semigroups axiom.

---

## Cross-repo dependencies

This discharge touches two repos:

* **gaussian-hilbert**: Stages A, Ag, E, and the route choice's local
  scaffolding.
* **markov-semigroups**: Route W needs the new `lsi_tensorize` axiom
  (a single-line declaration plus its docstring). Route N already
  uses the existing 4 BGL Ch. 2 + 2 Gross axioms; no new axioms
  needed.

Coordinated pin bumps required:
1. Add the `lsi_tensorize` axiom (Route W) or fully-built BE
   infrastructure (Route N) to markov-semigroups.
2. Bump gaussian-hilbert's `markov-semigroups` pin.
3. Land Stages A, Ag, E in gaussian-hilbert.

---

## Acceptance criteria

* `lake build` succeeds in gaussian-hilbert.
* The axiom keyword no longer appears at
  `GaussianHilbert/OUEigenfunctions.lean:724`.
* `#print axioms GaussianHilbert.ouSemigroupAct_eLpNorm_hypercontractive`
  yields **exactly**:
  - Route W: `[propext, Classical.choice, Quot.sound, MarkovSemigroups.lsi_tensorize, ...]`
    plus whatever Gross-cluster axioms `gross_lsi_implies_hypercontractive`
    transitively pulls in.
  - Route N: same Gross-cluster axioms without `lsi_tensorize`.
* `#print axioms GaussianHilbert.polynomial_chaos_concentration`
  similarly reflects the new transitive dependency on the Gross axioms
  (and `lsi_tensorize` if Route W).
* `AXIOM_AUDIT.md` and `STATUS.md` updated.

---

## Status

**~80% complete (2026-05-15).** Phase 2 + Phase 3 smoke test landed.
Remaining: ~1-2 active days of adapter work (E.1 + E.2). Phase 2.5
follow-up (Fubini-lift cleanup of the polarization-introduced axiom)
is independent and optional.

Pre-conditions all satisfied:
- Chaos infrastructure end-to-end axiom-free (2026-05-11 #print axioms).
- Multivariate BE instance proved (markov-semigroups main, `e1e2011`).
- Lp-carrier Phase 1+2 bundles proved (markov-semigroups
  `feat/lp-carrier-stdGaussianFin-dirichletmarkov`, `6782dc7`).
- Phase 3 smoke test compiling (gaussian-hilbert `phase-3-smoke-test`,
  `0f0c5eb`) — bundle reachable, slots into
  `gross_lsi_implies_hypercontractive`.

---

## Related plan docs

* [`ou-discharge-codex-plan.md`](ou-discharge-codex-plan.md) — Route 1
  (spectral shortcut, **DONE 2026-05-10**) and Route 2 (Mehler
  integral, which is Stage A of this plan).
* [`ou-mehler-discharge-plan.md`](ou-mehler-discharge-plan.md) — the
  older broader 5-stage plan. Stages B and C′ (Markov-semigroup laws +
  Hermite eigenvalues for the OU pair) are now superseded — the OU
  pair is already discharged via the spectral shortcut. Only Stage A,
  Stage C/C-β, and Stage E remain relevant, captured here.
* [`polynomial-density-codex-plan.md`](polynomial-density-codex-plan.md)
  — **DONE 2026-05-11** (via L²-orthogonal-complement / Carleman route,
  different from the 3-milestone Stone-Weierstrass plan).
