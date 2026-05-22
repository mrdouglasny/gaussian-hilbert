# Gemini deep-think query — spectral-shortcut OU vetting

I'm planning a Lean 4 / Mathlib formalization step and want a deep
mathematical + architectural vet before handing off to a coding agent
(codex).

## Setup

`gaussian-hilbert` is a Lean 4 project building Wiener chaos /
multivariate-Hermite analysis on `L²(γ_n)` where
`γ_n = stdGaussianFin n` is the n-D standard Gaussian on `Fin n → ℝ`.

Already proved (no axioms):

- `wienerChaos n k : Submodule ℝ (Lp ℝ 2 (stdGaussianFin n))` — k-th
  Wiener chaos, defined as `(Submodule.span ℝ {hermiteMultiLp α | totalDegree α = k}).topologicalClosure`.
- `wienerChaos_isHilbertSum n : IsHilbertSum ℝ (fun k : ℕ => wienerChaos n k) (Lp ℝ 2 (stdGaussianFin n))` —
  the orthogonal Hilbert-sum decomposition.
- `chaosCoordEquiv n : Lp ℝ 2 (stdGaussianFin n) ≃ₗᵢ[ℝ] lp (fun k : ℕ => wienerChaos n k) 2` —
  the resulting coordinate isometry.

## Goal

Replace two opaque axioms with theorems:

1. `ouSemigroupAct (n : ℕ) (t : ℝ) : Lp ℝ 2 (stdGaussianFin n) →L[ℝ] Lp ℝ 2 (stdGaussianFin n)`
   (currently an opaque CLM declaration).
2. `ouSemigroupAct_eq_smul_of_mem_wienerChaos {n k} (t) (ht : 0 ≤ t) (f) (hf : f ∈ wienerChaos n k) :
       ouSemigroupAct n t f = Real.exp (-(k : ℝ) * t) • f`.

A third axiom `ouSemigroupAct_eLpNorm_hypercontractive`
(Bonami-Beckner-Nelson) is OUT OF SCOPE — we keep it as an axiom for
now. It asserts
`‖ouSemigroupAct n t f‖_{Lp} ≤ ‖f‖_{L²}` for `e^{2t} ≥ p-1`.

## Two candidate routes

### Route A (Mehler integral, traditional)

Build `ouSemigroupAct` as the L²-CLM lifting of the Mehler integral

  `(M_t f)(x) = ∫ f(e^{-t}·x + √(1-e^{-2t})·y) dγ_n(y)`.

Then prove the chaos-eigenvalue equation by induction on k + Stein's
lemma + Hermite recurrence (the "induction + Stein" route, no DCT, no
infinite series).

Estimated 2-3 weeks Lean work.

### Route B (SPECTRAL SHORTCUT)

Define `ouSemigroupAct` *directly* as the spectral diagonal on the
chaos decomposition:

```
chaosDecay k t := Real.exp (-(k : ℝ) * t)
chaosDiagCLM n t ht :
  lp (fun k : ℕ => wienerChaos n k) 2 →L[ℝ] lp (fun k : ℕ => wienerChaos n k) 2
chaosDiagCLM acts as: f ↦ (k ↦ chaosDecay k t • f k)

ouSemigroupAct n t :=
  if ht : 0 ≤ t then
    chaosCoordEquiv⁻¹ ∘ chaosDiagCLM n t ht ∘ chaosCoordEquiv
  else 0
```

The chaos-eigenvalue theorem is then near-definitional: for
`f ∈ wienerChaos n k`,
`chaosCoordEquiv f = lp.single 2 k ⟨f, hf⟩` (by
`IsHilbertSum.linearIsometryEquiv_symm_apply_single`), `chaosDiagCLM`
applied to a single-supported `lp` element is
`chaosDecay k t • lp.single 2 k x`, and the inverse equiv recovers
`e^{-kt} • f`.

Estimated 3-5 days (~150-300 lines).

## My questions for the deep vet

1. **Mathematical correctness**: Is the spectral-shortcut Route B's
   `ouSemigroupAct` mathematically equal to "the" OU semigroup on
   `L²(γ_n)` as understood in the literature (Bakry-Émery / Janson)?
   Or is it merely a *spectrally-correct* operator that happens to
   satisfy the chaos-eigenvalue equation, while not necessarily being
   the actual Markov OU semigroup?

2. **Sufficiency for downstream consumers**: The downstream consumers
   in this codebase use `ouSemigroupAct` only via:

   (a) The chaos-eigenvalue equation (Route B makes this trivial).

   (b) The Bonami-Nelson hypercontractive bound (kept as axiom for
   now — `ouSemigroupAct_eLpNorm_hypercontractive`).

   The hypercontractivity axiom asserts
   `‖ouSemigroupAct n t f‖_{Lp} ≤ ‖f‖_{L²}` for `e^{2t} ≥ p-1`. This
   bound is a *property* of the textbook OU semigroup (proved via
   Bakry-Émery curvature 1 + Gross). If Route B's `ouSemigroupAct` is
   provably equal to the textbook OU semigroup, the hypercontractivity
   axiom is correct as stated. If Route B's `ouSemigroupAct` is some
   *other* operator that just happens to act diagonally on chaos with
   `e^{-kt}`, the hypercontractivity claim *about that other operator*
   might not hold.

   So the key question: is the spectral diagonal
   `f ↦ ∑_k e^{-kt} P_k f` (where `P_k` is the orthogonal projection
   onto `wienerChaos n k`) **the same operator** as the Mehler
   integral `f ↦ ∫ f(e^{-t}·x + √(1-e^{-2t})·y) dγ(y)` on `L²(γ_n)`?

3. **Spectral theorem application**: My understanding is yes, they ARE
   the same operator — the Mehler integral has L² spectral
   decomposition with eigenvalues `e^{-kt}` on the k-th chaos, and the
   spectral theorem says any bounded normal operator equals its
   spectral integral. So the spectral diagonal is the spectral form of
   the Mehler operator. But I want this confirmed — particularly
   whether there are subtle issues about:

   (a) self-adjointness vs normalcy,

   (b) needing C₀-semigroup continuity in t,

   (c) the boundary behavior at k → ∞ in the `lp(wienerChaos)` model.

4. **Lean-architectural concerns**: Is there any reason to prefer
   Route A over Route B for the *Lean formalization* (ignoring time)?
   E.g., does Route B create some unprovable obligation later (like
   proving Markovianity / positivity) that would force us back to
   Route A?

5. **Spectral-shortcut completeness**: To make Route B's
   `ouSemigroupAct` agree with the textbook OU semigroup, would we
   need to *additionally* prove the integral formula

   `(ouSemigroupAct n t f)(x) = ∫ f(e^{-t}·x + √(1-e^{-2t})·y) dγ_n(y) for a.e. x`

   Or does the spectral-on-chaos definition already pin down a unique
   operator (yes, by spectral uniqueness, but does Lean see it that
   way)?

Please assess: is Route B safe to ship, both mathematically and as a
basis for the hypercontractivity axiom? Are there warnings I should
add to the codex hand-off plan?
