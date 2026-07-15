/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Task GA.2 — off-diagonal `G_{01}(z) → 0` for large σ-ratio (decay mechanism)

**Physical content (structural root cause of the unlike-pair divergence, Group GA).**  For `N = 2`
the GA-matrix off-diagonal entry `G_{01}(z) = [adj Q̂₀(z)]_{01} / det Q̂₀(z)` (`= −Q̂₀_{10}/det`).
From B.2's decomposition `Q̂₀ = P̂ + Ê·exp(−z·σ_min)` the off-diagonal *numerator* carries a factor
`exp(−z·(σ₁−σ₀)/2) → 0`, while `det Q̂₀(z)` tends to a nonzero limit (M.4).  Hence `G_{01}(z) → 0`
as `z → ∞`, so `(1 − G²) ≈ 1` and the large factor `exp(z·R_{01})` has **no** algebraic
cancellation — why GA.1's base diverges for unlike pairs but not the N=1 pair (C.2).

## What is proved here (the decay mechanism)

`g_mat_offdiag_decay` isolates the limit argument at the level that does not depend on the explicit
N=2 `Q̂₀` cofactor: given the numerator's exponential decay bound `|num z| ≤ C·exp(−z·λ)` (with
`λ = (σ₁−σ₀)/2 > 0`, the B.2-derived off-diagonal factor) and `det Q̂₀(z) → L ≠ 0` (M.4), the ratio
`num/den → 0`.  Helper `exp_neg_mul_atTop` supplies `exp(−z·λ) → 0`.

## Deferred (the concrete N=2 cofactor)

Discharging the two hypotheses — proving `|Q̂₀_{01}(z)| ≤ C·exp(−z·(σ₁−σ₀)/2)` and
`det Q̂₀(z) → L ≠ 0` from the explicit N=2 `Q0_mat` (B.2) — is the remaining high-effort step, left
for a follow-up (needs the B.2 entry formula + a dominated exp-decay estimate).

Status: ◑ decay mechanism DONE (2026-07-15), axiom-clean; concrete N=2 `Q̂₀` cofactor deferred.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Filter Topology

namespace FMSA.OffDiagDecay

/-- `exp(−z·λ) → 0` as `z → ∞`, for `λ > 0`.  (The off-diagonal decay factor from B.2.) -/
theorem exp_neg_mul_atTop {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun z : ℝ => Real.exp (-z * lam)) atTop (𝓝 0) := by
  simp only [neg_mul]
  exact Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hlam))

/-- **Task GA.2 (decay mechanism).**  If the off-diagonal numerator decays exponentially,
`|num z| ≤ C·exp(−z·λ)` with `λ > 0` (the B.2 factor `exp(−z·(σ₁−σ₀)/2)`), and the determinant
tends to a nonzero limit, `den z → L ≠ 0` (M.4), then the GA-matrix off-diagonal entry
`G_{01}(z) = num z / den z → 0` as `z → ∞`.  Proof: squeeze `num → 0` via `exp_neg_mul_atTop`,
then `num/den → 0/L = 0`. -/
theorem g_mat_offdiag_decay {num den : ℝ → ℝ} {C lam L : ℝ}
    (hlam : 0 < lam)
    (hnum : ∀ z, |num z| ≤ C * Real.exp (-z * lam))
    (hden : Tendsto den atTop (𝓝 L)) (hL : L ≠ 0) :
    Tendsto (fun z => num z / den z) atTop (𝓝 0) := by
  have hnum0 : Tendsto num atTop (𝓝 0) := by
    apply squeeze_zero_norm hnum
    simpa using (exp_neg_mul_atTop hlam).const_mul C
  have h := hnum0.div hden hL
  rw [zero_div] at h
  exact h

end FMSA.OffDiagDecay
