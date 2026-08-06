/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HSMixture.Q0DetLimit

/-!
# Task GA.2 — off-diagonal `G_{01}(z) → 0` for large σ-ratio (decay mechanism)

**Physical content (structural root cause of the unlike-pair divergence, Group GA).**  For `N = 2`
the GA-matrix off-diagonal entry `G_{01}(z) = [adj Q̂₀(z)]_{01} / det Q̂₀(z)` (`= −Q̂₀_{10}/det`).
From M.10's decomposition `Q̂₀ = P̂ + Ê·exp(−z·σ_min)` the off-diagonal *numerator* carries a factor
`exp(−z·(σ₁−σ₀)/2) → 0`, while `det Q̂₀(z)` tends to a nonzero limit (M.4).  Hence `G_{01}(z) → 0`
as `z → ∞`, so `(1 − G²) ≈ 1` and the large factor `exp(z·R_{01})` has **no** algebraic
cancellation — why GA.1's base diverges for unlike pairs but not the N=1 pair (C.2).

## What is proved here (the decay mechanism)

`g_mat_offdiag_decay` isolates the limit argument at the level that does not depend on the explicit
N=2 `Q̂₀` cofactor: given the numerator's exponential decay bound `|num z| ≤ C·exp(−z·λ)` (with
`λ = (σ₁−σ₀)/2 > 0`, the M.10-derived off-diagonal factor) and `det Q̂₀(z) → L ≠ 0` (M.4), the ratio
`num/den → 0`.  Helper `exp_neg_mul_atTop` supplies `exp(−z·λ) → 0`.

## Concrete N=2 cofactor (DONE)

The two hypotheses are now discharged from the explicit physical `Q0_mat_phys` in
`LeanCode/HSMixture/Q0DetLimit.lean`: `Q0_mat_phys_offdiag01_tendsto_zero` (the off-diagonal
entry `→ 0`) and `Q0_mat_phys_det_tendsto_one` (`det → 1 ≠ 0`). Instead of the literal global
bound `|Q̂₀_{01}(z)| ≤ C·exp(−z·(σ₁−σ₀)/2)` — which has no clean constant on all of `(0,∞)` (the
bracket is `O(1/z)`, blowing up as `z→0⁺`) — we use the stronger, sufficient
`Tendsto num atTop (𝓝 0)` via `g_mat_offdiag_decay'`. The final `g_mat_offdiag_decay_concrete`
gives `Q0_mat_phys(z) 0 1 / det Q0_mat_phys(z) → 0`. **Axiom-clean**: the nonzero limit `L = 1`
is *proved*, not assumed (no `Q0_moment_det_pos`).

Status: ✓ DONE (2026-07-15), axiom-clean — mechanism + concrete N=2 `Q̂₀` cofactor.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Filter Topology

open FMSA.MatrixQ0

namespace FMSA.OffDiagDecay

/-- `exp(−z·λ) → 0` as `z → ∞`, for `λ > 0`.  (The off-diagonal decay factor from M.10.) -/
theorem exp_neg_mul_atTop {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun z : ℝ => Real.exp (-z * lam)) atTop (𝓝 0) := by
  simp only [neg_mul]
  exact Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hlam))

/-- **Task GA.2 (decay mechanism, `Tendsto` form).**  If the off-diagonal numerator tends to `0`
and the determinant tends to a nonzero limit `L`, then `G_{01}(z) = num z / den z → 0`.  This is
the clean form the concrete N=2 discharge uses; the exponential-bound form `g_mat_offdiag_decay`
is a corollary. -/
theorem g_mat_offdiag_decay' {num den : ℝ → ℝ} {L : ℝ}
    (hnum : Tendsto num atTop (𝓝 0)) (hden : Tendsto den atTop (𝓝 L)) (hL : L ≠ 0) :
    Tendsto (fun z => num z / den z) atTop (𝓝 0) := by
  have h := hnum.div hden hL
  rwa [zero_div] at h

/-- **Task GA.2 (decay mechanism, exponential-bound form).**  If the off-diagonal numerator decays
exponentially, `|num z| ≤ C·exp(−z·λ)` with `λ > 0` (the M.10 factor `exp(−z·(σ₁−σ₀)/2)`), and the
determinant tends to a nonzero limit `den z → L ≠ 0`, then `G_{01}(z) = num z / den z → 0`.  Proof:
squeeze `num → 0` via `exp_neg_mul_atTop`, then apply `g_mat_offdiag_decay'`. -/
theorem g_mat_offdiag_decay {num den : ℝ → ℝ} {C lam L : ℝ}
    (hlam : 0 < lam)
    (hnum : ∀ z, |num z| ≤ C * Real.exp (-z * lam))
    (hden : Tendsto den atTop (𝓝 L)) (hL : L ≠ 0) :
    Tendsto (fun z => num z / den z) atTop (𝓝 0) := by
  have hnum0 : Tendsto num atTop (𝓝 0) := by
    apply squeeze_zero_norm hnum
    simpa using (exp_neg_mul_atTop hlam).const_mul C
  exact g_mat_offdiag_decay' hnum0 hden hL

/-- **Task GA.2 (concrete, N=2).**  For the explicit physical Baxter matrix `Q0_mat_phys` with
`σ₀ < σ₁` and a physical mixture (`η < 1` ⇔ `0 < vacMix`, `ρᵢ ≥ 0`, `σᵢ > 0`), the GA-matrix
off-diagonal ratio `Q0_mat_phys(z) 0 1 / det Q0_mat_phys(z) → 0` as `z → ∞`.  Discharges the two
mechanism hypotheses from `Q0DetLimit.lean`: the off-diagonal entry `→ 0`
(`Q0_mat_phys_offdiag01_tendsto_zero`) and `det → 1 ≠ 0` (`Q0_mat_phys_det_tendsto_one`).
**Axiom-clean** — the nonzero limit `L = 1` is *proved*, not assumed (no `Q0_moment_det_pos`). -/
theorem g_mat_offdiag_decay_concrete (sigma rho : Fin 2 → ℝ)
    (hσ : sigma 0 < sigma 1) (hvac : 0 < vacMix rho sigma) (hrho : ∀ i, 0 ≤ rho i)
    (hsig : ∀ i, 0 < sigma i) :
    Tendsto (fun z => Q0_mat_phys z sigma rho 0 1 / (Q0_mat_phys z sigma rho).det) atTop (𝓝 0) :=
  g_mat_offdiag_decay'
    (Q0_mat_phys_offdiag01_tendsto_zero sigma rho hσ hvac.ne' hrho hsig)
    (Q0_mat_phys_det_tendsto_one hvac.ne' hrho hsig)
    one_ne_zero

end FMSA.OffDiagDecay
