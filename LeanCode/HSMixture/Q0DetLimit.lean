/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HSMixture.Q0DetRankTwo

/-!
# Large-`z` limits of the physical Baxter matrix `Q0_mat_phys` (support for Task GA.2)

This file is the **limits (`Tendsto`) layer** on top of the rank-2 apparatus in
`Q0DetRankTwo.lean` (Tasks M.4–M.8). It proves the two facts the Task GA.2 mechanism
(`FMSA.OffDiagDecay.g_mat_offdiag_decay`) needs, from the *explicit* physical matrix:

* `Q0_mat_phys_offdiag01_tendsto_zero` — the off-diagonal entry `Q0_mat_phys(z) 0 1 → 0`
  (for `σ₀ < σ₁`), and
* `Q0_mat_phys_det_tendsto_one` — `det Q0_mat_phys(z) → 1` (so the determinant tends to a
  **nonzero** limit `L = 1`; **axiom-clean** — this does NOT use the `Q0_moment_det_pos` axiom).

Everything reduces to one pair of atomic analytic facts, `p1(σ,z) → 0` and `p2(σ,z) → 0` as
`z → ∞` (`σ > 0`), propagated through the existing `fFun`/`gFun`/`Umat`/`Vmat` definitions and
the `Q0_mat_phys = 1 − U·V` / `det = det(1 − V·U)` reductions. The determinant stays bounded (→1)
even though individual off-diagonal entries blow up as `z → ∞`, because the reduced 2×2 `V·U`
entries are `∑ⱼ ρⱼ·(…)` sums in which the `exp(zσⱼ/2)·exp(−zσⱼ/2) = 1` cancellation removes the
`z`-growth — the structural reason the FMSA GA-matrix-mix "2YK" construction diverges for unlike
pairs (Group GA).
-/

set_option linter.style.longLine false

open Filter Topology Real

namespace FMSA.MatrixQ0

/-! ### Atomic limits: `p1, p2 → 0` -/

/-- `exp(-(z·σ)) → 0` as `z → ∞` for `σ > 0`. -/
theorem exp_neg_scaled_tendsto {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun z : ℝ => Real.exp (-(z * σ))) atTop (𝓝 0) := by
  have h : Tendsto (fun z : ℝ => -(z * σ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hσ)
  exact Real.tendsto_exp_atBot.comp h

/-- `p1(σ,z) = (1 − zσ − e^{−zσ})/z² → 0` as `z → ∞`, for `σ > 0`. -/
theorem p1_tendsto_zero {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun z : ℝ => p1 σ z) atTop (𝓝 0) := by
  have h1 : Tendsto (fun z : ℝ => (z ^ 2)⁻¹) atTop (𝓝 0) :=
    (tendsto_pow_atTop (by norm_num)).inv_tendsto_atTop
  have h2 : Tendsto (fun z : ℝ => σ * z⁻¹) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.const_mul σ; rwa [mul_zero] at this
  have h3 : Tendsto (fun z : ℝ => Real.exp (-(z * σ)) * (z ^ 2)⁻¹) atTop (𝓝 0) := by
    have := (exp_neg_scaled_tendsto hσ).mul h1; rwa [mul_zero] at this
  have hcongr : (fun z : ℝ => p1 σ z) =ᶠ[atTop]
      (fun z => (z ^ 2)⁻¹ - σ * z⁻¹ - Real.exp (-(z * σ)) * (z ^ 2)⁻¹) := by
    filter_upwards [eventually_gt_atTop 0] with z hz
    have hz' : z ≠ 0 := hz.ne'
    unfold p1
    field_simp
    try ring
  rw [tendsto_congr' hcongr]
  have := (h1.sub h2).sub h3
  simpa using this

/-- `p2(σ,z) = (1 − zσ + (zσ)²/2 − e^{−zσ})/z³ → 0` as `z → ∞`, for `σ > 0`. -/
theorem p2_tendsto_zero {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun z : ℝ => p2 σ z) atTop (𝓝 0) := by
  have h1 : Tendsto (fun z : ℝ => (z ^ 3)⁻¹) atTop (𝓝 0) :=
    (tendsto_pow_atTop (by norm_num)).inv_tendsto_atTop
  have h2 : Tendsto (fun z : ℝ => σ * (z ^ 2)⁻¹) atTop (𝓝 0) := by
    have hp : Tendsto (fun z : ℝ => (z ^ 2)⁻¹) atTop (𝓝 0) :=
      (tendsto_pow_atTop (n := 2) (by norm_num)).inv_tendsto_atTop
    have := hp.const_mul σ; rwa [mul_zero] at this
  have h3 : Tendsto (fun z : ℝ => σ ^ 2 / 2 * z⁻¹) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.const_mul (σ ^ 2 / 2); rwa [mul_zero] at this
  have h4 : Tendsto (fun z : ℝ => Real.exp (-(z * σ)) * (z ^ 3)⁻¹) atTop (𝓝 0) := by
    have := (exp_neg_scaled_tendsto hσ).mul h1; rwa [mul_zero] at this
  have hcongr : (fun z : ℝ => p2 σ z) =ᶠ[atTop]
      (fun z => (z ^ 3)⁻¹ - σ * (z ^ 2)⁻¹ + σ ^ 2 / 2 * z⁻¹ - Real.exp (-(z * σ)) * (z ^ 3)⁻¹) := by
    filter_upwards [eventually_gt_atTop 0] with z hz
    have hz' : z ≠ 0 := hz.ne'
    unfold p2
    field_simp
    try ring
  rw [tendsto_congr' hcongr]
  have := ((h1.sub h2).add h3).sub h4
  simpa using this

/-! ### Propagation to `fFun`, `gFun`, and the reduced `Vmat*Umat` entries -/

/-- `fFun rho sigma i z → 0` as `z → ∞`. -/
theorem fFun_tendsto_zero {N : ℕ} {rho sigma : Fin N → ℝ} (i : Fin N) (hsig : 0 < sigma i) :
    Tendsto (fun z : ℝ => fFun rho sigma i z) atTop (𝓝 0) := by
  have hp1 := p1_tendsto_zero (σ := sigma i) hsig
  have hp2 := p2_tendsto_zero (σ := sigma i) hsig
  have ha : Tendsto (fun z : ℝ => p1 (sigma i) z * sigma i) atTop (𝓝 0) := by
    have := hp1.mul_const (sigma i); rwa [zero_mul] at this
  have hb : Tendsto (fun z : ℝ => 2 * p2 (sigma i) z) atTop (𝓝 0) := by
    have := hp2.const_mul (2 : ℝ); rwa [mul_zero] at this
  have hcomb : Tendsto (fun z : ℝ => p1 (sigma i) z * sigma i + 2 * p2 (sigma i) z) atTop (𝓝 0) := by
    have := ha.add hb; simpa using this
  unfold fFun
  have := hcomb.const_mul (Real.pi / vacMix rho sigma); rwa [mul_zero] at this

/-- `gFun rho sigma i z → 0` as `z → ∞`. -/
theorem gFun_tendsto_zero {N : ℕ} {rho sigma : Fin N → ℝ} (i : Fin N) (hsig : 0 < sigma i) :
    Tendsto (fun z : ℝ => gFun rho sigma i z) atTop (𝓝 0) := by
  have hp1 := p1_tendsto_zero (σ := sigma i) hsig
  have hp2 := p2_tendsto_zero (σ := sigma i) hsig
  have hterm1 : Tendsto (fun z : ℝ => Real.pi / vacMix rho sigma * p1 (sigma i) z) atTop (𝓝 0) := by
    have := hp1.const_mul (Real.pi / vacMix rho sigma); rwa [mul_zero] at this
  have ha : Tendsto (fun z : ℝ => p1 (sigma i) z * sigma i / 2) atTop (𝓝 0) := by
    have := (hp1.mul_const (sigma i)).div_const (2 : ℝ)
    simpa using this
  have hcomb : Tendsto (fun z : ℝ => p1 (sigma i) z * sigma i / 2 + p2 (sigma i) z) atTop (𝓝 0) := by
    have := ha.add hp2; simpa using this
  have hterm2 : Tendsto (fun z : ℝ => Real.pi ^ 2 * xi2 rho sigma / vacMix rho sigma ^ 2 *
      (p1 (sigma i) z * sigma i / 2 + p2 (sigma i) z)) atTop (𝓝 0) := by
    have := hcomb.const_mul (Real.pi ^ 2 * xi2 rho sigma / vacMix rho sigma ^ 2)
    rwa [mul_zero] at this
  unfold gFun
  have := hterm1.add hterm2; simpa using this

/-- General `Vmat*Umat` entry (any `(k,l)`): `√ρ·√ρ = ρ` and the `exp` cancellation.
Generalizes `VU_apply_00` from `Q0DetRankTwo.lean`. -/
theorem VU_apply {N : ℕ} (z : ℝ) (sigma rho : Fin N → ℝ) (hrho : ∀ j, 0 ≤ rho j) (k l : Fin 2) :
    (Vmat z sigma rho * Umat z sigma rho) k l =
      ∑ j, rho j * (if k = 0 then 1 else sigma j) *
        (if l = 0 then fFun rho sigma j z else gFun rho sigma j z) := by
  simp only [Matrix.mul_apply, Umat, Vmat, Fin.isValue]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hsq : Real.sqrt (rho j) * Real.sqrt (rho j) = rho j := Real.mul_self_sqrt (hrho j)
  have hexp : Real.exp (-(z * sigma j / 2)) * Real.exp (z * sigma j / 2) = 1 := by
    rw [← Real.exp_add]; norm_num
  have hkey :
      Real.sqrt (rho j) * Real.exp (-(z * sigma j / 2)) * (if k = 0 then 1 else sigma j) *
        (Real.sqrt (rho j) * Real.exp (z * sigma j / 2) *
          (if l = 0 then fFun rho sigma j z else gFun rho sigma j z)) =
      Real.sqrt (rho j) * Real.sqrt (rho j) *
        (Real.exp (-(z * sigma j / 2)) * Real.exp (z * sigma j / 2)) *
        ((if k = 0 then 1 else sigma j) *
          (if l = 0 then fFun rho sigma j z else gFun rho sigma j z)) := by ring
  rw [hkey, hsq, hexp]
  ring

/-- Each `Vmat*Umat` entry → 0 as `z → ∞` (finite species-sum of `fFun`/`gFun`, all → 0). -/
theorem VU_entry_tendsto_zero {N : ℕ} {sigma rho : Fin N → ℝ}
    (hrho : ∀ j, 0 ≤ rho j) (hsig : ∀ j, 0 < sigma j) (k l : Fin 2) :
    Tendsto (fun z : ℝ => (Vmat z sigma rho * Umat z sigma rho) k l) atTop (𝓝 0) := by
  have hfun : (fun z : ℝ => (Vmat z sigma rho * Umat z sigma rho) k l) =
      (fun z : ℝ => ∑ j, rho j * (if k = 0 then 1 else sigma j) *
        (if l = 0 then fFun rho sigma j z else gFun rho sigma j z)) :=
    funext (fun z => VU_apply z sigma rho hrho k l)
  rw [hfun]
  have hsum : Tendsto (fun z : ℝ => ∑ j, rho j * (if k = 0 then 1 else sigma j) *
        (if l = 0 then fFun rho sigma j z else gFun rho sigma j z))
        atTop (𝓝 (∑ _j : Fin N, (0:ℝ))) := by
    apply tendsto_finsetSum
    intro j _
    have hcoeff : Tendsto (fun z : ℝ => if l = 0 then fFun rho sigma j z else gFun rho sigma j z)
        atTop (𝓝 0) := by
      by_cases hl : l = 0
      · simp only [hl, if_true]; exact fFun_tendsto_zero j (hsig j)
      · simp only [hl, if_false]; exact gFun_tendsto_zero j (hsig j)
    have := hcoeff.const_mul (rho j * (if k = 0 then 1 else sigma j))
    rw [mul_zero] at this
    simpa [mul_assoc] using this
  simpa using hsum

/-! ### The two facts Task GA.2 needs -/

/-- **`det Q0_mat_phys(z) → 1` as `z → ∞`** (any `n`): the reduced 2×2 determinant
`(1−VU₀₀)(1−VU₁₁) − VU₀₁·VU₁₀ → 1·1 − 0·0 = 1`. Axiom-clean; supplies the nonzero limit `L = 1`. -/
theorem Q0_mat_phys_det_tendsto_one {N : ℕ} {sigma rho : Fin N → ℝ}
    (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i) (hsig : ∀ i, 0 < sigma i) :
    Tendsto (fun z : ℝ => (Q0_mat_phys z sigma rho).det) atTop (𝓝 1) := by
  have hcongr : (fun z : ℝ => (Q0_mat_phys z sigma rho).det) =ᶠ[atTop]
      (fun z => (1 - (Vmat z sigma rho * Umat z sigma rho) 0 0) *
                  (1 - (Vmat z sigma rho * Umat z sigma rho) 1 1) -
                (Vmat z sigma rho * Umat z sigma rho) 0 1 *
                  (Vmat z sigma rho * Umat z sigma rho) 1 0) := by
    filter_upwards [eventually_ne_atTop 0] with z hz
    rw [Q0_mat_phys_det_eq_two_by_two hz hvac hrho, Matrix.det_fin_two]
    simp [Matrix.sub_apply]
  rw [tendsto_congr' hcongr]
  have h00 := VU_entry_tendsto_zero hrho hsig 0 0
  have h11 := VU_entry_tendsto_zero hrho hsig 1 1
  have h01 := VU_entry_tendsto_zero hrho hsig 0 1
  have h10 := VU_entry_tendsto_zero hrho hsig 1 0
  have hc : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hf1 : Tendsto (fun z : ℝ => 1 - (Vmat z sigma rho * Umat z sigma rho) 0 0) atTop (𝓝 1) := by
    have := hc.sub h00; simpa using this
  have hf2 : Tendsto (fun z : ℝ => 1 - (Vmat z sigma rho * Umat z sigma rho) 1 1) atTop (𝓝 1) := by
    have := hc.sub h11; simpa using this
  have hprod1 := hf1.mul hf2
  have hprod2 := h01.mul h10
  have := hprod1.sub hprod2
  simpa using this

/-- **Off-diagonal entry `Q0_mat_phys(z) 0 1 → 0`** for the physical N=2 mixture with `σ₀ < σ₁`.
`Q0_mat_phys = 1 − U·V` ⇒ entry(0,1) `= −(U·V)₀₁ = −√(ρ₀ρ₁)·exp(−((σ₁−σ₀)/2)z)·(fFun 0 + gFun 0·σ₁)`;
both `exp(−λz) → 0` (`λ = (σ₁−σ₀)/2 > 0`) and the bracket `→ 0`. -/
theorem Q0_mat_phys_offdiag01_tendsto_zero (sigma rho : Fin 2 → ℝ)
    (hσ : sigma 0 < sigma 1) (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i)
    (hsig : ∀ i, 0 < sigma i) :
    Tendsto (fun z : ℝ => Q0_mat_phys z sigma rho 0 1) atTop (𝓝 0) := by
  have hcongr : (fun z : ℝ => Q0_mat_phys z sigma rho 0 1) =ᶠ[atTop]
      (fun z => -(Real.sqrt (rho 0 * rho 1) * Real.exp (-((sigma 1 - sigma 0) / 2 * z)) *
                  (fFun rho sigma 0 z + gFun rho sigma 0 z * sigma 1))) := by
    filter_upwards [eventually_ne_atTop 0] with z hz
    rw [Q0_mat_phys_eq_one_sub_mul hz hvac hrho, Matrix.sub_apply, Matrix.one_apply,
        UV_apply z sigma rho hrho 0 1]
    simp
  rw [tendsto_congr' hcongr]
  have hlam : 0 < (sigma 1 - sigma 0) / 2 := by linarith
  have hexp : Tendsto (fun z : ℝ => Real.exp (-((sigma 1 - sigma 0) / 2 * z))) atTop (𝓝 0) := by
    simpa [mul_comm] using exp_neg_scaled_tendsto (σ := (sigma 1 - sigma 0) / 2) hlam
  have hbr : Tendsto (fun z : ℝ => fFun rho sigma 0 z + gFun rho sigma 0 z * sigma 1)
      atTop (𝓝 0) := by
    have hf := fFun_tendsto_zero (rho := rho) (sigma := sigma) 0 (hsig 0)
    have hg := gFun_tendsto_zero (rho := rho) (sigma := sigma) 0 (hsig 0)
    have hg' : Tendsto (fun z : ℝ => gFun rho sigma 0 z * sigma 1) atTop (𝓝 0) := by
      have := hg.mul_const (sigma 1); rwa [zero_mul] at this
    have := hf.add hg'; simpa using this
  have hAB : Tendsto (fun z : ℝ => Real.sqrt (rho 0 * rho 1) *
      Real.exp (-((sigma 1 - sigma 0) / 2 * z))) atTop (𝓝 0) := by
    have := hexp.const_mul (Real.sqrt (rho 0 * rho 1)); rwa [mul_zero] at this
  have hABC : Tendsto (fun z : ℝ => Real.sqrt (rho 0 * rho 1) *
      Real.exp (-((sigma 1 - sigma 0) / 2 * z)) *
      (fFun rho sigma 0 z + gFun rho sigma 0 z * sigma 1)) atTop (𝓝 0) := by
    have := hAB.mul hbr; rwa [mul_zero] at this
  have := hABC.neg; simpa using this

end FMSA.MatrixQ0
