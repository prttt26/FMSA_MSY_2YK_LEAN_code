/-
Copyright (c) 2026. All rights reserved.
-/
import LeanCode.HSMixture.Q0DetRankTwo
import LeanCode.Analysis.ExpTaylorLimits

/-!
# `det(Q̂₀) ≥ 1` and the `z → 0` removable values (`OZFIX.17` — the `k=0` compressibility)

The origin value of the matrix Baxter determinant — the `s = 0` removable limit `c` of
`det Q̂₀`, physically the `k = 0` structure factor = **compressibility** — must be nonzero for the
homotopy `hreal` at `z = 0`.  `pyhs_mixture_no_spinodal` is stated with `k ≠ 0` and does not reach it.

This file provides the strict bound.  `moment_key` in fact gives `ad − bc ≥ a + d`, so the `2×2`
determinant `det = 1 − (a+d) + (ad − bc) ≥ 1` (`Q0_moment_det_ge_one`, `Q0_mat_phys_det_ge_one`) — a
strict-with-margin bound that **survives the `z → 0` limit**: `Re(c) = lim_{z→0⁺} det ≥ 1`.
Together with the real removable values `p1 → −σ²/2`, `p2 → σ³/6` (`p1_tendsto_zero_nhds`,
`p2_tendsto_zero_nhds`, from the complex `phi1_tendsto`/`phi2_tendsto` via `ofReal`), this is the
analytic input to `c ≠ 0` (`MixtureDetOrigin.lean`).  **Axiom-clean** — no physics axiom.
-/

open Filter Topology

namespace FMSA.MatrixQ0
noncomputable section

/-- `ofReal` maps the real punctured neighbourhood of `0` into the complex one. -/
theorem ofReal_tendsto_nhdsNE : Tendsto (Complex.ofReal) (𝓝[≠] (0:ℝ)) (𝓝[≠] (0:ℂ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
    exact Complex.ofReal_ne_zero.mpr hz

/-- `p1(σ,z) → −σ²/2` as `z → 0` (real removable value of the Baxter `φ₁` kernel). -/
theorem p1_tendsto_zero_nhds {σ : ℝ} (hσ : σ ≠ 0) :
    Tendsto (fun z : ℝ => p1 σ z) (𝓝[≠] (0:ℝ)) (𝓝 (-σ ^ 2 / 2)) := by
  rw [← tendsto_ofReal_iff]
  have heq : (fun z : ℝ => ((p1 σ z : ℝ) : ℂ))
      = (fun s : ℂ => (1 - s * (σ : ℂ) - Complex.exp (-(s * (σ : ℂ)))) / s ^ 2) ∘ Complex.ofReal := by
    funext z; simp only [Function.comp_apply, p1]; push_cast [Complex.ofReal_exp]; ring
  rw [heq, show (((-σ ^ 2 / 2 : ℝ)) : ℂ) = -(σ : ℂ) ^ 2 / 2 by push_cast; ring]
  exact (FMSA.ExpTaylorLimits.phi1_tendsto (σ : ℂ) (Complex.ofReal_ne_zero.mpr hσ)).comp
    ofReal_tendsto_nhdsNE

/-- `p2(σ,z) → σ³/6` as `z → 0` (real removable value of the Baxter `φ₂` kernel). -/
theorem p2_tendsto_zero_nhds {σ : ℝ} (hσ : σ ≠ 0) :
    Tendsto (fun z : ℝ => p2 σ z) (𝓝[≠] (0:ℝ)) (𝓝 (σ ^ 3 / 6)) := by
  rw [← tendsto_ofReal_iff]
  have heq : (fun z : ℝ => ((p2 σ z : ℝ) : ℂ))
      = (fun s : ℂ => (1 - s * (σ : ℂ) + (s * (σ : ℂ)) ^ 2 / 2 - Complex.exp (-(s * (σ : ℂ)))) / s ^ 3)
          ∘ Complex.ofReal := by
    funext z; simp only [Function.comp_apply, p2]; push_cast [Complex.ofReal_exp]; ring
  rw [heq, show (((σ ^ 3 / 6 : ℝ)) : ℂ) = (σ : ℂ) ^ 3 / 6 by push_cast; ring]
  exact (FMSA.ExpTaylorLimits.phi2_tendsto (σ : ℂ) (Complex.ofReal_ne_zero.mpr hσ)).comp
    ofReal_tendsto_nhdsNE

/-- **`det(Q̂₀) ≥ 1`** (stronger than `Q0_moment_det_pos`): `moment_key` gives `ad − bc ≥ a + d`, so
`det = 1 − (a+d) + (ad − bc) ≥ 1`.  The margin survives the `z → 0` limit. -/
theorem Q0_moment_det_ge_one {N : ℕ} {z : ℝ} {sigma rho : Fin N → ℝ}
    (hz : 0 < z) (hvac : 0 < vacMix rho sigma) (hrho : ∀ i, 0 ≤ rho i) (hsigma : ∀ i, 0 < sigma i) :
    1 ≤ (1 - (Vmat z sigma rho * Umat z sigma rho) 0 0) *
          (1 - (Vmat z sigma rho * Umat z sigma rho) 1 1) -
        (Vmat z sigma rho * Umat z sigma rho) 0 1 * (Vmat z sigma rho * Umat z sigma rho) 1 0 := by
  have h00 : (Vmat z sigma rho * Umat z sigma rho) 0 0 = ∑ j, rho j * fFun rho sigma j z := by
    rw [VU_apply' z sigma rho hrho]; simp
  have h01 : (Vmat z sigma rho * Umat z sigma rho) 0 1 = ∑ j, rho j * gFun rho sigma j z := by
    rw [VU_apply' z sigma rho hrho]; simp
  have h10 : (Vmat z sigma rho * Umat z sigma rho) 1 0 = ∑ k, rho k * sigma k * fFun rho sigma k z := by
    rw [VU_apply' z sigma rho hrho]; simp
  have h11 : (Vmat z sigma rho * Umat z sigma rho) 1 1 = ∑ k, rho k * sigma k * gFun rho sigma k z := by
    rw [VU_apply' z sigma rho hrho]; simp
  rw [h00, h01, h10, h11]; nlinarith [moment_key hz hvac hrho hsigma]

/-- **`1 ≤ det Q0_mat_phys(z)` for `z > 0`, any `N`.**  The Woodbury reduction
`det Q̂₀ = det(1 − VU)` (`Q0_mat_phys_det_eq_two_by_two`) has the *same* `2×2` reduced matrix for
every `N`, so `Q0_moment_det_ge_one`'s general-`N` bound `1 ≤ (1−(VU)₀₀)(1−(VU)₁₁) − (VU)₀₁(VU)₁₀`
gives `1 ≤ det Q̂₀`.  The margin survives `z → 0` (the `k=0` compressibility). -/
theorem Q0_mat_phys_det_ge_one_N {N : ℕ} {z : ℝ} {sigma rho : Fin N → ℝ}
    (hz : 0 < z) (hvac : 0 < vacMix rho sigma) (hrho : ∀ i, 0 ≤ rho i) (hsigma : ∀ i, 0 < sigma i) :
    1 ≤ (Q0_mat_phys z sigma rho).det := by
  rw [Q0_mat_phys_det_eq_two_by_two hz.ne' hvac.ne' hrho, Matrix.det_fin_two]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply]
  have hkey := Q0_moment_det_ge_one hz hvac hrho hsigma
  simp only [Matrix.mul_apply] at hkey
  norm_num at hkey ⊢; linarith [hkey]

/-- `1 ≤ det Q0_mat_phys(z)` for `z > 0` (`N = 2`, the `Fin 2`-specialised wrapper). -/
theorem Q0_mat_phys_det_ge_one {z : ℝ} {sigma rho : Fin 2 → ℝ}
    (hz : 0 < z) (hvac : 0 < vacMix rho sigma) (hrho : ∀ i, 0 ≤ rho i) (hsigma : ∀ i, 0 < sigma i) :
    1 ≤ (Q0_mat_phys z sigma rho).det :=
  Q0_mat_phys_det_ge_one_N hz hvac hrho hsigma

end
end FMSA.MatrixQ0
