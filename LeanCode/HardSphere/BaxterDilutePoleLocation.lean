/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterDiluteDecay
import LeanCode.HardSphere.BaxterPoles

/-!
# Dilute-regime Baxter pole location: all poles in the open upper half-plane — Task POLE.11 (task b)

The premise of Task `POLE.11` ("Baxter poles in the open half-plane") is the Hurwitz/root-location
statement that every zero of `1 - ρ·Q̂(k)` (equivalently every nonzero zero of `G_baxter`) lies in
the open upper half-plane `Im k > 0`.  In the **dilute regime** `M := ∫₀^σ|q0| < 1`
(`η < (3-√7)/2 ≈ 0.177`, `q0AbsL1_lt_one_of_dilute`) this is elementary — the SAME `L¹` mass bound
as the decay result, extended to the **closed lower half-plane** via `‖e^{-ikr}‖ = e^{r·Im k}`:

  for `Im k ≤ 0` and `r ≥ 0`,  `e^{r·Im k} ≤ 1`,  so
  `‖Q̂(k)‖ = ‖∫₀^σ q0(r) e^{-ikr} dr‖ ≤ ∫₀^σ |q0(r)| e^{r·Im k} dr ≤ ∫₀^σ|q0| = M < 1`,

hence `Q̂(k) ≠ 1` and `G_baxter(k) ≠ 0` throughout the closed lower half-plane.  So every nonzero
Baxter pole has `Im k > 0`.

* `Qhat_complex_norm_le_L1_of_im_nonpos` — `‖Q̂(k)‖ ≤ M` on `{Im k ≤ 0}`.
* `Qhat_complex_ne_one_of_im_nonpos_of_dilute` / `G_baxter_ne_zero_of_im_nonpos_of_dilute` — the
  nonvanishing on the closed lower half-plane.
* `baxter_pole_im_pos_of_dilute` — the headline: every nonzero `G_baxter` zero has `Im k > 0`.

This proves POLE.11's *premise* (the poles-in-open-UHP condition) in the dilute regime — the
companion, on the pole side, to `BaxterDiluteDecay.lean`'s *conclusion* (the actual decay).  For
`η ≳ 0.177` the mass bound `M ≥ 1` fails on the real axis (`Im k = 0`), so this elementary route
caps at the same threshold; the general-`η` root-location is Hermite–Biehler-scale (see
`proof_notes_pole.md` POLE.11).
-/

open MeasureTheory Set Real Filter Topology intervalIntegral

namespace FMSA.HardSphere

noncomputable section

/-- **`‖Q̂(k)‖ ≤ M` on the closed lower half-plane.** `‖q0(r) e^{-ikr}‖ = |q0(r)| e^{r·Im k}`, and
`e^{r·Im k} ≤ 1` for `Im k ≤ 0`, `r ≥ 0`, so the transform is bounded by the `L¹` mass. -/
theorem Qhat_complex_norm_le_L1_of_im_nonpos {eta sigma rho : ℝ} (hsigma : 0 < sigma) {k : ℂ}
    (hk : k.im ≤ 0) :
    ‖Qhat_complex eta sigma rho k‖ ≤ q0AbsL1 eta sigma rho := by
  unfold Qhat_complex q0AbsL1
  have hcont : Continuous (fun r : ℝ => (q0_poly eta sigma rho r : ℂ) *
      Complex.exp (-Complex.I * k * (r:ℂ))) :=
    (Complex.continuous_ofReal.comp (q0_poly_continuous eta sigma rho)).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  calc ‖∫ r in (0:ℝ)..sigma, (q0_poly eta sigma rho r : ℂ)
          * Complex.exp (-Complex.I * k * (r:ℂ))‖
      ≤ ∫ r in (0:ℝ)..sigma, ‖(q0_poly eta sigma rho r : ℂ)
          * Complex.exp (-Complex.I * k * (r:ℂ))‖ :=
        intervalIntegral.norm_integral_le_integral_norm hsigma.le
    _ ≤ ∫ r in (0:ℝ)..sigma, |q0_poly eta sigma rho r| := by
        apply intervalIntegral.integral_mono_on hsigma.le
        · exact hcont.norm.intervalIntegrable _ _
        · exact ((q0_poly_continuous eta sigma rho).abs).intervalIntegrable _ _
        · intro r hr
          have hr0 : (0:ℝ) ≤ r := hr.1
          have hexp : ‖Complex.exp (-Complex.I * k * (r:ℂ))‖ = Real.exp (r * k.im) := by
            rw [Complex.norm_exp]; congr 1
            simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
            ring
          have hle1 : Real.exp (r * k.im) ≤ 1 :=
            Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hr0 hk)
          calc ‖(q0_poly eta sigma rho r : ℂ) * Complex.exp (-Complex.I * k * (r:ℂ))‖
              = ‖(q0_poly eta sigma rho r : ℂ)‖ * ‖Complex.exp (-Complex.I * k * (r:ℂ))‖ :=
                norm_mul _ _
            _ = |q0_poly eta sigma rho r| * Real.exp (r * k.im) := by
                rw [Complex.norm_real, hexp, Real.norm_eq_abs]
            _ ≤ |q0_poly eta sigma rho r| * 1 :=
                mul_le_mul_of_nonneg_left hle1 (abs_nonneg _)
            _ = |q0_poly eta sigma rho r| := mul_one _

/-- **`Q̂(k) ≠ 1` on the closed lower half-plane (dilute).** `‖Q̂(k)‖ ≤ M < 1 = ‖1‖`. -/
theorem Qhat_complex_ne_one_of_im_nonpos_of_dilute {eta sigma rho : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 ≤ rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (hdilute : eta < (3 - Real.sqrt 7) / 2)
    {k : ℂ} (hk : k.im ≤ 0) :
    Qhat_complex eta sigma rho k ≠ 1 := by
  intro h
  have hM : q0AbsL1 eta sigma rho < 1 :=
    q0AbsL1_lt_one_of_dilute heta0 heta1 hsigma hrho heta_def hdilute
  have hle := Qhat_complex_norm_le_L1_of_im_nonpos (eta := eta) (rho := rho) hsigma hk
  rw [h, norm_one] at hle
  linarith

/-- **`G_baxter(k) ≠ 0` on the closed lower half-plane, `k ≠ 0` (dilute).**  `G_baxter(k) =
(-ik)³·(1-Q̂(k))` (`baxter_cube_mul_F_eq_G`): both factors are nonzero. -/
theorem G_baxter_ne_zero_of_im_nonpos_of_dilute {eta sigma rho : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 ≤ rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (hdilute : eta < (3 - Real.sqrt 7) / 2)
    {k : ℂ} (hk_im : k.im ≤ 0) (hk0 : k ≠ 0) :
    G_baxter eta sigma rho k ≠ 0 := by
  rw [← baxter_cube_mul_F_eq_G eta sigma rho hsigma hk0]
  apply mul_ne_zero
  · exact pow_ne_zero 3 (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hk0)
  · rw [sub_ne_zero]
    exact (Qhat_complex_ne_one_of_im_nonpos_of_dilute heta0 heta1 hsigma hrho heta_def hdilute
      hk_im).symm

/-- **Conditional root-location (the Hermite–Biehler / symbol-nonvanishing reduction).**
If `Q̂` avoids the value `1` throughout the closed lower half-plane — the statement a
Hermite–Biehler argument (or, in the dilute regime, the `L¹` bound above) establishes — then every
nonzero zero of `G_baxter` lies in the open upper half-plane.

This is the general-`η` skeleton: it isolates the one hard analytic input (`hsym`, the closed-LHP
nonvanishing of the symbol) as an explicit hypothesis, keeping the reduction itself axiom-clean.
The dilute theorem below is its instance (`hsym := Qhat_complex_ne_one_of_im_nonpos_of_dilute`); a
general-`η` proof discharges `hsym` via the (abstract, MA-group) Hermite–Biehler axiom
`hermite_biehler_exp_poly_no_lower_zero` (`Analysis/HermiteBiehler.lean`). -/
theorem baxter_pole_im_pos_of_symbol_ne_one {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (hsym : ∀ z : ℂ, z.im ≤ 0 → z ≠ 0 → Qhat_complex eta sigma rho z ≠ 1)
    {k : ℂ} (hk_zero : G_baxter eta sigma rho k = 0) (hk0 : k ≠ 0) :
    0 < k.im := by
  by_contra h
  push Not at h
  have hQ : Qhat_complex eta sigma rho k ≠ 1 := hsym k h hk0
  rw [← baxter_cube_mul_F_eq_G eta sigma rho hsigma hk0] at hk_zero
  rcases mul_eq_zero.mp hk_zero with h1 | h2
  · exact (pow_ne_zero 3 (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hk0)) h1
  · exact hQ (sub_eq_zero.mp h2).symm

/-- **POLE.11 root-location premise, dilute regime: every nonzero Baxter pole lies in the OPEN
upper half-plane.**  For `η < (3-√7)/2`, every nonzero zero `k` of `G_baxter` has `0 < Im k`.
Instance of `baxter_pole_im_pos_of_symbol_ne_one`. -/
theorem baxter_pole_im_pos_of_dilute {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 ≤ rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    (hdilute : eta < (3 - Real.sqrt 7) / 2) {k : ℂ}
    (hk_zero : G_baxter eta sigma rho k = 0) (hk0 : k ≠ 0) :
    0 < k.im :=
  baxter_pole_im_pos_of_symbol_ne_one hsigma
    (fun _z hz _hz0 =>
      Qhat_complex_ne_one_of_im_nonpos_of_dilute heta0 heta1 hsigma hrho heta_def hdilute hz)
    hk_zero hk0

end

end FMSA.HardSphere
