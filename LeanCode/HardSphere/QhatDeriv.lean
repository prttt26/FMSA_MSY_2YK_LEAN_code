/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterZeros
import LeanCode.HardSphere.BaxterDiluteDecay

/-!
# Explicit derivative of `Qhat_complex`

`deriv_Qhat_complex`: `Q̂'(z) = ∫₀^σ q0(r)·(−i r)·e^{−i z r} dr`. The existing
`entire_poly_exp_integral` (`BaxterZeros.lean`) proves *differentiability* but discards the
derivative value; `hasDerivAt_poly_exp_integral` re-runs the identical
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` argument and exposes the
`HasDerivAt`. Needed for the joint `(η,z)`-continuity of `logDeriv (1 − Q̂(−·))` in the half-disk
argument-principle count that retires `baxter_no_open_lhp_pole_core` (MA.14).
-/

open MeasureTheory intervalIntegral Real Set

namespace FMSA.HardSphere

/-- `HasDerivAt` form of `entire_poly_exp_integral`: exposes the explicit derivative
`∫₀^σ P(r)·(−i r)·e^{−i k₀ r} dr`. Same proof as `entire_poly_exp_integral`, returning `key.2`. -/
theorem hasDerivAt_poly_exp_integral (P : ℝ → ℝ) (hP : Continuous P) (sigma : ℝ)
    (hsigma : 0 < sigma) (k0 : ℂ) :
    HasDerivAt (fun k : ℂ => ∫ r in (0:ℝ)..sigma, (P r : ℂ) * Complex.exp (-Complex.I * k * r))
      (∫ r in (0:ℝ)..sigma, (P r : ℂ) * (-Complex.I * r) *
        Complex.exp (-Complex.I * k0 * r)) k0 := by
  set F : ℂ → ℝ → ℂ := fun k r => (P r : ℂ) * Complex.exp (-Complex.I * k * r) with hFdef
  set F' : ℂ → ℝ → ℂ := fun k r => (P r : ℂ) * (-Complex.I * r) * Complex.exp (-Complex.I * k * r)
    with hF'def
  set C : ℝ := |k0.im| + 1 with hCdef
  set bound : ℝ → ℝ := fun t => |P t| * sigma * Real.exp (sigma * C) with hbounddef
  have hFcont : ∀ x : ℂ, Continuous (fun r : ℝ => F x r) := by
    intro x
    apply Continuous.mul
    · exact Complex.continuous_ofReal.comp hP
    · exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hF'cont : ∀ x : ℂ, Continuous (fun r : ℝ => F' x r) := by
    intro x
    apply Continuous.mul
    · apply Continuous.mul
      · exact Complex.continuous_ofReal.comp hP
      · fun_prop
    · exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := k0) (bound := bound) (a := (0:ℝ)) (b := sigma) (μ := volume)
    (s := Metric.ball k0 1)
    (Metric.ball_mem_nhds k0 one_pos)
    (Filter.Eventually.of_forall (fun x => (hFcont x).aestronglyMeasurable))
    ((hFcont k0).intervalIntegrable 0 sigma)
    (hF'cont k0).aestronglyMeasurable
    ?_ ?_ ?_
  · exact key.2
  · filter_upwards with t ht x hx
    rw [hF'def]
    rw [Set.uIoc_of_le hsigma.le] at ht
    have hbound_im : t * x.im ≤ sigma * C := by
      have h1 : |x.im - k0.im| ≤ ‖x - k0‖ := Complex.abs_im_le_norm (x - k0)
      have h2 : ‖x - k0‖ < 1 := by
        have := Metric.mem_ball.mp hx
        rwa [dist_eq_norm] at this
      have h3 : |x.im| < C := by
        rw [hCdef]
        have := abs_sub_abs_le_abs_sub x.im k0.im
        linarith [h1, h2]
      have h4 : x.im ≤ |x.im| := le_abs_self _
      have h5 : t * x.im ≤ t * |x.im| := mul_le_mul_of_nonneg_left h4 ht.1.le
      have h6 : t * |x.im| ≤ sigma * |x.im| := mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)
      have h7 : sigma * |x.im| ≤ sigma * C := mul_le_mul_of_nonneg_left h3.le hsigma.le
      linarith [h5, h6, h7]
    have hnorm_exp : ‖Complex.exp (-Complex.I * x * t)‖ = Real.exp (t * x.im) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    have hnorm_t : ‖(-Complex.I * (t:ℂ))‖ = |t| := by
      rw [norm_mul]; simp
    have hnorm_P : ‖(P t : ℂ)‖ = |P t| := Complex.norm_real (P t)
    rw [norm_mul, norm_mul, hnorm_exp, hnorm_t, hnorm_P]
    have habst : |t| = t := abs_of_pos ht.1
    rw [habst, hbounddef]
    have hexp_mono : Real.exp (t * x.im) ≤ Real.exp (sigma * C) := Real.exp_le_exp.mpr hbound_im
    calc |P t| * t * Real.exp (t * x.im) ≤ |P t| * sigma * Real.exp (t * x.im) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          apply mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _)
      _ ≤ |P t| * sigma * Real.exp (sigma * C) := by
          apply mul_le_mul_of_nonneg_left hexp_mono
          positivity
  · apply Continuous.intervalIntegrable
    exact (hP.abs.mul continuous_const).mul continuous_const
  · filter_upwards with t ht x hx
    rw [hFdef, hF'def]
    have h1 : HasDerivAt (fun y : ℂ => -Complex.I * y * t) (-Complex.I * t) x := by
      have h2 : HasDerivAt (fun y : ℂ => y * (t:ℂ)) (t:ℂ) x := by
        simpa using (hasDerivAt_id x).mul_const (t:ℂ)
      have h3 := h2.const_mul (-Complex.I)
      simpa [mul_assoc] using h3
    have h4 := h1.cexp
    have h5 := h4.const_mul ((P t : ℂ))
    refine h5.congr_deriv ?_
    ring

/-- **Explicit derivative of `Qhat_complex`.** `Q̂'(z) = ∫₀^σ q0(r)·(−i r)·e^{−i z r} dr`. -/
theorem deriv_Qhat_complex (eta sigma rho : ℝ) (hsigma : 0 < sigma) (z : ℂ) :
    deriv (Qhat_complex eta sigma rho) z
      = ∫ r in (0:ℝ)..sigma, (q0_poly eta sigma rho r : ℂ) * (-Complex.I * r) *
          Complex.exp (-Complex.I * z * r) :=
  (hasDerivAt_poly_exp_integral (q0_poly eta sigma rho) (q0_poly_continuous eta sigma rho)
    sigma hsigma z).deriv

end FMSA.HardSphere
