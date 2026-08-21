/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZ.MSADCFTransform

/-!
# MSAEXACT.1 — the exterior (non-compact) Yukawa transforms of the Baxter factor

Group **MSAEXACT** (`proof_notes_msa_exact.md`).  Numerical partner: `msaexact1_cside_check.py`.

The physical hard-core Yukawa MSA has an **infinite-range** direct correlation function
(`c = −βu = K e^{−z(r−σ)}/r` outside the core), so its Baxter factorisation function `q(r)` is
**not** compactly supported — it carries a Yukawa tail `∝ e^{−zr}` on all of `(0, ∞)`.  Concretely
`Q̂(s)` has a genuine simple pole at `s = −z` (residue the amplitude `D = D̃ e^{z}`), which a
transform over `[0, σ]` — being entire in `k` — can never reproduce.  (This is exactly why the
compact ansatz `q0_poly + D e^{−zr}` of `msaexact1_iff_core` cannot equal the physical factor: an
entire function cannot equal one with poles.)

The two half-line transforms this file supplies are the ones the *non-compact* Baxter factor needs:

    ∫_{r>0} e^{−zr} cos(kr) dr = z / (z² + k²),      ∫_{r>0} e^{−zr} sin(kr) dr = k / (z² + k²).

The sine one is `yukawa_tail_sine_integral` at `σ = 0`; the cosine one is proved here by the same
route (an explicit antiderivative that decays because the exponential does).
-/

open MeasureTheory intervalIntegral Real Set Filter Topology

namespace FMSA.MSAExact

/-- The half-line integrand `e^{−zr}cos(kr)` decays exponentially, so it is integrable on `(0, ∞)`.
-/
private theorem exp_cos_integrableOn_Ioi {z : ℝ} (hz : 0 < z) (k : ℝ) :
    IntegrableOn (fun r => Real.exp (-z * r) * Real.cos (k * r)) (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hz)) ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun r => ?_
    have hc : ‖Real.cos (k * r)‖ ≤ 1 := by simpa using Real.abs_cos_le_one (k * r)
    calc ‖Real.exp (-z * r) * Real.cos (k * r)‖
        = Real.exp (-z * r) * ‖Real.cos (k * r)‖ := by
          rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-z * r) * 1 := mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
      _ = Real.exp (-z * r) := by rw [mul_one]

/-- **The exterior cosine transform.** `∫_{r>0} e^{−zr}cos(kr) dr = z/(z²+k²)`.

Antiderivative `−e^{−zr}(z cos kr − k sin kr)/(z²+k²)`, which tends to `0` because the exponential
does and the trigonometric bracket is bounded — the only place `z > 0` is used.  The cosine partner
of `yukawa_tail_sine_integral`, but over `(0, ∞)` rather than `(σ, ∞)`. -/
theorem exp_cos_integral_Ioi {z : ℝ} (hz : 0 < z) (k : ℝ) :
    (∫ r in Ioi (0 : ℝ), Real.exp (-z * r) * Real.cos (k * r)) = z / (z ^ 2 + k ^ 2) := by
  have hzk : z ^ 2 + k ^ 2 ≠ 0 := by positivity
  set F : ℝ → ℝ := fun r =>
    -(Real.exp (-z * r) * (z * Real.cos (k * r) - k * Real.sin (k * r))) / (z ^ 2 + k ^ 2) with hF
  have hderiv : ∀ r ∈ Ici (0 : ℝ),
      HasDerivAt F (Real.exp (-z * r) * Real.cos (k * r)) r := by
    intro r _
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-z * t))
        (-z * Real.exp (-z * r)) r := by
      have : HasDerivAt (fun t : ℝ => -z * t) (-z) r := by
        simpa using (hasDerivAt_id r).const_mul (-z)
      simpa [mul_comm] using this.exp
    have hcos : HasDerivAt (fun t : ℝ => Real.cos (k * t)) (-(k * Real.sin (k * r))) r := by
      simpa [mul_comm] using ((hasDerivAt_id r).const_mul k).cos
    have hsin : HasDerivAt (fun t : ℝ => Real.sin (k * t)) (k * Real.cos (k * r)) r := by
      simpa [mul_comm] using ((hasDerivAt_id r).const_mul k).sin
    have hin : HasDerivAt (fun t : ℝ => z * Real.cos (k * t) - k * Real.sin (k * t))
        (z * -(k * Real.sin (k * r)) - k * (k * Real.cos (k * r))) r :=
      (hcos.const_mul z).sub (hsin.const_mul k)
    refine (((hexp.mul hin).neg).div_const (z ^ 2 + k ^ 2)).congr_deriv ?_
    field_simp
    ring
  have htend : Tendsto F atTop (𝓝 0) := by
    have hbound : ∀ r : ℝ, ‖F r‖
        ≤ ((|z| + |k|) / (z ^ 2 + k ^ 2)) * Real.exp (-z * r) := by
      intro r
      have hs : |Real.sin (k * r)| ≤ 1 := Real.abs_sin_le_one _
      have hc : |Real.cos (k * r)| ≤ 1 := Real.abs_cos_le_one _
      have htr : |z * Real.cos (k * r) - k * Real.sin (k * r)| ≤ |z| + |k| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul]
        have h1 : |z| * |Real.cos (k * r)| ≤ |z| * 1 :=
          mul_le_mul_of_nonneg_left hc (abs_nonneg _)
        have h2 : |k| * |Real.sin (k * r)| ≤ |k| * 1 :=
          mul_le_mul_of_nonneg_left hs (abs_nonneg _)
        linarith
      have hpos : (0 : ℝ) < z ^ 2 + k ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hzk)
      rw [hF]
      simp only [Real.norm_eq_abs, abs_div, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_pos hpos]
      rw [div_le_iff₀ hpos]
      have := mul_le_mul_of_nonneg_left htr (Real.exp_pos (-z * r)).le
      calc Real.exp (-z * r) * |z * Real.cos (k * r) - k * Real.sin (k * r)|
          ≤ Real.exp (-z * r) * (|z| + |k|) := this
        _ = (|z| + |k|) / (z ^ 2 + k ^ 2) * Real.exp (-z * r) * (z ^ 2 + k ^ 2) := by field_simp
    refine squeeze_zero_norm hbound ?_
    have : Tendsto (fun r : ℝ => Real.exp (-z * r)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith : -z < 0))
    simpa using this.const_mul ((|z| + |k|) / (z ^ 2 + k ^ 2))
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
      (exp_cos_integrableOn_Ioi hz k) htend, hF]
  simp only [mul_zero, Real.exp_zero, one_mul, Real.cos_zero, Real.sin_zero, mul_one,
    mul_zero, sub_zero]
  field_simp
  ring

/-- **The exterior sine transform.** `∫_{r>0} e^{−zr}sin(kr) dr = k/(z²+k²)`.

The `σ = 0` case of `yukawa_tail_sine_integral` (`e^{−z(r−σ)} = e^{−zr}`, `cos 0 = 1`, `sin 0 = 0`).
-/
theorem exp_sin_integral_Ioi {z : ℝ} (hz : 0 < z) (k : ℝ) :
    (∫ r in Ioi (0 : ℝ), Real.exp (-z * r) * Real.sin (k * r)) = k / (z ^ 2 + k ^ 2) := by
  have h := yukawa_tail_sine_integral hz k 0
  simp only [sub_zero, mul_zero, Real.cos_zero, Real.sin_zero, mul_one, mul_zero,
    add_zero] at h
  exact h

end FMSA.MSAExact
