/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterOriginTripleZero
import LeanCode.HardSphere.BaxterDilutePoleLocation
import LeanCode.Analysis.ZeroCountHomotopy

/-!
# `1 − Q̂ ≠ 0` on the open lower half-plane, all physical `η` — retiring `MA.14`

This file discharges the last domain-referencing axiom `baxter_no_open_lhp_pole_core` (`MA.14`) by
running the `η`-homotopy of `proof_notes_pole.md` → "POLE.11-general / MA.14" against the abstract
homotopy-invariance axiom `zeroFree_lowerHalfPlane_of_homotopy` (`Analysis/ZeroCountHomotopy.lean`).

The whole argument is phrased on the **entire** function `H_η(k) = 1 − Qhat_complex η σ ρ(η) k`
rather than on `G_baxter` directly: `G_baxter = i·k³·(1−Q̂)` (`G_baxter_eq_I_mul_cube`), so for
`k≠0` their zeros coincide, but `1−Q̂` has no artificial `k³` zero at the origin — the boundary
point that would otherwise sit on the contour.  Input 3 (`one_sub_Qhat_complex_zero_ne_zero`) says
`1−Q̂(0)≠0`, so the whole real axis (origin included) is zero-free with no contour indentation.

## The four homotopy inputs (all proved elsewhere, assembled here)

1. base case `η < (3−√7)/2`   — `Qhat_complex_ne_one_of_im_nonpos_of_dilute`
2. real axis `k ≠ 0`          — `G_baxter_ne_zero_of_real` (`‖Npoly‖²−‖Dpoly‖²=k⁶`)
3. origin `k = 0`             — `one_sub_Qhat_complex_zero_ne_zero`
4. escape radius (uniform)    — `exists_uniform_escape_radius`

## Key structural lemma making joint continuity trivial

`q0_poly = ρq'·φ1 + ρq''·φ2` with `φ1, φ2` **independent of `η`** on the integration domain, so
`Qhat_complex η σ ρ k = (ρq')·qKernel1 σ k + (ρq'')·qKernel2 σ k` — the `η`-dependence is entirely
in the two scalar coefficients, the `k`-dependence entirely in two fixed integrals.  Joint
continuity of `(η,k) ↦ 1 − Q̂` then reduces to (scalar continuity in `η`) × (continuity of the
fixed integrals in `k`).
-/

open Complex Set MeasureTheory
open scoped Real

namespace FMSA.HardSphere

noncomputable section

/-- Fixed `k`-integral carrying the `φ1` part of `q0_poly` (independent of `η, ρ`). -/
noncomputable def qKernel1 (sigma : ℝ) (k : ℂ) : ℂ :=
  ∫ r in (0:ℝ)..sigma, (phi1_real sigma r : ℂ) * Complex.exp (-Complex.I * k * r)

/-- Fixed `k`-integral carrying the `φ2` part of `q0_poly` (independent of `η, ρ`). -/
noncomputable def qKernel2 (sigma : ℝ) (k : ℂ) : ℂ :=
  ∫ r in (0:ℝ)..sigma, (phi2_real sigma r : ℂ) * Complex.exp (-Complex.I * k * r)

/-- The integrand of `qKernel1`, as a jointly continuous function of `(k, r)`. -/
private theorem continuous_qKernel1_integrand (sigma : ℝ) :
    Continuous (Function.uncurry
      (fun k r => (phi1_real sigma r : ℂ) * Complex.exp (-Complex.I * k * r))) := by
  unfold Function.uncurry
  refine Continuous.mul ?_ ?_
  · exact Complex.continuous_ofReal.comp ((phi1_real_continuous sigma).comp continuous_snd)
  · exact Complex.continuous_exp.comp (by fun_prop)

private theorem continuous_qKernel2_integrand (sigma : ℝ) :
    Continuous (Function.uncurry
      (fun k r => (phi2_real sigma r : ℂ) * Complex.exp (-Complex.I * k * r))) := by
  unfold Function.uncurry
  refine Continuous.mul ?_ ?_
  · exact Complex.continuous_ofReal.comp ((phi2_real_continuous sigma).comp continuous_snd)
  · exact Complex.continuous_exp.comp (by fun_prop)

/-- `qKernel1` is continuous in `k` (parametric interval integral, fixed limits). -/
theorem qKernel1_continuous (sigma : ℝ) : Continuous (qKernel1 sigma) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_qKernel1_integrand sigma) 0 sigma

theorem qKernel2_continuous (sigma : ℝ) : Continuous (qKernel2 sigma) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_qKernel2_integrand sigma) 0 sigma

/-- **The `Q̂` factorization** `Q̂ = (ρq')·qKernel1 + (ρq'')·qKernel2`.  The `η`-dependence lives
only in the two scalar coefficients; the `k`-dependence only in the two fixed integrals. -/
theorem Qhat_complex_eq_kernels (eta sigma rho : ℝ) (k : ℂ) :
    Qhat_complex eta sigma rho k
      = (rho * q_prime_py eta sigma : ℂ) * qKernel1 sigma k
        + (rho * q_doubleprime_py eta : ℂ) * qKernel2 sigma k := by
  have hint1 : IntervalIntegrable
      (fun r => (rho * q_prime_py eta sigma : ℂ)
        * ((phi1_real sigma r : ℂ) * Complex.exp (-Complex.I * k * r))) volume 0 sigma := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      ((Complex.continuous_ofReal.comp (phi1_real_continuous sigma)).mul
        (Complex.continuous_exp.comp (by fun_prop)))
  have hint2 : IntervalIntegrable
      (fun r => (rho * q_doubleprime_py eta : ℂ)
        * ((phi2_real sigma r : ℂ) * Complex.exp (-Complex.I * k * r))) volume 0 sigma := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      ((Complex.continuous_ofReal.comp (phi2_real_continuous sigma)).mul
        (Complex.continuous_exp.comp (by fun_prop)))
  rw [qKernel1, qKernel2, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add hint1 hint2, Qhat_complex]
  refine intervalIntegral.integral_congr (fun r _ => ?_)
  simp only [q0_poly]
  push_cast
  ring

/-- Physical density `ρ(η) = 6η/(πσ³)` at fixed `σ` (the constraint along the homotopy). -/
noncomputable def rhoPhys (sigma t : ℝ) : ℝ := 6 * t / (Real.pi * sigma ^ 3)

/-- The homotopy family `H_t(k) = 1 − Q̂_t(k)`, entire in `k`, along the physical `ρ = ρ(t)`. -/
noncomputable def baxterH (sigma t : ℝ) (k : ℂ) : ℂ :=
  1 - Qhat_complex t sigma (rhoPhys sigma t) k

theorem rhoPhys_continuous (sigma : ℝ) : Continuous (rhoPhys sigma) := by
  unfold rhoPhys; fun_prop

/-- **Joint continuity** of `(t,k) ↦ H_t(k)` on `[a,b] × ℂ` for `b < 1`.  Immediate from the kernel
factorization: the `t`-dependence is two scalar coefficients (rational in `η`, regular for `η<1`),
the `k`-dependence two fixed continuous integrals. -/
theorem baxterH_continuousOn {a b sigma : ℝ} (hb : b < 1) :
    ContinuousOn (fun p : ℝ × ℂ => baxterH sigma p.1 p.2)
      (Set.Icc a b ×ˢ (Set.univ : Set ℂ)) := by
  have hden : ∀ t ∈ Set.Icc a b, (1 - t) ^ 2 ≠ 0 := fun t ht =>
    (pow_pos (by have := ht.2; linarith : (0 : ℝ) < 1 - t) 2).ne'
  have hqp : ContinuousOn (fun t => q_prime_py t sigma) (Set.Icc a b) := by
    simp only [q_prime_py]; exact ContinuousOn.div (by fun_prop) (by fun_prop) hden
  have hqpp : ContinuousOn (fun t => q_doubleprime_py t) (Set.Icc a b) := by
    simp only [q_doubleprime_py]; exact ContinuousOn.div (by fun_prop) (by fun_prop) hden
  have hc1 : ContinuousOn (fun t => ((rhoPhys sigma t * q_prime_py t sigma : ℝ) : ℂ))
      (Set.Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn ((rhoPhys_continuous sigma).continuousOn.mul hqp)
  have hc2 : ContinuousOn (fun t => ((rhoPhys sigma t * q_doubleprime_py t : ℝ) : ℂ))
      (Set.Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn ((rhoPhys_continuous sigma).continuousOn.mul hqpp)
  have heq : (fun p : ℝ × ℂ => baxterH sigma p.1 p.2)
      = fun p : ℝ × ℂ => 1
          - ((rhoPhys sigma p.1 * q_prime_py p.1 sigma : ℝ) : ℂ) * qKernel1 sigma p.2
          - ((rhoPhys sigma p.1 * q_doubleprime_py p.1 : ℝ) : ℂ) * qKernel2 sigma p.2 := by
    funext p; simp only [baxterH]; rw [Qhat_complex_eq_kernels]; push_cast; ring
  rw [heq]
  refine (continuousOn_const.sub ?_).sub ?_
  · exact (hc1.comp continuous_fst.continuousOn (fun p hp => hp.1)).mul
      ((qKernel1_continuous sigma).comp continuous_snd).continuousOn
  · exact (hc2.comp continuous_fst.continuousOn (fun p hp => hp.1)).mul
      ((qKernel2_continuous sigma).comp continuous_snd).continuousOn

/-- `η = π·ρ(η)·σ³/6` — the physical constraint holds definitionally for `ρ = rhoPhys σ η`. -/
private theorem rhoPhys_constraint {sigma t : ℝ} (hsigma : 0 < sigma) :
    t = Real.pi * rhoPhys sigma t * sigma ^ 3 / 6 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hs : sigma ≠ 0 := hsigma.ne'
  unfold rhoPhys; field_simp <;> ring

/-- **`H_η ≠ 0` on the open lower half-plane, every physical `η ∈ (0,1)`.**  For `η` below the
dilute wall `(3−√7)/2` the base case applies directly; otherwise homotope from `(3−√7)/4` (safely
dilute) up to `η`, discharging the four inputs of `zeroFree_lowerHalfPlane_of_homotopy`. -/
theorem baxterH_ne_zero_of_im_neg {sigma t : ℝ} (hsigma : 0 < sigma) (ht0 : 0 < t) (ht1 : t < 1)
    {k : ℂ} (hk : k.im < 0) : baxterH sigma t k ≠ 0 := by
  have hs7hi : Real.sqrt 7 < 3 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 7 by norm_num), Real.sqrt_nonneg 7]
  have hrhoNonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ rhoPhys sigma u := fun u hu => by
    unfold rhoPhys; positivity
  rcases le_or_gt t ((3 - Real.sqrt 7) / 4) with hsmall | hbig
  · -- Direct base case: `t` below the dilute wall.
    have hd := Qhat_complex_ne_one_of_im_nonpos_of_dilute ht0 ht1 hsigma
      (hrhoNonneg t ht0.le) (rhoPhys_constraint hsigma) (by linarith) hk.le
    exact sub_ne_zero.mpr (Ne.symm hd)
  · -- Homotopy case: `(3−√7)/4 < t`.
    have ha0 : 0 < (3 - Real.sqrt 7) / 4 := by linarith
    have ha1 : (3 - Real.sqrt 7) / 4 < 1 := by linarith [Real.sqrt_nonneg 7]
    obtain ⟨R, hRpos, hRbound⟩ := exists_uniform_escape_radius (a := (3 - Real.sqrt 7) / 4)
      (b := t) (sigma := sigma) ht1 (rhoPhys_continuous sigma).continuousOn
    have hholo : ∀ s ∈ Set.Icc ((3 - Real.sqrt 7) / 4) t, Differentiable ℂ (baxterH sigma s) :=
      fun s _ => (differentiable_const 1).sub (Qhat_complex_entire s sigma (rhoPhys sigma s) hsigma)
    have hbound : ∀ s ∈ Set.Icc ((3 - Real.sqrt 7) / 4) t, ∀ z : ℂ, z.im ≤ 0 →
        baxterH sigma s z = 0 → ‖z‖ < R := by
      intro s hs z hzim hHz
      by_contra hlt
      push_neg at hlt
      have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hlt; linarith
      have hG0 : G_baxter s sigma (rhoPhys sigma s) z = 0 :=
        (Qhat_pole_iff_G_baxter_zero s sigma (rhoPhys sigma s) hsigma hz0).mp hHz
      exact G_baxter_ne_zero_of_norm_dominant hsigma hzim (hRbound s hs z hlt) hG0
    have hreal : ∀ s ∈ Set.Icc ((3 - Real.sqrt 7) / 4) t, ∀ z : ℂ, z.im = 0 →
        baxterH sigma s z ≠ 0 := by
      intro s hs z hzim
      have hs0 : 0 < s := lt_of_lt_of_le ha0 hs.1
      have hs1 : s < 1 := lt_of_le_of_lt hs.2 ht1
      have hdef := rhoPhys_constraint (sigma := sigma) (t := s) hsigma
      have hz : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hzim])
      show (1 : ℂ) - Qhat_complex s sigma (rhoPhys sigma s) z ≠ 0
      by_cases hre : z.re = 0
      · have hz0 : z = 0 := by rw [hz, hre]; simp
        rw [hz0]
        exact one_sub_Qhat_complex_zero_ne_zero hs0 hsigma hs1 hdef
      · intro hH
        have hz0 : z ≠ 0 := by rw [hz]; simpa using hre
        have hG : G_baxter s sigma (rhoPhys sigma s) z ≠ 0 := by
          rw [hz]; exact G_baxter_ne_zero_of_real hsigma hs1 hdef hre
        exact hG ((Qhat_pole_iff_G_baxter_zero s sigma (rhoPhys sigma s) hsigma hz0).mp hH)
    have hbase : ∀ z : ℂ, z.im < 0 → baxterH sigma ((3 - Real.sqrt 7) / 4) z ≠ 0 := by
      intro z hzim
      have hd := Qhat_complex_ne_one_of_im_nonpos_of_dilute ha0 ha1 hsigma
        (hrhoNonneg _ ha0.le) (rhoPhys_constraint hsigma) (by linarith) hzim.le
      exact sub_ne_zero.mpr (Ne.symm hd)
    exact FMSA.Analysis.zeroFree_lowerHalfPlane_of_homotopy (H := baxterH sigma)
      (a := (3 - Real.sqrt 7) / 4) (b := t) (R := R) hbig.le hRpos (baxterH_continuousOn ht1)
      hholo hbound hreal hbase k hk

/-- **`1 − Q̂ ≠ 0` (equivalently `Q̂ ≠ 1`) on the open lower half-plane, for every physical
mixture.**  Retires the domain axiom `baxter_no_open_lhp_pole_core`. -/
theorem Qhat_complex_ne_one_of_im_neg {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) {k : ℂ} (hk : k.im < 0) :
    Qhat_complex eta sigma rho k ≠ 1 := by
  have hrhoeq : rhoPhys sigma eta = rho := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hs : sigma ≠ 0 := hsigma.ne'
    unfold rhoPhys; rw [heta_def]; field_simp
  have hH := baxterH_ne_zero_of_im_neg hsigma heta0 heta1 hk
  unfold baxterH at hH
  rw [hrhoeq] at hH
  exact fun hQ => hH (by rw [hQ]; ring)

end

end FMSA.HardSphere
