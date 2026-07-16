/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterWienerHopf

/-!
# Task POLE.1 — `Qhat_complex : ℂ → ℂ`, entire, closed form

The Fourier transform `q̂0(k) = ∫₀^σ q0_poly(r)·e^{-ikr} dr` of `q0_poly`
(`BaxterRealSpace.lean`, Task `BAXTER.1`) is known so far only for **real** `k`
(`q0poly_cos_integral_formula`/`q0poly_sin_integral_formula`, `BaxterWienerHopf.lean`,
Task `BAXTER.3`). This file extends it to a genuine entire function `Qhat_complex : ℂ → ℂ`,
the first ingredient the Banach/Newton pole-existence strategy (Task `BAXTER.2`) needs.

## Proof strategy

1. **Entireness** (`Qhat_complex_entire`): a general lemma (`entire_poly_exp_integral`) shows
   `k ↦ ∫₀^σ P(r)·e^{-ikr} dr` is differentiable at every `k₀ : ℂ`, for *any* continuous
   `P : ℝ → ℝ`, via `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
   (`Mathlib.Analysis.Calculus.ParametricIntervalIntegral`) — the dominating bound
   `|P(t)|·σ·exp(σ·(|Im k₀|+1))` comes from `‖e^{-ikr}‖ = exp(r·Im(k))` and a ball-membership
   estimate on `Im(k)`. `q0_poly` expands to a quadratic polynomial on `[0,σ]`
   (`q0_poly_inner`), which is trivially globally continuous, so the general lemma applies
   directly — **no** need to separately establish continuity of `q0_poly` itself (a piecewise
   definition via `phi1_real`/`phi2_real`) or to handle its `k=0` closed-form singularity: the
   entireness proof works from the raw integral representation, not the closed form below.

2. **Closed form** (`Qhat_complex_formula`, `k ≠ 0`): the complex analogue of
   `q0poly_cos_integral_formula`/`_sin_integral_formula`, derived the same way (`HasDerivAt`+FTC
   on the `{1,r,r²}` basis) but directly against `Complex.exp(-ikr)` rather than splitting into
   `cos`/`sin` — the antiderivatives of `rⁿ·e^{cr}` (`c = -ik`) are the standard
   integration-by-parts closed forms, verified by direct differentiation before being formalized.
-/

open MeasureTheory intervalIntegral Real Set

namespace FMSA.HardSphere

/-! ### General entireness lemma for polynomial-times-complex-exponential integrals -/

/-- **Entireness of `k ↦ ∫₀^σ P(r)·e^{-ikr} dr`** for any continuous `P : ℝ → ℝ`. The dominated
convergence argument uses the bound `‖P(r)·e^{-ikr}‖ ≤ |P(r)|·e^{σ·(|Im k₀|+1)}` on a unit ball
around `k₀`, and the pointwise derivative `-i·r·P(r)·e^{-ikr}` (product/chain rule, `HasDerivAt`
composed via `HasDerivAt.comp_ofReal`). -/
theorem entire_poly_exp_integral (P : ℝ → ℝ) (hP : Continuous P) (sigma : ℝ) (hsigma : 0 < sigma) :
    Differentiable ℂ (fun k : ℂ => ∫ r in (0:ℝ)..sigma, (P r : ℂ) *
      Complex.exp (-Complex.I * k * r)) := by
  intro k0
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
  · exact key.2.differentiableAt
  · -- h_bound
    filter_upwards with t ht x hx
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
  · -- bound_integrable
    apply Continuous.intervalIntegrable
    exact (hP.abs.mul continuous_const).mul continuous_const
  · -- h_diff
    filter_upwards with t ht x hx
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

/-! ### ζ0, ζ1, ζ2 — degree-0/1/2 complex-exponential moments -/

/-- **ζ0 formula:** `∫0^σ e^{-ikr} dr = e^{-ikσ}/c - 1/c`, `c = -ik`. -/
theorem zeta0_formula {k : ℂ} (hk : k ≠ 0) (sigma : ℝ) :
    ∫ r in (0:ℝ)..sigma, Complex.exp (-Complex.I * k * r) =
      Complex.exp (-Complex.I * k * sigma) / (-Complex.I * k) - 1 / (-Complex.I * k) := by
  have hc : (-Complex.I * k) ≠ 0 := by simp [Complex.I_ne_zero, hk]
  have hderiv : ∀ r : ℝ, HasDerivAt
      (fun r : ℝ => Complex.exp (-Complex.I * k * r) / (-Complex.I * k))
      (Complex.exp (-Complex.I * k * r)) r := by
    intro r
    have h1 : HasDerivAt (fun z : ℂ => -Complex.I * k * z) (-Complex.I * k) (r:ℂ) := by
      have h2 : HasDerivAt (fun z : ℂ => z) (1:ℂ) (r:ℂ) := hasDerivAt_id (r:ℂ)
      simpa using h2.const_mul (-Complex.I * k)
    have h4 := (h1.cexp).comp_ofReal
    have h5 := h4.div_const (-Complex.I * k)
    refine h5.congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun r => Complex.exp (-Complex.I * k * r)) volume 0 sigma := by
    apply Continuous.intervalIntegrable
    exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => hderiv r) hint]
  simp

/-- **ζ1 formula:** `∫0^σ r·e^{-ikr} dr = (σ/c - 1/c²)·e^{-ikσ} + 1/c²`, `c = -ik`. -/
theorem zeta1_formula {k : ℂ} (hk : k ≠ 0) (sigma : ℝ) :
    ∫ r in (0:ℝ)..sigma, (r:ℂ) * Complex.exp (-Complex.I * k * r) =
      ((sigma:ℂ) / (-Complex.I * k) - 1 / (-Complex.I * k) ^ 2) *
          Complex.exp (-Complex.I * k * sigma) + 1 / (-Complex.I * k) ^ 2 := by
  set c : ℂ := -Complex.I * k with hcdef
  have hc : c ≠ 0 := by simp [hcdef, Complex.I_ne_zero, hk]
  have hderiv : ∀ r : ℝ, HasDerivAt (fun r : ℝ => ((r:ℂ) / c - 1 / c ^ 2) * Complex.exp (c * r))
      ((r:ℂ) * Complex.exp (c * r)) r := by
    intro r
    have hp1 : HasDerivAt (fun r : ℝ => (r:ℂ) / c - 1 / c ^ 2) (1 / c) r := by
      have h1 : HasDerivAt (fun r : ℝ => (r:ℂ)) (1:ℂ) r := (hasDerivAt_id (r:ℂ)).comp_ofReal
      have h2 := (h1.div_const c).sub_const (1 / c ^ 2)
      simpa using h2
    have hp2 : HasDerivAt (fun r : ℝ => Complex.exp (c * r)) (c * Complex.exp (c * r)) r := by
      have h1 : HasDerivAt (fun z : ℂ => c * z) c (r:ℂ) := by
        have h2 : HasDerivAt (fun z : ℂ => z) (1:ℂ) (r:ℂ) := hasDerivAt_id (r:ℂ)
        simpa using h2.const_mul c
      have h4 := h1.cexp.comp_ofReal
      refine h4.congr_deriv ?_
      ring
    have hprod := hp1.mul hp2
    refine hprod.congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun r : ℝ => (r:ℂ) * Complex.exp (c * r)) volume 0 sigma := by
    apply Continuous.intervalIntegrable
    exact Complex.continuous_ofReal.mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => hderiv r) hint]
  simp

/-- **ζ2 formula:** `∫0^σ r²·e^{-ikr} dr = (σ²/c - 2σ/c² + 2/c³)·e^{-ikσ} - 2/c³`, `c = -ik`. -/
theorem zeta2_formula {k : ℂ} (hk : k ≠ 0) (sigma : ℝ) :
    ∫ r in (0:ℝ)..sigma, (r:ℂ) ^ 2 * Complex.exp (-Complex.I * k * r) =
      ((sigma:ℂ) ^ 2 / (-Complex.I * k) - 2 * (sigma:ℂ) / (-Complex.I * k) ^ 2 +
          2 / (-Complex.I * k) ^ 3) * Complex.exp (-Complex.I * k * sigma) -
        2 / (-Complex.I * k) ^ 3 := by
  set c : ℂ := -Complex.I * k with hcdef
  have hc : c ≠ 0 := by simp [hcdef, Complex.I_ne_zero, hk]
  have hderiv : ∀ r : ℝ,
      HasDerivAt (fun r : ℝ => ((r:ℂ) ^ 2 / c - 2 * (r:ℂ) / c ^ 2 + 2 / c ^ 3) *
          Complex.exp (c * r))
        ((r:ℂ) ^ 2 * Complex.exp (c * r)) r := by
    intro r
    have hidC : HasDerivAt (fun r : ℝ => (r:ℂ)) (1:ℂ) r := (hasDerivAt_id (r:ℂ)).comp_ofReal
    have hp1 : HasDerivAt (fun r : ℝ => (r:ℂ) ^ 2 / c - 2 * (r:ℂ) / c ^ 2 + 2 / c ^ 3)
        (2 * (r:ℂ) / c - 2 / c ^ 2) r := by
      have hsq : HasDerivAt (fun r : ℝ => (r:ℂ) ^ 2) (2 * (r:ℂ)) r := by
        have h := hidC.mul hidC
        change HasDerivAt (fun r : ℝ => (r:ℂ) * (r:ℂ)) _ r at h
        have h' := h.congr_deriv (show (1:ℂ) * (r:ℂ) + (r:ℂ) * 1 = 2 * (r:ℂ) by ring)
        exact h'.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun r => by ring))
      have h1 := hsq.div_const c
      have h2 := hidC.const_mul (2 : ℂ)
      have h3 := h2.div_const (c ^ 2)
      have h4 := (h1.sub h3).add_const (2 / c ^ 3)
      refine h4.congr_deriv ?_
      field_simp
    have hp2 : HasDerivAt (fun r : ℝ => Complex.exp (c * r)) (c * Complex.exp (c * r)) r := by
      have h1 : HasDerivAt (fun z : ℂ => c * z) c (r:ℂ) := by
        have h2 : HasDerivAt (fun z : ℂ => z) (1:ℂ) (r:ℂ) := hasDerivAt_id (r:ℂ)
        simpa using h2.const_mul c
      have h4 := h1.cexp.comp_ofReal
      refine h4.congr_deriv ?_
      ring
    have hprod := hp1.mul hp2
    refine hprod.congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun r : ℝ => (r:ℂ) ^ 2 * Complex.exp (c * r)) volume 0 sigma := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_ofReal.pow 2).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => hderiv r) hint]
  simp

/-- **ζ4 formula:** `∫0^σ r⁴·e^{-ikr} dr = [σ⁴/c-4σ³/c²+12σ²/c³-24σ/c⁴+24/c⁵]·e^{-ikσ} - 24/c⁵`,
`c = -ik`. Needed for `Ĉ(k)`'s complex extension (`c_HS`'s cubic inner polynomial, times the
extra `r` factor `radial_fourier`'s kernel carries, gives degree-4 moments). -/
theorem zeta4_formula {k : ℂ} (hk : k ≠ 0) (sigma : ℝ) :
    ∫ r in (0:ℝ)..sigma, (r:ℂ) ^ 4 * Complex.exp (-Complex.I * k * r) =
      ((sigma:ℂ) ^ 4 / (-Complex.I * k) - 4 * (sigma:ℂ) ^ 3 / (-Complex.I * k) ^ 2 +
          12 * (sigma:ℂ) ^ 2 / (-Complex.I * k) ^ 3 - 24 * (sigma:ℂ) / (-Complex.I * k) ^ 4 +
          24 / (-Complex.I * k) ^ 5) * Complex.exp (-Complex.I * k * sigma) -
        24 / (-Complex.I * k) ^ 5 := by
  set c : ℂ := -Complex.I * k with hcdef
  have hc : c ≠ 0 := by simp [hcdef, Complex.I_ne_zero, hk]
  have hderiv : ∀ r : ℝ,
      HasDerivAt (fun r : ℝ => ((r:ℂ) ^ 4 / c - 4 * (r:ℂ) ^ 3 / c ^ 2 +
          12 * (r:ℂ) ^ 2 / c ^ 3 - 24 * (r:ℂ) / c ^ 4 + 24 / c ^ 5) * Complex.exp (c * r))
        ((r:ℂ) ^ 4 * Complex.exp (c * r)) r := by
    intro r
    have hidC : HasDerivAt (fun r : ℝ => (r:ℂ)) (1:ℂ) r := (hasDerivAt_id (r:ℂ)).comp_ofReal
    have hr2 : HasDerivAt (fun r : ℝ => (r:ℂ) ^ 2) (2 * (r:ℂ)) r := by
      have h := (hasDerivAt_pow 2 (r:ℂ)).comp_ofReal
      simpa using h
    have hr3 : HasDerivAt (fun r : ℝ => (r:ℂ) ^ 3) (3 * (r:ℂ) ^ 2) r := by
      have h := (hasDerivAt_pow 3 (r:ℂ)).comp_ofReal
      simpa using h
    have hr4 : HasDerivAt (fun r : ℝ => (r:ℂ) ^ 4) (4 * (r:ℂ) ^ 3) r := by
      have h := (hasDerivAt_pow 4 (r:ℂ)).comp_ofReal
      simpa using h
    have hp1 : HasDerivAt (fun r : ℝ => (r:ℂ) ^ 4 / c - 4 * (r:ℂ) ^ 3 / c ^ 2 +
          12 * (r:ℂ) ^ 2 / c ^ 3 - 24 * (r:ℂ) / c ^ 4 + 24 / c ^ 5)
        (4 * (r:ℂ) ^ 3 / c - 12 * (r:ℂ) ^ 2 / c ^ 2 + 24 * (r:ℂ) / c ^ 3 - 24 / c ^ 4) r := by
      have h1 := hr4.div_const c
      have h2 := (hr3.const_mul (4:ℂ)).div_const (c^2)
      have h3 := (hr2.const_mul (12:ℂ)).div_const (c^3)
      have h4 := (hidC.const_mul (24:ℂ)).div_const (c^4)
      have h5 : HasDerivAt (fun _ : ℝ => (24:ℂ) / c ^ 5) 0 r := hasDerivAt_const r _
      have hsum := (((h1.sub h2).add h3).sub h4).add h5
      refine hsum.congr_deriv ?_
      field_simp
      ring
    have hp2 : HasDerivAt (fun r : ℝ => Complex.exp (c * r)) (c * Complex.exp (c * r)) r := by
      have h1 : HasDerivAt (fun z : ℂ => c * z) c (r:ℂ) := by
        have h2 : HasDerivAt (fun z : ℂ => z) (1:ℂ) (r:ℂ) := hasDerivAt_id (r:ℂ)
        simpa using h2.const_mul c
      have h4 := h1.cexp.comp_ofReal
      refine h4.congr_deriv ?_
      ring
    have hprod := hp1.mul hp2
    refine hprod.congr_deriv ?_
    field_simp
    ring
  have hint : IntervalIntegrable (fun r : ℝ => (r:ℂ) ^ 4 * Complex.exp (c * r)) volume 0 sigma := by
    apply Continuous.intervalIntegrable
    exact (Complex.continuous_ofReal.pow 4).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => hderiv r) hint]
  simp

/-! ### Generic quadratic-moment assembly (complex exponential) -/

private lemma integral_quadratic_cexp (A B C : ℝ) {k : ℂ} (hk : k ≠ 0) (sigma : ℝ) :
    ∫ r in (0:ℝ)..sigma, ((A + B * r + C * r ^ 2 : ℝ) : ℂ) *
        Complex.exp (-Complex.I * k * r) =
    (A:ℂ) * (Complex.exp (-Complex.I * k * sigma) / (-Complex.I * k) - 1 / (-Complex.I * k)) +
      (B:ℂ) * (((sigma:ℂ) / (-Complex.I * k) - 1 / (-Complex.I * k) ^ 2) *
          Complex.exp (-Complex.I * k * sigma) + 1 / (-Complex.I * k) ^ 2) +
      (C:ℂ) * (((sigma:ℂ) ^ 2 / (-Complex.I * k) - 2 * (sigma:ℂ) / (-Complex.I * k) ^ 2 +
          2 / (-Complex.I * k) ^ 3) * Complex.exp (-Complex.I * k * sigma) -
        2 / (-Complex.I * k) ^ 3) := by
  have hcongr : ∫ r in (0:ℝ)..sigma,
      ((A + B * r + C * r ^ 2 : ℝ) : ℂ) * Complex.exp (-Complex.I * k * r) =
      ∫ r in (0:ℝ)..sigma,
        ((A:ℂ) * Complex.exp (-Complex.I * k * r) +
            (B:ℂ) * ((r:ℂ) * Complex.exp (-Complex.I * k * r)) +
          (C:ℂ) * ((r:ℂ) ^ 2 * Complex.exp (-Complex.I * k * r))) := by
    apply intervalIntegral.integral_congr
    intro r _
    push_cast
    ring
  rw [hcongr]
  have hiA : IntervalIntegrable (fun r : ℝ => (A:ℂ) * Complex.exp (-Complex.I * k * r))
      volume 0 sigma := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))
  have hiB : IntervalIntegrable
      (fun r : ℝ => (B:ℂ) * ((r:ℂ) * Complex.exp (-Complex.I * k * r))) volume 0 sigma := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (Complex.continuous_ofReal.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)))
  have hiC : IntervalIntegrable
      (fun r : ℝ => (C:ℂ) * ((r:ℂ) ^ 2 * Complex.exp (-Complex.I * k * r))) volume 0 sigma := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul ((Complex.continuous_ofReal.pow 2).mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)))
  rw [intervalIntegral.integral_add (hiA.add hiB) hiC,
      intervalIntegral.integral_add hiA hiB,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      zeta0_formula hk sigma, zeta1_formula hk sigma, zeta2_formula hk sigma]

/-! ### `Qhat_complex` — the entire Fourier transform of `q0_poly` -/

/-- **`Qhat_complex`**: the Fourier transform `q̂0(k) = ∫₀^σ q0_poly(r)·e^{-ikr} dr` of `q0_poly`
(`BaxterRealSpace.lean`), now valued at any complex `k` (not just real `k` as in
`q0poly_cos_integral_formula`/`_sin_integral_formula`). Agrees with `Re[q̂0(k)] - i·Im[q̂0(k)]`
of those two theorems when `k` is real (`e^{-ikr} = cos(kr) - i·sin(kr)`). -/
noncomputable def Qhat_complex (eta sigma rho : ℝ) (k : ℂ) : ℂ :=
  ∫ r in (0:ℝ)..sigma, (q0_poly eta sigma rho r : ℂ) * Complex.exp (-Complex.I * k * r)

/-- `Qhat_complex` rewritten via `q0_poly_inner`'s quadratic expansion on `[0,σ]`. -/
private theorem Qhat_complex_eq_poly (eta sigma rho : ℝ) (hsigma : 0 < sigma) (k : ℂ) :
    Qhat_complex eta sigma rho k =
      ∫ r in (0:ℝ)..sigma,
        (((rho * q_doubleprime_py eta * sigma ^ 2 / 2 - rho * q_prime_py eta sigma * sigma) +
          (rho * q_prime_py eta sigma - rho * q_doubleprime_py eta * sigma) * r +
          (rho * q_doubleprime_py eta / 2) * r ^ 2 : ℝ) : ℂ) *
          Complex.exp (-Complex.I * k * r) := by
  unfold Qhat_complex
  apply intervalIntegral.integral_congr
  intro r hr
  simp only [Set.uIcc_of_le hsigma.le, Set.mem_Icc] at hr
  dsimp only
  rw [q0_poly_inner hr.2]
  push_cast
  ring

/-- **Task POLE.1, entireness half.** `Qhat_complex` is entire (differentiable at every
`k : ℂ`), proved from the raw integral representation via `entire_poly_exp_integral` applied to
the (globally continuous) quadratic form `q0_poly_inner` gives on `[0,σ]` — sidesteps the
closed-form's spurious removable singularity at `k=0` entirely. -/
theorem Qhat_complex_entire (eta sigma rho : ℝ) (hsigma : 0 < sigma) :
    Differentiable ℂ (Qhat_complex eta sigma rho) := by
  have heq : Qhat_complex eta sigma rho =
      fun k : ℂ => ∫ r in (0:ℝ)..sigma,
        (((rho * q_doubleprime_py eta * sigma ^ 2 / 2 - rho * q_prime_py eta sigma * sigma) +
          (rho * q_prime_py eta sigma - rho * q_doubleprime_py eta * sigma) * r +
          (rho * q_doubleprime_py eta / 2) * r ^ 2 : ℝ) : ℂ) *
          Complex.exp (-Complex.I * k * r) := by
    funext k
    exact Qhat_complex_eq_poly eta sigma rho hsigma k
  rw [heq]
  exact entire_poly_exp_integral
    (fun r => rho * q_doubleprime_py eta * sigma ^ 2 / 2 - rho * q_prime_py eta sigma * sigma +
      (rho * q_prime_py eta sigma - rho * q_doubleprime_py eta * sigma) * r +
      rho * q_doubleprime_py eta / 2 * r ^ 2)
    (by fun_prop) sigma hsigma

/-- **Task POLE.1, closed-form half.** `Qhat_complex` in closed form for `k ≠ 0` (complex),
the direct analytic continuation of `q0poly_cos_integral_formula`/`_sin_integral_formula`. -/
theorem Qhat_complex_formula (eta sigma rho : ℝ) (hsigma : 0 < sigma) {k : ℂ} (hk : k ≠ 0) :
    Qhat_complex eta sigma rho k =
    (rho * q_doubleprime_py eta * sigma ^ 2 / 2 - rho * q_prime_py eta sigma * sigma : ℝ) *
        (Complex.exp (-Complex.I * k * sigma) / (-Complex.I * k) - 1 / (-Complex.I * k)) +
      (rho * q_prime_py eta sigma - rho * q_doubleprime_py eta * sigma : ℝ) *
        (((sigma:ℂ) / (-Complex.I * k) - 1 / (-Complex.I * k) ^ 2) *
            Complex.exp (-Complex.I * k * sigma) + 1 / (-Complex.I * k) ^ 2) +
      (rho * q_doubleprime_py eta / 2 : ℝ) *
        (((sigma:ℂ) ^ 2 / (-Complex.I * k) - 2 * (sigma:ℂ) / (-Complex.I * k) ^ 2 +
            2 / (-Complex.I * k) ^ 3) * Complex.exp (-Complex.I * k * sigma) -
          2 / (-Complex.I * k) ^ 3) := by
  rw [Qhat_complex_eq_poly eta sigma rho hsigma,
      integral_quadratic_cexp _ _ _ hk sigma]

end HardSphere

end FMSA
