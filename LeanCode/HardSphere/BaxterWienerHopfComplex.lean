/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterResidue
import LeanCode.HardSphere.BaxterWienerHopf

/-!
# Task OZFIX.2 — complex-`k` extension of the Baxter Wiener–Hopf factorization

`baxter_wiener_hopf_factorization` (`BaxterWienerHopf.lean`, Task `BAXTER.3`) gives, at **real**
`k ≠ 0`:

    `(1 - Qhat(k)) * (1 - Qhat(-k)) = 1 - ρ·Chat_complex(k)`

(written there via explicit `cos`/`sin` integrals rather than `Qhat_complex` directly). `OZFIX.2`
needs this identity at the **complex** poles `k_n` of `G_baxter` (which have `Im(k_n) > 0`), since
`residue_term`'s numerator uses `Chat_complex` while `G_baxter`'s zero condition
(`baxter_cube_mul_F_eq_G`, `BaxterPoles.lean`) is stated via `Qhat_complex` — no lemma connected
these two off the real axis before this file.

## Strategy

Rather than re-deriving the real-axis proof's algebra (`q0poly_cos/sin_integral_formula` vs.
`radial_fourier_c_HS_formula`, closed via a Pythagorean `sin²+cos²=1` substitution) directly for
complex `k`, this file **analytically continues** the already-proven real-axis identity via the
one-variable **identity theorem** (`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`,
Mathlib): both sides of the target identity are holomorphic on `ℂ \ {0}` (a preconnected set,
`isConnected_compl_singleton_of_one_lt_rank`), and they agree on the (real) punctured neighborhood
of any nonzero real point, which suffices to force equality on all of `ℂ \ {0}`. This avoids
redoing the `field_simp`/Pythagorean-identity algebra in the complex setting.

## Pieces

1. `Qhat_complex_eq_cos_sub_I_sin` / `Qhat_complex_conj_eq_neg`: real/imaginary decomposition and
   conjugate symmetry of `Qhat_complex` at real `k`, both via the interval-integral real/imaginary
   splitting technique (`ContinuousLinearMap.intervalIntegral_comp_comm` for conjugation,
   `intervalIntegral.integral_ofReal` for the split).
2. `Chat_complex_eq_radial_fourier`: `Chat_complex` agrees with the real radial sine-transform
   `radial_fourier (c_HS eta sigma)` at real `k` — a domain-reduction (`Ioi 0 → [0,σ]`, mirroring
   `OZExteriorBridge.lean`'s `radial3d_conv_cHS_eq_Ioo`) plus an `exp(±ikr) → cos/sin` conversion.
3. `baxter_wiener_hopf_complex_real`: combines (1)+(2)+`baxter_wiener_hopf_factorization` into the
   complex-valued identity at real `k ≠ 0`.
4. `baxter_wiener_hopf_complex`: the complex-`k` extension via the identity theorem.
-/

open MeasureTheory Real Set intervalIntegral Filter Topology

namespace FMSA.HardSphere

/-! ### `Qhat_complex` at real `k`: real/imaginary decomposition and conjugate symmetry -/

/-- `Qhat_complex` at a real `k`, split into its real (`cos`) and imaginary (`-sin`) parts. -/
theorem Qhat_complex_eq_cos_sub_I_sin {eta sigma rho : ℝ} {k : ℝ} :
    Qhat_complex eta sigma rho (k:ℂ) =
      ((∫ r in (0:ℝ)..sigma, q0_poly eta sigma rho r * Real.cos (k * r) : ℝ):ℂ) -
        Complex.I * ((∫ r in (0:ℝ)..sigma, q0_poly eta sigma rho r * Real.sin (k * r) : ℝ):ℂ) := by
  unfold Qhat_complex
  have hcontpoly : Continuous (fun r : ℝ => (q0_poly eta sigma rho r : ℂ)) :=
    Complex.continuous_ofReal.comp (q0_poly_continuous eta sigma rho)
  have hcos : Continuous (fun r : ℝ => (q0_poly eta sigma rho r : ℂ) * (Real.cos (k * r) : ℂ)) :=
    hcontpoly.mul (Complex.continuous_ofReal.comp (by fun_prop))
  have hsin : Continuous (fun r : ℝ => (q0_poly eta sigma rho r : ℂ) * (Real.sin (k * r) : ℂ)) :=
    hcontpoly.mul (Complex.continuous_ofReal.comp (by fun_prop))
  have hpt : ∀ r : ℝ, (q0_poly eta sigma rho r : ℂ) * Complex.exp (-Complex.I * (k:ℂ) * (r:ℂ)) =
      (q0_poly eta sigma rho r : ℂ) * (Real.cos (k * r) : ℂ) -
        Complex.I * ((q0_poly eta sigma rho r : ℂ) * (Real.sin (k * r) : ℂ)) := by
    intro r
    have hz : (-Complex.I * (k:ℂ) * (r:ℂ)) = ((-(k * r) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hz, Complex.exp_mul_I]
    push_cast
    simp only [Complex.cos_neg, Complex.sin_neg]
    ring
  calc ∫ r in (0:ℝ)..sigma, (q0_poly eta sigma rho r : ℂ) * Complex.exp (-Complex.I * (k:ℂ) * r)
      = ∫ r in (0:ℝ)..sigma, ((q0_poly eta sigma rho r : ℂ) * (Real.cos (k * r) : ℂ) -
          Complex.I * ((q0_poly eta sigma rho r : ℂ) * (Real.sin (k * r) : ℂ))) :=
        intervalIntegral.integral_congr (fun r _ => hpt r)
    _ = (∫ r in (0:ℝ)..sigma, (q0_poly eta sigma rho r : ℂ) * (Real.cos (k * r) : ℂ)) -
          ∫ r in (0:ℝ)..sigma,
            Complex.I * ((q0_poly eta sigma rho r : ℂ) * (Real.sin (k * r) : ℂ)) :=
        intervalIntegral.integral_sub (hcos.intervalIntegrable 0 sigma)
          ((continuous_const.mul hsin).intervalIntegrable 0 sigma)
    _ = ((∫ r in (0:ℝ)..sigma, q0_poly eta sigma rho r * Real.cos (k * r) : ℝ):ℂ) -
          Complex.I *
            ((∫ r in (0:ℝ)..sigma, q0_poly eta sigma rho r * Real.sin (k * r) : ℝ):ℂ) := by
        rw [show (fun r : ℝ => (q0_poly eta sigma rho r : ℂ) * (Real.cos (k * r) : ℂ)) =
            (fun r : ℝ => ((q0_poly eta sigma rho r * Real.cos (k * r) : ℝ) : ℂ)) from by
          funext r; push_cast; ring]
        rw [show (fun r : ℝ => Complex.I * ((q0_poly eta sigma rho r : ℂ) *
            (Real.sin (k * r) : ℂ))) =
            (fun r : ℝ => Complex.I * ((q0_poly eta sigma rho r * Real.sin (k * r) : ℝ) : ℂ)) from
            by funext r; push_cast; ring]
        rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_ofReal]

/-- **Conjugate symmetry** of `Qhat_complex` at real `k`: `Qhat_complex` is the Fourier transform
of a real-valued function, so `conj(Qhat(k)) = Qhat(-k)` — proved by commuting conjugation
(`Complex.conjCLE`, an `ℝ`-linear continuous map) past the interval integral
(`ContinuousLinearMap.intervalIntegral_comp_comm`) and `Complex.exp_conj` pointwise. -/
theorem Qhat_complex_conj_eq_neg {eta sigma rho : ℝ} {k : ℝ} :
    (starRingEnd ℂ) (Qhat_complex eta sigma rho (k:ℂ)) =
      Qhat_complex eta sigma rho (-(k:ℂ)) := by
  unfold Qhat_complex
  have hcont : Continuous (fun r : ℝ => (q0_poly eta sigma rho r : ℂ) *
      Complex.exp (-Complex.I * (k:ℂ) * r)) := by
    have h1 : Continuous (fun r : ℝ => (q0_poly eta sigma rho r : ℂ)) :=
      Complex.continuous_ofReal.comp (q0_poly_continuous eta sigma rho)
    exact h1.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hint : IntervalIntegrable (fun r : ℝ => (q0_poly eta sigma rho r : ℂ) *
      Complex.exp (-Complex.I * (k:ℂ) * r)) volume 0 sigma := hcont.intervalIntegrable 0 sigma
  have hL := ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ)
    (Complex.conjCLE : ℂ →L[ℝ] ℂ) hint
  simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] at hL
  rw [← hL]
  apply intervalIntegral.integral_congr
  intro r _
  change (starRingEnd ℂ) ((q0_poly eta sigma rho r : ℂ) *
      Complex.exp (-Complex.I * (k:ℂ) * (r:ℂ))) =
      (q0_poly eta sigma rho r : ℂ) * Complex.exp (-Complex.I * (-(k:ℂ)) * (r:ℂ))
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  ring

/-! ### `Chat_complex` at real `k`: agrees with `radial_fourier (c_HS eta sigma)` -/

/-- `Chat_complex` (the complex extension of the OZ hard-sphere DCF transform) agrees with the
real radial sine-transform `radial_fourier (c_HS eta sigma)` at any real `k`. Domain reduction
(`Set.Ioi 0 → [0,σ]`) mirrors `OZExteriorBridge.lean`'s `radial3d_conv_cHS_eq_Ioo`; the
`exp(±ikr) → sin(kr)` step mirrors `Qhat_complex_eq_cos_sub_I_sin`'s technique. -/
theorem Chat_complex_eq_radial_fourier {eta sigma : ℝ} (hsigma : 0 < sigma) {k : ℝ} :
    Chat_complex eta sigma (k : ℂ) = ((radial_fourier (c_HS eta sigma) k : ℝ) : ℂ) := by
  have hIoo : ∫ r in Set.Ioi (0:ℝ), r * c_HS eta sigma r * Real.sin (k * r) =
      ∫ r in Set.Ioo (0:ℝ) sigma, r * c_HS eta sigma r * Real.sin (k * r) := by
    rw [← Ioo_union_Ici_eq_Ioi hsigma]
    apply MeasureTheory.integral_union_eq_left_of_forall isClosed_Ici.measurableSet
    intro t ht
    simp [c_HS_outer ht]
  have hInterval : ∫ r in Set.Ioo (0:ℝ) sigma, r * c_HS eta sigma r * Real.sin (k * r) =
      ∫ r in (0:ℝ)..sigma, r * c_HS eta sigma r * Real.sin (k * r) := by
    rw [intervalIntegral.integral_of_le hsigma.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc,
      MeasureTheory.integral_Icc_eq_integral_Ioo]
  have hpoly : ∫ r in (0:ℝ)..sigma, r * c_HS eta sigma r * Real.sin (k * r) =
      ∫ r in (0:ℝ)..sigma, Chat_poly eta sigma r * Real.sin (k * r) := by
    apply intervalIntegral.integral_congr_uIoo
    intro r hr
    rw [Set.uIoo_of_le hsigma.le] at hr
    change r * c_HS eta sigma r * Real.sin (k * r) = Chat_poly eta sigma r * Real.sin (k * r)
    rw [Chat_poly_eq_mul_c_HS hr.2]
  have hcontpoly : Continuous (fun r : ℝ => (Chat_poly eta sigma r : ℂ)) :=
    Complex.continuous_ofReal.comp (Chat_poly_continuous eta sigma)
  have hcontexp : ∀ c : ℂ, Continuous (fun r : ℝ => Complex.exp (-Complex.I * c * r)) := fun c =>
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hJ : Chat_J eta sigma (k:ℂ) =
      ((∫ r in (0:ℝ)..sigma, Chat_poly eta sigma r * Real.sin (k * r) : ℝ) : ℂ) := by
    unfold Chat_J Chat_F
    have hexp : ∀ r : ℝ, Complex.exp (-Complex.I * (-(k:ℂ)) * r) -
        Complex.exp (-Complex.I * (k:ℂ) * r) =
        ((2 * Real.sin (k * r) : ℝ) : ℂ) * Complex.I := by
      intro r
      have h1 : (-Complex.I * (-(k:ℂ)) * r) = ((k * r : ℝ):ℂ) * Complex.I := by push_cast; ring
      have h2 : (-Complex.I * (k:ℂ) * r) = ((-(k * r) : ℝ):ℂ) * Complex.I := by push_cast; ring
      rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I]
      push_cast
      simp only [Complex.cos_neg, Complex.sin_neg]
      ring
    have hcont1 : IntervalIntegrable (fun r : ℝ => (Chat_poly eta sigma r : ℂ) *
        Complex.exp (-Complex.I * (-(k:ℂ)) * r)) volume 0 sigma :=
      (hcontpoly.mul (hcontexp (-(k:ℂ)))).intervalIntegrable 0 sigma
    have hcont2 : IntervalIntegrable (fun r : ℝ => (Chat_poly eta sigma r : ℂ) *
        Complex.exp (-Complex.I * (k:ℂ) * r)) volume 0 sigma :=
      (hcontpoly.mul (hcontexp (k:ℂ))).intervalIntegrable 0 sigma
    rw [← intervalIntegral.integral_sub hcont1 hcont2]
    have hrw : (fun r : ℝ => (Chat_poly eta sigma r : ℂ) *
          Complex.exp (-Complex.I * (-(k:ℂ)) * r) -
        (Chat_poly eta sigma r : ℂ) * Complex.exp (-Complex.I * (k:ℂ) * r)) =
        (fun r : ℝ => ((Chat_poly eta sigma r * (2 * Real.sin (k * r)) : ℝ) : ℂ) * Complex.I) := by
      funext r
      rw [← mul_sub, hexp r]
      push_cast
      ring
    rw [show (∫ r in (0:ℝ)..sigma, (Chat_poly eta sigma r : ℂ) *
          Complex.exp (-Complex.I * (-(k:ℂ)) * r) -
        (Chat_poly eta sigma r : ℂ) * Complex.exp (-Complex.I * (k:ℂ) * r)) =
        ∫ r in (0:ℝ)..sigma, ((Chat_poly eta sigma r * (2 * Real.sin (k * r)) : ℝ) : ℂ) *
          Complex.I from by rw [hrw]]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
    rw [show (∫ x in (0:ℝ)..sigma, Chat_poly eta sigma x * (2 * Real.sin (k * x))) =
        2 * ∫ x in (0:ℝ)..sigma, Chat_poly eta sigma x * Real.sin (k * x) from by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      ring]
    push_cast
    field_simp
  unfold Chat_complex
  rw [hJ, ← hpoly, ← hInterval, ← hIoo]
  unfold radial_fourier
  push_cast
  ring

/-! ### Real-axis complex Wiener–Hopf identity, then its complex-`k` extension -/

/-- **Complex-valued Wiener–Hopf factorization, real `k`.** Combines
`Qhat_complex_eq_cos_sub_I_sin`/`Qhat_complex_conj_eq_neg` (turning
`baxter_wiener_hopf_factorization`'s `(1-Re)²+(Im)²` shape into a product) with
`Chat_complex_eq_radial_fourier`. -/
theorem baxter_wiener_hopf_complex_real {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (heta : eta < 1) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) {k : ℝ} (hk : k ≠ 0) :
    (1 - Qhat_complex eta sigma rho (k:ℂ)) * (1 - Qhat_complex eta sigma rho (-(k:ℂ))) =
      1 - (rho:ℂ) * Chat_complex eta sigma (k:ℂ) := by
  set A : ℝ := ∫ r in (0:ℝ)..sigma, q0_poly eta sigma rho r * Real.cos (k * r) with hA
  set B : ℝ := ∫ r in (0:ℝ)..sigma, q0_poly eta sigma rho r * Real.sin (k * r) with hB
  have hk1 : Qhat_complex eta sigma rho (k:ℂ) = (A:ℂ) - Complex.I * (B:ℂ) :=
    Qhat_complex_eq_cos_sub_I_sin
  have hk2 : Qhat_complex eta sigma rho (-(k:ℂ)) = (A:ℂ) + Complex.I * (B:ℂ) := by
    rw [← Qhat_complex_conj_eq_neg, hk1]
    simp [map_sub, map_mul, Complex.conj_I]
  have hreal : (1 - A) ^ 2 + B ^ 2 = 1 - rho * radial_fourier (c_HS eta sigma) k :=
    baxter_wiener_hopf_factorization eta sigma rho k hsigma hk heta heta_def
  rw [hk1, hk2]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hstep : (1 - ((A:ℂ) - Complex.I * (B:ℂ))) * (1 - ((A:ℂ) + Complex.I * (B:ℂ))) =
      (((1 - A) ^ 2 + B ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [hI]
    ring
  rw [hstep, hreal, Chat_complex_eq_radial_fourier hsigma]
  push_cast
  ring

/-- **Complex-`k` Wiener–Hopf factorization (Task `OZFIX.2` bridge).** Analytically
continues `baxter_wiener_hopf_complex_real` from the real axis to all of `k ≠ 0` via the
one-variable identity theorem: both sides are holomorphic on the preconnected set `{k ≠ 0}`
(`Qhat_complex_entire` is unconditionally entire; `Chat_complex` is holomorphic away from `0`,
`Chat_complex_differentiableAt`), and they agree on a real punctured neighborhood of `1`. -/
theorem baxter_wiener_hopf_complex {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (heta : eta < 1) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) {k : ℂ} (hk : k ≠ 0) :
    (1 - Qhat_complex eta sigma rho k) * (1 - Qhat_complex eta sigma rho (-k)) =
      1 - (rho:ℂ) * Chat_complex eta sigma k := by
  set f : ℂ → ℂ := fun k => (1 - Qhat_complex eta sigma rho k) *
    (1 - Qhat_complex eta sigma rho (-k)) with hf_def
  set g : ℂ → ℂ := fun k => 1 - (rho:ℂ) * Chat_complex eta sigma k with hg_def
  suffices h : Set.EqOn f g {k : ℂ | k ≠ 0} from h hk
  have hpc : IsPreconnected ({(0:ℂ)}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) _).isPreconnected
  have hz0 : (1:ℂ) ∈ ({(0:ℂ)}ᶜ : Set ℂ) := by simp
  have hf_diff : Differentiable ℂ f :=
    (differentiable_const 1|>.sub (Qhat_complex_entire eta sigma rho hsigma)).mul
      (differentiable_const 1|>.sub
        ((Qhat_complex_entire eta sigma rho hsigma).comp differentiable_neg))
  have hfa : AnalyticOnNhd ℂ f ({(0:ℂ)}ᶜ : Set ℂ) :=
    hf_diff.differentiableOn.analyticOnNhd isOpen_compl_singleton
  have hga : AnalyticOnNhd ℂ g ({(0:ℂ)}ᶜ : Set ℂ) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
    intro z hz
    have hz' : z ≠ 0 := hz
    exact ((differentiableAt_const 1).sub
      ((differentiableAt_const (rho:ℂ)).mul
        (Chat_complex_differentiableAt eta sigma hsigma hz'))).differentiableWithinAt
  have hxseq : Tendsto (fun n : ℕ => ((1 + 1 / ((n:ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (1:ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h1 : Tendsto (fun n : ℕ => (1 + 1 / ((n:ℝ) + 1) : ℝ)) atTop (𝓝 (1:ℝ)) := by
        have h2 : Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) atTop (𝓝 (0:ℝ)) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using h2.const_add 1
      exact (Complex.continuous_ofReal.tendsto 1).comp h1
    · apply Eventually.of_forall
      intro n
      simp only [Set.mem_compl_singleton_iff]
      intro hcontra
      have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      have heq := Complex.ofReal_injective hcontra
      linarith [heq]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1:ℂ), f z = g z := by
    apply hxseq.frequently
    apply Eventually.frequently
    apply Eventually.of_forall
    intro n
    change (1 - Qhat_complex eta sigma rho _) * (1 - Qhat_complex eta sigma rho (-_)) =
      1 - (rho:ℂ) * Chat_complex eta sigma _
    exact baxter_wiener_hopf_complex_real hsigma heta heta_def (by positivity)
  exact hfa.eqOn_of_preconnected_of_frequently_eq hga hpc hz0 hfreq

end FMSA.HardSphere
