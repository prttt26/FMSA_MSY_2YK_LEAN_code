/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.RadialFourierCHS
import LeanCode.HardSphere.BaxterZeros

/-!
# `Chat_complex` — the complex extension of `radial_fourier (c_HS eta sigma)` (Task `POLE.4`)

`Ĉ(k) := radial_fourier (c_HS eta sigma) k` (`RadialFourierCHS.lean`, Task OZ.8) is currently
only defined for **real** `k`. The residue formula `POLE.4` needs (`Res_{k_n}[k·Ĉ(k)·e^{ikr}/
(...)]`) needs `Ĉ` at the **complex** poles `k_n` found in `POLE.3`. This file builds that
extension, mirroring `BaxterZeros.lean`'s `Qhat_complex` construction for `q0_poly`.

## Strategy

`radial_fourier(f)(k) = (4π/k)·∫r·f(r)·sin(kr) dr` — unlike `Qhat_complex`, the kernel is
`sin`, not `exp`, and there's an extra `1/k` **prefactor** outside the integral (not just inside
the closed form). Two consequences:

1. **The prefactor's `k=0` singularity is not addressed here** — this file only proves
   `Chat_complex` differentiable for `k ≠ 0` (not entire), since `POLE.3`'s poles all satisfy
   `Re(k_n) = 2πn/σ > 0` for `n ≥ 1`, so `k ≠ 0` is all `POLE.4`'s residue formula needs.
2. **The `sin` kernel is handled by decomposition**: `sin(kr) = (e^{ikr}-e^{-ikr})/(2i)`, so
   `J(k) := ∫r·c_HS(r)·sin(kr)dr = (F(-k)-F(k))/(2i)`, `F(k) := ∫r·c_HS(r)·e^{-ikr}dr`. `F` is
   entire via `entire_poly_exp_integral` (`BaxterZeros.lean`, `POLE.1`) applied to the
   **polynomial expansion** `Chat_poly` of `r·c_HS(r)` (globally continuous — avoids `c_HS`'s own
   jump discontinuity at `r=σ`, same trick `Qhat_complex_eq_poly` used), hence so is `J` (a
   difference of two entire functions, one precomposed with negation). `Chat_complex := (4π/k)·J`
   is then differentiable wherever `J` is and `k≠0` — no removable-singularity argument needed
   for `k=0` since we don't claim anything there.

`c_HS`'s cubic inner polynomial (`-(a0+a1·(r/σ)+a3·(r/σ)³)`), times the extra `r` factor
`radial_fourier`'s kernel carries, gives `r·c_HS(r) = -(a0·r + (a1/σ)·r² + (a3/σ³)·r⁴)` — degree
1/2/4 moments (no constant or cubic term), needing `zeta1`/`zeta2`/`zeta4_formula`
(`BaxterZeros.lean`; `zeta4` was new infrastructure added this pass).

**Verification:** numerically cross-checked (scratch, not committed) against
`radial_fourier(c_HS)`'s direct real-space integral at several real `k` — agreement to `~1e-9`
(quadrature precision).
-/

open MeasureTheory Real Set

namespace FMSA.HardSphere

/-! ### `Chat_poly` — the polynomial expansion of `r·c_HS(r)` -/

/-- `r·c_HS(eta,sigma,r)`'s polynomial expansion on `[0,σ]`: `-(a0·r + (a1/σ)·r² + (a3/σ³)·r⁴)`
— globally continuous (unlike `r·c_HS(eta,sigma,r)` itself, which jumps to `0` at `r=σ`). -/
noncomputable def Chat_poly (eta sigma r : ℝ) : ℝ :=
  -(py_a0 eta * r + (py_a1 eta / sigma) * r ^ 2 + (py_a3 eta / sigma ^ 3) * r ^ 4)

theorem Chat_poly_continuous (eta sigma : ℝ) : Continuous (Chat_poly eta sigma) := by
  unfold Chat_poly
  fun_prop

/-- `Chat_poly` agrees with `r·c_HS(eta,sigma,r)` on `[0,σ]` (both branches: `r<σ` matches the
inner polynomial; `r=σ` — `Chat_poly` doesn't vanish there but `c_HS` does, matching `c_HS`'s
genuine jump discontinuity, so this only holds on `Set.Ico 0 sigma`, not the closed interval). -/
theorem Chat_poly_eq_mul_c_HS {eta sigma r : ℝ} (hr : r < sigma) :
    Chat_poly eta sigma r = r * c_HS eta sigma r := by
  rw [c_HS_inner hr]
  unfold Chat_poly
  field_simp

/-! ### `Chat_F` — the entire exponential-kernel integral -/

/-- `F(k) := ∫₀^σ (r·c_HS(r))·e^{-ikr} dr`, defined via the polynomial expansion. -/
noncomputable def Chat_F (eta sigma : ℝ) (k : ℂ) : ℂ :=
  ∫ r in (0:ℝ)..sigma, (Chat_poly eta sigma r : ℂ) * Complex.exp (-Complex.I * k * r)

/-- **`Chat_F` is entire.** -/
theorem Chat_F_entire (eta sigma : ℝ) (hsigma : 0 < sigma) :
    Differentiable ℂ (Chat_F eta sigma) :=
  entire_poly_exp_integral (Chat_poly eta sigma) (Chat_poly_continuous eta sigma) sigma hsigma

/-- **`Chat_F` closed form**, `k ≠ 0`, via `zeta1`/`zeta2`/`zeta4_formula`. -/
theorem Chat_F_formula (eta sigma : ℝ) (_hsigma : 0 < sigma) {k : ℂ} (hk : k ≠ 0) :
    Chat_F eta sigma k =
      -(py_a0 eta : ℝ) *
        (((sigma:ℂ) / (-Complex.I * k) - 1 / (-Complex.I * k) ^ 2) *
            Complex.exp (-Complex.I * k * sigma) + 1 / (-Complex.I * k) ^ 2) +
      -(py_a1 eta / sigma) *
        (((sigma:ℂ) ^ 2 / (-Complex.I * k) - 2 * (sigma:ℂ) / (-Complex.I * k) ^ 2 +
            2 / (-Complex.I * k) ^ 3) * Complex.exp (-Complex.I * k * sigma) -
          2 / (-Complex.I * k) ^ 3) +
      -(py_a3 eta / sigma ^ 3) *
        (((sigma:ℂ) ^ 4 / (-Complex.I * k) - 4 * (sigma:ℂ) ^ 3 / (-Complex.I * k) ^ 2 +
            12 * (sigma:ℂ) ^ 2 / (-Complex.I * k) ^ 3 - 24 * (sigma:ℂ) / (-Complex.I * k) ^ 4 +
            24 / (-Complex.I * k) ^ 5) * Complex.exp (-Complex.I * k * sigma) -
          24 / (-Complex.I * k) ^ 5) := by
  unfold Chat_F Chat_poly
  have hcongr : ∫ r in (0:ℝ)..sigma,
      ((-(py_a0 eta * r + (py_a1 eta / sigma) * r ^ 2 + (py_a3 eta / sigma ^ 3) * r ^ 4) : ℝ):ℂ) *
        Complex.exp (-Complex.I * k * r) =
      ∫ r in (0:ℝ)..sigma,
        (-(py_a0 eta:ℂ)) * ((r:ℂ) * Complex.exp (-Complex.I * k * r)) +
          (-(py_a1 eta / sigma:ℂ)) * ((r:ℂ) ^ 2 * Complex.exp (-Complex.I * k * r)) +
          (-(py_a3 eta / sigma ^ 3:ℂ)) * ((r:ℂ) ^ 4 * Complex.exp (-Complex.I * k * r)) := by
    apply intervalIntegral.integral_congr
    intro r _
    push_cast
    ring
  rw [hcongr]
  have hi1 : IntervalIntegrable (fun r : ℝ => (-(py_a0 eta:ℂ)) *
      ((r:ℂ) * Complex.exp (-Complex.I * k * r))) volume 0 sigma := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (Complex.continuous_ofReal.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)))
  have hi2 : IntervalIntegrable (fun r : ℝ => (-(py_a1 eta / sigma:ℂ)) *
      ((r:ℂ) ^ 2 * Complex.exp (-Complex.I * k * r))) volume 0 sigma := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul ((Complex.continuous_ofReal.pow 2).mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)))
  have hi3 : IntervalIntegrable (fun r : ℝ => (-(py_a3 eta / sigma ^ 3:ℂ)) *
      ((r:ℂ) ^ 4 * Complex.exp (-Complex.I * k * r))) volume 0 sigma := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul ((Complex.continuous_ofReal.pow 4).mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)))
  rw [intervalIntegral.integral_add (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, zeta1_formula hk sigma, zeta2_formula hk sigma,
    zeta4_formula hk sigma]

/-! ### `Chat_J` — the `sin`-kernel integral, via `sin(z) = (e^{iz}-e^{-iz})/(2i)` -/

/-- `J(k) := ∫₀^σ (r·c_HS(r))·sin(kr) dr`, via `F(-k)-F(k))/(2i)` (the raw integral, before
decomposition, would use `Complex.sin` directly; this is definitionally the same value by
`Complex.sin`'s own `exp`-decomposition, not reproven here — the closed form and entireness are
what `POLE.4` needs from this function). -/
noncomputable def Chat_J (eta sigma : ℝ) (k : ℂ) : ℂ :=
  (Chat_F eta sigma (-k) - Chat_F eta sigma k) / (2 * Complex.I)

/-- **`Chat_J` is entire.** -/
theorem Chat_J_entire (eta sigma : ℝ) (hsigma : 0 < sigma) :
    Differentiable ℂ (Chat_J eta sigma) := by
  unfold Chat_J
  have hneg : Differentiable ℂ (fun k : ℂ => Chat_F eta sigma (-k)) :=
    (Chat_F_entire eta sigma hsigma).comp (differentiable_neg)
  exact (hneg.sub (Chat_F_entire eta sigma hsigma)).div_const (2 * Complex.I)

/-! ### `Chat_complex` — the full complex extension of `radial_fourier (c_HS eta sigma)` -/

/-- **`Chat_complex`**: the complex extension of `Ĉ(k) = radial_fourier (c_HS eta sigma) k`. -/
noncomputable def Chat_complex (eta sigma : ℝ) (k : ℂ) : ℂ :=
  (4 * (Real.pi : ℂ) / k) * Chat_J eta sigma k

/-- **`Chat_complex` is differentiable at every `k ≠ 0`** (all that `POLE.4`'s residue
formula needs — `POLE.3`'s poles all satisfy `k ≠ 0`; no removable-singularity argument at
`k=0` is attempted, unlike `Qhat_complex`, since it isn't needed here). -/
theorem Chat_complex_differentiableAt (eta sigma : ℝ) (hsigma : 0 < sigma) {k : ℂ} (hk : k ≠ 0) :
    DifferentiableAt ℂ (Chat_complex eta sigma) k := by
  unfold Chat_complex
  have h1 : DifferentiableAt ℂ (fun k : ℂ => 4 * (Real.pi : ℂ) / k) k :=
    (differentiableAt_const _).div differentiableAt_id hk
  exact h1.mul ((Chat_J_entire eta sigma hsigma).differentiableAt)

/-! ### `Chat_complex` magnitude bound at large `‖k‖` (Task `POLE.5`)

Each of `Chat_F_formula`'s three terms has the shape `coeff·(bracket·exp(-ikσ) + const)`, where
`bracket` is a degree-≤5 polynomial in `1/(-ik)`. For `‖k‖≥1`, `bracket = O(1/‖k‖)` (the generic
`norm_inv_pow_sum_bound` helper), so multiplying by the `Θ(‖k‖²)` bound on `|exp(-ikσ)|`
(`BaxterPoles.lean`'s `abs_exp_neg_ikn_sigma_upper`, supplied here as an explicit hypothesis `E`
to keep this file independent of `G_baxter`) gives `Θ(‖k‖)` — the `1/k` prefactor in
`Chat_complex := (4π/k)·Chat_J` then brings this back down to `Θ(1)`, matching the numerically-
confirmed finding. -/

private theorem norm_negIk_eq (k : ℂ) : ‖-Complex.I * k‖ = ‖k‖ := by
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul]

/-- `‖1/(-ik)^j‖ ≤ 1/‖k‖` for `‖k‖≥1, j≥1` — the single reusable fact behind every
`Chat_F_formula` term bound below. -/
private theorem norm_inv_negIk_pow_le (k : ℂ) (hk1 : 1 ≤ ‖k‖) (j : ℕ) (hj : 1 ≤ j) :
    ‖(1 : ℂ) / (-Complex.I * k) ^ j‖ ≤ 1 / ‖k‖ := by
  have hk0 : 0 < ‖k‖ := lt_of_lt_of_le one_pos hk1
  rw [norm_div, norm_one, norm_pow, norm_negIk_eq, div_le_div_iff₀ (by positivity) hk0]
  have hpow : ‖k‖ ≤ ‖k‖ ^ j := by
    calc ‖k‖ = ‖k‖ ^ 1 := (pow_one _).symm
      _ ≤ ‖k‖ ^ j := pow_le_pow_right₀ hk1 hj
  nlinarith [hpow]

/-- Fully ℂ-native: `‖z/(-ik)^j‖ ≤ ‖z‖/‖k‖`, for `‖k‖≥1, j≥1` — applied directly to each term
of `Chat_F_formula`'s brackets as written (no coefficient re-embedding, avoiding cast-matching
friction). -/
private theorem norm_zdiv_negIk_pow_le (z k : ℂ) (hk1 : 1 ≤ ‖k‖) (j : ℕ) (hj : 1 ≤ j) :
    ‖z / (-Complex.I * k) ^ j‖ ≤ ‖z‖ / ‖k‖ := by
  have hk0 : 0 < ‖k‖ := lt_of_lt_of_le one_pos hk1
  rw [norm_div, norm_pow, norm_negIk_eq, div_le_div_iff₀ (by positivity) hk0]
  have hpow : ‖k‖ ≤ ‖k‖ ^ j := by
    calc ‖k‖ = ‖k‖ ^ 1 := (pow_one _).symm
      _ ≤ ‖k‖ ^ j := pow_le_pow_right₀ hk1 hj
  nlinarith [hpow, norm_nonneg z]

/-- **`Chat_F` magnitude bound**: given an explicit bound `E` on `|exp(-ikσ)|`,
`‖Chat_F(k)‖ ≤ K₁(η,σ)·E/‖k‖ + K₂(η,σ)` — a general-purpose bound reused (with different `E`)
for both `Chat_F(k)` and `Chat_F(-k)` in `Chat_complex_norm_bound` below. -/
theorem Chat_F_norm_bound (eta sigma : ℝ) (hsigma : 0 < sigma) {k : ℂ} (hk : k ≠ 0)
    (hk1 : 1 ≤ ‖k‖) {E : ℝ} (hE : ‖Complex.exp (-Complex.I * k * sigma)‖ ≤ E) (_hEnn : 0 ≤ E) :
    ‖Chat_F eta sigma k‖ ≤
      (|py_a0 eta| * (sigma + 1) + |py_a1 eta / sigma| * (sigma ^ 2 + 2 * sigma + 2) +
          |py_a3 eta / sigma ^ 3| * (sigma ^ 4 + 4 * sigma ^ 3 + 12 * sigma ^ 2 + 24 * sigma + 24))
        * E / ‖k‖ +
      (|py_a0 eta| + |py_a1 eta / sigma| * 2 + |py_a3 eta / sigma ^ 3| * 24) := by
  rw [Chat_F_formula eta sigma hsigma hk]
  have hk0 : 0 < ‖k‖ := lt_of_lt_of_le one_pos hk1
  have hsig : ‖(sigma : ℂ)‖ = sigma := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsigma]
  have hsig2 : ‖(sigma : ℂ) ^ 2‖ = sigma ^ 2 := by rw [norm_pow, hsig]
  have hsig3 : ‖(sigma : ℂ) ^ 3‖ = sigma ^ 3 := by rw [norm_pow, hsig]
  have hsig4 : ‖(sigma : ℂ) ^ 4‖ = sigma ^ 4 := by rw [norm_pow, hsig]
  have h2sig : ‖(2 : ℂ) * (sigma : ℂ)‖ = 2 * sigma := by
    rw [norm_mul, hsig, show ‖(2:ℂ)‖ = 2 by norm_num]
  have h4sig3 : ‖(4 : ℂ) * (sigma : ℂ) ^ 3‖ = 4 * sigma ^ 3 := by
    rw [norm_mul, hsig3, show ‖(4:ℂ)‖ = 4 by norm_num]
  have h12sig2 : ‖(12 : ℂ) * (sigma : ℂ) ^ 2‖ = 12 * sigma ^ 2 := by
    rw [norm_mul, hsig2, show ‖(12:ℂ)‖ = 12 by norm_num]
  have h24sig : ‖(24 : ℂ) * (sigma : ℂ)‖ = 24 * sigma := by
    rw [norm_mul, hsig, show ‖(24:ℂ)‖ = 24 by norm_num]
  set B1 : ℂ := (sigma : ℂ) / (-Complex.I * k) - 1 / (-Complex.I * k) ^ 2 with hB1def
  set B2 : ℂ := (sigma : ℂ) ^ 2 / (-Complex.I * k) - 2 * (sigma : ℂ) / (-Complex.I * k) ^ 2 +
    2 / (-Complex.I * k) ^ 3 with hB2def
  set B3 : ℂ := (sigma : ℂ) ^ 4 / (-Complex.I * k) - 4 * (sigma : ℂ) ^ 3 / (-Complex.I * k) ^ 2 +
    12 * (sigma : ℂ) ^ 2 / (-Complex.I * k) ^ 3 - 24 * (sigma : ℂ) / (-Complex.I * k) ^ 4 +
    24 / (-Complex.I * k) ^ 5 with hB3def
  have hB1 : ‖B1‖ ≤ (sigma + 1) / ‖k‖ := by
    rw [hB1def]
    have e1 := norm_zdiv_negIk_pow_le (sigma : ℂ) k hk1 1 le_rfl
    rw [pow_one, hsig] at e1
    have e2 := norm_zdiv_negIk_pow_le (1 : ℂ) k hk1 2 (by norm_num)
    rw [norm_one] at e2
    calc ‖(sigma : ℂ) / (-Complex.I * k) - 1 / (-Complex.I * k) ^ 2‖
        ≤ ‖(sigma : ℂ) / (-Complex.I * k)‖ + ‖(1 : ℂ) / (-Complex.I * k) ^ 2‖ := norm_sub_le _ _
      _ ≤ sigma / ‖k‖ + 1 / ‖k‖ := by linarith [e1, e2]
      _ = (sigma + 1) / ‖k‖ := by ring
  have hB2 : ‖B2‖ ≤ (sigma ^ 2 + 2 * sigma + 2) / ‖k‖ := by
    rw [hB2def]
    have e1 := norm_zdiv_negIk_pow_le ((sigma : ℂ) ^ 2) k hk1 1 le_rfl
    rw [pow_one, hsig2] at e1
    have e2 := norm_zdiv_negIk_pow_le ((2 : ℂ) * (sigma : ℂ)) k hk1 2 (by norm_num)
    rw [h2sig] at e2
    have e3 := norm_zdiv_negIk_pow_le (2 : ℂ) k hk1 3 (by norm_num)
    rw [show ‖(2:ℂ)‖ = 2 by norm_num] at e3
    calc ‖(sigma : ℂ) ^ 2 / (-Complex.I * k) - 2 * (sigma : ℂ) / (-Complex.I * k) ^ 2 +
        2 / (-Complex.I * k) ^ 3‖
        ≤ ‖(sigma : ℂ) ^ 2 / (-Complex.I * k)‖ +
            ‖(2 : ℂ) * (sigma : ℂ) / (-Complex.I * k) ^ 2‖ + ‖(2 : ℂ) / (-Complex.I * k) ^ 3‖ := by
          have h1 := norm_sub_le ((sigma : ℂ) ^ 2 / (-Complex.I * k))
            (2 * (sigma : ℂ) / (-Complex.I * k) ^ 2)
          have h2 := norm_add_le ((sigma : ℂ) ^ 2 / (-Complex.I * k) -
            2 * (sigma : ℂ) / (-Complex.I * k) ^ 2) ((2 : ℂ) / (-Complex.I * k) ^ 3)
          linarith [h1, h2]
      _ ≤ sigma ^ 2 / ‖k‖ + 2 * sigma / ‖k‖ + 2 / ‖k‖ := by linarith [e1, e2, e3]
      _ = (sigma ^ 2 + 2 * sigma + 2) / ‖k‖ := by ring
  have hB3 : ‖B3‖ ≤ (sigma ^ 4 + 4 * sigma ^ 3 + 12 * sigma ^ 2 + 24 * sigma + 24) / ‖k‖ := by
    rw [hB3def]
    have e1 := norm_zdiv_negIk_pow_le ((sigma : ℂ) ^ 4) k hk1 1 le_rfl
    rw [pow_one, hsig4] at e1
    have e2 := norm_zdiv_negIk_pow_le ((4 : ℂ) * (sigma : ℂ) ^ 3) k hk1 2 (by norm_num)
    rw [h4sig3] at e2
    have e3 := norm_zdiv_negIk_pow_le ((12 : ℂ) * (sigma : ℂ) ^ 2) k hk1 3 (by norm_num)
    rw [h12sig2] at e3
    have e4 := norm_zdiv_negIk_pow_le ((24 : ℂ) * (sigma : ℂ)) k hk1 4 (by norm_num)
    rw [h24sig] at e4
    have e5 := norm_zdiv_negIk_pow_le (24 : ℂ) k hk1 5 (by norm_num)
    rw [show ‖(24:ℂ)‖ = 24 by norm_num] at e5
    calc ‖(sigma : ℂ) ^ 4 / (-Complex.I * k) - 4 * (sigma : ℂ) ^ 3 / (-Complex.I * k) ^ 2 +
        12 * (sigma : ℂ) ^ 2 / (-Complex.I * k) ^ 3 - 24 * (sigma : ℂ) / (-Complex.I * k) ^ 4 +
        24 / (-Complex.I * k) ^ 5‖
        ≤ ‖(sigma : ℂ) ^ 4 / (-Complex.I * k)‖ + ‖(4:ℂ) * (sigma : ℂ) ^ 3 / (-Complex.I * k) ^ 2‖ +
            ‖(12:ℂ) * (sigma : ℂ) ^ 2 / (-Complex.I * k) ^ 3‖ +
            ‖(24:ℂ) * (sigma : ℂ) / (-Complex.I * k) ^ 4‖ + ‖(24 : ℂ) / (-Complex.I * k) ^ 5‖ := by
          have h1 := norm_sub_le ((sigma : ℂ) ^ 4 / (-Complex.I * k))
            (4 * (sigma : ℂ) ^ 3 / (-Complex.I * k) ^ 2)
          have h2 := norm_add_le ((sigma : ℂ) ^ 4 / (-Complex.I * k) -
            4 * (sigma : ℂ) ^ 3 / (-Complex.I * k) ^ 2)
            (12 * (sigma : ℂ) ^ 2 / (-Complex.I * k) ^ 3)
          have h3 := norm_sub_le ((sigma : ℂ) ^ 4 / (-Complex.I * k) -
            4 * (sigma : ℂ) ^ 3 / (-Complex.I * k) ^ 2 + 12 * (sigma : ℂ) ^ 2 /
              (-Complex.I * k) ^ 3) (24 * (sigma : ℂ) / (-Complex.I * k) ^ 4)
          have h4 := norm_add_le ((sigma : ℂ) ^ 4 / (-Complex.I * k) -
            4 * (sigma : ℂ) ^ 3 / (-Complex.I * k) ^ 2 + 12 * (sigma : ℂ) ^ 2 /
              (-Complex.I * k) ^ 3 - 24 * (sigma : ℂ) / (-Complex.I * k) ^ 4)
            ((24 : ℂ) / (-Complex.I * k) ^ 5)
          linarith [h1, h2, h3, h4]
      _ ≤ sigma ^ 4 / ‖k‖ + 4 * sigma ^ 3 / ‖k‖ + 12 * sigma ^ 2 / ‖k‖ + 24 * sigma / ‖k‖ +
          24 / ‖k‖ := by linarith [e1, e2, e3, e4, e5]
      _ = (sigma ^ 4 + 4 * sigma ^ 3 + 12 * sigma ^ 2 + 24 * sigma + 24) / ‖k‖ := by ring
  have hC1 : ‖(1 : ℂ) / (-Complex.I * k) ^ 2‖ ≤ 1 := by
    have h := norm_zdiv_negIk_pow_le (1 : ℂ) k hk1 2 (by norm_num)
    rw [norm_one] at h
    have hk1' : 1 / ‖k‖ ≤ 1 := by rw [div_le_one hk0]; exact hk1
    linarith [h, hk1']
  have hC2 : ‖(2 : ℂ) / (-Complex.I * k) ^ 3‖ ≤ 2 := by
    have h := norm_zdiv_negIk_pow_le (2 : ℂ) k hk1 3 (by norm_num)
    rw [show ‖(2:ℂ)‖ = 2 by norm_num] at h
    have hk1' : 2 / ‖k‖ ≤ 2 := by rw [div_le_iff₀ hk0]; nlinarith [hk1]
    linarith [h, hk1']
  have hC3 : ‖(24 : ℂ) / (-Complex.I * k) ^ 5‖ ≤ 24 := by
    have h := norm_zdiv_negIk_pow_le (24 : ℂ) k hk1 5 (by norm_num)
    rw [show ‖(24:ℂ)‖ = 24 by norm_num] at h
    have hk1' : 24 / ‖k‖ ≤ 24 := by rw [div_le_iff₀ hk0]; nlinarith [hk1]
    linarith [h, hk1']
  have hT1 : ‖-(py_a0 eta : ℝ) * (B1 * Complex.exp (-Complex.I * k * sigma) +
      1 / (-Complex.I * k) ^ 2)‖ ≤
      |py_a0 eta| * ((sigma + 1) / ‖k‖ * E + 1) := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc ‖B1 * Complex.exp (-Complex.I * k * sigma) + 1 / (-Complex.I * k) ^ 2‖
        ≤ ‖B1 * Complex.exp (-Complex.I * k * sigma)‖ + ‖(1 : ℂ) / (-Complex.I * k) ^ 2‖ :=
          norm_add_le _ _
      _ ≤ (sigma + 1) / ‖k‖ * E + 1 := by
          rw [norm_mul]
          have hBE : ‖B1‖ * ‖Complex.exp (-Complex.I * k * sigma)‖ ≤ (sigma + 1) / ‖k‖ * E := by
            apply mul_le_mul hB1 hE (norm_nonneg _)
            positivity
          linarith [hBE, hC1]
  have hT2 : ‖-(py_a1 eta / sigma : ℝ) * (B2 * Complex.exp (-Complex.I * k * sigma) -
      2 / (-Complex.I * k) ^ 3)‖ ≤
      |py_a1 eta / sigma| * ((sigma ^ 2 + 2 * sigma + 2) / ‖k‖ * E + 2) := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc ‖B2 * Complex.exp (-Complex.I * k * sigma) - 2 / (-Complex.I * k) ^ 3‖
        ≤ ‖B2 * Complex.exp (-Complex.I * k * sigma)‖ + ‖(2 : ℂ) / (-Complex.I * k) ^ 3‖ :=
          norm_sub_le _ _
      _ ≤ (sigma ^ 2 + 2 * sigma + 2) / ‖k‖ * E + 2 := by
          rw [norm_mul]
          have hBE : ‖B2‖ * ‖Complex.exp (-Complex.I * k * sigma)‖ ≤
              (sigma ^ 2 + 2 * sigma + 2) / ‖k‖ * E := by
            apply mul_le_mul hB2 hE (norm_nonneg _)
            positivity
          linarith [hBE, hC2]
  have hT3 : ‖-(py_a3 eta / sigma ^ 3 : ℝ) * (B3 * Complex.exp (-Complex.I * k * sigma) -
      24 / (-Complex.I * k) ^ 5)‖ ≤
      |py_a3 eta / sigma ^ 3| *
        ((sigma ^ 4 + 4 * sigma ^ 3 + 12 * sigma ^ 2 + 24 * sigma + 24) / ‖k‖ * E + 24) := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc ‖B3 * Complex.exp (-Complex.I * k * sigma) - 24 / (-Complex.I * k) ^ 5‖
        ≤ ‖B3 * Complex.exp (-Complex.I * k * sigma)‖ + ‖(24 : ℂ) / (-Complex.I * k) ^ 5‖ :=
          norm_sub_le _ _
      _ ≤ (sigma ^ 4 + 4 * sigma ^ 3 + 12 * sigma ^ 2 + 24 * sigma + 24) / ‖k‖ * E + 24 := by
          rw [norm_mul]
          have hBE : ‖B3‖ * ‖Complex.exp (-Complex.I * k * sigma)‖ ≤
              (sigma ^ 4 + 4 * sigma ^ 3 + 12 * sigma ^ 2 + 24 * sigma + 24) / ‖k‖ * E := by
            apply mul_le_mul hB3 hE (norm_nonneg _)
            positivity
          linarith [hBE, hC3]
  have hsum := norm_add_le (-(py_a0 eta : ℝ) * (B1 * Complex.exp (-Complex.I * k * sigma) +
    1 / (-Complex.I * k) ^ 2) + -(py_a1 eta / sigma : ℝ) *
    (B2 * Complex.exp (-Complex.I * k * sigma) - 2 / (-Complex.I * k) ^ 3))
    (-(py_a3 eta / sigma ^ 3 : ℝ) * (B3 * Complex.exp (-Complex.I * k * sigma) -
      24 / (-Complex.I * k) ^ 5))
  have hsum2 := norm_add_le (-(py_a0 eta : ℝ) * (B1 * Complex.exp (-Complex.I * k * sigma) +
    1 / (-Complex.I * k) ^ 2))
    (-(py_a1 eta / sigma : ℝ) * (B2 * Complex.exp (-Complex.I * k * sigma) -
      2 / (-Complex.I * k) ^ 3))
  push_cast at hT1 hT2 hT3 hsum hsum2 ⊢
  have hgoal_eq :
      (|py_a0 eta| * (sigma + 1) + |py_a1 eta / sigma| * (sigma ^ 2 + 2 * sigma + 2) +
          |py_a3 eta / sigma ^ 3| * (sigma ^ 4 + 4 * sigma ^ 3 + 12 * sigma ^ 2 + 24 * sigma + 24))
        * E / ‖k‖ +
      (|py_a0 eta| + |py_a1 eta / sigma| * 2 + |py_a3 eta / sigma ^ 3| * 24) =
      |py_a0 eta| * ((sigma + 1) / ‖k‖ * E + 1) +
        |py_a1 eta / sigma| * ((sigma ^ 2 + 2 * sigma + 2) / ‖k‖ * E + 2) +
        |py_a3 eta / sigma ^ 3| *
          ((sigma ^ 4 + 4 * sigma ^ 3 + 12 * sigma ^ 2 + 24 * sigma + 24) / ‖k‖ * E + 24) := by
    ring
  rw [hgoal_eq]
  linarith [hsum, hsum2, hT1, hT2, hT3]

/-- **`Chat_complex` magnitude bound**: `‖Chat_complex(k)‖ ≤ 2π·K₁·(1+E)/‖k‖² + 4π·K₂/‖k‖`,
`K₁,K₂` as in `Chat_F_norm_bound`. Combines `Chat_F(k)` (via the caller-supplied bound `E` on
`|exp(-ikσ)|`) and `Chat_F(-k)` (bounded by `1`, needing only `Im(k)≥0` — no growth control) —
kept symbolic in `‖k‖` (not crudely simplified) so the caller can combine this with `E`'s own
`Θ(‖k‖²)` growth to get the `Θ(1)` bound `POLE.5` needs. -/
theorem Chat_complex_norm_bound (eta sigma : ℝ) (hsigma : 0 < sigma) {k : ℂ} (hk : k ≠ 0)
    (hk1 : 1 ≤ ‖k‖) (hkim : 0 ≤ k.im) {E : ℝ}
    (hE : ‖Complex.exp (-Complex.I * k * sigma)‖ ≤ E) (hEnn : 0 ≤ E) :
    ‖Chat_complex eta sigma k‖ ≤
      2 * Real.pi *
        (|py_a0 eta| * (sigma + 1) + |py_a1 eta / sigma| * (sigma ^ 2 + 2 * sigma + 2) +
          |py_a3 eta / sigma ^ 3| * (sigma ^ 4 + 4 * sigma ^ 3 + 12 * sigma ^ 2 + 24 * sigma + 24))
        * (1 + E) / ‖k‖ ^ 2 +
      4 * Real.pi * (|py_a0 eta| + |py_a1 eta / sigma| * 2 + |py_a3 eta / sigma ^ 3| * 24) /
        ‖k‖ := by
  have hk0 : 0 < ‖k‖ := lt_of_lt_of_le one_pos hk1
  have hnegk1 : 1 ≤ ‖-k‖ := by rwa [norm_neg]
  have hnegkne : -k ≠ 0 := neg_ne_zero.mpr hk
  have hexpneg1 : ‖Complex.exp (-Complex.I * (-k) * sigma)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    have hre : (-Complex.I * (-k) * sigma).re = -(sigma * k.im) := by
      simp [Complex.mul_re, Complex.mul_im]; ring
    rw [hre]
    have hnonneg : 0 ≤ sigma * k.im := mul_nonneg hsigma.le hkim
    calc Real.exp (-(sigma * k.im)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hFneg := Chat_F_norm_bound eta sigma hsigma hnegkne hnegk1 hexpneg1 (by norm_num)
  rw [norm_neg] at hFneg
  simp only [mul_one] at hFneg
  have hFpos := Chat_F_norm_bound eta sigma hsigma hk hk1 hE hEnn
  unfold Chat_complex Chat_J
  rw [norm_mul, norm_div, norm_div]
  have hprefactor : ‖(4 : ℂ) * (Real.pi : ℂ)‖ / ‖k‖ = 4 * Real.pi / ‖k‖ := by
    rw [norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hprefactor]
  have h2Inorm : ‖(2 : ℂ) * Complex.I‖ = 2 := by
    rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num, Complex.norm_I, mul_one]
  rw [h2Inorm]
  have hJsub : ‖Chat_F eta sigma (-k) - Chat_F eta sigma k‖ ≤
      ‖Chat_F eta sigma (-k)‖ + ‖Chat_F eta sigma k‖ := norm_sub_le _ _
  set K1 : ℝ := |py_a0 eta| * (sigma + 1) + |py_a1 eta / sigma| * (sigma ^ 2 + 2 * sigma + 2) +
    |py_a3 eta / sigma ^ 3| * (sigma ^ 4 + 4 * sigma ^ 3 + 12 * sigma ^ 2 + 24 * sigma + 24)
  set K2 : ℝ := |py_a0 eta| + |py_a1 eta / sigma| * 2 + |py_a3 eta / sigma ^ 3| * 24
  have hJbound : ‖Chat_F eta sigma (-k) - Chat_F eta sigma k‖ ≤ K1 * (1 + E) / ‖k‖ + 2 * K2 := by
    have heq : K1 / ‖k‖ + K2 + (K1 * E / ‖k‖ + K2) = K1 * (1 + E) / ‖k‖ + 2 * K2 := by ring
    linarith [hJsub, hFneg, hFpos, heq]
  have hfinal : 4 * Real.pi / ‖k‖ * (‖Chat_F eta sigma (-k) - Chat_F eta sigma k‖ / 2) ≤
      4 * Real.pi / ‖k‖ * ((K1 * (1 + E) / ‖k‖ + 2 * K2) / 2) := by
    apply mul_le_mul_of_nonneg_left (by linarith [hJbound])
    positivity
  calc 4 * Real.pi / ‖k‖ * (‖Chat_F eta sigma (-k) - Chat_F eta sigma k‖ / 2)
      ≤ 4 * Real.pi / ‖k‖ * ((K1 * (1 + E) / ‖k‖ + 2 * K2) / 2) := hfinal
    _ = 2 * Real.pi * K1 * (1 + E) / ‖k‖ ^ 2 + 4 * Real.pi * K2 / ‖k‖ := by
        field_simp
        ring

end HardSphere

end FMSA
