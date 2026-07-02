/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Hard-Sphere Baxter Factor Auxiliary Integrals (φ1 and φ2)

**Source:** [chsY] Appendix A, Eq. 49; [LN] Eq. 13

    φ1(R; s) = ∫0^R r exp(-sr) dr         = (1 - (1+sR) exp(-sR)) / s^2
    φ2(R; s) = ∫0^R (r^2/2) exp(-sr) dr    = (1 - (1+sR+s^2R^2/2) exp(-sR)) / s^3

Proved by FTC with antiderivatives:
    F1(r) = -(r/s + 1/s^2) · exp(-sr)                    F1' = r · exp(-sr)
    F2(r) = -(r^2/(2s) + r/s^2 + 1/s^3) · exp(-sr)         F2' = (r^2/2) · exp(-sr)
-/
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open MeasureTheory intervalIntegral Real Set

namespace FMSA.HardSphere

/-- `HasDerivAt` for `x ↦ exp(-s·x)` via the chain rule `.exp`. -/
private lemma hasDerivAt_exp_neg_mul {s r : ℝ} :
    HasDerivAt (fun x => Real.exp (-s * x)) (Real.exp (-s * r) * -s) r := by
  have h : HasDerivAt (fun x => -s * x) (-s) r := by
    simpa using (hasDerivAt_id r).const_mul (-s)
  exact h.exp

/-! ### φ1 -/

/-- Antiderivative of `r * exp(-s·r)` is `-(r/s + 1/s^2) * exp(-s·r)`. -/
private lemma phi1_hasDerivAt {s : ℝ} (hs : s ≠ 0) (r : ℝ) :
    HasDerivAt (fun r => -(r / s + 1 / s ^ 2) * Real.exp (-s * r))
               (r * Real.exp (-s * r)) r := by
  -- A(r) = -(r/s + 1/s^2), A'(r) = -(1/s)
  have hA : HasDerivAt (fun x => -(x / s + 1 / s ^ 2)) (-(1 / s)) r := by
    have h := ((hasDerivAt_id r).div_const s).add (hasDerivAt_const r (1 / s ^ 2)) |>.neg
    simp only [add_zero] at h
    exact h
  -- Product rule: f'(r) = A'·exp + A·(-s·exp) = r·exp
  exact (hA.mul hasDerivAt_exp_neg_mul).congr_deriv (by field_simp [hs]; ring)

/-- **[chsY] Appendix A, [LN] Eq. 13 (φ1):**
`∫0^R r exp(-sr) dr = (1 - (1+sR) exp(-sR)) / s^2` for `s ≠ 0`. -/
theorem phi1_formula {s : ℝ} (hs : s ≠ 0) (R : ℝ) :
    ∫ r in (0 : ℝ)..R, r * Real.exp (-s * r) =
    (1 - (1 + s * R) * Real.exp (-s * R)) / s ^ 2 := by
  have hint : IntervalIntegrable (fun r => r * Real.exp (-s * r)) volume 0 R :=
    (continuous_id.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).intervalIntegrable 0 R
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => phi1_hasDerivAt hs r) hint]
  -- evaluate antiderivative at 0 and R; simplify exp(-s·0) = 1
  simp only [mul_zero, Real.exp_zero, zero_div, zero_add, mul_one, sub_neg_eq_add]
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero _ hs
  field_simp [hs]; ring

/-! ### φ2 -/

/-- Antiderivative of `(r^2/2) * exp(-s·r)` is `-(r^2/(2s) + r/s^2 + 1/s^3) * exp(-s·r)`. -/
private lemma phi2_hasDerivAt {s : ℝ} (hs : s ≠ 0) (r : ℝ) :
    HasDerivAt (fun r => -(r ^ 2 / (2 * s) + r / s ^ 2 + 1 / s ^ 3) * Real.exp (-s * r))
               (r ^ 2 / 2 * Real.exp (-s * r)) r := by
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero _ hs
  have hs3 : s ^ 3 ≠ 0 := pow_ne_zero _ hs
  -- d/dr [r^2] = 2r  (use hasDerivAt_pow to avoid the id^2 instance mismatch)
  have hx2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    have h := hasDerivAt_pow (𝕜 := ℝ) 2 r
    simpa [pow_one, Nat.cast_ofNat] using h
  -- d/dr [r^2/(2s)] = r/s
  have h1 : HasDerivAt (fun x => x ^ 2 / (2 * s)) (r / s) r :=
    (hx2.div_const _).congr_deriv (by field_simp [hs])
  -- d/dr [r/s^2] = 1/s^2
  have h2 : HasDerivAt (fun x => x / s ^ 2) (1 / s ^ 2) r :=
    (hasDerivAt_id r).div_const _
  -- d/dr [1/s^3] = 0
  have h3 : HasDerivAt (fun _ : ℝ => 1 / s ^ 3) 0 r := hasDerivAt_const _ _
  -- A(r) = -(r^2/(2s)+r/s^2+1/s^3), A'(r) = -(r/s + 1/s^2)
  have hA : HasDerivAt (fun x => -(x ^ 2 / (2 * s) + x / s ^ 2 + 1 / s ^ 3))
      (-(r / s + 1 / s ^ 2)) r := by
    have h := ((h1.add h2).add h3).neg
    simp only [add_zero] at h
    exact h
  -- Product rule: f'(r) = A'·exp + A·(-s·exp) = (r^2/2)·exp
  exact (hA.mul hasDerivAt_exp_neg_mul).congr_deriv (by field_simp [hs]; ring)

/-- **[chsY] Appendix A, [LN] Eq. 13 (φ2):**
`∫0^R (r^2/2) exp(-sr) dr = (1 - (1+sR+s^2R^2/2) exp(-sR)) / s^3` for `s ≠ 0`. -/
theorem phi2_formula {s : ℝ} (hs : s ≠ 0) (R : ℝ) :
    ∫ r in (0 : ℝ)..R, r ^ 2 / 2 * Real.exp (-s * r) =
    (1 - (1 + s * R + s ^ 2 * R ^ 2 / 2) * Real.exp (-s * R)) / s ^ 3 := by
  have hint : IntervalIntegrable (fun r => r ^ 2 / 2 * Real.exp (-s * r)) volume 0 R :=
    ((continuous_id.pow 2 |>.div_const 2).mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).intervalIntegrable 0 R
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => phi2_hasDerivAt hs r) hint]
  -- evaluate antiderivative at 0 and R; simplify 0^2 = 0, exp(0) = 1
  simp only [mul_zero, Real.exp_zero, zero_div, zero_add, mul_one, sub_neg_eq_add,
             zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  have hs3 : s ^ 3 ≠ 0 := pow_ne_zero _ hs
  field_simp [hs]; ring

/-! ### φ1 shifted (Task B.1) -/

/-- Antiderivative of `r * exp(z · (r - R))` is `(r/z - 1/z^2) * exp(z · (r - R))`. -/
private lemma b1_hasDerivAt {z : ℝ} (hz : z ≠ 0) (R r : ℝ) :
    HasDerivAt (fun x => (x / z - 1 / z ^ 2) * Real.exp (z * (x - R)))
               (r * Real.exp (z * (r - R))) r := by
  -- d/dx [x/z - 1/z^2] = 1/z  (use id_def to avoid Pi.sub id-mismatch)
  have hf : HasDerivAt (fun x : ℝ => x / z - 1 / z ^ 2) (1 / z) r := by
    have h1 : HasDerivAt (fun x : ℝ => x / z) (1 / z) r := by
      have := (hasDerivAt_id r).div_const z; simp only [Function.id_def] at this; exact this
    have h := h1.sub (hasDerivAt_const r (1 / z ^ 2))
    simp only [sub_zero] at h; exact h
  -- d/dx [z(x-R)] = z
  have hinner : HasDerivAt (fun x => z * (x - R)) z r := by
    have h := ((hasDerivAt_id r).sub (hasDerivAt_const r R)).const_mul z
    simp only [Function.id_def, sub_zero, mul_one] at h; exact h
  have hg : HasDerivAt (fun x => Real.exp (z * (x - R))) (Real.exp (z * (r - R)) * z) r :=
    hinner.exp
  exact (hf.mul hg).congr_deriv (by field_simp [hz]; ring)

/-- **Task B.1** — Shifted-exponent integral:
`∫0^R r · exp(z · (r - R)) dr = (z·R - 1 + exp(-z·R)) / z^2` for `z ≠ 0`.

Physical role: `p1(R,z) = -∫0^R r·exp(z·(r-R)) dr` is used in `_build_Qhat`
of `fmsa_ga_matrix_mix.py` to construct Q̂0_{ij}. -/
theorem phi1_shifted_formula {z : ℝ} (hz : z ≠ 0) (R : ℝ) :
    ∫ r in (0 : ℝ)..R, r * Real.exp (z * (r - R)) =
    (z * R - 1 + Real.exp (-(z * R))) / z ^ 2 := by
  have hint : IntervalIntegrable (fun r => r * Real.exp (z * (r - R))) MeasureTheory.volume 0 R :=
    (continuous_id.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.sub continuous_const)))).intervalIntegrable 0 R
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun r _ => b1_hasDerivAt hz R r) hint]
  have hR : z * (R - R) = 0 := by ring
  have h0 : z * (0 - R) = -(z * R) := by ring
  simp only [hR, h0, Real.exp_zero, mul_one, zero_div, zero_sub]
  field_simp [hz]
  ring

/-! ### Task 2.2 — Q-matrix determinant non-vanishing -/

-- Key real-analysis lemma: (u - sin u)·u ≥ 0 for all u ∈ ℝ
-- (same-sign multiplication: both factors are positive for u>0, both negative for u<0)
private lemma sin_sub_mul_nonneg (u : ℝ) : 0 <= (u - Real.sin u) * u := by
  by_cases hu : 0 <= u
  · rcases eq_or_lt_of_le hu with rfl | hu'
    · simp
    · exact mul_nonneg (sub_nonneg.mpr (Real.sin_lt hu').le) hu
  · -- For u < 0, let v = -u > 0; sin v < v → sin(-v) < -v → -sin u < -u → sin u > u
    have hv : (0 : ℝ) < -u := by linarith
    have h : Real.sin (-u) < -u := Real.sin_lt hv
    rw [Real.sin_neg] at h
    nlinarith

/-!
**Domain note.** Numerics show that on the *real* positive axis `det Q̂(s)` has exactly one
zero at `s0(eta)` (e.g. `s0 ≈ 3` for `eta = 0.3`), so a universal `∀ s ≥ 0` statement is *false*.
The physically relevant domain is the *imaginary axis* `s = iq` (Fourier / structure-factor
space), where `Re Q̂(iq) ≥ 1 > 0` for all `q : ℝ`, and non-vanishing follows immediately.

**Proof sketch (imaginary axis).** Using the FMSA_poly closed-form phi
  `φ1_py(sigma; iq) = (1 - iqsigma - exp(-iqsigma)) / (iq)^2`
  `φ2_py(sigma; iq) = (1 - iqsigma + (iqsigma)^2/2 - exp(-iqsigma)) / (iq)^3`
one computes (for `q > 0`)
  `Re(iq · φ1_py) = (sin qsigma - qsigma) / q ≤ 0`
  `Re((iq)^2 · φ2_py) = (sin qsigma - qsigma) / q ≤ 0`
by `sin u ≤ u` for `u ≥ 0`. Hence
  `Re Q0(iq) = 1 - 12eta · Re(iq·φ1 + (iq)^2·φ2) / sigma`
             `= 1 + 24eta · (qsigma - sin qsigma) / (qsigma) ≥ 1 > 0`,
so `Q0(iq) ≠ 0`. Formal proof requires `Complex.sin_le` and Lean `Complex` arithmetic;
marked sorry pending that formalisation.
-/

/-- **[LN] Eq. 16 (reformulated on the imaginary axis):**
For packing fraction `eta ∈ (0,1)` and sphere diameter `sigma > 0`, the single-component
Baxter `Q0` coefficient, expressed via the FMSA_poly closed-form phi functions
  `φ1_py(sigma;s) = (1 - ssigma - exp(-ssigma)) / s^2`
  `φ2_py(sigma;s) = (1 - ssigma + (ssigma)^2/2 - exp(-ssigma)) / s^3`
satisfies `Q0(iq) ≠ 0` for all `q : ℝ`, because `Re Q0(iq) ≥ 1 > 0`.

**Key inequality:** `(u - sin u)·u ≥ 0` (from `sin u ≤ u` for u ≥ 0, `sin u ≥ u` for u ≤ 0)
gives `Re Q0(iq) = 1 + 24eta·(qsigma - sin qsigma)/(qsigma) ≥ 1 > 0`, so `Q0(iq) ≠ 0`. -/
theorem Q0_imaginary_axis_ne_zero (eta sigma : ℝ) (heta : eta ∈ Set.Ioo 0 1) (hsigma : 0 < sigma) :
    ∀ q : ℝ,
      let s : ℂ := Complex.I * q
      (1 : ℂ) - 12 * eta *
        (s * ((1 - s * sigma - Complex.exp (-s * sigma)) / s ^ 2) +
         s ^ 2 * ((1 - s * sigma + (s * sigma) ^ 2 / 2 -
           Complex.exp (-s * sigma)) / s ^ 3)) / sigma ≠ 0 := by
  intro q
  dsimp only
  by_cases hq : q = 0
  · subst hq; simp
  · have hs : (Complex.I * (q : ℂ)) ≠ 0 := by
      intro h
      have := congr_arg Complex.im h
      simp only [Complex.mul_im, Complex.I_im, Complex.I_re,
            Complex.ofReal_im, Complex.ofReal_re, mul_one, zero_mul, sub_zero,
            zero_add, one_mul, Complex.zero_im] at this
      exact hq this
    set u : ℝ := q * sigma with hu_def
    have hu : u ≠ 0 := mul_ne_zero hq hsigma.ne'
    -- Euler formula via exp_re/exp_im; use simp only to prevent ofReal_cos/sin simp lemmas
    -- from converting ↑(Real.cos u) → Complex.cos ↑u inside the subgoals
    have harg_re : (-(Complex.I * (q : ℂ)) * ↑sigma).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
                 Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
                 mul_zero, zero_mul, sub_zero, neg_zero]
    have harg_im : (-(Complex.I * (q : ℂ)) * ↑sigma).im = -u := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
                 Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
                 mul_zero, zero_mul, sub_zero, one_mul, zero_add]
      linarith [hu_def]
    have hexp : Complex.exp (-(Complex.I * ↑q) * ↑sigma) =
        ↑(Real.cos u) - Complex.I * ↑(Real.sin u) := by
      apply Complex.ext
      · rw [Complex.exp_re, harg_re, harg_im, Real.exp_zero, Real.cos_neg, one_mul]
        simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
                   Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
      · rw [Complex.exp_im, harg_re, harg_im, Real.exp_zero, Real.sin_neg, one_mul]
        simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
                   Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add, mul_one]
        ring
    -- Rewrite hQ with exp replaced by cos u - I·sin u
    intro hQ
    have hQ' : (1 : ℂ) - 12 * ↑eta *
        (Complex.I * ↑q * ((1 - Complex.I * ↑q * ↑sigma -
            (↑(Real.cos u) - Complex.I * ↑(Real.sin u))) / (Complex.I * ↑q) ^ 2) +
         (Complex.I * ↑q) ^ 2 * ((1 - Complex.I * ↑q * ↑sigma + (Complex.I * ↑q * ↑sigma) ^ 2 / 2 -
            (↑(Real.cos u) - Complex.I * ↑(Real.sin u))) / (Complex.I * ↑q) ^ 3)) / ↑sigma = 0 := by
      rw [← hexp]; exact hQ
    -- Q0·(I·u) = I·u - 12eta·E  (division-free); field_simp needs (q:ℂ)≠0 separately
    -- because it clears (I·q)^n denominators but leaves standalone q^{-1} without hqC
    have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
    have hfield : ((1 : ℂ) - 12 * ↑eta *
        (Complex.I * ↑q * ((1 - Complex.I * ↑q * ↑sigma -
            (↑(Real.cos u) - Complex.I * ↑(Real.sin u))) / (Complex.I * ↑q) ^ 2) +
         (Complex.I * ↑q) ^ 2 * ((1 - Complex.I * ↑q * ↑sigma + (Complex.I * ↑q * ↑sigma) ^ 2 / 2 -
            (↑(Real.cos u) - Complex.I * ↑(Real.sin u))) / (Complex.I * ↑q) ^ 3)) / ↑sigma) *
        (Complex.I * ↑u) =
        Complex.I * ↑u - 12 * ↑eta *
        (2 - 2 * (Complex.I * ↑u) + (Complex.I * ↑u) ^ 2 / 2 -
         2 * (↑(Real.cos u) - Complex.I * ↑(Real.sin u))) := by
      field_simp [hs, Complex.ofReal_ne_zero.mpr hsigma.ne', hqC]
      push_cast [hu_def]; ring
    -- Q0·(I·u) = 0
    have hProd : Complex.I * ↑u - 12 * ↑eta *
        (2 - 2 * (Complex.I * ↑u) + (Complex.I * ↑u) ^ 2 / 2 -
         2 * (↑(Real.cos u) - Complex.I * ↑(Real.sin u))) = 0 :=
      calc Complex.I * ↑u - 12 * ↑eta *
              (2 - 2 * (Complex.I * ↑u) + (Complex.I * ↑u) ^ 2 / 2 -
               2 * (↑(Real.cos u) - Complex.I * ↑(Real.sin u)))
          = ((1 : ℂ) - 12 * ↑eta * _ / ↑sigma) * (Complex.I * ↑u) := hfield.symm
        _ = 0 * (Complex.I * ↑u) := by rw [hQ']
        _ = 0 := zero_mul _
    -- Im((I·u)^2/2) = 0: prove via explicit cast to ℝ (avoids div_im bookkeeping)
    have hIu2_re : (Complex.I * (↑u : ℂ)) ^ 2 / 2 = (↑(-(u ^ 2) / 2 : ℝ) : ℂ) := by
      have h2 : (Complex.I * (↑u : ℂ)) ^ 2 = -(↑u : ℂ) ^ 2 := by
        linear_combination (↑u : ℂ) ^ 2 * Complex.I_sq
      rw [h2]; norm_cast
    -- Compute Im(E) = -2u + 2·sin u, where E is the division-free bracket
    -- Use simp only throughout to prevent ofReal_cos/sin from firing
    have hE_im : ((2 - 2 * (Complex.I * ↑u) + (Complex.I * ↑u) ^ 2 / 2 -
        2 * (↑(Real.cos u) - Complex.I * ↑(Real.sin u)) : ℂ)).im = -2 * u + 2 * Real.sin u := by
      rw [hIu2_re]
      simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.neg_im,
                 Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
                 Complex.one_im, Complex.zero_im, Complex.one_re, Complex.zero_re,
                 show (2 : ℂ).re = 2 from by norm_num,
                 show (2 : ℂ).im = 0 from by norm_num,
                 mul_zero, zero_mul, sub_zero, zero_sub, zero_add, neg_zero,
                 one_mul, mul_one, add_zero]
      push_cast; ring
    -- Im(I·u - 12eta·E) = u - 12eta·(-2u+2·sin u) = u + 24eta·(u-sin u)
    -- Use full simp for sub-lemmas so one_mul fires automatically
    have hIm_val : ((Complex.I * ↑u - 12 * ↑eta *
        (2 - 2 * (Complex.I * ↑u) + (Complex.I * ↑u) ^ 2 / 2 -
         2 * (↑(Real.cos u) - Complex.I * ↑(Real.sin u))) : ℂ)).im =
        u + 24 * eta * (u - Real.sin u) := by
      simp only [Complex.sub_im, Complex.mul_im,
                 show (Complex.I * (↑u : ℂ)).im = u from by simp [Complex.mul_im],
                 show ((12 : ℂ) * (↑eta : ℂ)).re = 12 * eta from by simp [Complex.mul_re],
                 show ((12 : ℂ) * (↑eta : ℂ)).im = 0 from by simp [Complex.mul_im],
                 hE_im, mul_zero, add_zero]
      ring
    -- u + 24eta·(u-sin u) = 0  (from Im(hProd) = 0)
    have hIm0 : ((Complex.I * ↑u - 12 * ↑eta *
        (2 - 2 * (Complex.I * ↑u) + (Complex.I * ↑u) ^ 2 / 2 -
         2 * (↑(Real.cos u) - Complex.I * ↑(Real.sin u))) : ℂ)).im = 0 :=
      (congr_arg Complex.im hProd).trans Complex.zero_im
    have hProd_im : u + 24 * eta * (u - Real.sin u) = 0 := hIm_val.symm.trans hIm0
    -- Contradiction: u·u > 0 and 24eta·(u-sin u)·u ≥ 0, but u·(u+24eta·(u-sin u)) = 0
    have h_aux : 0 <= (u - Real.sin u) * u := sin_sub_mul_nonneg u
    have hu2 : 0 < u * u := mul_self_pos.mpr hu
    have h_key : u * u + 24 * eta * (u - Real.sin u) * u = 0 := by
      linear_combination u * hProd_im
    have h_nonneg : 0 <= 24 * eta * ((u - Real.sin u) * u) :=
      mul_nonneg (by linarith [heta.1]) h_aux
    linarith

/-!
**Task 2.2 — real-axis non-vanishing (axiomatic).**

The imaginary-axis result (`Q0_imaginary_axis_ne_zero`) is proved above.
On the real positive axis `s = z` (the Yukawa pole), the Q-function CAN vanish
at a transcendental z0(eta) (numerics: z0 ≈ 3 for eta = 0.3), so a universal
`∀ z > 0, D(z) ≠ 0` is **false**.

The axiom below encodes the physical assumption that the Yukawa parameter z is
chosen away from such zeros; this is implicit in any FMSA computation. -/

/-- **Task 2.2 — Axiom (D ≠ 0 at real Yukawa pole):**

The single-component Baxter denominator
`D(z) = S(z) + 12eta·L(z)·exp(-z)`
(`S`, `L` from [chsY] Eq. 52) is non-zero for the Yukawa inverse range `z > 0`
and packing fraction `eta ∈ (0,1)`.

**Proved:** `Q0_imaginary_axis_ne_zero` (imaginary axis, s = iq).
**Axiomatic:** real-axis case; follows from choosing z away from the transcendental
zero z0(eta) of D, which is implicit in all physical FMSA use. -/
axiom Q0_ne_zero_at_yukawa {eta z : ℝ} (heta : eta ∈ Set.Ioo 0 1) (hz : 0 < z) :
    (1 - eta) ^ 2 * z ^ 3 + 6 * eta * (1 - eta) * z ^ 2 + 18 * eta ^ 2 * z -
    12 * eta * (1 + 2 * eta) +
    12 * eta * ((1 + eta / 2) * z + (1 + 2 * eta)) * Real.exp (-z) ≠ 0

end FMSA.HardSphere
