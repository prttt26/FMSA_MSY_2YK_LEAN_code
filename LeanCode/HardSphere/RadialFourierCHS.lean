/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.RadialFourier
import LeanCode.HardSphere.PYOZ

/-!
# Task OZ.8 — closed-form sine-transform of `c_HS` + bridge to `C_HS_laplace`/`S0`

## Summary

`OZFourierBridge.lean` (Task OZ.7) proves the Fourier-domain OZ equation unconditionally, but
leaves `radial_fourier (c_HS eta sigma) k` as an abstract transform, not a closed form. This
file supplies that closed form (`radial_fourier_c_HS_formula`, Part A) and proves it agrees
with `C_HS_laplace_formula` (`PYOZ.lean`) under the substitution `s ↦ -i·k` (Part B) — via
*direct algebraic computation* on the two already-known closed forms, not general
analytic-continuation/identity-theorem machinery.

**Not attempted here (deliberately out of scope):** deriving `g0_HS_contact_value` from this.
That needs inverting the closed-form-in-`k` Fourier-domain OZ solution back to real space
(residue calculus / the classical PY closed-form solution) — a multi-session undertaking
comparable to the Baxter Wiener–Hopf work already flagged elsewhere as out of scope. See
`proof_notes_hard_sphere.md` Task OZ.8 for the full scoping discussion (Part C was eventually
supplied by a different route — see "Piece C" below, Task `BAXTER.7`, `proof_notes_baxter.md`).
-/

open MeasureTheory Set Real intervalIntegral

namespace FMSA.HardSphere

/-! ### Piece A.1 — domain reduction: `Ioi 0` to `[0,sigma]` -/

/-- **`radial_fourier (c_HS eta sigma) k` reduces to a finite `intervalIntegral` on
`[0,sigma]`.** `c_HS` vanishes identically for `r ≥ sigma`, so the `Set.Ioi 0` integral in
`radial_fourier`'s definition equals the `Set.Ioc 0 sigma` integral — via the same
indicator-rewrite technique as `setIntegral_Icc_eq_setIntegral_Ioi_indicator`
(`RadialFourier.lean`), used in the reverse direction. -/
theorem radial_fourier_c_HS_eq_intervalIntegral (eta sigma k : ℝ) (hsigma : 0 < sigma) :
    radial_fourier (c_HS eta sigma) k =
      (4 * Real.pi / k) * ∫ r in (0 : ℝ)..sigma, r * c_HS eta sigma r * Real.sin (k * r) := by
  unfold radial_fourier
  congr 1
  have hpt : Set.EqOn (fun r => r * c_HS eta sigma r * Real.sin (k * r))
      ((Set.Ioc 0 sigma).indicator (fun r => r * c_HS eta sigma r * Real.sin (k * r)))
      (Set.Ioi (0 : ℝ)) := by
    intro r hr0
    by_cases hr : r ∈ Set.Ioc (0 : ℝ) sigma
    · rw [Set.indicator_of_mem hr]
    · rw [Set.indicator_of_notMem hr]
      have hrge : sigma ≤ r := by
        simp only [Set.mem_Ioc, not_and, not_le] at hr
        exact (hr hr0).le
      simp [c_HS_outer hrge]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt,
    MeasureTheory.setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_self_of_subset_right Set.Ioc_subset_Ioi_self,
    ← intervalIntegral.integral_of_le hsigma.le]

/-! ### Piece A.2 — sine-power antiderivatives `∫ r^n sin(k·r) dr`, `n = 1, 2, 4`

Mirrors `phi1/phi2/phi4_formula` (`BaxterFactor.lean`/`PYOZ.lean`): guess the standard
integration-by-parts antiderivative, verify it via `HasDerivAt` + the product rule, then apply
`intervalIntegral.integral_eq_sub_of_hasDerivAt`. Antiderivatives numerically verified via
`sympy` before formalizing (residual `F'(r) - r^n·sin(k·r) = 0` for symbolic `r,k`). -/

private lemma hasDerivAt_sin_mul {k r : ℝ} :
    HasDerivAt (fun x => Real.sin (k * x)) (Real.cos (k * r) * k) r := by
  have h : HasDerivAt (fun x => k * x) k r := by simpa using (hasDerivAt_id r).const_mul k
  exact h.sin

private lemma hasDerivAt_cos_mul {k r : ℝ} :
    HasDerivAt (fun x => Real.cos (k * x)) (-Real.sin (k * r) * k) r := by
  have h : HasDerivAt (fun x => k * x) k r := by simpa using (hasDerivAt_id r).const_mul k
  exact h.cos

/-! #### ψ1 -/

/-- Antiderivative of `r·sin(k·r)` is `sin(k·r)/k² - r·cos(k·r)/k`. -/
private lemma psi1_hasDerivAt {k : ℝ} (hk : k ≠ 0) (r : ℝ) :
    HasDerivAt (fun r => Real.sin (k * r) / k ^ 2 - r * Real.cos (k * r) / k)
               (r * Real.sin (k * r)) r := by
  have hT1 : HasDerivAt (fun x => Real.sin (k * x) / k ^ 2) (Real.cos (k * r) * k / k ^ 2) r :=
    hasDerivAt_sin_mul.div_const (k ^ 2)
  have hT2 : HasDerivAt (fun x => x * Real.cos (k * x) / k)
      ((1 * Real.cos (k * r) + r * (-Real.sin (k * r) * k)) / k) r :=
    ((hasDerivAt_id r).mul hasDerivAt_cos_mul).div_const k
  exact (hT1.sub hT2).congr_deriv (by field_simp; ring)

/-- **ψ1 formula:** `∫0^sigma r·sin(k·r) dr = (sin(k·sigma) - k·sigma·cos(k·sigma)) / k²`. -/
theorem psi1_formula {k : ℝ} (hk : k ≠ 0) (sigma : ℝ) :
    ∫ r in (0 : ℝ)..sigma, r * Real.sin (k * r) =
    (Real.sin (k * sigma) - k * sigma * Real.cos (k * sigma)) / k ^ 2 := by
  have hint : IntervalIntegrable (fun r => r * Real.sin (k * r)) volume 0 sigma :=
    (continuous_id.mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).intervalIntegrable 0 sigma
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => psi1_hasDerivAt hk r) hint]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, zero_div, mul_one, zero_sub]
  field_simp [hk]; ring

/-! #### ψ2 -/

/-- Antiderivative of `r²·sin(k·r)` is `(2/k³ - r²/k)·cos(k·r) + (2r/k²)·sin(k·r)`. -/
private lemma psi2_hasDerivAt {k : ℝ} (hk : k ≠ 0) (r : ℝ) :
    HasDerivAt (fun r => (2 / k ^ 3 - r ^ 2 / k) * Real.cos (k * r) +
      (2 * r / k ^ 2) * Real.sin (k * r)) (r ^ 2 * Real.sin (k * r)) r := by
  have hx2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    have h := hasDerivAt_pow (𝕜 := ℝ) 2 r; simpa [Nat.cast_ofNat, pow_one] using h
  have hA : HasDerivAt (fun x => 2 / k ^ 3 - x ^ 2 / k) (-(2 * r / k)) r := by
    have h := (hasDerivAt_const r (2 / k ^ 3)).sub (hx2.div_const k)
    exact h.congr_deriv (by ring)
  have hB : HasDerivAt (fun x => 2 * x / k ^ 2) (2 / k ^ 2) r := by
    have h := ((hasDerivAt_id r).const_mul 2).div_const (k ^ 2)
    exact h.congr_deriv (by ring)
  have hT1 : HasDerivAt (fun x => (2 / k ^ 3 - x ^ 2 / k) * Real.cos (k * x))
      (-(2 * r / k) * Real.cos (k * r) + (2 / k ^ 3 - r ^ 2 / k) * (-Real.sin (k * r) * k)) r :=
    hA.mul hasDerivAt_cos_mul
  have hT2 : HasDerivAt (fun x => (2 * x / k ^ 2) * Real.sin (k * x))
      ((2 / k ^ 2) * Real.sin (k * r) + (2 * r / k ^ 2) * (Real.cos (k * r) * k)) r :=
    hB.mul hasDerivAt_sin_mul
  exact (hT1.add hT2).congr_deriv (by field_simp [hk]; ring)

/-- **ψ2 formula:**
`∫0^sigma r²·sin(k·r) dr = (2/k³ - sigma²/k)·cos(k·sigma) + (2·sigma/k²)·sin(k·sigma) - 2/k³`. -/
theorem psi2_formula {k : ℝ} (hk : k ≠ 0) (sigma : ℝ) :
    ∫ r in (0 : ℝ)..sigma, r ^ 2 * Real.sin (k * r) =
    (2 / k ^ 3 - sigma ^ 2 / k) * Real.cos (k * sigma) +
      (2 * sigma / k ^ 2) * Real.sin (k * sigma) - 2 / k ^ 3 := by
  have hint : IntervalIntegrable (fun r => r ^ 2 * Real.sin (k * r)) volume 0 sigma :=
    ((continuous_id.pow 2).mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).intervalIntegrable 0 sigma
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => psi2_hasDerivAt hk r) hint]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, zero_div, mul_one, zero_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, sub_zero]
  ring

/-! #### ψ4 -/

/-- Antiderivative of `r⁴·sin(k·r)` is
`(-24/k⁵ + 12r²/k³ - r⁴/k)·cos(k·r) + (-24r/k⁴ + 4r³/k²)·sin(k·r)`. -/
private lemma psi4_hasDerivAt {k : ℝ} (hk : k ≠ 0) (r : ℝ) :
    HasDerivAt (fun r => (-24 / k ^ 5 + 12 * r ^ 2 / k ^ 3 - r ^ 4 / k) * Real.cos (k * r) +
      (-24 * r / k ^ 4 + 4 * r ^ 3 / k ^ 2) * Real.sin (k * r))
      (r ^ 4 * Real.sin (k * r)) r := by
  have hx2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    have h := hasDerivAt_pow (𝕜 := ℝ) 2 r; simpa [Nat.cast_ofNat, pow_one] using h
  have hx3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * r ^ 2) r := by
    have h := hasDerivAt_pow (𝕜 := ℝ) 3 r; simpa [Nat.cast_ofNat] using h
  have hx4 : HasDerivAt (fun x : ℝ => x ^ 4) (4 * r ^ 3) r := by
    have h := hasDerivAt_pow (𝕜 := ℝ) 4 r; simpa [Nat.cast_ofNat] using h
  have hA : HasDerivAt (fun x => -24 / k ^ 5 + 12 * x ^ 2 / k ^ 3 - x ^ 4 / k)
      (12 * (2 * r) / k ^ 3 - 4 * r ^ 3 / k) r := by
    have h := ((hasDerivAt_const r (-24 / k ^ 5)).fun_add
      ((hx2.div_const (k ^ 3)).const_mul 12)).fun_sub (hx4.div_const k)
    simp only [← mul_div_assoc] at h
    rw [show (0 : ℝ) + 12 * (2 * r) / k ^ 3 - 4 * r ^ 3 / k =
        12 * (2 * r) / k ^ 3 - 4 * r ^ 3 / k from by ring] at h
    exact h
  have hB : HasDerivAt (fun x => -24 * x / k ^ 4 + 4 * x ^ 3 / k ^ 2)
      (-24 / k ^ 4 + 4 * (3 * r ^ 2) / k ^ 2) r := by
    have h := (((hasDerivAt_id r).const_mul (-24)).div_const (k ^ 4)).fun_add
      ((hx3.div_const (k ^ 2)).const_mul 4)
    simp only [id_eq, ← mul_div_assoc] at h
    rw [show -24 * (1 : ℝ) / k ^ 4 + 4 * (3 * r ^ 2) / k ^ 2 =
        -24 / k ^ 4 + 4 * (3 * r ^ 2) / k ^ 2 from by ring] at h
    exact h
  have hT1 : HasDerivAt (fun x => (-24 / k ^ 5 + 12 * x ^ 2 / k ^ 3 - x ^ 4 / k) * Real.cos (k * x))
      ((12 * (2 * r) / k ^ 3 - 4 * r ^ 3 / k) * Real.cos (k * r) +
        (-24 / k ^ 5 + 12 * r ^ 2 / k ^ 3 - r ^ 4 / k) * (-Real.sin (k * r) * k)) r :=
    hA.mul hasDerivAt_cos_mul
  have hT2 : HasDerivAt (fun x => (-24 * x / k ^ 4 + 4 * x ^ 3 / k ^ 2) * Real.sin (k * x))
      ((-24 / k ^ 4 + 4 * (3 * r ^ 2) / k ^ 2) * Real.sin (k * r) +
        (-24 * r / k ^ 4 + 4 * r ^ 3 / k ^ 2) * (Real.cos (k * r) * k)) r :=
    hB.mul hasDerivAt_sin_mul
  exact (hT1.add hT2).congr_deriv (by field_simp [hk]; ring)

/-- **ψ4 formula:** `∫0^sigma r⁴·sin(k·r) dr =`
`(-24/k⁵ + 12sigma²/k³ - sigma⁴/k)·cos(k·sigma)`
`+ (-24sigma/k⁴ + 4sigma³/k²)·sin(k·sigma) + 24/k⁵`. -/
theorem psi4_formula {k : ℝ} (hk : k ≠ 0) (sigma : ℝ) :
    ∫ r in (0 : ℝ)..sigma, r ^ 4 * Real.sin (k * r) =
    (-24 / k ^ 5 + 12 * sigma ^ 2 / k ^ 3 - sigma ^ 4 / k) * Real.cos (k * sigma) +
      (-24 * sigma / k ^ 4 + 4 * sigma ^ 3 / k ^ 2) * Real.sin (k * sigma) + 24 / k ^ 5 := by
  have hint : IntervalIntegrable (fun r => r ^ 4 * Real.sin (k * r)) volume 0 sigma :=
    ((continuous_id.pow 4).mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).intervalIntegrable 0 sigma
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => psi4_hasDerivAt hk r) hint]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, zero_div, mul_one, zero_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, sub_zero]
  ring

/-! ### Piece A.3 — assembly: closed-form sine-transform of `c_HS` -/

/-- **Task OZ.8, Part A — the closed-form sine-transform of `c_HS`.** Mirrors
`C_HS_laplace_formula`'s three-term structure exactly (`py_a0` term over `k²`, `py_a1` term
over `k³` with `/sigma`, `py_a3` term over `k⁵` with `/sigma³`), swapping the `phi1/phi2/phi4`
exponential antiderivatives for the `psi1/psi2/psi4` sine counterparts (Piece A.2). The
`c_HS`-vs-polynomial swap tolerates the single differing point `r = sigma` via `uIoo`
congruence, the same technique used throughout this codebase for this exact discontinuity
(`C_HS_laplace_eq_cHS`, `oz_forcing_integral_eq_movingBound`). -/
theorem radial_fourier_c_HS_formula (eta sigma k : ℝ) (hsigma : 0 < sigma) (hk : k ≠ 0) :
    radial_fourier (c_HS eta sigma) k =
    (4 * Real.pi / k) *
      (-py_a0 eta * (Real.sin (k * sigma) - k * sigma * Real.cos (k * sigma)) / k ^ 2 +
        -(py_a1 eta / sigma) *
          ((2 / k ^ 3 - sigma ^ 2 / k) * Real.cos (k * sigma) +
            (2 * sigma / k ^ 2) * Real.sin (k * sigma) - 2 / k ^ 3) +
        -(py_a3 eta / sigma ^ 3) *
          ((-24 / k ^ 5 + 12 * sigma ^ 2 / k ^ 3 - sigma ^ 4 / k) * Real.cos (k * sigma) +
            (-24 * sigma / k ^ 4 + 4 * sigma ^ 3 / k ^ 2) * Real.sin (k * sigma) +
            24 / k ^ 5)) := by
  rw [radial_fourier_c_HS_eq_intervalIntegral eta sigma k hsigma]
  congr 1
  have hexpand : Set.EqOn
      (fun r => r * c_HS eta sigma r * Real.sin (k * r))
      (fun r => (-py_a0 eta) * (r * Real.sin (k * r)) +
        (-(py_a1 eta / sigma)) * (r ^ 2 * Real.sin (k * r)) +
        (-(py_a3 eta / sigma ^ 3)) * (r ^ 4 * Real.sin (k * r)))
      (Set.uIoo (0 : ℝ) sigma) := by
    intro r hr
    rw [Set.uIoo_of_le hsigma.le] at hr
    simp only
    rw [c_HS_inner hr.2]
    field_simp
    ring
  rw [intervalIntegral.integral_congr_uIoo hexpand]
  have hi1 : IntervalIntegrable (fun r => (-py_a0 eta) * (r * Real.sin (k * r))) volume 0 sigma :=
    (continuous_const.mul (continuous_id.mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)))).intervalIntegrable 0 sigma
  have hi2 : IntervalIntegrable
      (fun r => (-(py_a1 eta / sigma)) * (r ^ 2 * Real.sin (k * r))) volume 0 sigma :=
    (continuous_const.mul ((continuous_id.pow 2).mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)))).intervalIntegrable 0 sigma
  have hi4 : IntervalIntegrable
      (fun r => (-(py_a3 eta / sigma ^ 3)) * (r ^ 4 * Real.sin (k * r))) volume 0 sigma :=
    (continuous_const.mul ((continuous_id.pow 4).mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)))).intervalIntegrable 0 sigma
  rw [intervalIntegral.integral_add (hi1.add hi2) hi4,
      intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      psi1_formula hk sigma, psi2_formula hk sigma, psi4_formula hk sigma]
  ring

/-! ### Piece B — bridge to `C_HS_laplace_formula`/`S0` via `s ↔ -ik`

No complex antiderivative work and no analytic-continuation/identity-theorem machinery: both
closed forms (`C_HS_laplace_formula`, already proved; `radial_fourier_c_HS_formula`, Part A)
are explicit algebraic expressions, so the bridge is a finite symbolic verification. -/

/-- **`C_HS_laplace_formula`'s RHS, as a plain algebraic expression over `ℂ`** (not an
integral) — literally the same shape with `s` and `Real.exp` promoted to `ℂ`/`Complex.exp`. -/
noncomputable def C_HS_laplace_expr (eta sigma : ℝ) (s : ℂ) : ℂ :=
  -(py_a0 eta : ℂ) * (1 - (1 + s * (sigma : ℂ)) * Complex.exp (-s * (sigma : ℂ))) / s ^ 2 +
  -((py_a1 eta : ℂ) / (sigma : ℂ)) *
    (2 - (2 + 2 * s * (sigma : ℂ) + s ^ 2 * (sigma : ℂ) ^ 2) *
      Complex.exp (-s * (sigma : ℂ))) / s ^ 3 +
  -((py_a3 eta : ℂ) / (sigma : ℂ) ^ 3) *
    (24 - (24 + 24 * s * (sigma : ℂ) + 12 * s ^ 2 * (sigma : ℂ) ^ 2 +
      4 * s ^ 3 * (sigma : ℂ) ^ 3 + s ^ 4 * (sigma : ℂ) ^ 4) *
      Complex.exp (-s * (sigma : ℂ))) / s ^ 5

/-- **Sanity link:** `C_HS_laplace_expr` is a faithful complex lift of `C_HS_laplace_formula` —
they agree (after casting to `ℂ`) for real `s`. -/
theorem C_HS_laplace_expr_ofReal {eta sigma s : ℝ} (hsigma : 0 < sigma) (hs : s ≠ 0) :
    C_HS_laplace_expr eta sigma (s : ℂ) = (C_HS_laplace eta sigma s : ℂ) := by
  rw [C_HS_laplace_formula hsigma hs]
  unfold C_HS_laplace_expr
  push_cast
  ring

/-- **Division by a real multiple of `I`.** `(z/((r:ℂ)·I)).im = -z.re/r` — splits via
`z/((r:ℂ)·I) = z/(r:ℂ)/I = -(z/(r:ℂ)·I)` (`Complex.div_I`), then `Complex.div_ofReal_re`
(`@[simp]`, already in Mathlib) handles the real division. -/
private lemma im_div_ofReal_mul_I (z : ℂ) (r : ℝ) :
    (z / ((r : ℂ) * Complex.I)).im = -z.re / r := by
  rw [div_mul_eq_div_div, Complex.div_I, Complex.neg_im, Complex.mul_im, Complex.I_im,
    Complex.I_re, Complex.div_ofReal_re]
  ring

/-- **Main bridge theorem — the literal `s ↔ -ik` correspondence.** `radial_fourier`'s closed
form (Part A) equals `(4π/k)` times the imaginary part of `C_HS_laplace_expr` evaluated at
`s = -ik`. -/
theorem radial_fourier_c_HS_eq_C_HS_laplace_expr (eta sigma k : ℝ)
    (hsigma : 0 < sigma) (hk : 0 < k) :
    radial_fourier (c_HS eta sigma) k =
      (4 * Real.pi / k) * (C_HS_laplace_expr eta sigma (-Complex.I * k)).im := by
  rw [radial_fourier_c_HS_formula eta sigma k hsigma hk.ne']
  congr 1
  unfold C_HS_laplace_expr
  have hexp : Complex.exp (-(-Complex.I * (k : ℂ)) * (sigma : ℂ)) =
      Real.cos (k * sigma) + Real.sin (k * sigma) * Complex.I := by
    rw [show -(-Complex.I * (k : ℂ)) * (sigma : ℂ) = ((k * sigma : ℝ) : ℂ) * Complex.I from by
      push_cast; ring]
    exact Complex.exp_ofReal_mul_I (k * sigma)
  rw [hexp]
  have hs2 : (-Complex.I * (k : ℂ)) ^ 2 = ((-(k ^ 2) : ℝ) : ℂ) := by
    push_cast; linear_combination (k : ℂ) ^ 2 * Complex.I_sq
  have hs3 : (-Complex.I * (k : ℂ)) ^ 3 = ((k ^ 3 : ℝ) : ℂ) * Complex.I := by
    push_cast; linear_combination (-(k : ℂ) ^ 3 * Complex.I) * Complex.I_sq
  have hs4 : (-Complex.I * (k : ℂ)) ^ 4 = ((k ^ 4 : ℝ) : ℂ) := by
    push_cast; linear_combination (k : ℂ) ^ 4 * Complex.I_pow_four
  have hs5 : (-Complex.I * (k : ℂ)) ^ 5 = ((-(k ^ 5) : ℝ) : ℂ) * Complex.I := by
    push_cast; linear_combination (-(k : ℂ) ^ 5 * Complex.I) * Complex.I_pow_four
  rw [hs2, hs3, hs4, hs5, Complex.add_im, Complex.add_im,
    Complex.div_ofReal_im, im_div_ofReal_mul_I, im_div_ofReal_mul_I]
  simp only [← Complex.ofReal_pow, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.neg_im, Complex.neg_re, Complex.mul_im, Complex.mul_re, Complex.sub_im,
    Complex.sub_re, Complex.add_im, Complex.add_re, Complex.ofReal_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, Complex.one_im, Complex.one_re, Complex.re_ofNat,
    Complex.im_ofNat]
  field_simp
  ring

/-! ### Piece C (Task BAXTER.7, formerly Task OZ.16) — large-`k` asymptotic of `Ĉ(k)` and `Ĥ(k)`

`radial_fourier_c_HS_formula` (Piece A) gives an *exact* closed form for
`Ĉ(k) := radial_fourier (c_HS eta sigma) k`. Expanding it out isolates the leading `cos(kσ)/k²`
term exactly, leaving a genuinely bounded (not just asserted) remainder of order `1/k³` — pure
finite algebra, cross-checked with `sympy` before this write-up. Combined with `Ĉ(k) → 0`, the
same bound propagates to `Ĥ(k) := Ĉ(k)/(1-ρĈ(k))`, supplying Task BAXTER.7
(`proof_notes_baxter.md`). -/

/-- **`Ĉ(k)`'s leading `cos(kσ)/k²` coefficient.** Already known in closed form via `py_f1_eq`
(`PYDCF.lean`) to equal `(1+η/2)/(1-η)²`. -/
noncomputable def cHS_leading_coeff (eta : ℝ) : ℝ := py_a0 eta + py_a1 eta + py_a3 eta

/-- **Exact remainder identity (Task BAXTER.7, step 1).** `Ĉ(k)` minus its `cos(kσ)/k²` leading
term is exactly `(4π/k³)` times a finite trig-and-inverse-power expression — pure algebra on
`radial_fourier_c_HS_formula`, cross-checked with `sympy` before this write-up. -/
theorem radial_fourier_c_HS_remainder_eq (eta sigma k : ℝ) (hsigma : 0 < sigma) (hk : k ≠ 0) :
    radial_fourier (c_HS eta sigma) k -
      4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2 =
    (4 * Real.pi / k ^ 3) *
      ((-(py_a0 eta) - 2 * py_a1 eta - 4 * py_a3 eta) * Real.sin (k * sigma) +
        (-(2 * py_a1 eta + 12 * py_a3 eta) / sigma) * (Real.cos (k * sigma) / k) +
        (2 * py_a1 eta / sigma) / k +
        (24 * py_a3 eta / sigma ^ 2) * (Real.sin (k * sigma) / k ^ 2) +
        (24 * py_a3 eta / sigma ^ 3) * (Real.cos (k * sigma) / k ^ 3) -
        (24 * py_a3 eta / sigma ^ 3) / k ^ 3) := by
  unfold cHS_leading_coeff
  rw [radial_fourier_c_HS_formula eta sigma k hsigma hk]
  field_simp
  ring

/-- Uniform bound on a term `c * (t / k ^ n)` with `|t| ≤ 1`, for `k ≥ 1`. -/
private lemma abs_coeff_mul_div_pow_le (c t k : ℝ) (n : ℕ) (hk : 1 ≤ k) (ht : |t| ≤ 1) :
    |c * (t / k ^ n)| ≤ |c| := by
  have hkn : (1 : ℝ) ≤ k ^ n := one_le_pow₀ hk
  have hkn0 : (0 : ℝ) < k ^ n := lt_of_lt_of_le one_pos hkn
  rw [abs_mul, abs_div, abs_of_pos hkn0]
  have h1 : |t| / k ^ n ≤ 1 := (div_le_one hkn0).2 (ht.trans hkn)
  calc |c| * (|t| / k ^ n) ≤ |c| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
    _ = |c| := mul_one _

/-- **Bound constant for Task BAXTER.7's `O(1/k³)` remainder** — literally the sum of the absolute
values of the six coefficients appearing in `radial_fourier_c_HS_remainder_eq`'s bracket. -/
noncomputable def cHS_remainder_bound (eta sigma : ℝ) : ℝ :=
  |(-(py_a0 eta) - 2 * py_a1 eta - 4 * py_a3 eta)| +
  |(-(2 * py_a1 eta + 12 * py_a3 eta) / sigma)| +
  |2 * py_a1 eta / sigma| +
  |24 * py_a3 eta / sigma ^ 2| +
  |24 * py_a3 eta / sigma ^ 3| +
  |24 * py_a3 eta / sigma ^ 3|

theorem cHS_remainder_bound_nonneg (eta sigma : ℝ) : 0 ≤ cHS_remainder_bound eta sigma := by
  unfold cHS_remainder_bound; positivity

/-- **Task BAXTER.7, step 2:** the remainder bracket in `radial_fourier_c_HS_remainder_eq` is
bounded, uniformly in `k ≥ 1`, by the explicit constant `cHS_remainder_bound`. -/
theorem cHS_remainder_bracket_bound (eta sigma k : ℝ) (hk : 1 ≤ k) :
    |(-(py_a0 eta) - 2 * py_a1 eta - 4 * py_a3 eta) * Real.sin (k * sigma) +
        (-(2 * py_a1 eta + 12 * py_a3 eta) / sigma) * (Real.cos (k * sigma) / k) +
        (2 * py_a1 eta / sigma) / k +
        (24 * py_a3 eta / sigma ^ 2) * (Real.sin (k * sigma) / k ^ 2) +
        (24 * py_a3 eta / sigma ^ 3) * (Real.cos (k * sigma) / k ^ 3) -
        (24 * py_a3 eta / sigma ^ 3) / k ^ 3| ≤ cHS_remainder_bound eta sigma := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le one_pos hk
  have hs : |Real.sin (k * sigma)| ≤ 1 := Real.abs_sin_le_one _
  have hc : |Real.cos (k * sigma)| ≤ 1 := Real.abs_cos_le_one _
  have hT1 : |(-(py_a0 eta) - 2 * py_a1 eta - 4 * py_a3 eta) * Real.sin (k * sigma)| ≤
      |(-(py_a0 eta) - 2 * py_a1 eta - 4 * py_a3 eta)| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hs
  have hT2 : |(-(2 * py_a1 eta + 12 * py_a3 eta) / sigma) * (Real.cos (k * sigma) / k)| ≤
      |(-(2 * py_a1 eta + 12 * py_a3 eta) / sigma)| := by
    have h := abs_coeff_mul_div_pow_le (-(2 * py_a1 eta + 12 * py_a3 eta) / sigma)
      (Real.cos (k * sigma)) k 1 hk hc
    rwa [pow_one] at h
  have hT3 : |(2 * py_a1 eta / sigma) / k| ≤ |2 * py_a1 eta / sigma| := by
    rw [abs_div, abs_of_pos hk0]
    exact div_le_self (abs_nonneg _) hk
  have hT4 : |(24 * py_a3 eta / sigma ^ 2) * (Real.sin (k * sigma) / k ^ 2)| ≤
      |24 * py_a3 eta / sigma ^ 2| :=
    abs_coeff_mul_div_pow_le (24 * py_a3 eta / sigma ^ 2) (Real.sin (k * sigma)) k 2 hk hs
  have hT5 : |(24 * py_a3 eta / sigma ^ 3) * (Real.cos (k * sigma) / k ^ 3)| ≤
      |24 * py_a3 eta / sigma ^ 3| :=
    abs_coeff_mul_div_pow_le (24 * py_a3 eta / sigma ^ 3) (Real.cos (k * sigma)) k 3 hk hc
  have hT6 : |(24 * py_a3 eta / sigma ^ 3) / k ^ 3| ≤ |24 * py_a3 eta / sigma ^ 3| := by
    have hk3 : (0 : ℝ) < k ^ 3 := by positivity
    rw [abs_div, abs_of_pos hk3]
    exact div_le_self (abs_nonneg _) (one_le_pow₀ hk)
  have e1 := abs_le.mp hT1
  have e2 := abs_le.mp hT2
  have e3 := abs_le.mp hT3
  have e4 := abs_le.mp hT4
  have e5 := abs_le.mp hT5
  have e6 := abs_le.mp hT6
  rw [abs_le]
  unfold cHS_remainder_bound
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, e5.1, e5.2, e6.1, e6.2]

/-- **Task BAXTER.7, step 3 (assembly):** `Ĉ(k)` deviates from its `cos(kσ)/k²` leading term by
at most `(4π·cHS_remainder_bound)/k³`, for all `k ≥ 1`. -/
theorem radial_fourier_c_HS_remainder_le (eta sigma k : ℝ) (hsigma : 0 < sigma) (hk : 1 ≤ k) :
    |radial_fourier (c_HS eta sigma) k -
        4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2| ≤
      4 * Real.pi * cHS_remainder_bound eta sigma / k ^ 3 := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le one_pos hk
  rw [radial_fourier_c_HS_remainder_eq eta sigma k hsigma hk0.ne']
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 4 * Real.pi / k ^ 3)]
  have hbound := cHS_remainder_bracket_bound eta sigma k hk
  have hpos : (0:ℝ) ≤ 4 * Real.pi / k ^ 3 := by positivity
  calc 4 * Real.pi / k ^ 3 * _ ≤ 4 * Real.pi / k ^ 3 * cHS_remainder_bound eta sigma :=
        mul_le_mul_of_nonneg_left hbound hpos
    _ = 4 * Real.pi * cHS_remainder_bound eta sigma / k ^ 3 := by ring

/-- **`Ĉ(k) = O(1/k²)`, with an explicit constant.** -/
noncomputable def cHS_bound (eta sigma : ℝ) : ℝ :=
  4 * Real.pi * sigma * |cHS_leading_coeff eta| + 4 * Real.pi * cHS_remainder_bound eta sigma

theorem cHS_bound_nonneg (eta sigma : ℝ) (hsigma : 0 < sigma) : 0 ≤ cHS_bound eta sigma := by
  unfold cHS_bound
  have h1 : (0:ℝ) ≤ 4 * Real.pi * sigma * |cHS_leading_coeff eta| := by positivity
  have h2 : (0:ℝ) ≤ 4 * Real.pi * cHS_remainder_bound eta sigma :=
    mul_nonneg (by positivity) (cHS_remainder_bound_nonneg eta sigma)
  linarith

theorem radial_fourier_c_HS_le (eta sigma k : ℝ) (hsigma : 0 < sigma) (hk : 1 ≤ k) :
    |radial_fourier (c_HS eta sigma) k| ≤ cHS_bound eta sigma / k ^ 2 := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le one_pos hk
  have hrem := radial_fourier_c_HS_remainder_le eta sigma k hsigma hk
  have hk2pos : (0:ℝ) < k ^ 2 := by positivity
  have hlead : |4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2| ≤
      4 * Real.pi * sigma * |cHS_leading_coeff eta| / k ^ 2 := by
    rw [show (4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2 : ℝ) =
        (4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma)) / k ^ 2 from
      by ring,
      abs_div, abs_of_pos hk2pos, div_le_div_iff_of_pos_right hk2pos]
    have hXeq : |4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma)| =
        4 * Real.pi * sigma * |cHS_leading_coeff eta| * |Real.cos (k * sigma)| := by
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 4 * Real.pi * sigma)]
    rw [hXeq]
    calc 4 * Real.pi * sigma * |cHS_leading_coeff eta| * |Real.cos (k * sigma)| ≤
        4 * Real.pi * sigma * |cHS_leading_coeff eta| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
      _ = 4 * Real.pi * sigma * |cHS_leading_coeff eta| := mul_one _
  have htri : |radial_fourier (c_HS eta sigma) k| ≤
      |4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2| +
      |radial_fourier (c_HS eta sigma) k -
        4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2| := by
    have h := abs_add_le
      (4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2)
      (radial_fourier (c_HS eta sigma) k -
        4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2)
    have heq2 : 4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2 +
        (radial_fourier (c_HS eta sigma) k -
          4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2) =
        radial_fourier (c_HS eta sigma) k := by ring
    rwa [heq2] at h
  have hk23 : k ^ 2 ≤ k ^ 3 := pow_le_pow_right₀ hk (by norm_num : 2 ≤ 3)
  have hb_nonneg : (0:ℝ) ≤ 4 * Real.pi * cHS_remainder_bound eta sigma :=
    mul_nonneg (by positivity) (cHS_remainder_bound_nonneg eta sigma)
  have hk3le : 4 * Real.pi * cHS_remainder_bound eta sigma / k ^ 3 ≤
      4 * Real.pi * cHS_remainder_bound eta sigma / k ^ 2 :=
    div_le_div_of_nonneg_left hb_nonneg (by positivity) hk23
  unfold cHS_bound
  rw [add_div]
  linarith [htri, hlead, hrem, hk3le]

/-- **`Ĥ(k) = Ĉ(k)/(1-ρĈ(k))`** — the closed-form Fourier-domain OZ solution (Task BAXTER.7's
main object), matching `oz_fourier_oz_eq_of_PY_core`'s `H·(1-ρC)=C` identity when the
denominator is nonzero. -/
noncomputable def Hhat_closed (eta sigma rho k : ℝ) : ℝ :=
  radial_fourier (c_HS eta sigma) k / (1 - rho * radial_fourier (c_HS eta sigma) k)

/-- **Task BAXTER.7 (main theorem).** For `k` past an explicit threshold (depending on
`eta,sigma,rho`), `Ĥ(k)` deviates from its `cos(kσ)/k²` leading term — coefficient
`4πσ(α0+α1+α3) = 4πσ(1+η/2)/(1-η)²` via `py_f1_eq` — by at most an explicit `O(1/k³)` bound. -/
theorem Hhat_closed_asymptotic (eta sigma rho k : ℝ) (hsigma : 0 < sigma)
    (hk : 1 + 2 * |rho| * cHS_bound eta sigma ≤ k) :
    |Hhat_closed eta sigma rho k -
        4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2| ≤
      (2 * |rho| * cHS_bound eta sigma ^ 2 + 4 * Real.pi * cHS_remainder_bound eta sigma) /
        k ^ 3 := by
  set K := cHS_bound eta sigma with hKdef
  have hKnn : 0 ≤ K := cHS_bound_nonneg eta sigma hsigma
  have hk1 : (1 : ℝ) ≤ k := by nlinarith [mul_nonneg (abs_nonneg rho) hKnn]
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le one_pos hk1
  have hCbound : |radial_fourier (c_HS eta sigma) k| ≤ K / k ^ 2 :=
    radial_fourier_c_HS_le eta sigma k hsigma hk1
  have hkk : k ≤ k ^ 2 := by
    have h := pow_le_pow_right₀ hk1 (by norm_num : 1 ≤ 2)
    rwa [pow_one] at h
  have hk2ge : 2 * |rho| * K ≤ k ^ 2 := by linarith [hk, hkk]
  have hk2pos : (0 : ℝ) < k ^ 2 := by positivity
  have h2 : |rho| * (K / k ^ 2) ≤ 1 / 2 := by
    rw [mul_div_assoc', div_le_iff₀ hk2pos]
    linarith [hk2ge]
  have hrhoC : |rho * radial_fourier (c_HS eta sigma) k| ≤ 1 / 2 := by
    rw [abs_mul]
    calc |rho| * |radial_fourier (c_HS eta sigma) k| ≤ |rho| * (K / k ^ 2) :=
          mul_le_mul_of_nonneg_left hCbound (abs_nonneg rho)
      _ ≤ 1 / 2 := h2
  have hdenom_ge : (1 : ℝ) / 2 ≤ |1 - rho * radial_fourier (c_HS eta sigma) k| := by
    have h := abs_sub_abs_le_abs_sub (1 : ℝ) (rho * radial_fourier (c_HS eta sigma) k)
    rw [abs_one] at h
    linarith [hrhoC, h]
  have hdenom_pos : (0 : ℝ) < |1 - rho * radial_fourier (c_HS eta sigma) k| := by linarith
  have hne : (1 - rho * radial_fourier (c_HS eta sigma) k) ≠ 0 := abs_pos.mp hdenom_pos
  have hne' : (1 - radial_fourier (c_HS eta sigma) k * rho) ≠ 0 := by
    rw [mul_comm]; exact hne
  have hHC : Hhat_closed eta sigma rho k - radial_fourier (c_HS eta sigma) k =
      rho * (radial_fourier (c_HS eta sigma) k) ^ 2 /
        (1 - rho * radial_fourier (c_HS eta sigma) k) := by
    unfold Hhat_closed
    field_simp
    ring
  have hCsq : (radial_fourier (c_HS eta sigma) k) ^ 2 ≤ (K / k ^ 2) ^ 2 := by
    rw [← sq_abs (radial_fourier (c_HS eta sigma) k)]
    exact pow_le_pow_left₀ (abs_nonneg _) hCbound 2
  have hstep1 : |Hhat_closed eta sigma rho k - radial_fourier (c_HS eta sigma) k| ≤
      2 * |rho| * K ^ 2 / k ^ 4 := by
    rw [hHC, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (radial_fourier (c_HS eta sigma) k))]
    have hnum_nonneg : (0:ℝ) ≤ |rho| * (radial_fourier (c_HS eta sigma) k) ^ 2 := by positivity
    have hstepA : |rho| * (radial_fourier (c_HS eta sigma) k) ^ 2 /
        |1 - rho * radial_fourier (c_HS eta sigma) k| ≤
        2 * (|rho| * (radial_fourier (c_HS eta sigma) k) ^ 2) := by
      have h := div_le_div_of_nonneg_left hnum_nonneg (by norm_num : (0:ℝ) < 1/2) hdenom_ge
      calc |rho| * (radial_fourier (c_HS eta sigma) k) ^ 2 /
          |1 - rho * radial_fourier (c_HS eta sigma) k|
          ≤ |rho| * (radial_fourier (c_HS eta sigma) k) ^ 2 / (1/2) := h
        _ = 2 * (|rho| * (radial_fourier (c_HS eta sigma) k) ^ 2) := by ring
    have hstepB : 2 * (|rho| * (radial_fourier (c_HS eta sigma) k) ^ 2) ≤
        2 * |rho| * K ^ 2 / k ^ 4 := by
      have h2sq : |rho| * (radial_fourier (c_HS eta sigma) k) ^ 2 ≤ |rho| * (K / k ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hCsq (abs_nonneg rho)
      have heq : 2 * (|rho| * (K / k ^ 2) ^ 2) = 2 * |rho| * K ^ 2 / k ^ 4 := by
        rw [div_pow]; ring
      linarith [h2sq, heq]
    exact hstepA.trans hstepB
  have hk34 : k ^ 3 ≤ k ^ 4 := pow_le_pow_right₀ hk1 (by norm_num : 3 ≤ 4)
  have hk34le : 2 * |rho| * K ^ 2 / k ^ 4 ≤ 2 * |rho| * K ^ 2 / k ^ 3 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hk34
  have hrem := radial_fourier_c_HS_remainder_le eta sigma k hsigma hk1
  have hfinal : |Hhat_closed eta sigma rho k -
        4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2| ≤
      |Hhat_closed eta sigma rho k - radial_fourier (c_HS eta sigma) k| +
      |radial_fourier (c_HS eta sigma) k -
        4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2| := by
    have h := abs_add_le (Hhat_closed eta sigma rho k - radial_fourier (c_HS eta sigma) k)
      (radial_fourier (c_HS eta sigma) k -
        4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2)
    have heq2 : (Hhat_closed eta sigma rho k - radial_fourier (c_HS eta sigma) k) +
        (radial_fourier (c_HS eta sigma) k -
          4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2) =
        Hhat_closed eta sigma rho k -
          4 * Real.pi * sigma * cHS_leading_coeff eta * Real.cos (k * sigma) / k ^ 2 := by ring
    rwa [heq2] at h
  rw [add_div]
  linarith [hfinal, hstep1, hk34le, hrem]

/-- **`1-ρĈ(k) ≠ 0` for `k` past the same explicit threshold used in `Hhat_closed_asymptotic`.**
Extracted as its own reusable fact (Task BAXTER.8 needs it directly, to turn
`oz_fourier_oz_eq_of_PY_core`'s `H·(1-ρC)=C` identity into `H=C/(1-ρC)=Hhat_closed`). -/
theorem one_sub_rho_mul_radial_fourier_c_HS_ne_zero (eta sigma rho k : ℝ) (hsigma : 0 < sigma)
    (hk : 1 + 2 * |rho| * cHS_bound eta sigma ≤ k) :
    (1 : ℝ) - rho * radial_fourier (c_HS eta sigma) k ≠ 0 := by
  have hKnn : 0 ≤ cHS_bound eta sigma := cHS_bound_nonneg eta sigma hsigma
  have hk1 : (1:ℝ) ≤ k := by nlinarith [mul_nonneg (abs_nonneg rho) hKnn]
  have hCbound : |radial_fourier (c_HS eta sigma) k| ≤ cHS_bound eta sigma / k ^ 2 :=
    radial_fourier_c_HS_le eta sigma k hsigma hk1
  have hkk : k ≤ k ^ 2 := by
    have h := pow_le_pow_right₀ hk1 (by norm_num : 1 ≤ 2)
    rwa [pow_one] at h
  have hk2ge : 2 * |rho| * cHS_bound eta sigma ≤ k ^ 2 := by linarith [hk, hkk]
  have hk2pos : (0 : ℝ) < k ^ 2 := by positivity
  have h2 : |rho| * (cHS_bound eta sigma / k ^ 2) ≤ 1 / 2 := by
    rw [mul_div_assoc', div_le_iff₀ hk2pos]
    linarith [hk2ge]
  have hrhoC : |rho * radial_fourier (c_HS eta sigma) k| ≤ 1 / 2 := by
    rw [abs_mul]
    calc |rho| * |radial_fourier (c_HS eta sigma) k| ≤ |rho| * (cHS_bound eta sigma / k ^ 2) :=
          mul_le_mul_of_nonneg_left hCbound (abs_nonneg rho)
      _ ≤ 1 / 2 := h2
  have hdenom_ge : (1 : ℝ) / 2 ≤ |1 - rho * radial_fourier (c_HS eta sigma) k| := by
    have h := abs_sub_abs_le_abs_sub (1 : ℝ) (rho * radial_fourier (c_HS eta sigma) k)
    rw [abs_one] at h
    linarith [hrhoC, h]
  have hdenom_pos : (0 : ℝ) < |1 - rho * radial_fourier (c_HS eta sigma) k| := by linarith
  exact abs_pos.mp hdenom_pos

end FMSA.HardSphere
