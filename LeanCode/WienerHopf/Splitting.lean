/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Wiener–Hopf Splitting of the Yukawa Kernel

**Source:** [chsY] Eq. 28

The Yukawa pair potential in k-space is `T_U(k, z) = 2z / (z^2 + k^2)`.
Its Wiener–Hopf (causal/anti-causal) factorisation gives two half-plane functions:

    B1(k, z) = 1 / (ik + z)      pole at k = -iz  (analytic in upper half-plane)
    D1(k, z) = 1 / (-ik + z)     pole at k = +iz  (analytic in lower half-plane)

This file proves the core algebraic identity: B1 + D1 = T_U.

The key algebraic fact used throughout is `Complex.I ^ 2 = -1`, which `ring` does
not know by default — all goals involving `Complex.I` require `linear_combination`
with `Complex.I_sq` as the hint.
-/

namespace FMSA.WienerHopf

/-- The Yukawa denominator factors over ℂ as a product of the two Wiener–Hopf denominators. -/
lemma yukawa_factor (k z : ℂ) :
    z ^ 2 + k ^ 2 = (Complex.I * k + z) * (-(Complex.I * k) + z) := by
  linear_combination k ^ 2 * Complex.I_sq

/-- **[chsY] Eq. 28.** The causal part B1 and anti-causal part D1 sum to the full
Yukawa kernel T_U:

    1/(ik + z) + 1/(-ik + z) = 2z / (z^2 + k^2)

Hypotheses require both denominators to be nonzero, which holds for all z with Re(z) > 0
and k real (the physical domain: z = inverse Yukawa length > 0, k = wavevector ∈ ℝ). -/
theorem yukawa_kernel_split (k z : ℂ)
    (h1 : Complex.I * k + z ≠ 0)
    (h2 : -(Complex.I * k) + z ≠ 0) :
    1 / (Complex.I * k + z) + 1 / (-(Complex.I * k) + z) =
    2 * z / (z ^ 2 + k ^ 2) := by
  have h3 : z ^ 2 + k ^ 2 ≠ 0 := by
    rw [yukawa_factor]; exact mul_ne_zero h1 h2
  field_simp [h1, h2, h3]
  linear_combination 2 * k ^ 2 * z * Complex.I_sq

/-! ### Task 3.2 — Support of T_S on (-∞, R_ij] -/

/-!
**Context ([chsY] Proof 2).** The inner-core first-order DCF is
`c_ij^(1)(r)` for `r ∈ [0, R_ij]` and `0` elsewhere. The Wiener–Hopf method requires
the Fourier integral

    T_S(k)_ij = ∫0^{R_ij} r · c_ij^(1)(r) · exp(-ikr) dr

to be the Fourier transform of a function supported on `(-∞, R_ij]`.

**Proof:** The integrand is zero outside `[0, R_ij]`, so `T_S = FT(g_R)` where
`g_R := r · c(r) · 1_{[0,R]}` has support ⊆ `[0, R] ⊆ (-∞, R]`.

**Sign convention:** Using `exp(-ikr)` (not `exp(+ikr)`) ensures `T_S(k)` is
analytic in `Im(k) < 0` when extended via the Paley–Wiener bound
`|T_S(k)| ≤ C · exp(R · max(0, -Im k))`.  With the opposite sign `exp(+ikr)`,
analyticity would be in `Im(k) > 0` and the support bound would be `[R_ij, ∞)`,
reversing the Wiener–Hopf splitting.
-/

/-- The inner-core indicator function `g_R(r) = r · c(r) · 1_{[0,R]}(r)`. -/
noncomputable def innerCoreFun (c : ℝ → ℝ) (R : ℝ) : ℝ → ℝ :=
  Set.indicator (Set.Icc 0 R) (fun r => r * c r)

/-- **[chsY] Proof 2 (support half):** The inner-core restriction `g_R` has
support contained in `(-∞, R]`, so its Fourier transform `T_S(k)` comes from a
function supported to the left of the contact distance `R`. -/
theorem innerCore_support_subset_Iic (c : ℝ → ℝ) (R : ℝ) :
    Function.support (innerCoreFun c R) ⊆ Set.Iic R := by
  intro x hx
  simp only [innerCoreFun, Function.mem_support, Set.indicator_apply, ne_eq] at hx
  split_ifs at hx with h
  · exact h.2
  · exact absurd rfl hx

/-- **[chsY] Proof 2 (integral form):** The Fourier integral `T_S(k)` over
`[0, R]` equals the full-line Fourier transform of `g_R`.

Proof chain:
  `∫0^R f = ∫_{Ioc 0 R} f`   (by `intervalIntegral.integral_of_le`)
  `= ∫_{Icc 0 R} f`          (by `integral_Icc_eq_integral_Ioc`, measure-zero boundary)
  `= ∫ r, indicator_{Icc} f` (by `integral_indicator`) -/
theorem T_S_eq_fourier_of_innerCore (c : ℝ → ℝ) (R k : ℝ) (hR : 0 <= R)
    (_hc : MeasureTheory.Integrable
        (fun r => (innerCoreFun c R r : ℂ) * Complex.exp (-Complex.I * k * r))) :
    (∫ r in (0:ℝ)..R, (r * c r : ℂ) * Complex.exp (-Complex.I * k * r)) =
    ∫ r, (innerCoreFun c R r : ℂ) * Complex.exp (-Complex.I * k * r) := by
  -- Rewrite integrand using indicator: (indicator S f r : ℂ) * g r = indicator S (f · * g) r
  have hind : ∀ r : ℝ,
      (innerCoreFun c R r : ℂ) * Complex.exp (-Complex.I * k * r) =
      Set.indicator (Set.Icc 0 R)
        (fun r => (r * c r : ℂ) * Complex.exp (-Complex.I * k * r)) r := by
    intro r
    simp only [innerCoreFun, Set.indicator_apply]
    split_ifs with h
    · push_cast; ring
    · simp
  simp_rw [hind]
  -- RHS: ∫ r, indicator Icc f r = ∫ r in Icc, f r
  rw [MeasureTheory.integral_indicator measurableSet_Icc]
  -- Goal: ∫ in 0..R = ∫ in Icc 0 R
  -- LHS: ∫ in 0..R = ∫ in Ioc 0 R (for 0 ≤ R)
  rw [intervalIntegral.integral_of_le hR]
  -- Goal: ∫ in Ioc 0 R = ∫ in Icc 0 R
  exact MeasureTheory.integral_Icc_eq_integral_Ioc.symm

end FMSA.WienerHopf
