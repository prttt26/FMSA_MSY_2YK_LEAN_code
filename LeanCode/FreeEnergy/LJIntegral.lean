/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Task F.2b — LJ Inner-Core Integral Identity (FMSA_poly Contact-LJ Approximation)

**Source:** `FMSA_MC_cleaned_2cpp.py`, `betaf1_inner` (line 1435) and `betaf2_lj` (line 1524)

The FMSA_poly contact-LJ approximation computes inner-core free energy by integrating
the LJ potential over [sigma_ij, R_ij] analytically.  The key integral identity is:

    ∫_sigma^R (sigma1^2/r1^0 - sigma^6/r^4) dr  =  R^3 · (-(sigma/R)1^2/9 + (sigma/R)^6/3 - 2(sigma/R)^3/9)

The original LJ integrand `[(sigma/r)1^2 - (sigma/r)^6] · r^2` equals `sigma1^2/r1^0 - sigma^6/r^4`,
so these are the same integral (`lj_integrand_eq`).

The code's `LJ_term = R^3 · (s1^2/9 - s^6/3 + 2s^3/9)` (s = sigma/R) satisfies:

    LJ_term  =  -∫_sigma^R (sigma1^2/r1^0 - sigma^6/r^4) dr          (`lj_term_eq`)

**Antiderivative:** `F(r) = (-sigma1^2/9) · (r^9)⁻¹ + (sigma^6/3) · (r^3)⁻¹`
  - `F'(r) = sigma1^2/r1^0 - sigma^6/r^4`  (`lj_antideriv_hasDerivAt`)
  - `F(R) = R^3 · (-s1^2/9 + s^6/3)`
  - `F(sigma) = 2sigma^3/9 = R^3 · (2s^3/9)`  ← **the lower-limit term; was missing in old code**
  - `F(R) - F(sigma) = R^3 · (-s1^2/9 + s^6/3 - 2s^3/9)`  ✓

**Bug fix (line 1523 comment):** Older FMSA_poly code had `R^3(s1^2/9 - s^6/3)`, omitting
the `+2s^3/9` term from F(sigma).  `lj_term_eq` proves the complete identity including F(sigma).
-/

open MeasureTheory intervalIntegral Real Set

namespace FMSA.FreeEnergy

/-! ### Antiderivative HasDerivAt -/

/-- The antiderivative `F(r) = (-sigma1^2/9)·(r^9)⁻¹ + (sigma^6/3)·(r^3)⁻¹` has derivative
`sigma1^2/r1^0 - sigma^6/r^4` for `r > 0`.

Proof: `d/dr[(-sigma1^2/9)·r⁻^9] = sigma1^2/r1^0` and `d/dr[(sigma^6/3)·r⁻^3] = -sigma^6/r^4`,
established via `hasDerivAt_pow` + `.inv` + `.const_mul`. -/
private lemma lj_antideriv_hasDerivAt {sigma : ℝ} (r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun r => (-sigma^12/9) * (r^9)⁻¹ + (sigma^6/3) * (r^3)⁻¹)
               (sigma^12 / r^10 - sigma^6 / r^4) r := by
  have hr' : r ≠ 0 := hr.ne'
  have h1 : HasDerivAt (fun r => (-sigma^12/9) * (r^9)⁻¹) (sigma^12 / r^10) r := by
    have h := ((hasDerivAt_pow 9 r).inv (pow_pos hr 9).ne').const_mul (-sigma^12 / 9)
    refine h.congr_deriv ?_
    field_simp; ring
  have h2 : HasDerivAt (fun r => (sigma^6/3) * (r^3)⁻¹) (-sigma^6 / r^4) r := by
    have h := ((hasDerivAt_pow 3 r).inv (pow_pos hr 3).ne').const_mul (sigma^6 / 3)
    refine h.congr_deriv ?_
    field_simp; ring
  exact (h1.add h2).congr_deriv (by ring)

/-! ### Integrability -/

lemma lj_integrable {sigma R : ℝ} (hsigma : 0 < sigma) (hsigmaR : sigma <= R) :
    IntervalIntegrable (fun r => sigma^12 / r^10 - sigma^6 / r^4) volume sigma R := by
  apply ContinuousOn.intervalIntegrable_of_Icc hsigmaR
  have hpos : ∀ r ∈ Set.Icc sigma R, (0 : ℝ) < r :=
    fun r hr => lt_of_lt_of_le hsigma (Set.mem_Icc.mp hr).1
  exact (continuousOn_const.div ((continuous_pow 10).continuousOn)
      (fun r hr => (pow_pos (hpos r hr) 10).ne')).sub
    (continuousOn_const.div ((continuous_pow 4).continuousOn)
      (fun r hr => (pow_pos (hpos r hr) 4).ne'))

/-! ### Main integral identity -/

/-- **Task F.5 — LJ inner-core integral (power-law form):**

    `∫_sigma^R (sigma1^2/r1^0 - sigma^6/r^4) dr  =  R^3 · (-(sigma/R)1^2/9 + (sigma/R)^6/3 - 2(sigma/R)^3/9)`

Proved by FTC using antiderivative `F(r) = (-sigma1^2/9)·(r^9)⁻¹ + (sigma^6/3)·(r^3)⁻¹`. -/
theorem lj_integral {sigma R : ℝ} (hsigma : 0 < sigma) (hR : 0 < R) (hsigmaR : sigma <= R) :
    ∫ r in sigma..R, (sigma^12 / r^10 - sigma^6 / r^4) =
    R^3 * (-(sigma/R)^12/9 + (sigma/R)^6/3 - 2*(sigma/R)^3/9) := by
  have hpos : ∀ r ∈ Set.uIcc sigma R, (0 : ℝ) < r := fun r hr => by
    rw [Set.uIcc_of_le hsigmaR] at hr
    exact lt_of_lt_of_le hsigma (Set.mem_Icc.mp hr).1
  rw [integral_eq_sub_of_hasDerivAt
      (fun r hr => lj_antideriv_hasDerivAt r (hpos r hr))
      (lj_integrable hsigma hsigmaR)]
  field_simp [hsigma.ne', hR.ne']
  ring

/-! ### Integrand equivalence and LJ_term corollary -/

/-- The original LJ integrand `((sigma/r)1^2 - (sigma/r)^6)·r^2` equals `sigma1^2/r1^0 - sigma^6/r^4`
for `r ≠ 0` (by `field_simp` + `ring`). -/
lemma lj_integrand_eq {sigma r : ℝ} (hr : r ≠ 0) :
    ((sigma/r)^12 - (sigma/r)^6) * r^2 = sigma^12 / r^10 - sigma^6 / r^4 := by
  field_simp [hr]

/-- **LJ_term identity (FMSA_poly code verification):**

The `LJ_term = R^3·(s1^2/9 - s^6/3 + 2s^3/9)` from `betaf1_inner`/`betaf2_lj`
(FMSA_MC_cleaned_2cpp.py lines 1435, 1524) satisfies:

    LJ_term  =  -∫_sigma^R (sigma1^2/r1^0 - sigma^6/r^4) dr

This includes the lower-limit term `+2s^3/9` (from `F(sigma) = 2sigma^3/9 = R^3·(2s^3/9)`)
that was missing in the older code (`R^3(s1^2/9 - s^6/3)` only). -/
theorem lj_term_eq {sigma R : ℝ} (hsigma : 0 < sigma) (hR : 0 < R) (hsigmaR : sigma <= R) :
    R^3 * ((sigma/R)^12/9 - (sigma/R)^6/3 + 2*(sigma/R)^3/9) =
    -(∫ r in sigma..R, (sigma^12 / r^10 - sigma^6 / r^4)) := by
  linarith [lj_integral hsigma hR hsigmaR]

end FMSA.FreeEnergy
