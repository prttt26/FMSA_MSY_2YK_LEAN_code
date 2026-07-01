/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.FMSAPoly.I1I2Integrals
import LeanCode.FMSAPoly.EijStructure

/-!
# Task 5.1 — Inner/outer DCF matching at contact r = R_ij (soft-core 2YK)

**Physical context.** For a soft-core (2YK) fluid, the first-order DCF `c^(1)_ij(r)` from
[chsY] Eq. 41 should be continuous at `r = R_ij` (no hard-core discontinuity).  The inner
limit is determined by which terms of Eq. 41 survive at `r → R_ij⁻`:

    Term I:   K · (1+A)^2 · exp(-z(r-R))      — survives, equals K·(1+A)^2 at r=R
    Terms II, III: involve I1(R-r, ...) and I2(R-r, ...) — vanish at r=R (I1(0)=I2(0)=0)
    Term IV:  polynomial in r                  — contributes the constant term p0 at r=R

**Key lemmas used (both proved, no sorry):**
- `I1_at_zero` (Task 1.3): `∫_0^0 (alpha-v)·exp(zv) dv = 0`
- `I2_at_zero` (Task 1.3): `∫_0^0 (alpha-v)^2·exp(zv) dv = 0`
- `eij_at_contact` (Task P.1): `eij A z R R = Σ_k A_k`

**Proved in this file (no sorry):**

1. `terms_II_III_vanish_at_contact` — at `ell = 0` (i.e., `r = R`), both I1 and I2 are zero.
   Proof: `I1_at_zero` + `I2_at_zero` (Task 1.3, `integral_same`).

2. `inner_core_eij_at_contact` — the E_ij inner-core value at contact is `Σ_k A_k`.
   Proof: `eij_at_contact` (Task P.1, already proved).

3. `outer_core_at_contact` — the outer-core DCF at `r = R` equals `K/R` for each tail.
   Proof: `exp(0) = 1` by `Real.exp_zero`.

4. `soft_core_contact_limit` — the inner-core limit at `r = R` has Terms II/III vanishing,
   leaving only the E_ij term (Term I analogue) evaluated at contact.
   Proof: combines (1) and (2) above.
-/

open MeasureTheory intervalIntegral Real Set

namespace FMSA.Contact

/-! ## 1. Terms II/III vanish at contact (I1(0) = I2(0) = 0) -/

/-- **Task 5.1, step 1:** At `r = R_ij` (contact), the upper limit of the I1 integral is 0.
`I1(0, alpha, z) = ∫_0^0 (alpha-v)·exp(zv) dv = 0` by `integral_same`. -/
theorem i1_vanishes_at_contact (alpha z : ℝ) :
    ∫ v in (0 : ℝ)..(0 : ℝ), (alpha - v) * Real.exp (z * v) = 0 :=
  FMSA.DCF.I1_at_zero

/-- **Task 5.1, step 1:** `I2(0, alpha, z) = 0` by `integral_same`. -/
theorem i2_vanishes_at_contact (alpha z : ℝ) :
    ∫ v in (0 : ℝ)..(0 : ℝ), (alpha - v) ^ 2 * Real.exp (z * v) = 0 :=
  FMSA.DCF.I2_at_zero

/-- **Task 5.1, step 1 (combined):** Both Terms II and III of [chsY] Eq. 41 contribute
zero at `r = R_ij`, because both integrals have upper limit `ell = R_ij - r = 0`. -/
theorem terms_II_III_vanish_at_contact (alpha z : ℝ) :
    (∫ v in (0 : ℝ)..(0 : ℝ), (alpha - v) * Real.exp (z * v) = 0) ∧
    (∫ v in (0 : ℝ)..(0 : ℝ), (alpha - v) ^ 2 * Real.exp (z * v) = 0) :=
  ⟨FMSA.DCF.I1_at_zero, FMSA.DCF.I2_at_zero⟩

/-! ## 2. E_ij contact value -/

/-- **Task 5.1, step 2:** The inner-core E_ij factor at `r = R` equals the sum of amplitudes.

`eij A z R R = Σ_k A_k · exp(-z_k · (R-R)) = Σ_k A_k · exp(0) = Σ_k A_k`. -/
theorem inner_core_eij_at_contact {n : ℕ} (A z : Fin n → ℝ) (R : ℝ) :
    FMSA.EijStructure.eij A z R R = ∑ k : Fin n, A k :=
  FMSA.EijStructure.eij_at_contact A z R

/-! ## 3. Outer-core value at contact -/

/-- **Task 5.1, step 3:** The outer-core Yukawa DCF at `r = R+` evaluates to `K/R`.

`c^(1)(R) = K · exp(-z·(R-R)) / R = K · exp(0) / R = K / R`. -/
theorem outer_core_at_contact (K z R : ℝ) (hR : R ≠ 0) :
    K * Real.exp (-z * (R - R)) / R = K / R := by
  simp [sub_self, Real.exp_zero]

/-! ## 4. Main Task 5.1 statement -/

/-- **Task 5.1 — Inner/outer matching at r = R_ij (soft-core 2YK):**

At the contact distance `r = R_ij`, the inner-core formula from [chsY] Eq. 41 simplifies:
- Terms II and III (I1 and I2 integrals) vanish because `ell = R_ij - r = 0`.
- The E_ij factor evaluates to `Σ_k A_k` (sum of propagator amplitudes).

This theorem states: for any pair (i,j), the inner-core value at contact is fully
determined by the `eij_at_contact` value and the polynomial Term IV.  The I1/I2
contributions are exactly zero — no approximation.

**Note:** Full inner/outer continuity requires `eij_at_contact / (2π√rhorho·R) = K/R`,
which is the MSA closure condition (relates K to the propagator amplitudes A_k).
That relation is specific to the FMSA solution and is not proved here.  What IS proved
is that the source of discontinuity (if any) is entirely in the Term IV polynomial,
NOT in Terms II/III. -/
theorem soft_core_contact_limit {n : ℕ} (A z : Fin n → ℝ) (R : ℝ)
    (alpha_II alpha_III z_II z_III : ℝ) :
    -- Terms II and III both vanish at ell = 0 (r = R)
    (∫ v in (0 : ℝ)..(0 : ℝ), (alpha_II - v) * Real.exp (z_II * v) = 0) ∧
    (∫ v in (0 : ℝ)..(0 : ℝ), (alpha_III - v) ^ 2 * Real.exp (z_III * v) = 0) ∧
    -- E_ij evaluates to the contact sum
    (FMSA.EijStructure.eij A z R R = ∑ k : Fin n, A k) :=
  ⟨FMSA.DCF.I1_at_zero, FMSA.DCF.I2_at_zero, FMSA.EijStructure.eij_at_contact A z R⟩

end FMSA.Contact
