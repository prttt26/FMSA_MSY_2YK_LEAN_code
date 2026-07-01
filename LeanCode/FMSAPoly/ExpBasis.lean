/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.FMSAPoly.EijStructure

/-!
# Tasks P.B1 + P.B2 — Exponential basis for inner-core DCF

Defines `qij(r) = a·exp(-z·(R-r)) + b·exp(+z·(R-r))` (the two-term exponential sum that
replaces the polynomial P_ij in FMSA_GA_matrix_mix) and proves:

- **P.B1** (`exp_basis_det_ne_zero`): the coefficient matrix determinant
  `exp(z·R) - exp(-z·R) ≠ 0` for `z, R > 0`, so the 2×2 boundary system always has a unique
  solution `(a, b)`.

- **P.B2** (`exp_basis_contact_bc`, `exp_basis_origin_bc`): if `(a, b)` satisfy the system,
  then `qij` evaluates to the correct boundary values at `r = R` and `r = 0` exactly.

- **P.B2 (full)** (`exp_basis_satisfies_contact`, `exp_basis_satisfies_origin`): combined with
  `eij` from Task P.1, both FMSA_poly boundary conditions hold with **zero error** — the
  structural failure proved in P.3/P.C1 for polynomials does not apply to `qij`.

## Contrast with P.3

Task P.3 (`poly_approx_fails_origin`) proves: for ANY polynomial `p` with `p(0) ≤ 0`,
the error `|exp(z·(R-r)) - p(r)|` is ≥ `exp(z·R)` at `r = 0`.  Task P.B2 proves the
exponential basis `qij` achieves **zero** error at both endpoints by construction.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open FMSA.EijStructure

namespace FMSA.ExpBasis

/-! ## Definition -/

/-- **Two-term exponential basis (FMSA_GA_matrix_mix):**
`qij a b z R r = a·exp(-z·(R-r)) + b·exp(+z·(R-r))`
This is Term I of [chsY] Eq. 41.  The parameters `(a, b)` are determined by the 2×2 boundary
system whose solvability is guaranteed by `exp_basis_det_ne_zero`. -/
noncomputable def qij (a b z R r : ℝ) : ℝ :=
  a * Real.exp (-(z * (R - r))) + b * Real.exp (z * (R - r))

/-! ## Boundary evaluation lemmas -/

/-- At contact `r = R`, both exponentials reduce to `exp(0) = 1`. -/
lemma qij_at_contact (a b z R : ℝ) : qij a b z R R = a + b := by
  unfold qij
  simp [sub_self]

/-- At the origin `r = 0`, `R - r = R`. -/
lemma qij_at_origin (a b z R : ℝ) :
    qij a b z R 0 = a * Real.exp (-(z * R)) + b * Real.exp (z * R) := by
  unfold qij
  simp [sub_zero]

/-! ## Task P.B1 — Determinant is nonzero -/

/-- **P.B1:** The 2×2 boundary system
```
a  +  b                        =  C1
a · exp(-z·R)  +  b · exp(+z·R) =  C2
```
has coefficient matrix determinant `exp(z·R) - exp(-z·R) = 2 sinh(z·R) ≠ 0` for `z, R > 0`.
Hence the system always has a unique solution `(a, b)`, regardless of the RHS values. -/
theorem exp_basis_det_ne_zero (z R : ℝ) (hz : 0 < z) (hR : 0 < R) :
    Real.exp (z * R) - Real.exp (-(z * R)) ≠ 0 := by
  have h1 : Real.exp (-(z * R)) < Real.exp (z * R) :=
    Real.exp_lt_exp.mpr (by linarith [mul_pos hz hR])
  linarith

/-! ## Task P.B2 — Boundary conditions are satisfied exactly -/

/-- **P.B2 (contact, abstract):** If `a + b = C` then `qij a b z R R = C`. -/
theorem exp_basis_contact_bc (a b z R C : ℝ) (hbc : a + b = C) :
    qij a b z R R = C := by
  rw [qij_at_contact]; exact hbc

/-- **P.B2 (origin, abstract):** If `a·exp(-z·R) + b·exp(+z·R) = C` then `qij a b z R 0 = C`. -/
theorem exp_basis_origin_bc (a b z R C : ℝ)
    (hbc : a * Real.exp (-(z * R)) + b * Real.exp (z * R) = C) :
    qij a b z R 0 = C := by
  rw [qij_at_origin]; exact hbc

/-- **P.B2 (full contact):** Under the contact boundary condition
`a + b = Σ K_t - Σ A_k` (from Task P.4), the sum `qij(R) + E_ij(R) = Σ K_t` holds exactly —
zero error at the contact. -/
theorem exp_basis_satisfies_contact {n : ℕ} (A z_arr : Fin n → ℝ) (K : Fin n → ℝ)
    (a b z R : ℝ)
    (hbc : a + b = ∑ t : Fin n, K t - ∑ k : Fin n, A k) :
    qij a b z R R + eij A z_arr R R = ∑ t : Fin n, K t := by
  rw [qij_at_contact, eij_at_contact]
  linarith

/-- **P.B2 (full origin):** Under the origin boundary condition
`a·exp(-z·R) + b·exp(+z·R) = -E_ij(0)` (from Task P.2 + P.1), the sum
`qij(0) + E_ij(0) = 0` holds exactly — zero error at the origin. -/
theorem exp_basis_satisfies_origin {n : ℕ} (A z_arr : Fin n → ℝ)
    (a b z R : ℝ)
    (horigin : a * Real.exp (-(z * R)) + b * Real.exp (z * R) = -(eij A z_arr R 0)) :
    qij a b z R 0 + eij A z_arr R 0 = 0 := by
  rw [qij_at_origin]
  linarith

end FMSA.ExpBasis
