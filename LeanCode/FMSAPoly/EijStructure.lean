/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Task P.1 — E_ij is a sum of decaying exponentials

In the FMSA_poly decomposition, the inner-core DCF is split as
`c^(1)_ij(r) = [E_ij(r) + P_ij(r)] / (2π√(rhoirhoj) · r)`,
where `E_ij` carries the exponential structure and `P_ij` is a polynomial correction.

`E_ij` is a finite sum of terms `A_k · exp(-z_k · (R - r))` with `z_k > 0`.
Each factor `exp(-z_k · (R - r))` is small (`≈ exp(-z_k·R)`) near `r = 0`
and equals 1 at the contact `r = R`.

## Main definitions and results

- `eij`: finite sum `Σ_k A_k · exp(-z_k · (R - r))`
- `eij_at_contact`: `E_ij(R) = Σ_k A_k`  (exp factors all collapse to 1)
- `eij_at_origin`: `E_ij(0) = Σ_k A_k · exp(-z_k · R)`  (exp factors are exponentially small)
- `eij_exp_factor_strictMono`: for `z > 0`, the factor `r ↦ exp(-z·(R-r))` is strictly increasing
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Real

namespace FMSA.EijStructure

/-! ## Definition -/

section BoundaryValues

variable {n : ℕ} (A z : Fin n → ℝ) (R : ℝ)

/-- **E_ij as a finite sum of decaying exponentials (Task P.1):**
`E_ij(r) = Σ_{k=0}^{n-1} A_k · exp(-z_k · (R - r))`
where `A_k` are propagator amplitudes and `z_k > 0` are Yukawa inverse ranges.
The factor `exp(-z_k·(R-r))` is ≈ 0 at `r = 0` and equals 1 at `r = R`. -/
noncomputable def eij (r : ℝ) : ℝ := ∑ k : Fin n, A k * Real.exp (-(z k) * (R - r))

/-! ## Boundary values -/

/-- **Contact value (Task P.1):** At `r = R`, every factor `exp(-z_k·(R-R)) = exp(0) = 1`,
so the sum collapses to `E_ij(R) = Σ_k A_k`. -/
theorem eij_at_contact : eij A z R R = ∑ k : Fin n, A k := by
  simp [eij, sub_self, mul_zero, Real.exp_zero]

/-- **Origin value (Task P.1):** At `r = 0`, each factor is `exp(-z_k·R)`,
giving `E_ij(0) = Σ_k A_k · exp(-z_k · R)`.
For large `z_k`, this is exponentially small. -/
theorem eij_at_origin : eij A z R 0 = ∑ k : Fin n, A k * Real.exp (-(z k) * R) := by
  simp [eij, sub_zero]

end BoundaryValues

/-! ## Monotonicity -/

/-- **Monotone growth (Task P.1):** For `z > 0`, the map `r ↦ exp(-z·(R-r))` is
strictly increasing.  Thus (when amplitudes `A_k` share the same sign) `E_ij` grows
monotonically from its exponentially small origin value to `Σ A_k` at contact. -/
theorem eij_exp_factor_strictMono (z R : ℝ) (hz : 0 < z) :
    StrictMono (fun r => Real.exp (-z * (R - r))) := by
  intro r1 r2 hr
  apply Real.exp_lt_exp.mpr
  nlinarith

end FMSA.EijStructure
