/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.FMSAPoly.EijStructure
import LeanCode.FMSAPoly.PolyApproxFails

/-!
# Task P.C1 — Corollary: FMSA_poly normalization forces large approximation error

This file chains Tasks P.1 + P.2 + P.3 into a single theorem:

1. **P.1** (`eij_at_origin`): `E_ij(0) = Σ_k A_k · exp(-z_k·R) ≥ 0` when `A_k ≥ 0`.
2. **P.2** (origin normalisation): `P_ij(0) = -E_ij(0) ≤ 0`.
3. **P.3** (`poly_approx_fails_origin`): `P_ij(0) ≤ 0` → error ≥ `exp(z0·R)` at r = 0.

**The paradox:** The normalisation condition that makes `c(r)/r` finite at r = 0 (Task P.2)
is **exactly** the condition that makes the polynomial approximation maximally bad (Task P.3).
FMSA_poly pays for its r = 0 regularity with catastrophic approximation error on all of [0, R].

## Main result

- `fmsa_poly_origin_failure` : under P.2 normalisation with `A_k ≥ 0`,
  `∃ r ∈ [0, R], |exp(z0·(R-r)) - P(r)| ≥ exp(z0·R)`
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open FMSA.EijStructure FMSA.PolyApproxFails

namespace FMSA.PolyApproxCorollary

section

variable {n : ℕ} (A z : Fin n → ℝ) (R : ℝ)

/-- **Origin failure corollary (Task P.C1):**
Under the FMSA_poly origin normalisation `E_ij(0) + P(0) = 0` with non-negative amplitudes
`A_k ≥ 0`, the polynomial `P` satisfies `P(0) = -E_ij(0) ≤ 0`, so by Task P.3
(`poly_approx_fails_origin`) the approximation error for `exp(z0·(R-r))` is ≥ `exp(z0·R)`.

This is the formal chain **P.1 → P.2 → P.3**: regularity at r = 0 ↔ catastrophic error. -/
theorem fmsa_poly_origin_failure (hR : 0 < R) (hA : ∀ k, 0 <= A k) (P : Polynomial ℝ)
    (z0 : ℝ) (hz0 : 0 < z0)
    (hnorm : eij A z R 0 + P.eval 0 = 0) :
    ∃ r ∈ Set.Icc 0 R, |Real.exp (z0 * (R - r)) - P.eval r| >= Real.exp (z0 * R) := by
  apply poly_approx_fails_origin z0 R hR hz0
  -- Need: P.eval 0 ≤ 0. From hnorm: P(0) = -E_ij(0). From P.1 + hA: E_ij(0) ≥ 0.
  have hE : 0 <= eij A z R 0 := by
    rw [eij_at_origin]
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (hA k) (Real.exp_nonneg _)
  linarith

end

end FMSA.PolyApproxCorollary
