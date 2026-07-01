/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Task M.1 — Matrix analog of g + a·exp(-z·sigma) = 1

For the multi-component Baxter Q-matrix `D = P + c • E` (where `c = exp(-z·sigma_min)` is
a scalar, `P` is the polynomial-part matrix, and `E` is the exponential-coefficient matrix),
with `D` invertible, the matrices

```
Ĝ := P · D⁻¹    (multi-component analog of g = S/D)
Â := E · D⁻¹    (multi-component analog of a = 12etaL/D)
```

satisfy:

```
Ĝ + c • Â = P · D⁻¹ + c • (E · D⁻¹) = (P + c • E) · D⁻¹ = D · D⁻¹ = I
```

This is the direct matrix lift of Task 4.2 (`g + a·e^{-z} = 1` in `SingleCompIdentity.lean`):
- N=1 scalar case:  `S/D + (12etaL/D)·e^{-z} = 1`  proved via `div_self`
- N>1 matrix case:  `P·D⁻¹ + c•(E·D⁻¹) = I`        proved via `mul_nonsing_inv`

The identity guarantees that the corrected inner-core formula
```
r·c^(1)_ij(r) = K·(1 - Ĝ^2_{ij})·e^{-z(r-R)} - K·Â^2_{ij}·e^{+z(r-R)} + Poly_{ij}(r)
```
uses coefficients `Ĝ_{ij}` and `Â_{ij}` satisfying the correct boundary identity.
See `problem_answers/multicomp_g_a_derivation.md` for the physical derivation.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace FMSA.MatrixIdentity

/-! ## Task M.1 — Main theorem -/

/-- **Task M.1 (abstract matrix identity):**
For any `n×n` matrices `P`, `E`, `D` over `ℝ` with `D = P + c • E` and `D` invertible,
```
P * D⁻¹ + c • (E * D⁻¹) = 1
```
This is the matrix analog of `g + a·exp(-z) = 1` (Task 4.2, `SingleCompIdentity.lean`).

**Proof:** Factor out `D⁻¹` on the right, substitute `D = P + c • E`, cancel `D * D⁻¹ = I`. -/
theorem g_mat_add_a_mat_exp_eq_one {n : ℕ}
    (P E D : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (hD_def : D = P + c • E)
    (hD : IsUnit D.det) :
    P * D⁻¹ + c • (E * D⁻¹) = 1 := by
  rw [← Algebra.smul_mul_assoc, ← add_mul, ← hD_def]
  exact Matrix.mul_nonsing_inv D hD

/-! ## Corollary: N=1 consistency check -/

/-- For `n = 1`, the matrices `P`, `E`, `D` are `1×1` (scalars), and the matrix theorem
reduces to the scalar `g + a·e^{-z} = 1`. This confirms the N=1 limit is consistent
with `SingleCompIdentity.lean`. -/
theorem g_mat_n1_eq_scalar (P E D c : ℝ)
    (hD_def : D = P + c * E)
    (hD : D ≠ 0) :
    P / D + c * (E / D) = 1 := by
  have hnum : P + c * E = D := hD_def.symm
  rw [← mul_div_assoc, ← add_div, hnum, div_self hD]

end FMSA.MatrixIdentity
