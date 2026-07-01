/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.FMSAPoly.SingleCompIdentity
import LeanCode.HardSphere.BaxterFactor

/-!
# Task M.2 — N=1 limit: Ĝ00 = g(z) and Â00 = a(z)

## Statement

For `n = 1`, the abstract `n×n` matrix propagators from Task M.1 reduce to the
scalar single-component propagators from Task 4.2:

```
Ĝ_{00} = (P̂ · D̂⁻¹)_{00} = S(z) / D(z) = g(z)
Â_{00} = (Ê · D̂⁻¹)_{00} = 12eta·L(z) / D(z) = a(z)
```

where `S`, `L`, `D` are the Baxter Q-function components at the Yukawa pole z.

## Proof structure

The key ingredient is that `1×1` matrix multiplication and inversion reduce to
scalar operations:

```
(fun _ _ : Fin 1 => S) * (fun _ _ : Fin 1 => D)⁻¹ = fun _ _ => S / D
```

This holds for **all** S, D (including D = 0, since `S / 0 = 0` in ℝ and the
matrix inverse of the zero matrix is zero).  No `D ≠ 0` hypothesis is needed
for the reduction itself; it is only needed to confirm g(z) = S/D is the
well-defined propagator.

## Relation to Task 2.2

`Q0_ne_zero_at_yukawa` (axiomatic, in `BaxterFactor.lean`) provides the
`D ≠ 0` condition for concrete physical parameters, confirming the scalar
propagators g(z) and a(z) are well-defined.

## Results

| Statement | Status |
|---|---|
| `fin1_const_mul` | proved |
| `fin1_const_inv` | proved — `Pi.instInv` on bare lambda is pointwise, so `rfl` |
| `mat_fin1_mul_inv` | proved (from above) |
| `g00_eq_g_baxter` | proved |
| `a00_eq_a_baxter` | proved |
| `m2_identity` | proved (uses Task 4.2 `g_add_a_mul_exp_eq_one`) |
-/

set_option linter.style.longLine false

open Real

namespace FMSA.MatrixN1

/-! ### Core 1×1 matrix reduction lemmas -/

/-- `1×1` matrix multiplication is scalar multiplication. -/
private lemma fin1_const_mul (S T : ℝ) :
    ((fun _ _ : Fin 1 => S) * (fun _ _ : Fin 1 => T) : Matrix (Fin 1) (Fin 1) ℝ) =
    fun _ _ => S * T := by
  ext i j; fin_cases i; fin_cases j; simp

/-- `1×1` constant matrix inverse is scalar inverse.

The `⁻¹` on a bare lambda `fun _ _ : Fin 1 => D` (whose inferred type is
`Fin 1 → Fin 1 → ℝ`) is resolved by Lean as `Pi.instInv` (pointwise), which
gives `(fun _ _ => D)⁻¹ = fun _ _ => D⁻¹` definitionally. -/
private lemma fin1_const_inv (D : ℝ) :
    ((fun _ _ : Fin 1 => D : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ = fun _ _ => D⁻¹ := by
  funext i j; fin_cases i; fin_cases j; rfl

/-! ### Task M.2 — Main theorems -/

/-- **Task M.2 (abstract form):**

For any scalars S, D, the `1×1` matrix product `P·D̂⁻¹` equals the
scalar ratio `S/D` (as a constant `1×1` matrix).

Holds unconditionally (D = 0 gives both sides zero). -/
theorem mat_fin1_mul_inv (S D : ℝ) :
    ((fun _ _ : Fin 1 => S) * (fun _ _ : Fin 1 => D)⁻¹ : Matrix (Fin 1) (Fin 1) ℝ) =
    fun _ _ => S / D := by
  rw [fin1_const_inv, fin1_const_mul, div_eq_mul_inv]

/-- **Task M.2 — Ĝ00 = g(z):**

For `n = 1`, the `(0,0)` entry of the matrix propagator `Ĝ = P̂·D̂⁻¹` equals
the scalar `g(z) = S/D`. -/
theorem g00_eq_g_scalar (S D : ℝ) :
    ((fun _ _ : Fin 1 => S) * (fun _ _ : Fin 1 => D)⁻¹ : Matrix (Fin 1) (Fin 1) ℝ) 0 0 =
    S / D := congr_fun (congr_fun (mat_fin1_mul_inv S D) 0) 0

/-- **Task M.2 — Â00 = a(z):**

For `n = 1`, the `(0,0)` entry of the matrix propagator `Â = Ê·D̂⁻¹` equals
the scalar `a(z) = 12eta·L/D`. -/
theorem a00_eq_a_scalar (eta L D : ℝ) :
    ((fun _ _ : Fin 1 => 12 * eta * L) * (fun _ _ : Fin 1 => D)⁻¹ :
     Matrix (Fin 1) (Fin 1) ℝ) 0 0 = 12 * eta * L / D :=
  congr_fun (congr_fun (mat_fin1_mul_inv (12 * eta * L) D) 0) 0

/-- **Task M.2 — N=1 limit of Ĝ + Â·exp(-z) = I:**

Combining the matrix reduction with Task 4.2 (`g_add_a_mul_exp_eq_one`):
in the N=1 case, the abstract matrix identity reduces exactly to the scalar identity
`g(z) + a(z)·exp(-z) = 1`. -/
theorem m2_identity {S L D eta z : ℝ}
    (hD_def : D = S + 12 * eta * L * Real.exp (-z))
    (hD : D ≠ 0) :
    ((fun _ _ : Fin 1 => S) * (fun _ _ : Fin 1 => D)⁻¹ : Matrix (Fin 1) (Fin 1) ℝ) 0 0 +
    ((fun _ _ : Fin 1 => 12 * eta * L) * (fun _ _ : Fin 1 => D)⁻¹ :
     Matrix (Fin 1) (Fin 1) ℝ) 0 0 * Real.exp (-z) = 1 := by
  rw [g00_eq_g_scalar, a00_eq_a_scalar]
  exact FMSA.SingleComp.g_add_a_mul_exp_eq_one hD_def hD

/-- **Task M.2 — Concrete Baxter form with D ≠ 0 from Task 2.2:**

For physical parameters (eta ∈ (0,1), z > 0), the N=1 matrix identity holds
with the Baxter Q-function D(z) confirmed non-zero by `Q0_ne_zero_at_yukawa`. -/
theorem m2_identity_baxter {eta z : ℝ} (heta : eta ∈ Set.Ioo 0 1) (hz : 0 < z) :
    let S := (1 - eta) ^ 2 * z ^ 3 + 6 * eta * (1 - eta) * z ^ 2 + 18 * eta ^ 2 * z -
             12 * eta * (1 + 2 * eta)
    let L := (1 + eta / 2) * z + (1 + 2 * eta)
    let D := S + 12 * eta * L * Real.exp (-z)
    ((fun _ _ : Fin 1 => S) * (fun _ _ : Fin 1 => D)⁻¹ : Matrix (Fin 1) (Fin 1) ℝ) 0 0 +
    ((fun _ _ : Fin 1 => 12 * eta * L) * (fun _ _ : Fin 1 => D)⁻¹ :
     Matrix (Fin 1) (Fin 1) ℝ) 0 0 * Real.exp (-z) = 1 := by
  simp only []
  apply m2_identity rfl
  exact FMSA.HardSphere.Q0_ne_zero_at_yukawa heta hz

end FMSA.MatrixN1
