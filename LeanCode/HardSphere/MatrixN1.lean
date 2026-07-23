/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.Analysis.MatrixFin1
import LeanCode.HardSphere.SingleCompIdentity
import LeanCode.HardSphere.BaxterFactor

/-!
# Task M.2 — N=1 limit: Ĝ00 = g(z) and Â00 = a(z)

## Statement

For `N = 1`, the abstract `N×N` matrix propagators from Task M.1 reduce to the scalar
single-component propagators from Task M.9:

```
Ĝ_{00} = (P̂ · D̂⁻¹)_{00} = S(z) / D(z) = g(z)
Â_{00} = (Ê · D̂⁻¹)_{00} = 12eta·L(z) / D(z) = a(z)
```

where `S`, `L`, `D` are the Baxter Q-function components at the Yukawa pole z.

## Proof structure

The `1×1` reduction itself is pure linear algebra and now lives in
`Analysis/MatrixFin1.lean` (`mat_fin1_mul_inv`, `mat_fin1_mul_inv_apply`) — split out
2026-07-19 so that `Analysis/` stays citable without the physics. This file keeps only the
physics-named specialisations and the Baxter instance.

## Relation to Task 2.2

`Q0_ne_zero_at_yukawa` (`BaxterFactor.lean`) supplies the `D ≠ 0` condition for concrete physical
parameters, confirming the scalar propagators g(z) and a(z) are well-defined.

## Results

| Statement | Status |
|---|---|
| `g00_eq_g_scalar` | proved — `mat_fin1_mul_inv_apply` at `S` |
| `a00_eq_a_scalar` | proved — same at `12·eta·L` |
| `m2_identity` | proved (uses Task M.9 `g_add_a_mul_exp_eq_one`) |
| `m2_identity_baxter` | proved (uses Task 2.2 `Q0_ne_zero_at_yukawa`) |
-/

set_option linter.style.longLine false

open Real

namespace FMSA.MatrixN1

/-! ### Task M.2 — Main theorems -/

/-- **Task M.2 — Ĝ00 = g(z):**

For `N = 1`, the `(0,0)` entry of the matrix propagator `Ĝ = P̂·D̂⁻¹` equals the scalar
`g(z) = S/D`. -/
theorem g00_eq_g_scalar (S D : ℝ) :
    ((fun _ _ : Fin 1 => S) * (fun _ _ : Fin 1 => D)⁻¹ : Matrix (Fin 1) (Fin 1) ℝ) 0 0 =
    S / D := FMSA.MatrixFin1.mat_fin1_mul_inv_apply S D

/-- **Task M.2 — Â00 = a(z):**

For `N = 1`, the `(0,0)` entry of the matrix propagator `Â = Ê·D̂⁻¹` equals the scalar
`a(z) = 12eta·L/D`. -/
theorem a00_eq_a_scalar (eta L D : ℝ) :
    ((fun _ _ : Fin 1 => 12 * eta * L) * (fun _ _ : Fin 1 => D)⁻¹ :
     Matrix (Fin 1) (Fin 1) ℝ) 0 0 = 12 * eta * L / D :=
  FMSA.MatrixFin1.mat_fin1_mul_inv_apply (12 * eta * L) D

/-- **Task M.2 — N=1 limit of Ĝ + Â·exp(-z) = I:**

Combining the matrix reduction with Task M.9 (`g_add_a_mul_exp_eq_one`): in the N=1 case, the
abstract matrix identity reduces exactly to the scalar identity `g(z) + a(z)·exp(-z) = 1`. -/
theorem m2_identity {S L D eta z : ℝ}
    (hD_def : D = S + 12 * eta * L * Real.exp (-z))
    (hD : D ≠ 0) :
    ((fun _ _ : Fin 1 => S) * (fun _ _ : Fin 1 => D)⁻¹ : Matrix (Fin 1) (Fin 1) ℝ) 0 0 +
    ((fun _ _ : Fin 1 => 12 * eta * L) * (fun _ _ : Fin 1 => D)⁻¹ :
     Matrix (Fin 1) (Fin 1) ℝ) 0 0 * Real.exp (-z) = 1 := by
  rw [g00_eq_g_scalar, a00_eq_a_scalar]
  exact FMSA.SingleComp.g_add_a_mul_exp_eq_one hD_def hD

/-- **Task M.2 — Concrete Baxter form with D ≠ 0 from Task 2.2:**

For physical parameters (eta ∈ (0,1), z > 0), the N=1 matrix identity holds with the Baxter
Q-function D(z) confirmed non-zero by `Q0_ne_zero_at_yukawa`. -/
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
