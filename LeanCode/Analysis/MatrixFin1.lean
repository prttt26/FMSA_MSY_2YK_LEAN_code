/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# `1×1` matrices are scalars

Constant `Matrix (Fin 1) (Fin 1) ℝ` multiplication and inversion reduce to the scalar operations.
Pure linear algebra over arbitrary reals — no physics enters, which is why this lives in
`Analysis/` (split out of `HardSphere/MatrixN1.lean` on 2026-07-19; the physics-named
specialisations `g00_eq_g_scalar` / `a00_eq_a_scalar` and the Baxter instances stay there).

Everything is **unconditional**: at `D = 0` both sides are `0`, since `S / 0 = 0` in `ℝ` and the
matrix inverse of the zero matrix is the zero matrix. No `D ≠ 0` hypothesis is needed for the
reduction itself — only for interpreting `S / D` as a well-defined propagator.
-/

set_option linter.style.longLine false

namespace FMSA.MatrixFin1

/-- `1×1` matrix multiplication is scalar multiplication. -/
private lemma fin1_const_mul (S T : ℝ) :
    ((fun _ _ : Fin 1 => S) * (fun _ _ : Fin 1 => T) : Matrix (Fin 1) (Fin 1) ℝ) =
    fun _ _ => S * T := by
  ext i j; fin_cases i; fin_cases j; simp

/-- `1×1` constant matrix inverse is scalar inverse.

The `⁻¹` on a bare lambda `fun _ _ : Fin 1 => D` (whose inferred type is `Fin 1 → Fin 1 → ℝ`) is
resolved by Lean as `Pi.instInv` (pointwise), which gives `(fun _ _ => D)⁻¹ = fun _ _ => D⁻¹`
definitionally — hence `rfl`. -/
private lemma fin1_const_inv (D : ℝ) :
    ((fun _ _ : Fin 1 => D : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ = fun _ _ => D⁻¹ := by
  funext i j; fin_cases i; fin_cases j; rfl

/-- **`1×1` propagator reduction.**  For any scalars `S`, `D`, the matrix product `S · D⁻¹` is the
constant `1×1` matrix `S / D`.  Unconditional (`D = 0` sends both sides to `0`). -/
theorem mat_fin1_mul_inv (S D : ℝ) :
    ((fun _ _ : Fin 1 => S) * (fun _ _ : Fin 1 => D)⁻¹ : Matrix (Fin 1) (Fin 1) ℝ) =
    fun _ _ => S / D := by
  rw [fin1_const_inv, fin1_const_mul, div_eq_mul_inv]

/-- Entry form of `mat_fin1_mul_inv`: the sole entry of `S · D⁻¹` is `S / D`. -/
theorem mat_fin1_mul_inv_apply (S D : ℝ) :
    ((fun _ _ : Fin 1 => S) * (fun _ _ : Fin 1 => D)⁻¹ : Matrix (Fin 1) (Fin 1) ℝ) 0 0 =
    S / D := congr_fun (congr_fun (mat_fin1_mul_inv S D) 0) 0

end FMSA.MatrixFin1
