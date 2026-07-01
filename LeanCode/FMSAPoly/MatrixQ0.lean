/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.FMSAPoly.QhatDecomposition

/-!
# Task M.3 — det(Q̂₀) ≠ 0 for valid multi-component parameters

## Context

The multi-component Baxter Q-matrix Q̂₀(z) is an n×n matrix whose (i,j) entry
(from Task B.2 / `b2_qhat_entry_decomp`) has the form:
```
Q̂₀_{ij}(z) = δ_{ij} − √(ρᵢρⱼ) · exp(−λᵢⱼ·z) · [Q'ᵢⱼ·p₁(σᵢ,z) + Q''ᵢⱼ·p₂(σᵢ,z)]
```
where:
- `λᵢⱼ = (σⱼ − σᵢ)/2`  (size asymmetry shift)
- `p₁(σ,z) = (1 − z·σ − exp(−z·σ)) / z²`
- `p₂(σ,z) = (1 − z·σ + (z·σ)²/2 − exp(−z·σ)) / z³`
- `Q'ᵢⱼ`, `Q''ᵢⱼ` are Baxter DCF coefficients (from the multicomponent PY hard-sphere DCF)
- `√(ρᵢρⱼ)` is the geometric-mean density factor

## Statement

For a physically valid n-component mixture (total packing fraction η < 1, all σᵢ > 0,
all ρᵢ ≥ 0, and Yukawa pole z > 0):
```
det(Q̂₀(z)) ≠ 0
```
equivalently, `IsUnit (Q0_mat ...).det`, which supplies `hD : IsUnit D.det`
for the abstract matrix identity `P·D⁻¹ + c·(E·D⁻¹) = I` (Task M.1).

## Status

| Statement | Status |
|---|---|
| `q0_entry` | defined (concrete B.2 formula) |
| `Q0_mat` | defined (assembled n×n matrix) |
| `Q0_mat_decomp` | proved (entry-wise application of B.2) |
| `Q0_mat_isUnit_det` | **axiom** (multi-component analog of `Q0_ne_zero_at_yukawa`) |
| `Q0_mat_n1_eq_scalar` | proved (N=1 consistency: matrix entry matches scalar Q₀) |

## Why this is hard

The N=1 case is already axiomatic (`Q0_ne_zero_at_yukawa` in `BaxterFactor.lean`).
The n-component case requires bounding `det(I − C)` where `C` is the off-diagonal
correction matrix, via either:
- Matrix norm: `‖C‖ < 1` ⟹ det(I−C) ≠ 0 (Neumann series in finite dimensions)
- Continuity: det is continuous, non-zero at z=0 (det(I) = 1), propagated to all z>0
Both routes are outside current Mathlib scope for this specific matrix.
-/

set_option linter.style.longLine false

open Real

namespace FMSA.MatrixQ0

/-! ### Scalar entry formula -/

/-- The (i,j) scalar entry of Q̂₀(z), parameterized by:
- `z`: Yukawa pole (> 0)
- `sigma_i`: diameter of species i
- `lam_ij = (sigma_j − sigma_i)/2`: size asymmetry parameter
- `Qp_ij`, `Qpp_ij`: Baxter DCF coefficients Q'ᵢⱼ, Q''ᵢⱼ
- `rho_geo_ij = √(ρᵢρⱼ)`: geometric-mean density
- `delta_ij`: Kronecker delta (1 if i=j, 0 otherwise) -/
noncomputable def q0_entry (z sigma_i lam_ij Qp_ij Qpp_ij rho_geo_ij delta_ij : ℝ) : ℝ :=
  delta_ij - rho_geo_ij * exp (-(lam_ij * z)) *
    (Qp_ij  * ((1 - z * sigma_i - exp (-(z * sigma_i))) / z ^ 2) +
     Qpp_ij * ((1 - z * sigma_i + (z * sigma_i) ^ 2 / 2 - exp (-(z * sigma_i))) / z ^ 3))

/-- The n×n Baxter Q-matrix Q̂₀(z), assembled from `q0_entry`.

Parameters:
- `sigma : Fin n → ℝ`: species diameters
- `rho_geo : Fin n → Fin n → ℝ`: `rho_geo i j = √(ρᵢ · ρⱼ)`
- `Qp Qpp : Fin n → Fin n → ℝ`: Baxter DCF coefficients -/
noncomputable def Q0_mat {n : ℕ} (z : ℝ)
    (sigma : Fin n → ℝ)
    (rho_geo : Fin n → Fin n → ℝ)
    (Qp Qpp : Fin n → Fin n → ℝ)
    : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => q0_entry z (sigma i) ((sigma j - sigma i) / 2)
               (Qp i j) (Qpp i j) (rho_geo i j) (if i = j then 1 else 0)

/-! ### Entry decomposition (proved from Task B.2) -/

/-- Each (i,j) entry of Q̂₀ satisfies the B.2 decomposition
`Q̂₀_{ij} = P̂_{ij} + Ê_{ij} · exp(-z · σ_min)`. -/
theorem Q0_mat_entry_decomp {n : ℕ} (z sigma_min : ℝ) (hz : z ≠ 0)
    (sigma : Fin n → ℝ)
    (rho_geo : Fin n → Fin n → ℝ)
    (Qp Qpp : Fin n → Fin n → ℝ)
    (i j : Fin n)
    (hR : (sigma j - sigma i) / 2 + sigma i = (sigma i + sigma j) / 2) :
    Q0_mat z sigma rho_geo Qp Qpp i j =
    ((if i = j then 1 else 0) -
     rho_geo i j * exp (-((sigma j - sigma i) / 2 * z)) *
       (Qp i j * ((1 - z * sigma i) / z ^ 2) +
        Qpp i j * ((1 - z * sigma i + (z * sigma i) ^ 2 / 2) / z ^ 3))) +
    rho_geo i j * exp (-(z * ((sigma i + sigma j) / 2 - sigma_min))) *
      (Qp i j / z ^ 2 + Qpp i j / z ^ 3) * exp (-(z * sigma_min)) := by
  unfold Q0_mat q0_entry
  exact FMSA.PathB.b2_qhat_entry_decomp z (sigma i) ((sigma j - sigma i) / 2)
    ((sigma i + sigma j) / 2) sigma_min (rho_geo i j) (Qp i j) (Qpp i j)
    (if i = j then 1 else 0) hz hR

/-! ### Task M.3 — Main axiom -/

/-- **Task M.3 (axiom): `det(Q̂₀) ≠ 0` for physical parameters.**

For z > 0, σᵢ > 0, ρᵢ ≥ 0, and physical Baxter coefficients with total packing
fraction η < 1, the Baxter Q-matrix is invertible.

This is the multi-component analog of `Q0_ne_zero_at_yukawa` (N=1 case,
`BaxterFactor.lean`).  The proof is axiomatic because it requires either:
- A matrix norm bound `‖I − Q̂₀‖ < 1` (outside current Mathlib scope), or
- A continuity + positivity argument generalizing the N=1 analytic argument.

**Usage:** Provides `IsUnit (Q0_mat ...).det`, i.e., the `hD` hypothesis for
`g_mat_add_a_mat_exp_eq_one` (Task M.1), making Ĝ = P̂·Q̂₀⁻¹ well-defined. -/
axiom Q0_mat_isUnit_det {n : ℕ} {z : ℝ}
    {sigma : Fin n → ℝ}
    {rho_geo : Fin n → Fin n → ℝ}
    {Qp Qpp : Fin n → Fin n → ℝ}
    (hz : 0 < z)
    (hsigma : ∀ i, 0 < sigma i)
    (hrho : ∀ i j, 0 ≤ rho_geo i j)
    (heta : (Real.pi / 6 * ∑ i : Fin n, rho_geo i i ^ 2 * sigma i ^ 3) ∈ Set.Ioo 0 1) :
    IsUnit (Q0_mat z sigma rho_geo Qp Qpp).det

/-! ### N=1 consistency check -/

/-- For n=1, the Q̂₀ matrix is 1×1, and its single entry matches the scalar
single-component Q₀ formula.

Concretely: `Q0_mat z σ ρ_geo Qp Qpp 0 0 = 1 − ρ · [Q'·p₁(σ,z) + Q''·p₂(σ,z)]`
with `λ₀₀ = 0` (no size asymmetry for a single component). -/
theorem Q0_mat_n1_entry (z sigma rho_geo Qp Qpp : ℝ) :
    Q0_mat z (fun _ : Fin 1 => sigma)
             (fun _ _ : Fin 1 => rho_geo)
             (fun _ _ : Fin 1 => Qp)
             (fun _ _ : Fin 1 => Qpp) 0 0 =
    1 - rho_geo * exp 0 *
      (Qp  * ((1 - z * sigma - exp (-(z * sigma))) / z ^ 2) +
       Qpp * ((1 - z * sigma + (z * sigma) ^ 2 / 2 - exp (-(z * sigma))) / z ^ 3)) := by
  unfold Q0_mat q0_entry
  simp

end FMSA.MatrixQ0
