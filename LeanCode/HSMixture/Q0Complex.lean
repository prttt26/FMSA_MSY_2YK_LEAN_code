/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HSMixture.MatrixQ0

/-!
# Task Y1.1 — Complex Laplace-space Baxter matrix `Q̂₀(s)`

The complex (`s = −ik ∈ ℂ`) Baxter factor matrix of the hard-sphere mixture, [LN] Eq. 10:
```
{Q̂₀(s)}_{ij} = δ_{ij} − (ρ_iρ_j)^{1/2} e^{−sλ_{ij}} [ φ₁(R_i) Q'_{ij} + φ₂(R_i) Q''_j ],
φ₁(R) = (1 − sR − e^{−sR})/s²,   φ₂(R) = (1 − sR + (sR)²/2 − e^{−sR})/s³   (Eq. 13).
```
This is the **complexification** of the codebase's real `FMSA.MatrixQ0.q0_entry` / `Q0_mat`
(`MatrixQ0.lean`): the same expression with `z:ℝ`, `Real.exp` replaced by `s:ℂ`, `Complex.exp`.
It is the Laplace-space object underlying Group Y1 (`A_{ij}(s) = [Q̂₀(s)⁻¹]_{ij} − δ`, [LN] Eq. 70).

## Results

* `q0_entry_c`, `Q0_mat_c` — the complex entry / matrix.
* `q0_entry_c_real` — consistency with the trusted real `q0_entry` at real argument.
* `inv_apply_eq_adj_div_det` — `[Q̂₀(s)⁻¹]_{ij} = adj_{ij}/det` (Mathlib `Matrix.inv_def`);
  the `adj/det` form of the inverse ([LN] Eq. 14), the `G_{ij}` factor used downstream (Y1.4/Y1.6).

## Deferred

The closed-form inverse [LN] Eq. 14 (`{Q̂₀⁻¹}_{ij} = δ + 2π√(ρρ) W_{ij}(s)/(Δ det(s)) e^{−sλ}`, with
`W` Eq. 15, `det` Eq. 16) — a large algebraic identity; the `adj/det` form above is what the residue
chain needs.

Status: ✓ DONE (2026-07-15), axiom-clean.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace FMSA.Q0Complex

open scoped Matrix

/-- Complex Laplace-space Baxter entry ([LN] Eq. 10–13), `s ∈ ℂ`.  Complexification of the real
`FMSA.MatrixQ0.q0_entry`. -/
noncomputable def q0_entry_c (s : ℂ) (sigma_i lam_ij Qp_ij Qpp_ij rho_geo_ij delta_ij : ℂ) : ℂ :=
  delta_ij - rho_geo_ij * Complex.exp (-(lam_ij * s)) *
    (Qp_ij  * ((1 - s * sigma_i - Complex.exp (-(s * sigma_i))) / s ^ 2) +
     Qpp_ij * ((1 - s * sigma_i + (s * sigma_i) ^ 2 / 2 - Complex.exp (-(s * sigma_i))) / s ^ 3))

/-- Complex Baxter matrix `Q̂₀(s) : ℂ → Matrix (Fin N) (Fin N) ℂ` ([LN] Eq. 10), assembled from
`q0_entry_c`.  Complexification of the real `FMSA.MatrixQ0.Q0_mat`. -/
noncomputable def Q0_mat_c {N : ℕ} (s : ℂ)
    (sigma : Fin N → ℂ) (rho_geo : Fin N → Fin N → ℂ) (Qp Qpp : Fin N → Fin N → ℂ)
    : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => q0_entry_c s (sigma i) ((sigma j - sigma i) / 2)
               (Qp i j) (Qpp i j) (rho_geo i j) (if i = j then 1 else 0)

/-- **Consistency at real argument.**  With cast real data the complex entry is the cast of the real
`q0_entry` — grounding the complex def in the trusted real one. -/
theorem q0_entry_c_real (z sigma_i lam_ij Qp_ij Qpp_ij rho_geo_ij delta_ij : ℝ) :
    q0_entry_c (z : ℂ) sigma_i lam_ij Qp_ij Qpp_ij rho_geo_ij delta_ij
      = ((FMSA.MatrixQ0.q0_entry z sigma_i lam_ij Qp_ij Qpp_ij rho_geo_ij delta_ij : ℝ) : ℂ) := by
  unfold q0_entry_c FMSA.MatrixQ0.q0_entry
  push_cast [Complex.ofReal_exp]
  ring

/-- **Inverse entry = adjugate / det** — the `[Q̂₀(s)⁻¹]_{ij} = adj/det` form of [LN] Eq. 14
(Mathlib `Matrix.inv_def`; unconditional — both sides `0` when `det` is not a unit).  This is the
GA-matrix `G_{ij}(s)` factor. -/
theorem inv_apply_eq_adj_div_det {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    M⁻¹ i j = M.adjugate i j / M.det := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', inv_mul_eq_div]

end FMSA.Q0Complex
