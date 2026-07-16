/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaDCF.Q0Complex
import LeanCode.Analysis.ResidueAtSimplePole

/-!
# Tasks MML.1 / MML.2 — N=2 mixture HS-pole residue of `Q̂₀⁻¹`

Group MML foundation: for `N = 2` the complex Baxter matrix `Q̂₀(s)` (Y1.1, `Q0Complex.lean`) is `2×2`,
so its inverse is fully algebraic — `Q̂₀⁻¹ = adj(Q̂₀)/det(Q̂₀)`. The off-diagonal entry is
`[Q̂₀(s)⁻¹]₀₁ = −Q̂₀₀₁(s)/det(Q̂₀(s))`, and at a simple zero `s_k` of `det(Q̂₀)` (a hard-sphere pole)
the residue is `−Q̂₀₀₁(s_k)/det′(Q̂₀)(s_k)` — the `B_k` coefficient of `fmsa_hs_pole_residue.py`.

Everything reuses existing tools: Mathlib `Matrix.det_fin_two` / `adjugate_fin_two`,
`FMSA.Q0Complex.inv_apply_eq_adj_div_det` (Y1.1, `M⁻¹ = adj/det` unconditional), and
`FMSA.HardSphere.residue_of_simple_pole` (`ResidueAtSimplePole.lean`).

## Results

* `adjugate_fin_two_zero_one` / `inv_zero_one_eq` — for any `2×2` `M`: `adj(M)₀₁ = −M₀₁` and
  `M⁻¹₀₁ = −M₀₁/det M`.
* `Q0_det_fin_two` / `Q0inv_zero_one` — **MML.1**: the `Q̂₀` specializations, `det(Q̂₀) =
  Q̂₀₀₀Q̂₀₁₁ − Q̂₀₀₁Q̂₀₁₀` and `[Q̂₀(s)⁻¹]₀₁ = −Q̂₀₀₁(s)/det(Q̂₀(s))`.
* `b_k_residue` — **MML.2**: at a simple zero `s_k` of `det(Q̂₀)`,
  `Res_{z=s_k} [Q̂₀(z)⁻¹]₀₁ = −Q̂₀₀₁(s_k)/det′(Q̂₀)(s_k)` (the `Q̂₀`-cofactor part of `B_k`; the Yukawa
  propagator factor `K/(z_t²−s_k²)` is Y1.3/MML.3, separate).

The simple-zero data (det differentiable with `det′ ≠ 0`, entry continuous — all standard since the
entries are entire for `s_k ≠ 0`) enters as hypotheses, matching `residue_of_simple_pole`.

Status: ✓ DONE (MML.1, MML.2), axiom-clean. MZERO.1 (infinitely many HS poles) + MML.3 (full assembly)
deferred.
-/

set_option linter.style.longLine false

open Filter Topology
open scoped Matrix

namespace FMSA.MixtureHSPoles

/-! ### MML.1 — 2×2 adjugate / determinant / inverse -/

/-- For a `2×2` matrix, the `(0,1)` adjugate entry is `−M₀₁` (`Matrix.adjugate_fin_two`). -/
theorem adjugate_fin_two_zero_one (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M.adjugate 0 1 = -M 0 1 := by
  simp [Matrix.adjugate_fin_two]

/-- The `(0,1)` entry of a `2×2` inverse: `M⁻¹₀₁ = −M₀₁/det M` (unconditional, via
`inv_apply_eq_adj_div_det` + `adjugate_fin_two_zero_one`). -/
theorem inv_zero_one_eq (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M⁻¹ 0 1 = -M 0 1 / M.det := by
  rw [FMSA.Q0Complex.inv_apply_eq_adj_div_det, adjugate_fin_two_zero_one]

/-- **MML.1 — `det Q̂₀` for `N=2`.**  `det(Q̂₀(s)) = Q̂₀₀₀Q̂₀₁₁ − Q̂₀₀₁Q̂₀₁₀` (`Matrix.det_fin_two`). -/
theorem Q0_det_fin_two (s : ℂ) (sigma : Fin 2 → ℂ) (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ) :
    (FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp).det
      = (FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp) 0 0
          * (FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp) 1 1
        - (FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp) 0 1
          * (FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp) 1 0 :=
  Matrix.det_fin_two _

/-- **MML.1 — `[Q̂₀(s)⁻¹]₀₁ = −Q̂₀₀₁(s)/det(Q̂₀(s))`** (the [LN] 2×2 identity for the off-diagonal
inverse entry). -/
theorem Q0inv_zero_one (s : ℂ) (sigma : Fin 2 → ℂ) (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ) :
    (FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp)⁻¹ 0 1
      = -(FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp) 0 1
        / (FMSA.Q0Complex.Q0_mat_c s sigma rho_geo Qp Qpp).det :=
  inv_zero_one_eq _

/-! ### MML.2 — the `B_k` HS-pole residue -/

/-- **MML.2 — the `B_k` residue.**  At a simple zero `s_k` of `s ↦ det(Q̂₀(s))` (an HS pole:
`det(Q̂₀(s_k)) = 0`, `det` differentiable there with nonzero derivative `Dprime`; the entry `Q̂₀₀₁`
continuous at `s_k`), the off-diagonal inverse entry has residue
`Res_{z=s_k} [Q̂₀(z)⁻¹]₀₁ = −Q̂₀₀₁(s_k)/Dprime` — the `Q̂₀`-cofactor part of the `B_k` amplitude.
Wires `Q0inv_zero_one` (MML.1) into `residue_of_simple_pole`. -/
theorem b_k_residue (s_k : ℂ) (sigma : Fin 2 → ℂ) (rho_geo Qp Qpp : Fin 2 → Fin 2 → ℂ) (Dprime : ℂ)
    (hD : HasDerivAt (fun z => (FMSA.Q0Complex.Q0_mat_c z sigma rho_geo Qp Qpp).det) Dprime s_k)
    (hDz0 : (FMSA.Q0Complex.Q0_mat_c s_k sigma rho_geo Qp Qpp).det = 0)
    (hDprime : Dprime ≠ 0)
    (hNcont : ContinuousAt (fun z => (FMSA.Q0Complex.Q0_mat_c z sigma rho_geo Qp Qpp) 0 1) s_k) :
    Tendsto (fun z => (z - s_k) * ((FMSA.Q0Complex.Q0_mat_c z sigma rho_geo Qp Qpp)⁻¹ 0 1))
      (𝓝[≠] s_k)
      (𝓝 (-(FMSA.Q0Complex.Q0_mat_c s_k sigma rho_geo Qp Qpp) 0 1 / Dprime)) := by
  have hrw : ∀ z, (FMSA.Q0Complex.Q0_mat_c z sigma rho_geo Qp Qpp)⁻¹ 0 1
      = (-(FMSA.Q0Complex.Q0_mat_c z sigma rho_geo Qp Qpp) 0 1)
        / (FMSA.Q0Complex.Q0_mat_c z sigma rho_geo Qp Qpp).det :=
    fun z => Q0inv_zero_one z sigma rho_geo Qp Qpp
  simp_rw [hrw]
  exact FMSA.HardSphere.residue_of_simple_pole
    (fun z => -(FMSA.Q0Complex.Q0_mat_c z sigma rho_geo Qp Qpp) 0 1)
    (fun z => (FMSA.Q0Complex.Q0_mat_c z sigma rho_geo Qp Qpp).det)
    Dprime s_k hD hDz0 hDprime hNcont.neg

end FMSA.MixtureHSPoles
