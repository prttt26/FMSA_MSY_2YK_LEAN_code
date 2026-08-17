/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Basic

/-!
# Holomorphy of the matrix inverse — the analytic core of the eq (20) `A(−iy)` terms

The remaining terms of Tang & Lu's eq (20) integrand carry the factor
`A(−iy) = 2π(ρᵢρⱼ)^{1/2}W(−iy)/(Δ det(−iy))`, i.e. the entries of `[Q̂₀(−y)]⁻¹` (via the closed-form
inverse `Q0_mat_phys_inv_eq`).  For the contour-sum engine
(`ContourSumUpperHalfPlane.improper_integral_eq_sum_residues_upperHalfPlane`) to accept them, their
`hc`/`hd` need the **holomorphy of `[Q̂₀(−y)]⁻¹` in the upper half-plane**.

This file proves that entirely generally, with no reference to the Baxter structure: if every entry
of a matrix-valued function `M : ℂ → Matrix (Fin N) (Fin N) ℂ` is `DifferentiableAt w` and
`det (M w) ≠ 0`, then every entry of the inverse `z ↦ (M z)⁻¹ i j` is `DifferentiableAt w`
(`differentiableAt_matrix_inv`, with `ContinuousAt` and `[Q̂₀(−y)]⁻¹`-shaped `M(−y)` corollaries).
The route is `inv_def`
(`A⁻¹ = A.det⁻¹ʳ • A.adjugate`): the adjugate entries are dets of `updateRow`s (holomorphic by the
Leibniz permutation sum, `Matrix.det_apply`) and `Ring.inverse (det) = (det)⁻¹` is holomorphic where
`det ≠ 0`.  Everything is axiom-clean (`propext, Classical.choice, Quot.sound`).

**What this delivers, and what remains for the concrete `Q̂₀`.**  This is the reusable analytic crux
of the eq (20) `A(−iy)` terms.  Wiring it to the physical `Q0_mat_c` still needs:
(i) an **analytic representative** of `q0_entry_c` at `s = 0` — as written it carries `1/s²`, `1/s³`
factors whose singularity at `s = 0` is *removable* (numerators vanish to matching order) but
literally undefined, and the contour crosses `y = 0`; (ii) matching the **det non-vanishing
orientation** of `mixtureDet_pole_free_N` (`det (Q0_mat_c_phys (I·z)) ≠ 0` for `Im z < 0`, i.e.
`Re > 0`) to the contour variable `−y` in the closed UHP; (iii) the **arc bound** for the `A(−iy)`
terms, where the additive-diameter cancellation must still beat the `W/det` growth.  Those are the
concrete-`Q̂₀` assembly; the holomorphy engine here is the part that is genuinely general.
-/

open Matrix

namespace FMSA.MatrixHolo

/-- **Holomorphy of the determinant.**  If every entry `z ↦ (M z) a b` is `DifferentiableAt w`,
so is `z ↦ (M z).det`.  (Leibniz sum over permutations of entry products — `Matrix.det_apply`.) -/
theorem differentiableAt_matrix_det {N : ℕ} {M : ℂ → Matrix (Fin N) (Fin N) ℂ} {w : ℂ}
    (hM : ∀ a b, DifferentiableAt ℂ (fun z => M z a b) w) :
    DifferentiableAt ℂ (fun z => (M z).det) w := by
  have heq : (fun z => (M z).det)
      = ∑ sigma : Equiv.Perm (Fin N), fun z => Equiv.Perm.sign sigma • ∏ i, M z (sigma i) i := by
    funext z; simp only [Finset.sum_apply, Matrix.det_apply]
  rw [heq]
  refine DifferentiableAt.sum (fun sigma _ => ?_)
  refine DifferentiableAt.const_smul ?_ _
  have hp : (fun z => ∏ i, M z (sigma i) i) = ∏ i : Fin N, (fun z => M z (sigma i) i) := by
    funext z; rw [Finset.prod_apply]
  rw [hp]
  exact DifferentiableAt.finsetProd (fun i _ => hM (sigma i) i)

/-- An `updateRow` of a holomorphic matrix by a **constant** row stays holomorphic entrywise. -/
theorem differentiableAt_updateRow_entry {N : ℕ} {M : ℂ → Matrix (Fin N) (Fin N) ℂ} {w : ℂ}
    (hM : ∀ a b, DifferentiableAt ℂ (fun z => M z a b) w) (r : Fin N) (v : Fin N → ℂ)
    (a b : Fin N) :
    DifferentiableAt ℂ (fun z => (M z).updateRow r v a b) w := by
  by_cases haj : a = r
  · simpa only [Matrix.updateRow_apply, haj, if_true] using (differentiableAt_const (v b))
  · simpa only [Matrix.updateRow_apply, haj, if_false] using hM a b

/-- **Holomorphy of the adjugate**, entrywise: `adjugate A i j = det (A.updateRow j (e i))`. -/
theorem differentiableAt_matrix_adjugate {N : ℕ} {M : ℂ → Matrix (Fin N) (Fin N) ℂ} {w : ℂ}
    (hM : ∀ a b, DifferentiableAt ℂ (fun z => M z a b) w) (i j : Fin N) :
    DifferentiableAt ℂ (fun z => (M z).adjugate i j) w := by
  have heq : (fun z => (M z).adjugate i j)
      = fun z => ((M z).updateRow j (Pi.single i 1)).det := by
    funext z; rw [adjugate_apply]
  rw [heq]
  exact differentiableAt_matrix_det (fun a b => differentiableAt_updateRow_entry hM j _ a b)

/-- **Holomorphy of the matrix inverse.**  If every entry of `M` is `DifferentiableAt w` and
`det (M w) ≠ 0`, then every entry `z ↦ (M z)⁻¹ i j` is `DifferentiableAt w`.  (`inv_def`:
`A⁻¹ = A.det⁻¹ʳ • A.adjugate`; over `ℂ`, `Ring.inverse = ·⁻¹`.) -/
theorem differentiableAt_matrix_inv {N : ℕ} {M : ℂ → Matrix (Fin N) (Fin N) ℂ} {w : ℂ}
    (hM : ∀ a b, DifferentiableAt ℂ (fun z => M z a b) w) (hdet : (M w).det ≠ 0) (i j : Fin N) :
    DifferentiableAt ℂ (fun z => (M z)⁻¹ i j) w := by
  have heq : (fun z => (M z)⁻¹ i j)
      = fun z => ((M z).det)⁻¹ * (M z).adjugate i j := by
    funext z
    rw [inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [heq]
  exact ((differentiableAt_matrix_det hM).inv hdet).mul (differentiableAt_matrix_adjugate hM i j)

/-- **Holomorphy of `[M(−y)]⁻¹`** — the `[Q̂₀(−y)]⁻¹` shape of the eq (20) integrand.  If every
entry of `M` is `DifferentiableAt (−w)` and `det (M (−w)) ≠ 0`, then `y ↦ (M (−y))⁻¹ i j` is
`DifferentiableAt w` (chain rule with `y ↦ −y`). -/
theorem differentiableAt_matrix_inv_comp_neg {N : ℕ} {M : ℂ → Matrix (Fin N) (Fin N) ℂ} {w : ℂ}
    (hM : ∀ a b, DifferentiableAt ℂ (fun z => M z a b) (-w)) (hdet : (M (-w)).det ≠ 0)
    (i j : Fin N) :
    DifferentiableAt ℂ (fun y => (M (-y))⁻¹ i j) w := by
  have hM' : ∀ a b, DifferentiableAt ℂ (fun y => M (-y) a b) w :=
    fun a b => (hM a b).comp w differentiableAt_id.neg
  exact differentiableAt_matrix_inv hM' (by simpa using hdet) i j

/-- **Continuity of the matrix inverse** at a point where `det ≠ 0` — for the engine's `hc`. -/
theorem continuousAt_matrix_inv {N : ℕ} {M : ℂ → Matrix (Fin N) (Fin N) ℂ} {w : ℂ}
    (hM : ∀ a b, DifferentiableAt ℂ (fun z => M z a b) w) (hdet : (M w).det ≠ 0) (i j : Fin N) :
    ContinuousAt (fun z => (M z)⁻¹ i j) w :=
  (differentiableAt_matrix_inv hM hdet i j).continuousAt

end FMSA.MatrixHolo
