/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import LeanCode.Analysis.ZeroCountHomotopy

/-!
# Matrix determinant pole-freeness on the lower half-plane (`OZFIX.17`, matrix)

The scalar Baxter track retires `baxter_no_open_lhp_pole_core` (`MA.14`) by an `η`-homotopy on
`H = 1 − Q̂`, feeding the general argument-principle/Hurwitz axiom
`zeroFree_lowerHalfPlane_of_homotopy` (`Analysis/ZeroCountHomotopy.lean`). That axiom is stated for an
**arbitrary** continuous family of entire functions `H : ℝ → ℂ → ℂ`, so the matrix pole-freeness
`det Q̂ ≠ 0` on the open lower half-plane is the **same** axiom instantiated at `H t z = (M t z).det`
— **no new axiom** is needed for the matrix case.

`matDet_zeroFree_lowerHalfPlane_of_homotopy` packages this, converting entrywise regularity of the
matrix homotopy into `det` regularity (`differentiable_matrix_det`, `continuousOn_matrix_det` — the
Leibniz expansion is a finite sum of products of entries, so no matrix normed-space instance is
needed) and specialising the homotopy axiom.  Discharging its geometric hypotheses (`hbound`,
`hreal` = no real-axis `det`-zero = `pyhs_mixture_no_spinodal`, `hbase` = dilute limit `det → 1`) for
the physical mixture matrix `Q0_mat_c_phys` then yields LHP pole-freeness of the mixture Baxter
factor — the analytic input to the matrix OZ★ decay.
-/

open Matrix Set
namespace FMSA.MixtureOzStar
noncomputable section

/-- Entry-wise differentiability ⇒ `det` differentiable (the Leibniz expansion is a finite sum of
products of entries; no matrix normed-space instance needed). -/
theorem differentiable_matrix_det {N : ℕ} {f : ℂ → Matrix (Fin N) (Fin N) ℂ}
    (hf : ∀ a b, Differentiable ℂ (fun z => (f z) a b)) :
    Differentiable ℂ (fun z => (f z).det) := by
  have heq : (fun z => (f z).det)
      = fun z => ∑ σ : Equiv.Perm (Fin N),
          (↑↑(Equiv.Perm.sign σ) : ℂ) * ∏ i, (f z) (σ i) i := by
    funext z; rw [Matrix.det_apply']
  rw [heq]
  refine Differentiable.fun_sum fun σ _ => ?_
  exact (differentiable_const _).mul (Differentiable.fun_finsetProd fun i _ => hf (σ i) i)

/-- Entry-wise `ContinuousOn` ⇒ `det` `ContinuousOn`. -/
theorem continuousOn_matrix_det {N : ℕ} {M : ℝ → ℂ → Matrix (Fin N) (Fin N) ℂ} {S : Set (ℝ × ℂ)}
    (hM : ∀ a b, ContinuousOn (fun p : ℝ × ℂ => (M p.1 p.2) a b) S) :
    ContinuousOn (fun p : ℝ × ℂ => (M p.1 p.2).det) S := by
  have heq : (fun p : ℝ × ℂ => (M p.1 p.2).det)
      = fun p => ∑ σ : Equiv.Perm (Fin N),
          (↑↑(Equiv.Perm.sign σ) : ℂ) * ∏ i, (M p.1 p.2) (σ i) i := by
    funext p; rw [Matrix.det_apply']
  rw [heq]
  refine continuousOn_finsetSum _ fun σ _ => ?_
  exact continuousOn_const.mul (continuousOn_finsetProd _ fun i _ => hM (σ i) i)

/-- **Matrix determinant pole-freeness on the open lower half-plane, via homotopy.**  For a
`η`-homotopy `M : ℝ → ℂ → Matrix (Fin N) (Fin N) ℂ` of entrywise-entire matrices with no
`det`-zero on the real axis, a bounded LHP zero set, and a zero-free base point, `det (M b)` is
zero-free in the open lower half-plane.  Pure specialisation of the general
`zeroFree_lowerHalfPlane_of_homotopy` at `H t z = (M t z).det` — **no new axiom** — the matrix analog
of the scalar `baxter_no_open_lhp_pole_core` retirement (`BaxterLowerHalfPlane.lean`).  Hypotheses are
stated entrywise so no matrix normed-space instance is required. -/
theorem matDet_zeroFree_lowerHalfPlane_of_homotopy {N : ℕ}
    {M : ℝ → ℂ → Matrix (Fin N) (Fin N) ℂ} {a b R : ℝ} (hab : a ≤ b) (hR : 0 < R)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × ℂ => (M p.1 p.2) i j)
      (Set.Icc a b ×ˢ (Set.univ : Set ℂ)))
    (hholo : ∀ t ∈ Set.Icc a b, ∀ i j, Differentiable ℂ (fun z => (M t z) i j))
    (hbound : ∀ t ∈ Set.Icc a b, ∀ z : ℂ, z.im ≤ 0 → (M t z).det = 0 → ‖z‖ < R)
    (hreal : ∀ t ∈ Set.Icc a b, ∀ z : ℂ, z.im = 0 → (M t z).det ≠ 0)
    (hbase : ∀ z : ℂ, z.im < 0 → (M a z).det ≠ 0) :
    ∀ z : ℂ, z.im < 0 → (M b z).det ≠ 0 :=
  FMSA.Analysis.zeroFree_lowerHalfPlane_of_homotopy (H := fun t z => (M t z).det) hab hR
    (continuousOn_matrix_det hcont)
    (fun t ht => differentiable_matrix_det (fun i j => hholo t ht i j))
    hbound hreal hbase

end
end FMSA.MixtureOzStar
