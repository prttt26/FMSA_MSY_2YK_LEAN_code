import Mathlib

set_option linter.style.header false

/-! A two-dimensional exact obstruction to replacing entrywise
coefficient signs in the abstract one-tail positive system by
positive-semidefinite matrix coefficients. -/
noncomputable section
namespace FMSA.Convergence.T1LoewnerSignObstruction

open Matrix

private def K : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1

private def κ : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then 1 else (1 / 2 : ℝ))

/-- The second coefficient forced by `p=X+p²`, `h=I+κph`,
`X=τhKhᵀ`, after the first coefficient `p₁=K`. -/
private def P₂ : Matrix (Fin 2) (Fin 2) ℝ :=
  K * K + κ * (K * K) + (K * K) * κ

/-- The seed strength is rank-one positive semidefinite: its
quadratic form is the square of the coordinate sum. -/
theorem K_quadratic_nonnegative (x : Fin 2 → ℝ) :
    0 ≤ dotProduct x (K.mulVec x) := by
  simp only [K, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  nlinarith [sq_nonneg (x 0 + x 1)]

/-- Both diagonal entries of `κ` are strictly between zero and two. -/
theorem κ_diagonal_admissible (i : Fin 2) :
    0 < κ i i ∧ κ i i < 2 := by
  fin_cases i <;> norm_num [κ, Matrix.diagonal_apply]

private def witness : Fin 2 → ℝ := ![4, -5]

/-- The forced second coefficient has a negative quadratic form,
despite the PSD seed strength and positive diagonal `κ`. -/
theorem second_coefficient_not_psd :
    dotProduct witness (P₂.mulVec witness) = -4 := by
  norm_num [P₂, K, κ, witness, Matrix.mulVec, Matrix.mul_apply,
    Matrix.diagonal_apply, dotProduct, Fin.sum_univ_two]

theorem second_coefficient_not_quadratic_nonnegative :
    ¬ ∀ x : Fin 2 → ℝ, 0 ≤ dotProduct x (P₂.mulVec x) := by
  intro h
  have hx := h witness
  rw [second_coefficient_not_psd] at hx
  norm_num at hx

end FMSA.Convergence.T1LoewnerSignObstruction

/-- info: 'FMSA.Convergence.T1LoewnerSignObstruction.K_quadratic_nonnegative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.T1LoewnerSignObstruction.K_quadratic_nonnegative
/-- info: 'FMSA.Convergence.T1LoewnerSignObstruction.κ_diagonal_admissible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.T1LoewnerSignObstruction.κ_diagonal_admissible
/-- info: 'FMSA.Convergence.T1LoewnerSignObstruction.second_coefficient_not_psd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.T1LoewnerSignObstruction.second_coefficient_not_psd
/-- info: 'FMSA.Convergence.T1LoewnerSignObstruction.second_coefficient_not_quadratic_nonnegative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.T1LoewnerSignObstruction.second_coefficient_not_quadratic_nonnegative
