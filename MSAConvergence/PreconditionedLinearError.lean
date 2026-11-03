import MSAConvergence.NewtonBoxExistence

/-! Uniform linear-solution error and scalar pairing bounds from actual
row defects in the original finite Pi-space norm. No supplied inverse. -/
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace FMSA.Convergence.PreconditionedLinearError
open FMSA.Convergence.NewtonBoxExistence
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem solution_error_bound (C J : Matrix I I ℝ) (a b : I → ℝ)
    (q M : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hrow : ∀ i, ∑ j, |(1-C*J) i j| ≤ q)
    (hJa : J.mulVec a = b) (hM : ‖matrixCLM C b‖ ≤ M) :
    ‖a-matrixCLM C b‖ ≤ q*M/(1-q) := by
  have he : a-matrixCLM C b = matrixCLM (1-C*J) a := by
    rw [matrixCLM_defect]
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply,matrixCLM_apply,hJa]
  have hd : ‖a-matrixCLM C b‖ ≤ q*‖a‖ := by
    rw [he]
    exact ((matrixCLM (1-C*J)).le_opNorm a).trans
      (mul_le_mul_of_nonneg_right (matrixCLM_norm_le (1-C*J) q hq0 hrow) (norm_nonneg a))
  have ha : ‖a‖ ≤ ‖a-matrixCLM C b‖+M := by
    calc
      ‖a‖ = ‖(a-matrixCLM C b)+matrixCLM C b‖ := by congr 1; abel
      _ ≤ ‖a-matrixCLM C b‖+‖matrixCLM C b‖ := norm_add_le _ _
      _ ≤ ‖a-matrixCLM C b‖+M := add_le_add (le_refl _) hM
  have hden : 0 < 1-q := sub_pos.mpr hq1
  have han : ‖a‖ ≤ M/(1-q) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  calc
    ‖a-matrixCLM C b‖ ≤ q*‖a‖ := hd
    _ ≤ q*(M/(1-q)) := mul_le_mul_of_nonneg_left han hq0
    _ = q*M/(1-q) := by ring

/-- The true Pi-space norm controls any scalar finite pairing. -/
theorem pairing_norm_le (g v : I → ℝ) :
    |∑ i,g i*v i| ≤ (∑ i,|g i|)*‖v‖ := by
  change ‖∑ i,g i*v i‖ ≤ (∑ i,|g i|)*‖v‖
  calc
    _ ≤ ∑ i,‖g i*v i‖ := norm_sum_le _ _
    _ ≤ ∑ i,|g i| *‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (abs_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

end FMSA.Convergence.PreconditionedLinearError

/-- info: 'FMSA.Convergence.PreconditionedLinearError.solution_error_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PreconditionedLinearError.solution_error_bound

/-- info: 'FMSA.Convergence.PreconditionedLinearError.pairing_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PreconditionedLinearError.pairing_norm_le
