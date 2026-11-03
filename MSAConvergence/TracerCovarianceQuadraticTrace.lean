import MSAConvergence.TracerCovarianceEntryTrace

/-! Finite-dimensional trace control of positive covariance quadratic forms. -/
open Matrix FMSA.Convergence.TracerCovarianceEntryTrace
open scoped ComplexOrder BigOperators
noncomputable section
namespace FMSA.Convergence.TracerCovarianceQuadraticTrace
variable {N : ℕ}
/-- A positive covariance quadratic is bounded by trace times the square
of the vector one-norm. -/
theorem posdef_quadratic_norm_le_trace_l1_sq (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.PosDef) (x : Fin N → ℂ) :
    ‖∑ a : Fin N, ∑ b : Fin N, star (x a)*A a b*x b‖ ≤
      A.trace.re*(∑ a : Fin N, ‖x a‖)^2 := by
  have ht : 0 ≤ A.trace.re := (RCLike.nonneg_iff.mp hA.posSemidef.trace_nonneg).1
  have hentry (a b : Fin N) :
      ‖star (x a)*A a b*x b‖ ≤ A.trace.re*(‖x a‖*‖x b‖) := by
    simp only [norm_mul,norm_star]
    have hab := posdef_entry_norm_le_trace_re A hA a b
    have ha := norm_nonneg (x a)
    have hb := norm_nonneg (x b)
    nlinarith [mul_nonneg ha hb, mul_nonneg (sub_nonneg.mpr hab) (mul_nonneg ha hb)]
  calc
    ‖∑ a : Fin N, ∑ b : Fin N, star (x a)*A a b*x b‖ ≤
      ∑ a : Fin N, ‖∑ b : Fin N, star (x a)*A a b*x b‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin N, ∑ b : Fin N, ‖star (x a)*A a b*x b‖ := by
      apply Finset.sum_le_sum
      intro a _
      exact norm_sum_le _ _
    _ ≤ ∑ a : Fin N, ∑ b : Fin N, A.trace.re*(‖x a‖*‖x b‖) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact hentry a b
    _ = A.trace.re*(∑ a : Fin N, ‖x a‖)^2 := by
      calc
        _ = ∑ a : Fin N, (A.trace.re*‖x a‖)*(∑ b : Fin N, ‖x b‖) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          simp only [mul_assoc]
        _ = (∑ a : Fin N, A.trace.re*‖x a‖)*(∑ b : Fin N, ‖x b‖) := by
          rw [Finset.sum_mul]
        _ = A.trace.re*(∑ a : Fin N, ‖x a‖)^2 := by
          rw [← Finset.mul_sum]
          ring

/-- Finite Euclidean Cauchy–Schwarz with explicit species count. -/
theorem finite_l1_sq_le_card_l2_sq (x : Fin N → ℂ) :
    (∑ a : Fin N, ‖x a‖)^2 ≤ (N:ℝ)*(∑ a : Fin N, ‖x a‖^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin N => (1:ℝ)) (fun a => ‖x a‖)
  simpa using h

/-- A positive covariance quadratic is controlled by its trace and the
ordinary squared Euclidean norm of the forcing vector. -/
theorem posdef_quadratic_norm_le_trace_l2_sq
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.PosDef) (x : Fin N → ℂ) :
    ‖∑ a : Fin N, ∑ b : Fin N, star (x a)*A a b*x b‖ ≤
      (N:ℝ)*A.trace.re*(∑ a : Fin N, ‖x a‖^2) := by
  have ht : 0 ≤ A.trace.re :=
    (RCLike.nonneg_iff.mp hA.posSemidef.trace_nonneg).1
  calc
    _ ≤ A.trace.re*(∑ a : Fin N, ‖x a‖)^2 :=
      posdef_quadratic_norm_le_trace_l1_sq A hA x
    _ ≤ A.trace.re*((N:ℝ)*(∑ a : Fin N, ‖x a‖^2)) :=
      mul_le_mul_of_nonneg_left (finite_l1_sq_le_card_l2_sq x) ht
    _ = _ := by ring

/-- Transfer a scalar spectral-square domination into a positive covariance
quadratic domination by the corresponding weighted trace. -/
theorem posdef_quadratic_norm_le_weighted_trace
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.PosDef)
    (x : Fin N → ℂ) (C W : ℝ)
    (hvector : (∑ a : Fin N, ‖x a‖ ^ 2) ≤ C * W) :
    ‖∑ a : Fin N, ∑ b : Fin N, star (x a)*A a b*x b‖ ≤
      ((N:ℝ)*C)*(W*A.trace.re) := by
  have ht : 0 ≤ A.trace.re :=
    (RCLike.nonneg_iff.mp hA.posSemidef.trace_nonneg).1
  calc
    _ ≤ (N:ℝ)*A.trace.re*(∑ a : Fin N, ‖x a‖^2) :=
      posdef_quadratic_norm_le_trace_l2_sq A hA x
    _ ≤ ((N:ℝ)*A.trace.re)*(C*W) :=
      mul_le_mul_of_nonneg_left hvector (mul_nonneg (Nat.cast_nonneg _) ht)
    _ = _ := by ring

end FMSA.Convergence.TracerCovarianceQuadraticTrace
/-- info: 'FMSA.Convergence.TracerCovarianceQuadraticTrace.posdef_quadratic_norm_le_trace_l1_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerCovarianceQuadraticTrace.posdef_quadratic_norm_le_trace_l1_sq
/-- info: 'FMSA.Convergence.TracerCovarianceQuadraticTrace.finite_l1_sq_le_card_l2_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerCovarianceQuadraticTrace.finite_l1_sq_le_card_l2_sq
/-- info: 'FMSA.Convergence.TracerCovarianceQuadraticTrace.posdef_quadratic_norm_le_trace_l2_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerCovarianceQuadraticTrace.posdef_quadratic_norm_le_trace_l2_sq
/-- info: 'FMSA.Convergence.TracerCovarianceQuadraticTrace.posdef_quadratic_norm_le_weighted_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerCovarianceQuadraticTrace.posdef_quadratic_norm_le_weighted_trace
