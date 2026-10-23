import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearIntrinsicDefectPolynomial
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearDistinctReduction

/-! Identification of the unscaled cleared defect with actual Wronskians. -/
noncomputable section
open Polynomial
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

theorem intrinsicClearedDefect_blocks (P A B C D : Matrix n n R) (c : R) :
    intrinsicClearedDefect (Matrix.fromBlocks P 0 0 P)
      (completionOmega (n := n) (R := R)) (Matrix.fromBlocks A B C D) c =
    Matrix.fromBlocks
      (c • (-B+B.transpose)+A*P*B.transpose-B*P*A.transpose)
      (c • (A+D.transpose)+A*P*D.transpose-B*P*C.transpose)
      (c • (-D-A.transpose)+C*P*B.transpose-D*P*A.transpose)
      (c • (C-C.transpose)+C*P*D.transpose-D*P*C.transpose) := by
  simp only [intrinsicClearedDefect, completionOmega, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, zero_add, add_zero,
    Matrix.fromBlocks_add, Matrix.fromBlocks_smul]
  congr 1 <;> simp only [sub_eq_add_neg, neg_add_rev, Matrix.mul_neg, Matrix.neg_mul] <;> module

theorem matrix_mul_diagonal_entry (A B : Matrix n n R) (ρ : n → R) (i j : n) :
    (A*Matrix.diagonal ρ*B) i j = ∑ m, A i m*ρ m*B m j := by
  simp only [Matrix.mul_apply (M := A*Matrix.diagonal ρ), Matrix.mul_diagonal]

variable {N : ℕ} {ι : Type*} [Fintype ι]

def intrinsicWronskianMatrix (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :=
  Matrix.fromBlocks
    (fun i j => -(nonlinearDistinctVPolynomial z ρ σ Dt G i j).comp (-X))
    (nonlinearDistinctUPolynomial z ρ σ Dt G)
    (fun i j => -nonlinearDistinctUPolynomial z ρ σ Dt G j i)
    (nonlinearDistinctVPolynomial z ρ σ Dt G)

theorem polyMatrixTerm_density (ρ : Fin N → ℝ) :
    polyMatrixTerm 0 (originDensityMatrix ρ) =
      Matrix.fromBlocks (Matrix.diagonal (fun i => Polynomial.C (ρ i))) 0 0
        (Matrix.diagonal (fun i => Polynomial.C (ρ i))) := by
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [polyMatrixTerm, originDensityMatrix, Matrix.fromBlocks, Matrix.diagonal]
  all_goals split_ifs <;> simp_all

theorem polyMatrixTerm_omega :
    polyMatrixTerm 0 (completionOmega (n := Fin N) (R := ℝ)) =
      completionOmega (n := Fin N) (R := Polynomial ℝ) := by
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [polyMatrixTerm, completionOmega, Matrix.fromBlocks, Matrix.one_apply]

theorem intrinsicHNumerator_cleared_defect
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    intrinsicClearedDefect (polyMatrixTerm 0 (originDensityMatrix ρ))
      (polyMatrixTerm 0 (completionOmega (n := Fin N) (R := ℝ)))
      (intrinsicHNumerator z ρ σ Dt G) (X^3*intrinsicRatePairPolynomial z) =
    intrinsicRatePairPolynomial z • intrinsicWronskianMatrix z ρ σ Dt G := by
  have hs (f g : Fin N → Polynomial ℝ) :
      (∑ m, nonlinearDistinctRatePolynomial z*(nonlinearDistinctRatePolynomial z).comp (-X)*
        f m*Polynomial.C (ρ m)*g m) =
      nonlinearDistinctRatePolynomial z*(nonlinearDistinctRatePolynomial z).comp (-X)*
        ∑ m, Polynomial.C (ρ m)*f m*g m := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hc (f g : Fin N → Polynomial ℝ) :
      (∑ m, Polynomial.C (ρ m)*f m*g m) =
        ∑ m, Polynomial.C (ρ m)*g m*f m := by
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [polyMatrixTerm_density, polyMatrixTerm_omega]
  unfold intrinsicHNumerator
  rw [intrinsicClearedDefect_blocks]
  apply Matrix.ext
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [intrinsicWronskianMatrix, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply,
        smul_eq_mul, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.transpose_apply,
        matrix_mul_diagonal_entry]
      simp only [nonlinearDistinctVPolynomial, Polynomial.add_comp, Polynomial.sub_comp,
        Polynomial.mul_comp, Polynomial.sum_comp, Polynomial.C_comp,
        Polynomial.comp_assoc, Polynomial.neg_comp, Polynomial.X_comp, Polynomial.neg_comp,
        neg_neg, Polynomial.comp_X, nonlinearDistinctDenominator,
        Polynomial.pow_comp, intrinsicRatePairPolynomial]
      ring_nf
      simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
      ring_nf
      rw [hs,hs]
      all_goals ring_nf
      all_goals congr 1 <;> try ring
      all_goals apply Finset.sum_congr rfl
      all_goals intro m _; ring
    | inr j =>
      simp only [intrinsicWronskianMatrix, Matrix.fromBlocks_apply₁₂, Matrix.smul_apply,
        smul_eq_mul, Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply,
        matrix_mul_diagonal_entry, nonlinearDistinctUPolynomial,
        nonlinearDistinctDenominator, Polynomial.mul_comp, Polynomial.pow_comp,
        Polynomial.X_comp, intrinsicRatePairPolynomial]
      ring_nf
      simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
      ring_nf
      rw [hs,hs]
      all_goals ring_nf
      all_goals congr 1 <;> try ring
      all_goals apply Finset.sum_congr rfl
      all_goals intro m _; ring
  | inr i =>
    cases j with
    | inl j =>
      simp only [intrinsicWronskianMatrix, Matrix.fromBlocks_apply₂₁, Matrix.smul_apply,
        smul_eq_mul, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.transpose_apply,
        matrix_mul_diagonal_entry, nonlinearDistinctUPolynomial,
        nonlinearDistinctDenominator, Polynomial.mul_comp, Polynomial.pow_comp,
        Polynomial.X_comp, intrinsicRatePairPolynomial]
      ring_nf
      simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
      ring_nf
      rw [hs,hs]
      all_goals ring_nf
      rw [hc (fun m => nonlinearDistinctJNumerator z ρ σ Dt G i m)
        (fun m => (nonlinearDistinctJNumerator z ρ σ Dt G j m).comp (-X)),
        hc (fun m => (nonlinearDistinctLNumerator z ρ σ Dt G i m).comp (-X))
          (fun m => nonlinearDistinctLNumerator z ρ σ Dt G j m)]
    | inr j =>
      simp only [intrinsicWronskianMatrix, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply,
        smul_eq_mul, Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply,
        matrix_mul_diagonal_entry, nonlinearDistinctVPolynomial,
        nonlinearDistinctDenominator, Polynomial.mul_comp, Polynomial.pow_comp,
        Polynomial.X_comp, intrinsicRatePairPolynomial]
      ring_nf
      simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
      ring_nf
      rw [hs,hs]
      all_goals ring_nf
      all_goals congr 1 <;> try ring
      all_goals apply Finset.sum_congr rfl
      all_goals intro m _; ring

end FMSA.ExactMSA.MultiTailMixture
