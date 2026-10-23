import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearNormalizedOrigin
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearIntrinsicWronskian
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearPolynomialDegree

/-! Exact transport of cleared defects by the HS polynomial normalization. -/
noncomputable section
open Polynomial MSAMixture FMSA.MatrixQ0
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def intrinsicNormalizationMatrix (ρ σ : Fin N → ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) (Polynomial ℝ) :=
  (X^3 : Polynomial ℝ) • 1+
    intrinsicDPolynomial ρ σ*polyMatrixTerm 0 (originDensityMatrix ρ)

theorem intrinsicPolynomialDensity_symmetry (ρ : Fin N → ℝ) :
    (polyMatrixTerm 0 (originDensityMatrix ρ)).transpose =
      polyMatrixTerm 0 (originDensityMatrix ρ) := by
  rw [polyMatrixTerm_transpose, originDensityMatrix_transpose]

theorem intrinsicPolynomialDensity_commutes_omega (ρ : Fin N → ℝ) :
    polyMatrixTerm 0 (originDensityMatrix ρ)*
        polyMatrixTerm 0 (completionOmega (n := Fin N) (R := ℝ)) =
      polyMatrixTerm 0 (completionOmega (n := Fin N) (R := ℝ))*
        polyMatrixTerm 0 (originDensityMatrix ρ) := by
  rw [polyMatrixTerm_mul, polyMatrixTerm_mul, originDensityMatrix_commutes_omega]

theorem intrinsicPolynomialOmega_skew :
    (polyMatrixTerm 0 (completionOmega (n := Fin N) (R := ℝ))).transpose =
      -polyMatrixTerm 0 (completionOmega (n := Fin N) (R := ℝ)) := by
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [polyMatrixTerm, completionOmega, Matrix.fromBlocks, Matrix.transpose_apply, Matrix.one_apply, eq_comm]

theorem intrinsicNormalizationMatrix_degree (ρ σ : Fin N → ℝ) :
    PolyMatrixDegreeLE (intrinsicNormalizationMatrix ρ σ) 3 ∧
    polyMatrixCoeff 3 (intrinsicNormalizationMatrix ρ σ) = 1 := by
  have hd : PolyMatrixDegreeLE (intrinsicDPolynomial ρ σ) 2 := by
    apply polyMatrix_degree_add
    · apply polyMatrix_degree_add
      · exact fun i j => (polyMatrix_degree_term 0 _ i j).trans (by omega)
      · exact fun i j => (polyMatrix_degree_term 1 _ i j).trans (by omega)
    · exact polyMatrix_degree_term 2 _
  have hdp := polyMatrix_degree_mul hd (polyMatrix_degree_term 0 (originDensityMatrix ρ))
  have hlead : (X^3 : Polynomial ℝ) • (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) (Polynomial ℝ)) =
      polyMatrixTerm 3 (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) := by
    apply Matrix.ext
    intro i j
    simp [polyMatrixTerm, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  constructor
  · unfold intrinsicNormalizationMatrix
    rw [hlead]
    exact polyMatrix_degree_add (polyMatrix_degree_term 3 _) (fun i j => (hdp i j).trans (by omega))
  · unfold intrinsicNormalizationMatrix
    rw [hlead, polyMatrixCoeff_add, polyMatrixCoeff_term,
      polyMatrixCoeff_zero_of_degree_lt hdp (by omega)]
    simp

theorem intrinsicNormalizationMatrix_det_ne_zero (ρ σ : Fin N → ℝ) :
    Matrix.det (intrinsicNormalizationMatrix ρ σ) ≠ 0 :=
  polynomial_matrix_det_ne_zero_of_top_one _ 3
    (intrinsicNormalizationMatrix_degree ρ σ).1 (intrinsicNormalizationMatrix_degree ρ σ).2

theorem intrinsicNormalizedDefect_skew
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    (intrinsicNormalizedDefect z ρ σ Dt G).transpose =
      -intrinsicNormalizedDefect z ρ σ Dt G :=
  intrinsicClearedDefect_skew _ _ _ _ (intrinsicPolynomialDensity_symmetry ρ)
    (intrinsicPolynomialDensity_commutes_omega ρ) intrinsicPolynomialOmega_skew

theorem intrinsicNormalizedDefect_transport
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (hv : vacMix ρ σ ≠ 0) :
    (X^10 : Polynomial ℝ) • intrinsicNormalizedDefect z ρ σ Dt G =
      intrinsicNormalizationMatrix ρ σ *
        (intrinsicRatePairPolynomial z • intrinsicWronskianMatrix z ρ σ Dt G) *
      (intrinsicNormalizationMatrix ρ σ).transpose := by
  have hs := intrinsicClearedDefect_affine
    (polyMatrixTerm 0 (originDensityMatrix ρ))
    (polyMatrixTerm 0 (completionOmega (n := Fin N) (R := ℝ)))
    (intrinsicDPolynomial ρ σ) (intrinsicHNumerator z ρ σ Dt G)
    (X^3) (intrinsicRatePairPolynomial z)
    (intrinsicPolynomialDensity_symmetry ρ) (intrinsicPolynomialDensity_commutes_omega ρ)
  have hd : intrinsicClearedDefect (polyMatrixTerm 0 (originDensityMatrix ρ))
      (polyMatrixTerm 0 (completionOmega (n := Fin N) (R := ℝ)))
      (intrinsicDPolynomial ρ σ) (X^3) = 0 := originIntrinsicDPolynomial_defect_zero ρ σ
  rw [hd, smul_zero, zero_add, intrinsicHNumerator_cleared_defect] at hs
  have hn : (X^3*intrinsicRatePairPolynomial z) • intrinsicDPolynomial ρ σ+
      (X^3 : Polynomial ℝ) • intrinsicHNumerator z ρ σ Dt G+
      intrinsicDPolynomial ρ σ*polyMatrixTerm 0 (originDensityMatrix ρ)*
        intrinsicHNumerator z ρ σ Dt G = intrinsicNormalizedNumerator z ρ σ Dt G := by
    simp only [intrinsicNormalizedNumerator, smul_smul]
  rw [hn, intrinsicNormalizedNumerator_origin_factor z ρ σ Dt G hz hv] at hs
  have he : intrinsicClearedDefect (polyMatrixTerm 0 (originDensityMatrix ρ))
      (polyMatrixTerm 0 (completionOmega (n := Fin N) (R := ℝ)))
      ((X^5 : Polynomial ℝ) • intrinsicNormalizedReducedNumerator z ρ σ Dt G)
      ((X^3 : Polynomial ℝ)^2*intrinsicRatePairPolynomial z) =
      (X^10 : Polynomial ℝ) • intrinsicNormalizedDefect z ρ σ Dt G := by
    simp only [intrinsicClearedDefect, intrinsicNormalizedDefect, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.transpose_smul, smul_add, smul_smul]
    module
  rw [he] at hs
  simpa only [intrinsicNormalizationMatrix, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.transpose_mul, intrinsicPolynomialDensity_symmetry] using hs

end FMSA.ExactMSA.MultiTailMixture
