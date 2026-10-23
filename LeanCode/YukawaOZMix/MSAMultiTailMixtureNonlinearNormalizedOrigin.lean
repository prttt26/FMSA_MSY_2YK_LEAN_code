import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearIntrinsicDefectPolynomial
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearPolynomialCoefficients

/-! Origin constraints on the fully reduced, unscaled normalized defect. -/
noncomputable section
open Polynomial
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def intrinsicNormalizedDefect (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :=
  intrinsicClearedDefect (polyMatrixTerm 0 (originDensityMatrix ρ))
    (polyMatrixTerm 0 (completionOmega (n := Fin N) (R := ℝ)))
    (intrinsicNormalizedReducedNumerator z ρ σ Dt G) (X*intrinsicRatePairPolynomial z)

theorem intrinsicClearedDefect_coefficients
    {n : Type*} [Fintype n] [DecidableEq n]
    (P O : Matrix n n ℝ) (M : Matrix n n (Polynomial ℝ)) (q : Polynomial ℝ) :
    polyMatrixCoeff 0 (intrinsicClearedDefect (polyMatrixTerm 0 P) (polyMatrixTerm 0 O) M (X*q)) =
      polyMatrixCoeff 0 M*P*O*(polyMatrixCoeff 0 M).transpose ∧
    polyMatrixCoeff 1 (intrinsicClearedDefect (polyMatrixTerm 0 P) (polyMatrixTerm 0 O) M (X*q)) =
      q.coeff 0 • (polyMatrixCoeff 0 M*O+O*(polyMatrixCoeff 0 M).transpose) +
      polyMatrixCoeff 0 M*P*O*(polyMatrixCoeff 1 M).transpose +
      polyMatrixCoeff 1 M*P*O*(polyMatrixCoeff 0 M).transpose := by
  constructor
  all_goals
    simp only [intrinsicClearedDefect, polyMatrixCoeff_add, polyMatrixCoeff_smul_zero,
      polyMatrixCoeff_smul_one, polyMatrixCoeff_mul_zero, polyMatrixCoeff_mul_one,
      polyMatrixCoeff_transpose, polyMatrixCoeff_term]
    simp [Polynomial.mul_coeff_one, smul_add, Matrix.mul_add, Matrix.add_mul, add_assoc]

theorem intrinsicNormalizedDefect_origin_zero
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) (hz : ∀ u, z u ≠ 0) :
    polyMatrixCoeff 0 (intrinsicNormalizedDefect z ρ σ Dt G) = 0 ∧
    completionU (1 : Matrix (Fin N) (Fin N) ℝ)*
      polyMatrixCoeff 1 (intrinsicNormalizedDefect z ρ σ Dt G) = 0 := by
  obtain ⟨A,hA⟩ := originIntrinsicResidue_lagrangian z ρ σ Dt G hz
  have hS := originIntrinsicConstant_projection_zero z ρ σ Dt G
  have hd := intrinsic_lagrangian_origin_double_pole_zero ρ A
  have hp := intrinsic_lagrangian_origin_projection_zero ρ A _ hS
  dsimp only at hd hp
  have hc := intrinsicNormalizedReducedNumerator_origin_coefficients z ρ σ Dt G
  change polyMatrixCoeff 0 (intrinsicNormalizedReducedNumerator z ρ σ Dt G) = _ ∧
    polyMatrixCoeff 1 (intrinsicNormalizedReducedNumerator z ρ σ Dt G) = _ at hc
  have he := intrinsicClearedDefect_coefficients (originDensityMatrix ρ)
    (completionOmega (n := Fin N) (R := ℝ))
    (intrinsicNormalizedReducedNumerator z ρ σ Dt G) (intrinsicRatePairPolynomial z)
  change polyMatrixCoeff 0 (intrinsicNormalizedDefect z ρ σ Dt G) = _ ∧
    polyMatrixCoeff 1 (intrinsicNormalizedDefect z ρ σ Dt G) = _ at he
  rw [hc.1,hc.2,hA] at he
  constructor
  · rw [he.1]
    simpa only [Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_smul,
      smul_smul, hd, smul_zero] using hd
  · rw [he.2]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_smul,
      Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, smul_add, smul_smul,
      hd, smul_zero, add_zero, zero_add]
    have hh := congrArg (fun F => (intrinsicRatePairPolynomial z).coeff 0^2 • F) hp
    simp only [Matrix.mul_add, smul_add, Matrix.mul_smul, smul_zero] at hh ⊢
    convert hh using 1 <;> module

end FMSA.ExactMSA.MultiTailMixture
