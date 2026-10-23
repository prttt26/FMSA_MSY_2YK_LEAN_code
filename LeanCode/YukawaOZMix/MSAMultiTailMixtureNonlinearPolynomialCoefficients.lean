import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearMatrixPolynomial

/-! Low coefficients of polynomial matrix products. -/
noncomputable section
open Polynomial
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {n : Type*} [Fintype n] [DecidableEq n]

def polyMatrixCoeff (d : ℕ) (F : Matrix n n (Polynomial ℝ)) : Matrix n n ℝ :=
  F.map (fun p => p.coeff d)

theorem polyMatrixCoeff_add (d : ℕ) (F G : Matrix n n (Polynomial ℝ)) :
    polyMatrixCoeff d (F+G) = polyMatrixCoeff d F+polyMatrixCoeff d G := by
  ext i j
  simp [polyMatrixCoeff]

theorem polyMatrixCoeff_transpose (d : ℕ) (F : Matrix n n (Polynomial ℝ)) :
    polyMatrixCoeff d F.transpose = (polyMatrixCoeff d F).transpose := rfl

theorem polyMatrixCoeff_zero (d : ℕ) :
    polyMatrixCoeff d (0 : Matrix n n (Polynomial ℝ)) = 0 := by
  ext i j
  simp [polyMatrixCoeff]

theorem polyMatrixCoeff_term (d a : ℕ) (F : Matrix n n ℝ) :
    polyMatrixCoeff d (polyMatrixTerm a F) = if a = d then F else 0 :=
  by simpa only [polyMatrixCoeff, eq_comm] using polyMatrixTerm_coeff a d F

theorem polyMatrixCoeff_mul_zero (F G : Matrix n n (Polynomial ℝ)) :
    polyMatrixCoeff 0 (F*G) = polyMatrixCoeff 0 F*polyMatrixCoeff 0 G := by
  ext i j
  simp [polyMatrixCoeff, Matrix.mul_apply, Polynomial.finsetSum_coeff]

theorem polyMatrixCoeff_mul_one (F G : Matrix n n (Polynomial ℝ)) :
    polyMatrixCoeff 1 (F*G) = polyMatrixCoeff 0 F*polyMatrixCoeff 1 G+
      polyMatrixCoeff 1 F*polyMatrixCoeff 0 G := by
  ext i j
  simp [polyMatrixCoeff, Matrix.mul_apply, Polynomial.finsetSum_coeff,
    Polynomial.mul_coeff_one, Finset.sum_add_distrib]

theorem polyMatrixCoeff_smul_zero (p : Polynomial ℝ) (F : Matrix n n (Polynomial ℝ)) :
    polyMatrixCoeff 0 (p • F) = p.coeff 0 • polyMatrixCoeff 0 F := by
  ext i j
  simp [polyMatrixCoeff, Matrix.smul_apply, smul_eq_mul]

theorem polyMatrixCoeff_smul_one (p : Polynomial ℝ) (F : Matrix n n (Polynomial ℝ)) :
    polyMatrixCoeff 1 (p • F) = p.coeff 0 • polyMatrixCoeff 1 F+
      p.coeff 1 • polyMatrixCoeff 0 F := by
  ext i j
  simp [polyMatrixCoeff, Matrix.smul_apply, smul_eq_mul, Polynomial.mul_coeff_one]

end FMSA.ExactMSA.MultiTailMixture
