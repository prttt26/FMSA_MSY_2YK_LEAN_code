import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearPolynomialCoefficients
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Polynomial

/-! Degree bounds and cancellation for polynomial matrices with scalar leading term. -/
noncomputable section
open Polynomial
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {n : Type*} [Fintype n] [DecidableEq n]

def PolyMatrixDegreeLE (F : Matrix n n (Polynomial ℝ)) (d : ℕ) : Prop :=
  ∀ i j, (F i j).natDegree ≤ d

theorem polyMatrix_degree_add {F G : Matrix n n (Polynomial ℝ)} {a : ℕ}
    (hF : PolyMatrixDegreeLE F a) (hG : PolyMatrixDegreeLE G a) :
    PolyMatrixDegreeLE (F+G) a := by
  intro i j
  exact (Polynomial.natDegree_add_le _ _).trans (max_le (hF i j) (hG i j))

theorem polyMatrix_degree_mul {F G : Matrix n n (Polynomial ℝ)} {a b : ℕ}
    (hF : PolyMatrixDegreeLE F a) (hG : PolyMatrixDegreeLE G b) :
    PolyMatrixDegreeLE (F*G) (a+b) := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m _
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hF i m) (hG m j))

theorem polyMatrix_degree_smul {F : Matrix n n (Polynomial ℝ)} {p : Polynomial ℝ}
    {a b : ℕ} (hp : p.natDegree ≤ a) (hF : PolyMatrixDegreeLE F b) :
    PolyMatrixDegreeLE (p • F) (a+b) := by
  intro i j
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hp (hF i j))

theorem polyMatrix_degree_term (d : ℕ) (A : Matrix n n ℝ) :
    PolyMatrixDegreeLE (polyMatrixTerm d A) d := polyMatrixTerm_degree_le d A

theorem polyMatrix_degree_transpose {F : Matrix n n (Polynomial ℝ)} {a : ℕ}
    (hF : PolyMatrixDegreeLE F a) : PolyMatrixDegreeLE F.transpose a := by
  intro i j
  exact hF j i

theorem polyMatrixCoeff_zero_of_degree_lt {F : Matrix n n (Polynomial ℝ)} {a b : ℕ}
    (hF : PolyMatrixDegreeLE F a) (hab : a < b) : polyMatrixCoeff b F = 0 := by
  ext i j
  exact Polynomial.coeff_eq_zero_of_natDegree_lt ((hF i j).trans_lt hab)

theorem polynomial_matrix_det_top_coeff (F : Matrix n n (Polynomial ℝ)) (d : ℕ)
    (hF : PolyMatrixDegreeLE F d) :
    (Matrix.det F).coeff (Fintype.card n*d) = Matrix.det (polyMatrixCoeff d F) := by
  classical
  rw [Matrix.det_apply, Polynomial.finsetSum_coeff, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro g _
  convert! Polynomial.coeff_smul (R := ℝ) (Equiv.Perm.sign g) _ _
  convert! (Polynomial.coeff_prod_of_natDegree_le (s := Finset.univ)
    (fun i => F (g i) i) d (fun i _ => hF (g i) i)).symm using 1 <;>
    simp [polyMatrixCoeff]

theorem polynomial_matrix_det_ne_zero_of_top_one (F : Matrix n n (Polynomial ℝ)) (d : ℕ)
    (hF : PolyMatrixDegreeLE F d) (hc : polyMatrixCoeff d F = 1) : Matrix.det F ≠ 0 := by
  intro hz
  have hh := polynomial_matrix_det_top_coeff F d hF
  rw [hz, hc] at hh
  simpa using hh

theorem polynomial_matrix_congruence_cancel (B E : Matrix n n (Polynomial ℝ))
    (hB : Matrix.det B ≠ 0) (h : B*E*B.transpose = 0) : E = 0 := by
  have hh := congrArg (fun F => Matrix.adjugate B*F*Matrix.adjugate B.transpose) h
  have hbt : Matrix.det B.transpose = Matrix.det B := Matrix.det_transpose B
  have he : (Matrix.det B*Matrix.det B) • E = 0 := by
    simp only [← Matrix.mul_assoc] at hh
    rw [Matrix.adjugate_mul] at hh
    simp only [Matrix.smul_mul, Matrix.one_mul] at hh
    rw [Matrix.mul_assoc E B.transpose, Matrix.mul_adjugate, hbt] at hh
    simpa only [Matrix.mul_smul, Matrix.mul_one, smul_smul,
      Matrix.mul_zero, Matrix.zero_mul] using hh
  apply Matrix.ext
  intro i j
  have hij := congrFun (congrFun he i) j
  exact (mul_eq_zero.mp hij).resolve_left (mul_ne_zero hB hB)

end FMSA.ExactMSA.MultiTailMixture
