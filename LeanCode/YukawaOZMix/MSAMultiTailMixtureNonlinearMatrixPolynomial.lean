import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearIntrinsicOrigin
import Mathlib.Tactic.ComputeDegree

/-! Polynomial matrix bookkeeping for the exact affine normalization. -/
noncomputable section
open Polynomial
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {n : Type*} [Fintype n] [DecidableEq n]

def polyMatrixTerm (d : ℕ) (A : Matrix n n ℝ) : Matrix n n (Polynomial ℝ) :=
  fun i j => Polynomial.C (A i j)*X^d

theorem polyMatrixTerm_zero (d : ℕ) :
    polyMatrixTerm d (0 : Matrix n n ℝ) = 0 := by
  apply Matrix.ext
  intro i j
  simp [polyMatrixTerm]

theorem polyMatrixTerm_add (d : ℕ) (A B : Matrix n n ℝ) :
    polyMatrixTerm d (A+B) = polyMatrixTerm d A+polyMatrixTerm d B := by
  apply Matrix.ext
  intro i j
  simp [polyMatrixTerm, map_add, add_mul]

theorem polyMatrixTerm_shift (a b : ℕ) (A : Matrix n n ℝ) :
    (X^a : Polynomial ℝ) • polyMatrixTerm b A = polyMatrixTerm (a+b) A := by
  apply Matrix.ext
  intro i j
  simp only [polyMatrixTerm, Matrix.smul_apply, smul_eq_mul, pow_add]
  ring

theorem polyMatrixTerm_mul (a b : ℕ) (A B : Matrix n n ℝ) :
    polyMatrixTerm a A * polyMatrixTerm b B = polyMatrixTerm (a+b) (A*B) := by
  apply Matrix.ext
  intro i j
  simp only [polyMatrixTerm, Matrix.mul_apply, map_sum, pow_add, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  rw [map_mul]
  ring

theorem polyMatrixTerm_transpose (a : ℕ) (A : Matrix n n ℝ) :
    (polyMatrixTerm a A).transpose = polyMatrixTerm a A.transpose := rfl

theorem polyMatrixTerm_coeff (a d : ℕ) (A : Matrix n n ℝ) :
    (polyMatrixTerm a A).map (fun p => p.coeff d) = if d = a then A else 0 := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.map_apply, polyMatrixTerm, Polynomial.coeff_C_mul_X_pow]
  split_ifs <;> simp_all

theorem polyMatrixTerm_degree_le (a : ℕ) (A : Matrix n n ℝ) (i j : n) :
    (polyMatrixTerm a A i j).natDegree ≤ a := by
  unfold polyMatrixTerm
  compute_degree

def polyOriginD (D1 D2 D3 : Matrix n n ℝ) :=
  polyMatrixTerm 0 D3+polyMatrixTerm 1 D2+polyMatrixTerm 2 D1

def polyOriginH (H3 H2 H1 H0 Hp1 Hp2 Hp3 : Matrix n n ℝ) :=
  polyMatrixTerm 0 H3+polyMatrixTerm 1 H2+polyMatrixTerm 2 H1+
    polyMatrixTerm 3 H0+polyMatrixTerm 4 Hp1+polyMatrixTerm 5 Hp2+polyMatrixTerm 6 Hp3

theorem polynomial_origin_affine_jet_product
    (P D1 D2 D3 H3 H2 H1 H0 Hp1 Hp2 Hp3 : Matrix n n ℝ) :
    (X^3 : Polynomial ℝ) • polyOriginD D1 D2 D3 +
      (X^3 : Polynomial ℝ) • polyOriginH H3 H2 H1 H0 Hp1 Hp2 Hp3 +
      polyOriginD D1 D2 D3 * polyMatrixTerm 0 P * polyOriginH H3 H2 H1 H0 Hp1 Hp2 Hp3 =
    polyMatrixTerm 0 (D3*P*H3) +
    polyMatrixTerm 1 (D2*P*H3+D3*P*H2) +
    polyMatrixTerm 2 (D1*P*H3+D2*P*H2+D3*P*H1) +
    polyMatrixTerm 3 (H3+D3+D1*P*H2+D2*P*H1+D3*P*H0) +
    polyMatrixTerm 4 (H2+D2+D1*P*H1+D2*P*H0+D3*P*Hp1) +
    polyMatrixTerm 5 (H1+D1+D1*P*H0+D2*P*Hp1+D3*P*Hp2) +
    polyMatrixTerm 6 (H0+D1*P*Hp1+D2*P*Hp2+D3*P*Hp3) +
    polyMatrixTerm 7 (Hp1+D1*P*Hp2+D2*P*Hp3) +
    polyMatrixTerm 8 (Hp2+D1*P*Hp3) + polyMatrixTerm 9 Hp3 := by
  simp only [polyOriginD, polyOriginH, smul_add, Matrix.add_mul, Matrix.mul_add,
    polyMatrixTerm_shift, polyMatrixTerm_mul, polyMatrixTerm_add, Nat.reduceAdd]
  abel

def polyMatrixEval (s : ℝ) (F : Matrix n n (Polynomial ℝ)) : Matrix n n ℝ :=
  F.map (Polynomial.evalRingHom s)

theorem polyMatrixEval_add (s : ℝ) (F G : Matrix n n (Polynomial ℝ)) :
    polyMatrixEval s (F+G) = polyMatrixEval s F+polyMatrixEval s G := by
  ext i j
  simp [polyMatrixEval, Matrix.map_apply, Matrix.add_apply]

theorem polyMatrixEval_mul (s : ℝ) (F G : Matrix n n (Polynomial ℝ)) :
    polyMatrixEval s (F*G) = polyMatrixEval s F*polyMatrixEval s G := Matrix.map_mul

theorem polyMatrixEval_transpose (s : ℝ) (F : Matrix n n (Polynomial ℝ)) :
    polyMatrixEval s F.transpose = (polyMatrixEval s F).transpose := rfl

theorem polyMatrixEval_smul (s : ℝ) (p : Polynomial ℝ) (F : Matrix n n (Polynomial ℝ)) :
    polyMatrixEval s (p • F) = p.eval s • polyMatrixEval s F := by
  ext i j
  simp [polyMatrixEval, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]

theorem polyMatrixEval_term (s : ℝ) (a : ℕ) (A : Matrix n n ℝ) :
    polyMatrixEval s (polyMatrixTerm a A) = s^a • A := by
  ext i j
  simp [polyMatrixEval, polyMatrixTerm, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end FMSA.ExactMSA.MultiTailMixture
