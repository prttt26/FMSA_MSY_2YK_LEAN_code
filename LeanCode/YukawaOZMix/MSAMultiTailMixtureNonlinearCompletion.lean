import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic

/-! Uniform completion lemmas for a hard-sphere-normalized symplectic defect.

These lemmas isolate the origin residue and polynomial interpolation argument.
They do not assert that BH roots satisfy the required normalization/degree
hypotheses. That dictionary bridge is a separate obligation.
-/
noncomputable section
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture

section Origin
variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

def completionU (P : Matrix n n R) : Matrix n (n ⊕ n) R :=
  Matrix.fromCols 1 P

def completionV (P : Matrix n n R) : Matrix (n ⊕ n) n R :=
  Matrix.fromRows (-P) 1

def completionOmega : Matrix (n ⊕ n) (n ⊕ n) R :=
  Matrix.fromBlocks 0 1 (-1) 0

theorem completionU_mul_completionV (P : Matrix n n R) :
    completionU P * completionV P = 0 := by
  simp [completionU, completionV, Matrix.fromCols_mul_fromRows]

theorem completionU_mul_omega (P : Matrix n n R) (hP : P.transpose = P) :
    completionU P * completionOmega (n := n) (R := R) = (completionV P).transpose := by
  dsimp only [completionU, completionOmega]
  rw [Matrix.fromCols_mul_fromBlocks]
  simp [completionV, Matrix.transpose_fromRows, hP]

theorem completionOmega_mul_completionU_transpose
    (P : Matrix n n R) (hP : P.transpose = P) :
    completionOmega (n := n) (R := R) * (completionU P).transpose = -completionV P := by
  dsimp only [completionU, completionOmega]
  rw [Matrix.transpose_fromCols, Matrix.fromBlocks_mul_fromRows]
  simp [completionV, hP]

theorem completion_origin_double_pole_zero (P X : Matrix n n R)
    (hP : P.transpose = P) :
    (completionV P * X * completionU P) * completionOmega (n := n) (R := R) *
      (completionV P * X * completionU P).transpose = 0 := by
  calc
    _ = completionV P * X *
        ((completionU P * completionOmega (n := n) (R := R)) * (completionU P).transpose) *
        X.transpose * (completionV P).transpose := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 0 := by
      rw [completionU_mul_omega P hP, ← Matrix.transpose_mul,
        completionU_mul_completionV, Matrix.transpose_zero]
      simp

theorem completion_origin_residue_factorization
    (P X Z : Matrix n n R) (T : Matrix (n ⊕ n) (n ⊕ n) R)
    (hP : P.transpose = P) (hT : T * completionV P = completionV P * Z) :
    (completionV P * X * completionU P) * completionOmega (n := n) (R := R) * T.transpose +
      T * completionOmega (n := n) (R := R) * (completionV P * X * completionU P).transpose =
        completionV P * (X * Z.transpose - Z * X.transpose) *
          (completionV P).transpose := by
  have ht : (completionV P).transpose * T.transpose =
      Z.transpose * (completionV P).transpose := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose hT
  calc
    _ = completionV P * X * (completionU P * completionOmega (n := n) (R := R)) * T.transpose +
        T * (completionOmega (n := n) (R := R) * (completionU P).transpose) * X.transpose *
        (completionV P).transpose := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = _ := by
      rw [completionU_mul_omega P hP, completionOmega_mul_completionU_transpose P hP]
      simp only [Matrix.mul_neg, Matrix.neg_mul]
      rw [Matrix.mul_assoc (completionV P * X), ht, hT]
      simp only [sub_eq_add_neg, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem completion_origin_residue_bottom_block
    (P X : Matrix n n R) :
    (completionV P * X * (completionV P).transpose).toBlocks₂₂ = X := by
  simp [completionV, Matrix.transpose_fromRows, Matrix.fromRows_mul]

theorem completion_skew_origin_zero
    (P : Matrix n n R) (F : Matrix (n ⊕ n) (n ⊕ n) R)
    (hU : completionU P * F = 0) (hskew : F.transpose = -F)
    (h22 : F.toBlocks₂₂ = 0) : F = 0 := by
  have h := hU
  rw [← Matrix.fromBlocks_toBlocks F] at h
  simp only [completionU, Matrix.fromCols_mul_fromBlocks, Matrix.one_mul] at h
  rw [← Matrix.fromCols_zero] at h
  obtain ⟨ha, hb⟩ := Matrix.fromCols_inj h
  have h12 : F.toBlocks₁₂ = 0 := by simpa [h22] using hb
  have h21 : F.toBlocks₂₁ = 0 := by
    ext i j
    have ht := congrFun (congrFun hskew (Sum.inl j)) (Sum.inr i)
    change F (Sum.inr i) (Sum.inl j) = -F (Sum.inl j) (Sum.inr i) at ht
    have hz := congrFun (congrFun h12 j) i
    change F (Sum.inl j) (Sum.inr i) = 0 at hz
    change F (Sum.inr i) (Sum.inl j) = 0
    simpa [hz] using ht
  have h11 : F.toBlocks₁₁ = 0 := by simpa [h21] using ha
  rw [← Matrix.fromBlocks_toBlocks F, h11, h12, h21, h22]
  simp

end Origin

section Polynomial
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite-pole defect is identically zero once its origin is Lagrangian,
its lower block has the stronger infinity bound, and all finite pole values
vanish. The pole set is a set of distinct values, not a list of tail labels. -/
theorem completion_polynomial_zero
    (P : Matrix n n ℝ)
    (F : Matrix (n ⊕ n) (n ⊕ n) (Polynomial ℝ))
    (S : Finset ℝ) (hS : (0 : ℝ) ∉ S)
    (heval : ∀ s ∈ S, ∀ i j, (F i j).eval s = 0)
    (hdegree : ∀ i j, (F i j).natDegree ≤ S.card)
    (hbottom : ∀ i j, F (Sum.inr i) (Sum.inr j) = 0 ∨
      (F (Sum.inr i) (Sum.inr j)).natDegree < S.card)
    (hU : completionU P * F.map (Polynomial.eval 0) = 0)
    (hskew : (F.map (Polynomial.eval 0)).transpose =
      -(F.map (Polynomial.eval 0))) : F = 0 := by
  classical
  have hb (i j : n) : F (Sum.inr i) (Sum.inr j) = 0 := by
    rcases hbottom i j with h | h
    · exact h
    · exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
        _ S (fun s hs => heval s hs _ _) h
  have h22 : (F.map (Polynomial.eval 0)).toBlocks₂₂ = 0 := by
    ext i j
    simp [Matrix.toBlocks₂₂, Matrix.map, hb]
  have hzero := completion_skew_origin_zero P (F.map (Polynomial.eval 0)) hU hskew h22
  apply Matrix.ext
  intro i j
  change F i j = 0
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (insert 0 S)
  · intro s hs
    rcases Finset.mem_insert.mp hs with hs | hs
    · subst s
      exact congrFun (congrFun hzero i) j
    · exact heval s hs i j
  · rw [Finset.card_insert_of_notMem hS]
    exact Nat.lt_succ_of_le (hdegree i j)

end Polynomial
end FMSA.ExactMSA.MultiTailMixture
