import MSAConvergence.ComplexWronskianJets
import Mathlib.LinearAlgebra.SymplecticGroup

/-! First-order symplectic block completion and genuine entrywise matrix
Frechet derivatives. No curve inside a constraint set is assumed. -/
noncomputable section
open Filter Topology
open scoped BigOperators

namespace FMSA.Convergence.SymplecticTangent

section MatrixDerivatives
variable {P I : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable [Fintype I] [DecidableEq I]

/-- Entrywise actual differentiability preserves the existing amplitude norm. -/
def EntryDiff (F : P → Matrix I I ℂ) (p : P) : Prop :=
  ∀ i j, DifferentiableAt ℝ (fun a => F a i j) p

/-- The genuine entrywise Frechet derivative in an actual amplitude direction. -/
def matrixDerivative (F : P → Matrix I I ℂ) (p v : P) : Matrix I I ℂ :=
  Matrix.of (fun i j => fderiv ℝ (fun a => F a i j) p v)

/-- Fixed matrices have zero actual derivative. -/
theorem matrix_derivative_const (C : Matrix I I ℂ) (p v : P) :
    matrixDerivative (fun _ : P => C) p v = 0 := by
  ext i j
  simp [matrixDerivative]

/-- Addition commutes with the actual matrix derivative. -/
theorem matrix_derivative_add (F G : P → Matrix I I ℂ) (p v : P)
    (hF : EntryDiff F p) (hG : EntryDiff G p) :
    matrixDerivative (fun a => F a+G a) p v = matrixDerivative F p v+matrixDerivative G p v := by
  ext i j
  exact congrArg (fun L : P →L[ℝ] ℂ => L v) ((hF i j).hasFDerivAt.fun_add (hG i j).hasFDerivAt).fderiv

/-- Negation commutes with the actual matrix derivative. -/
theorem matrix_derivative_neg (F : P → Matrix I I ℂ) (p v : P) :
    matrixDerivative (fun a => -F a) p v = -matrixDerivative F p v := by
  ext i j
  simp only [matrixDerivative, Matrix.of_apply, Matrix.neg_apply, fderiv_fun_neg, neg_apply]

/-- Subtraction commutes with the actual matrix derivative. -/
theorem matrix_derivative_sub (F G : P → Matrix I I ℂ) (p v : P)
    (hF : EntryDiff F p) (hG : EntryDiff G p) :
    matrixDerivative (fun a => F a-G a) p v = matrixDerivative F p v-matrixDerivative G p v := by
  ext i j
  exact congrArg (fun L : P →L[ℝ] ℂ => L v) ((hF i j).hasFDerivAt.fun_sub (hG i j).hasFDerivAt).fderiv

/-- Transposition is fixed entry selection and commutes with actual variation. -/
theorem matrix_derivative_transpose (F : P → Matrix I I ℂ) (p v : P) :
    matrixDerivative (fun a => (F a).transpose) p v = (matrixDerivative F p v).transpose := rfl

/-- Fixed complex scalar multiplication commutes with the actual derivative. -/
theorem matrix_derivative_smul (c : ℂ) (F : P → Matrix I I ℂ) (p v : P) (hF : EntryDiff F p) :
    matrixDerivative (fun a => c • F a) p v = c • matrixDerivative F p v := by
  ext i j
  have h := congrArg (fun L : P →L[ℝ] ℂ => L v) ((hF i j).hasFDerivAt.const_mul c).fderiv
  simpa only [matrixDerivative, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, smul_apply] using h

/-- Genuine matrix product rule, proved by finite scalar products without
introducing a different matrix or amplitude norm instance. -/
theorem matrix_derivative_mul (F G : P → Matrix I I ℂ) (p v : P)
    (hF : EntryDiff F p) (hG : EntryDiff G p) :
    matrixDerivative (fun a => F a*G a) p v = matrixDerivative F p v*G p+F p*matrixDerivative G p v := by
  ext i j
  change fderiv ℝ (fun a => ∑ k, F a i k*G a k j) p v = _
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    (hF i k).hasFDerivAt.mul (hG k j).hasFDerivAt)
  change HasFDerivAt (fun a : P => ∑ k, F a i k*G a k j) _ p at hd
  rw [hd.fderiv]
  simp only [sum_apply, add_apply, smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.mul_apply, matrixDerivative, Matrix.of_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- Entrywise differentiability of a fixed matrix family. -/
theorem entry_diff_const (C : Matrix I I ℂ) (p : P) : EntryDiff (fun _ : P => C) p :=
  fun _ _ => differentiableAt_const _

/-- Entrywise differentiability is closed under addition. -/
theorem entry_diff_add (F G : P → Matrix I I ℂ) (p : P) (hF : EntryDiff F p) (hG : EntryDiff G p) :
    EntryDiff (fun a => F a+G a) p := fun i j => (hF i j).add (hG i j)

/-- Entrywise differentiability is closed under subtraction. -/
theorem entry_diff_sub (F G : P → Matrix I I ℂ) (p : P) (hF : EntryDiff F p) (hG : EntryDiff G p) :
    EntryDiff (fun a => F a-G a) p := fun i j => (hF i j).sub (hG i j)

/-- Entrywise differentiability is closed under negation. -/
theorem entry_diff_neg (F : P → Matrix I I ℂ) (p : P) (hF : EntryDiff F p) :
    EntryDiff (fun a => -F a) p := fun i j => (hF i j).neg

/-- Fixed transposition preserves entrywise differentiability. -/
theorem entry_diff_transpose (F : P → Matrix I I ℂ) (p : P) (hF : EntryDiff F p) :
    EntryDiff (fun a => (F a).transpose) p := fun i j => hF j i

/-- Fixed complex scaling preserves entrywise differentiability. -/
theorem entry_diff_smul (c : ℂ) (F : P → Matrix I I ℂ) (p : P) (hF : EntryDiff F p) :
    EntryDiff (fun a => c • F a) p := fun i j => (hF i j).const_mul c

/-- Matrix products preserve entrywise actual differentiability. -/
theorem entry_diff_mul (F G : P → Matrix I I ℂ) (p : P) (hF : EntryDiff F p) (hG : EntryDiff G p) :
    EntryDiff (fun a => F a*G a) p := by
  intro i j
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hF i k).hasFDerivAt.mul (hG k j).hasFDerivAt)
  change HasFDerivAt (fun a : P => ∑ k, F a i k*G a k j) _ p at hd
  exact hd.differentiableAt

/-- Multiplication by a fixed left matrix commutes with actual variation. -/
theorem matrix_derivative_const_mul (C : Matrix I I ℂ) (F : P → Matrix I I ℂ) (p v : P) (hF : EntryDiff F p) :
    matrixDerivative (fun a => C*F a) p v = C*matrixDerivative F p v := by
  simpa only [matrix_derivative_const, Matrix.zero_mul, zero_add] using
    matrix_derivative_mul (fun _ => C) F p v (entry_diff_const C p) hF

/-- Multiplication by a fixed right matrix commutes with actual variation. -/
theorem matrix_derivative_mul_const (F : P → Matrix I I ℂ) (C : Matrix I I ℂ) (p v : P) (hF : EntryDiff F p) :
    matrixDerivative (fun a => F a*C) p v = matrixDerivative F p v*C := by
  simpa only [matrix_derivative_const, Matrix.mul_zero, add_zero] using
    matrix_derivative_mul F (fun _ => C) p v hF (entry_diff_const C p)

/-- Actual product/subtraction derivative used in all four block equations. -/
theorem matrix_derivative_mul_sub_mul (F G H K : P → Matrix I I ℂ) (p v : P)
    (hF : EntryDiff F p) (hG : EntryDiff G p) (hH : EntryDiff H p) (hK : EntryDiff K p) :
    matrixDerivative (fun a => F a*G a-H a*K a) p v =
      (matrixDerivative F p v*G p+F p*matrixDerivative G p v)-
        (matrixDerivative H p v*K p+H p*matrixDerivative K p v) := by
  rw [matrix_derivative_sub _ _ p v (entry_diff_mul F G p hF hG) (entry_diff_mul H K p hH hK),
    matrix_derivative_mul F G p v hF hG, matrix_derivative_mul H K p v hH hK]

end MatrixDerivatives

/-- Linearized transpose symplecticity follows from linearized direct
symplecticity at an actual symplectic base point; no constrained curve. -/
theorem transpose_symplectic_tangent {I : Type*} [Fintype I] [DecidableEq I]
    (T dT O : Matrix I I ℂ) (hO : O*O = -1)
    (hbase : T.transpose*O*T = O)
    (hd : dT*O*T.transpose+T*O*dT.transpose = 0) :
    dT.transpose*O*T+T.transpose*O*dT = 0 := by
  have h := congrArg (fun X : Matrix I I ℂ => (T.transpose*O)*X*(O*T)) hd
  have he : (T.transpose*O)*(dT*O*T.transpose+T*O*dT.transpose)*(O*T) =
      (T.transpose*O*dT)*O*(T.transpose*O*T)+(T.transpose*O*T)*O*(dT.transpose*O*T) := by noncomm_ring
  rw [he, hbase, Matrix.mul_zero, Matrix.zero_mul] at h
  rw [Matrix.mul_assoc (T.transpose*O*dT) O O, hO, Matrix.mul_neg, Matrix.mul_one,
    Matrix.neg_mul, Matrix.one_mul] at h
  simpa only [← neg_add, neg_eq_zero, add_comm] using h

/-- The base block equations give the full transpose symplectic identity,
not merely the one source block used in the frozen value theorem. -/
theorem blocks_transpose_symplectic {N : ℕ} (A B M D : Matrix (Fin N) (Fin N) ℂ)
    (h11 : A*M.transpose-M*A.transpose = 0)
    (h12 : A*D.transpose-M*B.transpose = 1)
    (h22 : B*D.transpose-D*B.transpose = 0) :
    let T := Matrix.fromBlocks A M B D
    T.transpose*Matrix.J (Fin N) ℂ*T = Matrix.J (Fin N) ℂ := by
  let T := Matrix.fromBlocks A M B D
  have h21 : B*M.transpose-D*A.transpose = -1 := by
    have h := congrArg Matrix.transpose h12
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h
    simpa only [neg_sub] using congrArg Neg.neg h
  have ht : T ∈ Matrix.symplecticGroup (Fin N) ℂ := by
    rw [SymplecticGroup.mem_iff]
    dsimp only [T]
    simp only [Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.mul_one, Matrix.add_mul,
      Matrix.neg_mul, Matrix.one_mul, add_zero, zero_add]
    have z11 : M*A.transpose-A*M.transpose = 0 := by simpa only [neg_sub, neg_zero] using congrArg Neg.neg h11
    have z12 : M*B.transpose-A*D.transpose = -1 := by simpa only [neg_sub] using congrArg Neg.neg h12
    have z21 : D*A.transpose-B*M.transpose = 1 := by simpa only [neg_sub, neg_neg] using congrArg Neg.neg h21
    have z22 : D*B.transpose-B*D.transpose = 0 := by simpa only [neg_sub, neg_zero] using congrArg Neg.neg h22
    simp only [← sub_eq_add_neg, z11, z12, z21, z22]
  exact SymplecticGroup.mem_iff'.mp ht

/-- First-order source reciprocity follows from the actual base block
constraints and their vanishing first variations. The constraints need
not hold on any neighbourhood or along any root curve. -/
theorem blocks_source_reciprocity_tangent {N : ℕ}
    (A B M D dA dB dM dD : Matrix (Fin N) (Fin N) ℂ)
    (h11 : A*M.transpose-M*A.transpose = 0)
    (h12 : A*D.transpose-M*B.transpose = 1)
    (h22 : B*D.transpose-D*B.transpose = 0)
    (hd11 : dA*M.transpose+A*dM.transpose-dM*A.transpose-M*dA.transpose = 0)
    (hd12 : dA*D.transpose+A*dD.transpose-dM*B.transpose-M*dB.transpose = 0)
    (hd22 : dB*D.transpose+B*dD.transpose-dD*B.transpose-D*dB.transpose = 0) :
    dA.transpose*B+A.transpose*dB-dB.transpose*A-B.transpose*dA = 0 := by
  let T := Matrix.fromBlocks A M B D
  let dT := Matrix.fromBlocks dA dM dB dD
  have hbase : T.transpose*Matrix.J (Fin N) ℂ*T = Matrix.J (Fin N) ℂ :=
    blocks_transpose_symplectic A B M D h11 h12 h22
  have hd21 : dB*M.transpose+B*dM.transpose-dD*A.transpose-D*dA.transpose = 0 := by
    have h := congrArg Matrix.transpose hd12
    simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_zero] at h
    linear_combination (norm := noncomm_ring) -h
  have hdt : dT*Matrix.J (Fin N) ℂ*T.transpose+T*Matrix.J (Fin N) ℂ*dT.transpose = 0 := by
    dsimp only [T, dT]
    simp only [Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
      Matrix.one_mul, add_zero, zero_add, Matrix.fromBlocks_add]
    have z11 : dM*A.transpose-dA*M.transpose+(M*dA.transpose-A*dM.transpose) = 0 := by linear_combination (norm := noncomm_ring) -hd11
    have z12 : dM*B.transpose-dA*D.transpose+(M*dB.transpose-A*dD.transpose) = 0 := by linear_combination (norm := noncomm_ring) -hd12
    have z21 : dD*A.transpose-dB*M.transpose+(D*dA.transpose-B*dM.transpose) = 0 := by linear_combination (norm := noncomm_ring) -hd21
    have z22 : dD*B.transpose-dB*D.transpose+(D*dB.transpose-B*dD.transpose) = 0 := by linear_combination (norm := noncomm_ring) -hd22
    simp only [← sub_eq_add_neg]
    rw [z11, z12, z21, z22, Matrix.fromBlocks_zero]
  have h := transpose_symplectic_tangent T dT (Matrix.J (Fin N) ℂ) (Matrix.J_squared _ _) hbase hdt
  have he := congrArg (fun X : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ => X.toBlocks₁₁) h
  simp only [T, dT, Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
    Matrix.one_mul, add_zero, zero_add, Matrix.fromBlocks_add, Matrix.toBlocks_fromBlocks₁₁] at he
  change _ = (0 : Matrix (Fin N) (Fin N) ℂ) at he
  linear_combination (norm := noncomm_ring) -he

/-- Genuine Frechet-family version of first-order block completion.
Only base constraints and actual vanishing constraint derivatives are
inputs; no parameter curve satisfying those constraints is postulated. -/
theorem blocks_family_reciprocity_derivative {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {N : ℕ} (A B M D : P → Matrix (Fin N) (Fin N) ℂ) (p v : P)
    (hA : EntryDiff A p) (hB : EntryDiff B p) (hM : EntryDiff M p) (hD : EntryDiff D p)
    (h11 : A p*(M p).transpose-M p*(A p).transpose = 0)
    (h12 : A p*(D p).transpose-M p*(B p).transpose = 1)
    (h22 : B p*(D p).transpose-D p*(B p).transpose = 0)
    (hd11 : matrixDerivative (fun a => A a*(M a).transpose-M a*(A a).transpose) p v = 0)
    (hd12 : matrixDerivative (fun a => A a*(D a).transpose-M a*(B a).transpose) p v = 0)
    (hd22 : matrixDerivative (fun a => B a*(D a).transpose-D a*(B a).transpose) p v = 0) :
    matrixDerivative (fun a => (A a).transpose*B a-(B a).transpose*A a) p v = 0 := by
  have hAT := entry_diff_transpose A p hA
  have hBT := entry_diff_transpose B p hB
  have hMT := entry_diff_transpose M p hM
  have hDT := entry_diff_transpose D p hD
  rw [matrix_derivative_mul_sub_mul A (fun a => (M a).transpose) M (fun a => (A a).transpose) p v hA hMT hM hAT,
    matrix_derivative_transpose, matrix_derivative_transpose] at hd11
  rw [matrix_derivative_mul_sub_mul A (fun a => (D a).transpose) M (fun a => (B a).transpose) p v hA hDT hM hBT,
    matrix_derivative_transpose, matrix_derivative_transpose] at hd12
  rw [matrix_derivative_mul_sub_mul B (fun a => (D a).transpose) D (fun a => (B a).transpose) p v hB hDT hD hBT,
    matrix_derivative_transpose, matrix_derivative_transpose] at hd22
  simp only [sub_add_eq_sub_sub] at hd11 hd12 hd22
  have h := blocks_source_reciprocity_tangent (A p) (B p) (M p) (D p)
    (matrixDerivative A p v) (matrixDerivative B p v) (matrixDerivative M p v) (matrixDerivative D p v)
    h11 h12 h22 hd11 hd12 hd22
  rw [matrix_derivative_mul_sub_mul (fun a => (A a).transpose) B (fun a => (B a).transpose) A p v hAT hB hBT hA,
    matrix_derivative_transpose, matrix_derivative_transpose]
  simpa only [sub_add_eq_sub_sub] using h

/-- A unit right source renewal and its actual first-order renewal
transfer base and tangent source reciprocity to the solution. -/
theorem source_renewal_reciprocity_tangent {N : ℕ}
    (A J Y dA dJ dY : Matrix (Fin N) (Fin N) ℂ) (hu : IsUnit A)
    (hYA : Y*A = J) (hdYA : dY*A+Y*dA = dJ)
    (hR : A.transpose*J-J.transpose*A = 0)
    (hdR : dA.transpose*J+A.transpose*dJ-dJ.transpose*A-J.transpose*dA = 0) :
    Y.transpose = Y ∧ dY.transpose = dY := by
  have huT : IsUnit A.transpose := (Matrix.isUnit_iff_isUnit_det _).mpr
    (by simpa only [Matrix.det_transpose] using (Matrix.isUnit_iff_isUnit_det _).mp hu)
  have cancel (Z : Matrix (Fin N) (Fin N) ℂ) (h : A.transpose*Z*A = 0) : Z = 0 := by
    apply hu.mul_left_injective
    apply huT.mul_right_injective
    simpa only [Matrix.mul_assoc, Matrix.mul_zero, Matrix.zero_mul] using h
  have hY : Y.transpose = Y := by
    have hh : A.transpose*(Y-Y.transpose)*A = 0 := by
      calc
        _ = A.transpose*J-J.transpose*A := by rw [← hYA]; simp only [Matrix.transpose_mul]; noncomm_ring
        _ = 0 := hR
    exact (sub_eq_zero.mp (cancel _ hh)).symm
  refine ⟨hY, ?_⟩
  have h := hdR
  rw [← hYA, ← hdYA] at h
  simp only [Matrix.transpose_mul, Matrix.transpose_add, hY] at h
  have hh : A.transpose*(dY-dY.transpose)*A = 0 := by
    convert h using 1 <;> noncomm_ring
  exact (sub_eq_zero.mp (cancel _ hh)).symm

end FMSA.Convergence.SymplecticTangent

/-- info: 'FMSA.Convergence.SymplecticTangent.matrix_derivative_const' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.matrix_derivative_const

/-- info: 'FMSA.Convergence.SymplecticTangent.matrix_derivative_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.matrix_derivative_add

/-- info: 'FMSA.Convergence.SymplecticTangent.matrix_derivative_neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.matrix_derivative_neg

/-- info: 'FMSA.Convergence.SymplecticTangent.matrix_derivative_sub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.matrix_derivative_sub

/-- info: 'FMSA.Convergence.SymplecticTangent.matrix_derivative_transpose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.matrix_derivative_transpose

/-- info: 'FMSA.Convergence.SymplecticTangent.matrix_derivative_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.matrix_derivative_smul

/-- info: 'FMSA.Convergence.SymplecticTangent.matrix_derivative_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.matrix_derivative_mul

/-- info: 'FMSA.Convergence.SymplecticTangent.entry_diff_const' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.entry_diff_const

/-- info: 'FMSA.Convergence.SymplecticTangent.entry_diff_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.entry_diff_add

/-- info: 'FMSA.Convergence.SymplecticTangent.entry_diff_sub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.entry_diff_sub

/-- info: 'FMSA.Convergence.SymplecticTangent.entry_diff_neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.entry_diff_neg

/-- info: 'FMSA.Convergence.SymplecticTangent.entry_diff_transpose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.entry_diff_transpose

/-- info: 'FMSA.Convergence.SymplecticTangent.entry_diff_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.entry_diff_smul

/-- info: 'FMSA.Convergence.SymplecticTangent.entry_diff_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.entry_diff_mul

/-- info: 'FMSA.Convergence.SymplecticTangent.matrix_derivative_const_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.matrix_derivative_const_mul

/-- info: 'FMSA.Convergence.SymplecticTangent.matrix_derivative_mul_const' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.matrix_derivative_mul_const

/-- info: 'FMSA.Convergence.SymplecticTangent.matrix_derivative_mul_sub_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.matrix_derivative_mul_sub_mul

/-- info: 'FMSA.Convergence.SymplecticTangent.transpose_symplectic_tangent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.transpose_symplectic_tangent

/-- info: 'FMSA.Convergence.SymplecticTangent.blocks_transpose_symplectic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.blocks_transpose_symplectic

/-- info: 'FMSA.Convergence.SymplecticTangent.blocks_source_reciprocity_tangent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.blocks_source_reciprocity_tangent

/-- info: 'FMSA.Convergence.SymplecticTangent.blocks_family_reciprocity_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.blocks_family_reciprocity_derivative

/-- info: 'FMSA.Convergence.SymplecticTangent.source_renewal_reciprocity_tangent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.SymplecticTangent.source_renewal_reciprocity_tangent
