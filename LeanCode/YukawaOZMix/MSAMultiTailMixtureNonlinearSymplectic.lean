import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearWronskianFinite
import Mathlib.LinearAlgebra.SymplecticGroup

/-! The Wronskian relations imply source reciprocity by a finite symplectic
block identity. The general construction never divides by species densities,
so zero and signed densities are included. -/
noncomputable section
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

theorem symplectic_blocks_source_reciprocity
    (A B M D : Matrix (Fin N) (Fin N) ℂ)
    (h11 : A*M.transpose-M*A.transpose=0)
    (h12 : A*D.transpose-M*B.transpose=1)
    (h22 : B*D.transpose-D*B.transpose=0) :
    A.transpose*B-B.transpose*A=0 := by
  let T := Matrix.fromBlocks A M B D
  have h21 : B*M.transpose-D*A.transpose = -1 := by
    have h := congrArg Matrix.transpose h12
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_one] at h
    simpa only [neg_sub] using congrArg Neg.neg h
  have ht : T ∈ Matrix.symplecticGroup (Fin N) ℂ := by
    rw [SymplecticGroup.mem_iff]
    dsimp only [T]
    simp only [Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.mul_one,
      Matrix.add_mul, Matrix.neg_mul, Matrix.one_mul, add_zero, zero_add]
    have z11 : M*A.transpose-A*M.transpose=0 := by
      simpa only [neg_sub, neg_zero] using congrArg Neg.neg h11
    have z12 : M*B.transpose-A*D.transpose = -1 := by
      simpa only [neg_sub] using congrArg Neg.neg h12
    have z21 : D*A.transpose-B*M.transpose = 1 := by
      simpa only [neg_sub, neg_neg] using congrArg Neg.neg h21
    have z22 : D*B.transpose-B*D.transpose=0 := by
      simpa only [neg_sub, neg_zero] using congrArg Neg.neg h22
    simp only [← sub_eq_add_neg, z11, z12, z21, z22]
  have h := (SymplecticGroup.mem_iff.mp (SymplecticGroup.transpose_mem ht))
  have he := congrArg (fun X : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ => X.toBlocks₁₁) h
  change (T.transpose*Matrix.J (Fin N) ℂ*T.transpose.transpose).toBlocks₁₁ =
    (Matrix.J (Fin N) ℂ).toBlocks₁₁ at he
  simp only [T, Matrix.transpose_transpose, Matrix.J, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg,
    Matrix.mul_one, Matrix.add_mul, Matrix.neg_mul, Matrix.one_mul, add_zero, zero_add,
    Matrix.toBlocks_fromBlocks₁₁] at he
  simpa only [← sub_eq_add_neg, neg_sub, neg_zero] using congrArg Neg.neg he

theorem nonlinearWronskian_density_free_implies_reciprocity
    (J L Jm Lm : Matrix (Fin N) (Fin N) ℂ) (s : ℂ) (hs : s ≠ 0)
    (hu : nonlinearWronskianU J L Jm Lm (fun _ => 1) s=0)
    (hv : nonlinearWronskianV J L Lm (fun _ => 1) s=0)
    (hvm : nonlinearWronskianV Jm Lm L (fun _ => 1) (-s)=0) :
    J-J.transpose+s⁻¹ • (J.transpose*L-L.transpose*J)=0 := by
  let A := 1-s⁻¹ • L
  let D := 1+s⁻¹ • Lm
  let B := s⁻¹ • J
  let M := -(s⁻¹ • Jm)
  have h11 : A*M.transpose-M*A.transpose =
      s⁻¹ • nonlinearWronskianV Jm Lm L (fun _ => 1) (-s) := by
    simp only [A, M, nonlinearWronskianV, Matrix.diagonal_one, Matrix.mul_one,
      Matrix.transpose_neg, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_neg, Matrix.neg_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, neg_inv]
    module
  have h12 : A*D.transpose-M*B.transpose =
      1+s⁻¹ • nonlinearWronskianU J L Jm Lm (fun _ => 1) s := by
    simp only [A, D, M, B, nonlinearWronskianU, Matrix.diagonal_one, Matrix.mul_one,
      Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.sub_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.add_mul, Matrix.mul_add]
    module
  have h22 : B*D.transpose-D*B.transpose =
      s⁻¹ • nonlinearWronskianV J L Lm (fun _ => 1) s := by
    simp only [D, B, nonlinearWronskianV, Matrix.diagonal_one, Matrix.mul_one,
      Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    module
  rw [hu, smul_zero, add_zero] at h12
  rw [hv, smul_zero] at h22
  rw [hvm, smul_zero] at h11
  have h := symplectic_blocks_source_reciprocity A B M D h11 h12 h22
  have he : A.transpose*B-B.transpose*A =
      s⁻¹ • (J-J.transpose+s⁻¹ • (J.transpose*L-L.transpose*J)) := by
    simp only [A, B, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    module
  rw [he] at h
  exact (smul_eq_zero.mp h).resolve_left (inv_ne_zero hs)

theorem nonlinearWronskian_implies_reciprocity
    (J L Jm Lm : Matrix (Fin N) (Fin N) ℂ) (d : Fin N → ℂ)
    (s : ℂ) (hs : s ≠ 0)
    (hu : nonlinearWronskianU J L Jm Lm d s=0)
    (hv : nonlinearWronskianV J L Lm d s=0)
    (hvm : nonlinearWronskianV Jm Lm L d (-s)=0) :
    J-J.transpose+s⁻¹ • (J.transpose*Matrix.diagonal d*L-L.transpose*Matrix.diagonal d*J)=0 := by
  let P := Matrix.diagonal d
  let A := 1-s⁻¹ • (P*L)
  let D := 1+s⁻¹ • (Lm*P)
  let B := s⁻¹ • J
  let M := -(s⁻¹ • (P*Jm*P))
  have hPT : P.transpose=P := Matrix.diagonal_transpose _
  have h11 : A*M.transpose-M*A.transpose =
      s⁻¹ • (P*nonlinearWronskianV Jm Lm L d (-s)*P) := by
    simp only [A, M, nonlinearWronskianV, Matrix.transpose_neg, Matrix.transpose_smul,
      Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hPT,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_neg, Matrix.neg_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.add_mul, Matrix.mul_add]
    simp only [P, Matrix.mul_assoc]
    module
  have h12 : A*D.transpose-M*B.transpose =
      1+s⁻¹ • (P*nonlinearWronskianU J L Jm Lm d s) := by
    simp only [A, D, M, B, nonlinearWronskianU, Matrix.transpose_smul,
      Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, hPT,
      Matrix.sub_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.mul_sub]
    simp only [P, Matrix.mul_assoc]
    module
  have h22 : B*D.transpose-D*B.transpose =
      s⁻¹ • nonlinearWronskianV J L Lm d s := by
    simp only [D, B, nonlinearWronskianV, Matrix.transpose_smul,
      Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, hPT,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    simp only [P, Matrix.mul_assoc]
    module
  rw [hu, Matrix.mul_zero, smul_zero, add_zero] at h12
  rw [hv, smul_zero] at h22
  rw [hvm, Matrix.mul_zero, Matrix.zero_mul, smul_zero] at h11
  have h := symplectic_blocks_source_reciprocity A B M D h11 h12 h22
  have he : A.transpose*B-B.transpose*A =
      s⁻¹ • (J-J.transpose+s⁻¹ • (J.transpose*Matrix.diagonal d*L-L.transpose*Matrix.diagonal d*J)) := by
    simp only [A, B, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
      Matrix.transpose_mul, hPT, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    simp only [P, Matrix.mul_assoc]
    module
  rw [he] at h
  exact (smul_eq_zero.mp h).resolve_left (inv_ne_zero hs)

theorem nonlinearWronskian_implies_reciprocity_of_density_factor
    (J L Jm Lm S : Matrix (Fin N) (Fin N) ℂ) (d : Fin N → ℂ)
    (hST : S.transpose=S) (hSq : S*S=Matrix.diagonal d) (hSu : IsUnit S)
    (s : ℂ) (hs : s ≠ 0)
    (hu : nonlinearWronskianU J L Jm Lm d s=0)
    (hv : nonlinearWronskianV J L Lm d s=0)
    (hvm : nonlinearWronskianV Jm Lm L d (-s)=0) :
    J-J.transpose+s⁻¹ • (J.transpose*Matrix.diagonal d*L-L.transpose*Matrix.diagonal d*J)=0 := by
  have ht (X : Matrix (Fin N) (Fin N) ℂ) : (S*X*S).transpose=S*X.transpose*S := by
    simp only [Matrix.transpose_mul, hST, Matrix.mul_assoc]
  have hp (X Y : Matrix (Fin N) (Fin N) ℂ) :
      (S*X*S)*(S*Y*S)=S*X*Matrix.diagonal d*Y*S := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S S (Y*S), hSq]
  have hU (X Y Xm Ym : Matrix (Fin N) (Fin N) ℂ) (w : ℂ) :
      nonlinearWronskianU (S*X*S) (S*Y*S) (S*Xm*S) (S*Ym*S) (fun _ => 1) w=
        S*nonlinearWronskianU X Y Xm Ym d w*S := by
    simp only [nonlinearWronskianU, Matrix.diagonal_one, Matrix.mul_one, ht, hp,
      Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_smul,
      Matrix.add_mul, Matrix.sub_mul, Matrix.neg_mul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
  have hV (X Y Ym : Matrix (Fin N) (Fin N) ℂ) (w : ℂ) :
      nonlinearWronskianV (S*X*S) (S*Y*S) (S*Ym*S) (fun _ => 1) w=
        S*nonlinearWronskianV X Y Ym d w*S := by
    simp only [nonlinearWronskianV, Matrix.diagonal_one, Matrix.mul_one, ht, hp,
      Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul,
      Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
  have h := nonlinearWronskian_density_free_implies_reciprocity (S*J*S) (S*L*S)
    (S*Jm*S) (S*Lm*S) s hs
    (by rw [hU, hu, Matrix.mul_zero, Matrix.zero_mul])
    (by rw [hV, hv, Matrix.mul_zero, Matrix.zero_mul])
    (by rw [hV, hvm, Matrix.mul_zero, Matrix.zero_mul])
  have he : (S*J*S)-(S*J*S).transpose+s⁻¹ •
      ((S*J*S).transpose*(S*L*S)-(S*L*S).transpose*(S*J*S))=
      S*(J-J.transpose+s⁻¹ •
        (J.transpose*Matrix.diagonal d*L-L.transpose*Matrix.diagonal d*J))*S := by
    simp only [ht, hp, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul,
      Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
  rw [he] at h
  apply hSu.mul_right_injective
  apply hSu.mul_left_injective
  simpa only [Matrix.mul_zero, Matrix.zero_mul] using h

end FMSA.ExactMSA.MultiTailMixture
