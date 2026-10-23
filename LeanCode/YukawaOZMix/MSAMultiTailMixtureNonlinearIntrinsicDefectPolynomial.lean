import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearIntrinsicPolynomial
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearFactorCompletion
import Mathlib.RingTheory.PrincipalIdealDomain

/-! Cleared affine symplectic defects and cancellation of the origin factor. -/
noncomputable section
open Polynomial
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

def intrinsicClearedDefect (P O H : Matrix n n R) (c : R) :=
  c • (H*O+O*H.transpose)+H*P*O*H.transpose

theorem intrinsicClearedDefect_affine
    (P O D H : Matrix n n R) (c q : R)
    (hP : P.transpose = P) (hPO : P*O = O*P) :
    intrinsicClearedDefect P O ((c*q) • D+c • H+D*P*H) (c^2*q) =
      (c^2*q^2) • intrinsicClearedDefect P O D c +
      (c • 1+D*P)*intrinsicClearedDefect P O H (c*q)*(c • 1+P*D.transpose) := by
  simp only [intrinsicClearedDefect, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_smul, hP]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
  simp only [← Matrix.mul_assoc P O, hPO, Matrix.mul_assoc]
  module

theorem intrinsicClearedDefect_skew (P O H : Matrix n n R) (c : R)
    (hP : P.transpose = P) (hPO : P*O = O*P) (hO : O.transpose = -O) :
    (intrinsicClearedDefect P O H c).transpose = -intrinsicClearedDefect P O H c := by
  simp only [intrinsicClearedDefect, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_smul, hP, hO, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc O P, ← hPO, Matrix.mul_assoc]
  module

theorem polynomial_cancel_origin_power_dvd (p f : Polynomial ℝ) (k : ℕ)
    (hp0 : p.coeff 0 ≠ 0) (h : p ∣ X^k*f) : p ∣ f := by
  have hnd : ¬(X : Polynomial ℝ) ∣ p := by
    intro hd
    have hh := Polynomial.X_pow_dvd_iff.mp (by simpa using hd : (X : Polynomial ℝ)^1 ∣ p)
    exact hp0 (hh 0 (by omega))
  have hc : IsCoprime p (X : Polynomial ℝ) :=
    ((Polynomial.irreducible_X : Irreducible (X : Polynomial ℝ)).coprime_iff_not_dvd.mpr hnd).symm
  exact (hc.pow_right (n := k)).dvd_of_dvd_mul_left h

variable {N : ℕ}

theorem originDensityMatrix_mul_completionV (ρ : Fin N → ℝ) :
    originDensityMatrix ρ * completionV (1 : Matrix (Fin N) (Fin N) ℝ) =
      completionV (1 : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal ρ := by
  simp only [originDensityMatrix, completionV, Matrix.fromBlocks_mul_fromRows,
    Matrix.fromRows_mul, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, zero_add, add_zero, neg_zero]

theorem intrinsic_lagrangian_origin_double_pole_zero
    (ρ : Fin N → ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
    let U := completionU (1 : Matrix (Fin N) (Fin N) ℝ)
    let V := completionV (1 : Matrix (Fin N) (Fin N) ℝ)
    let O := completionOmega (n := Fin N) (R := ℝ)
    (V*A*U)*originDensityMatrix ρ*O*(V*A*U).transpose = 0 := by
  dsimp only
  calc
    _ = completionV (1 : Matrix (Fin N) (Fin N) ℝ)*A*completionU (1 : Matrix (Fin N) (Fin N) ℝ) *
        (originDensityMatrix ρ * completionOmega (n := Fin N) (R := ℝ) * (completionU (1 : Matrix (Fin N) (Fin N) ℝ)).transpose) *
        A.transpose * (completionV (1 : Matrix (Fin N) (Fin N) ℝ)).transpose := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 0 := by
      rw [Matrix.mul_assoc (originDensityMatrix ρ),
        completionOmega_mul_completionU_transpose (1 : Matrix (Fin N) (Fin N) ℝ)
          (by simp), Matrix.mul_neg, originDensityMatrix_mul_completionV]
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (completionU (1 : Matrix (Fin N) (Fin N) ℝ)),
        completionU_mul_completionV]
      simp

theorem intrinsic_lagrangian_origin_projection_zero
    (ρ : Fin N → ℝ) (A : Matrix (Fin N) (Fin N) ℝ)
    (S : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ)
    (hS : completionU (1 : Matrix (Fin N) (Fin N) ℝ)*S*completionV (1 : Matrix (Fin N) (Fin N) ℝ) = 0) :
    let U := completionU (1 : Matrix (Fin N) (Fin N) ℝ)
    let V := completionV (1 : Matrix (Fin N) (Fin N) ℝ)
    let O := completionOmega (n := Fin N) (R := ℝ)
    U*((V*A*U)*O+O*(V*A*U).transpose +
      (V*A*U)*originDensityMatrix ρ*O*S.transpose +
      S*originDensityMatrix ρ*O*(V*A*U).transpose) = 0 := by
  let U := completionU (1 : Matrix (Fin N) (Fin N) ℝ)
  let V := completionV (1 : Matrix (Fin N) (Fin N) ℝ)
  let O := completionOmega (n := Fin N) (R := ℝ)
  change U*S*V = 0 at hS
  have huv : U*V = 0 := completionU_mul_completionV _
  have hur : U*(V*A*U) = 0 := by
    simp only [← Matrix.mul_assoc, huv, Matrix.zero_mul]
  have huo : U*O = V.transpose := completionU_mul_omega _ Matrix.transpose_one
  have hou : O*U.transpose = -V :=
    completionOmega_mul_completionU_transpose _ Matrix.transpose_one
  have huor : U*O*(V*A*U).transpose = 0 := by
    rw [huo]
    simp only [Matrix.transpose_mul, ← Matrix.mul_assoc]
    rw [← Matrix.transpose_mul, huv, Matrix.transpose_zero]
    simp
  have hror : originDensityMatrix ρ*O*(V*A*U).transpose =
      -(V*Matrix.diagonal ρ*A.transpose*V.transpose) := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc O U.transpose, hou]
    simp only [Matrix.neg_mul, Matrix.mul_neg]
    rw [← Matrix.mul_assoc (originDensityMatrix ρ) V,
      originDensityMatrix_mul_completionV]
    simp only [Matrix.mul_assoc]
    rfl
  change U*((V*A*U)*O+O*(V*A*U).transpose +
    (V*A*U)*originDensityMatrix ρ*O*S.transpose + S*originDensityMatrix ρ*O*(V*A*U).transpose) = 0
  simp only [Matrix.mul_add, ← Matrix.mul_assoc]
  rw [huv, Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul, huor]
  simp only [Matrix.zero_mul, zero_add]
  simp only [Matrix.mul_assoc] at hror ⊢
  rw [hror]
  simp only [Matrix.mul_neg, ← Matrix.mul_assoc]
  rw [hS]
  simp

end FMSA.ExactMSA.MultiTailMixture
