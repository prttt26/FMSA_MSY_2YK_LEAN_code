import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearOriginLift
import Mathlib.Tactic.NoncommRing

/-! Unscaled kernel matrices keep conditions in zero-density rows visible.
The weighted affine product is D+H+D R H, with R the doubled density matrix. -/
noncomputable section
open Real MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

def originKernelMatrix (F : Fin N → Fin N → Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ := originLift (fun _ => 1) F

def originDensityMatrix (ρ : Fin N → ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  Matrix.fromBlocks (Matrix.diagonal ρ) 0 0 (Matrix.diagonal ρ)

theorem originKernelMatrix_add
    (F H : Fin N → Fin N → Matrix (Fin 2) (Fin 2) ℝ) :
    originKernelMatrix (fun i j => F i j+H i j) = originKernelMatrix F+originKernelMatrix H :=
  originLift_add _ F H

theorem originKernelMatrix_zero : originKernelMatrix (fun _ _ : Fin N => 0) = 0 :=
  originLift_zero _

theorem originKernelMatrix_density_mul (ρ : Fin N → ℝ)
    (F : Fin N → Fin N → Matrix (Fin 2) (Fin 2) ℝ) :
    originKernelMatrix F * originDensityMatrix ρ =
      originKernelMatrix (fun i j => ρ j • F i j) := by
  simp only [originKernelMatrix, originLift, originDensityMatrix, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul] <;> ring

theorem originKernelMatrix_weighted_mul (ρ : Fin N → ℝ)
    (F H : Fin N → Fin N → Matrix (Fin 2) (Fin 2) ℝ) :
    originKernelMatrix F * originDensityMatrix ρ * originKernelMatrix H =
      originKernelMatrix (fun i j => originJetIntegral (nonlinearDensityFunctional ρ)
        (fun m => F i m*H m j)) := by
  rw [originKernelMatrix_density_mul]
  unfold originKernelMatrix
  rw [originLift_mul]
  congr 1
  funext i j a b
  simp [originJetIntegral, nonlinearDensityFunctional, Matrix.smul_mul, Matrix.smul_apply,
    smul_eq_mul]

theorem originDensityMatrix_transpose (ρ : Fin N → ℝ) :
    (originDensityMatrix ρ).transpose = originDensityMatrix ρ := by
  simp [originDensityMatrix, Matrix.fromBlocks_transpose]

theorem originDensityMatrix_commutes_omega (ρ : Fin N → ℝ) :
    originDensityMatrix ρ * completionOmega (n := Fin N) (R := ℝ) =
      completionOmega (n := Fin N) (R := ℝ) * originDensityMatrix ρ := by
  simp only [originDensityMatrix, completionOmega, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul, zero_add, add_zero, neg_zero]

def intrinsicDefect {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (P O H : Matrix n n R) := H*O+O*H.transpose+H*P*O*H.transpose

theorem intrinsicDefect_affine_product {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (P O D H : Matrix n n R) (hP : P.transpose = P) (hPO : P*O = O*P) :
    intrinsicDefect P O (D+H+D*P*H) = intrinsicDefect P O D +
      (1+D*P)*intrinsicDefect P O H*(1+P*D.transpose) := by
  simp only [intrinsicDefect, Matrix.transpose_add, Matrix.transpose_mul, hP]
  have h (X : Matrix n n R) : P*O*X = O*P*X := by rw [hPO]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc P O, hPO, Matrix.mul_assoc]
  abel

theorem originKernelMatrix_smul (s : ℝ)
    (F : Fin N → Fin N → Matrix (Fin 2) (Fin 2) ℝ) :
    originKernelMatrix (fun i j => s • F i j) = s • originKernelMatrix F :=
  originLift_smul _ s F

theorem originKernelMatrix_transpose
    (F : Fin N → Fin N → Matrix (Fin 2) (Fin 2) ℝ) :
    (originKernelMatrix F).transpose = originKernelMatrix (fun i j => (F j i).transpose) := by
  ext i j
  cases i <;> cases j <;>
    simp [originKernelMatrix, originLift, Matrix.fromBlocks, Matrix.transpose_apply]

theorem originKernelMatrix_mul_omega
    (F : Fin N → Fin N → Matrix (Fin 2) (Fin 2) ℝ) :
    originKernelMatrix F * completionOmega (n := Fin N) (R := ℝ) =
      originKernelMatrix (fun i j => F i j * !![0, 1; -1, 0]) := by
  unfold originKernelMatrix originLift completionOmega
  rw [Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks, Matrix.mul_apply, Fin.sum_univ_two]

theorem omega_mul_originKernelMatrix
    (F : Fin N → Fin N → Matrix (Fin 2) (Fin 2) ℝ) :
    completionOmega (n := Fin N) (R := ℝ) * originKernelMatrix F =
      originKernelMatrix (fun i j => !![0, 1; -1, 0] * F i j) := by
  unfold originKernelMatrix originLift completionOmega
  rw [Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks, Matrix.mul_apply, Fin.sum_univ_two]

theorem originKernelMatrix_weighted_omega (ρ : Fin N → ℝ)
    (F H : Fin N → Fin N → Matrix (Fin 2) (Fin 2) ℝ) :
    originKernelMatrix F * originDensityMatrix ρ * completionOmega (n := Fin N) (R := ℝ) *
      (originKernelMatrix H).transpose =
      originKernelMatrix (fun i j => originJetIntegral (nonlinearDensityFunctional ρ)
        (fun m => F i m * !![0, 1; -1, 0] * (H j m).transpose)) := by
  rw [Matrix.mul_assoc (originKernelMatrix F) (originDensityMatrix ρ),
    originDensityMatrix_commutes_omega, ← Matrix.mul_assoc (originKernelMatrix F),
    originKernelMatrix_mul_omega, originKernelMatrix_transpose,
    originKernelMatrix_weighted_mul]

end FMSA.ExactMSA.MultiTailMixture
