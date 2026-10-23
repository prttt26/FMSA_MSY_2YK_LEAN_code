import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearMatrixPolynomial
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearHSAdmissibility

/-! Density-free verification of the intrinsic inverse HS reference. -/
noncomputable section
open Real Polynomial MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

def hsInverseKernel {R : Type*} [CommRing R] (a c x y s : R) : Matrix (Fin 2) (Fin 2) R :=
  !![hsAdmissibilityL a c y x (-s), hsAdmissibilityJ a c y x (-s);
    -hsAdmissibilityJ a c y x s, -hsAdmissibilityL a c y x s]

def hsInverseCrossKernel {R : Type*} [CommRing R] (x y s : R) : Matrix (Fin 2) (Fin 2) R :=
  !![x-y, -(s*x*y+x-y); s*x*y-x+y, x-y]

def intrinsicOmega2 {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]

theorem hsInverseKernel_linear_and_product {R : Type*} [CommRing R] (a c x y t s : R) :
    s^3 • (hsInverseKernel a c x y s * intrinsicOmega2 +
      intrinsicOmega2 * (hsInverseKernel a c y x s).transpose) =
      (-2*a*c*s^3) • hsInverseCrossKernel x y s ∧
    hsInverseKernel a c x t s * intrinsicOmega2 * (hsInverseKernel a c y t s).transpose =
      (a^2*s^3*t^2) • hsInverseCrossKernel x y s := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j
  all_goals
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two]
    simp [hsInverseKernel, hsInverseCrossKernel, intrinsicOmega2, hsAdmissibilityJ,
      hsAdmissibilityL]
    ring

theorem hsInverseKernel_weighted_defect_zero (a c s : ℝ) (ρ σ : Fin N → ℝ)
    (hm : a*(∑ m, ρ m*(σ m)^2) = 2*c) (i j : Fin N) :
    s^3 • (hsInverseKernel a c (σ i) (σ j) s * intrinsicOmega2 +
      intrinsicOmega2 * (hsInverseKernel a c (σ j) (σ i) s).transpose) +
    originJetIntegral (nonlinearDensityFunctional ρ) (fun m =>
      hsInverseKernel a c (σ i) (σ m) s * intrinsicOmega2 *
        (hsInverseKernel a c (σ j) (σ m) s).transpose) = 0 := by
  rw [(hsInverseKernel_linear_and_product a c (σ i) (σ j) 0 s).1]
  simp_rw [(hsInverseKernel_linear_and_product a c (σ i) (σ j) _ s).2]
  ext u v
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, originJetIntegral,
    nonlinearDensityFunctional, LinearMap.coe_mk, AddHom.coe_mk, Matrix.zero_apply]
  have hs : (∑ m, ρ m*(a^2*s^3*(σ m)^2*hsInverseCrossKernel (σ i) (σ j) s u v)) =
      a^2*s^3*hsInverseCrossKernel (σ i) (σ j) s u v*(∑ m, ρ m*(σ m)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hs]
  linear_combination a*s^3*hsInverseCrossKernel (σ i) (σ j) s u v*hm

theorem originIntrinsicD_kernel_HS_dictionary (ρ σ : Fin N → ℝ) (s : ℝ) (i j : Fin N) :
    originJetD3 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) +
      s • originJetD2 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) (σ j) +
      s^2 • originJetD1 (π/vacMix ρ σ) (σ i) (σ j) =
      hsInverseKernel (π/vacMix ρ σ) ((π/vacMix ρ σ)*xi2 ρ σ/2) (σ i) (σ j) s := by
  ext u v
  fin_cases u <;> fin_cases v <;>
    simp [originJetD1, originJetD2, originJetD3, hsInverseKernel, hsAdmissibilityJ,
      hsAdmissibilityL, smul_eq_mul] <;> ring

theorem originIntrinsicDPolynomial_eval_dictionary (ρ σ : Fin N → ℝ) (s : ℝ) :
    polyMatrixEval s (polyOriginD (originIntrinsicD1 ρ σ) (originIntrinsicD2 ρ σ)
      (originIntrinsicD3 ρ σ)) =
      originKernelMatrix (fun i j => hsInverseKernel (π/vacMix ρ σ)
        ((π/vacMix ρ σ)*xi2 ρ σ/2) (σ i) (σ j) s) := by
  simp only [polyOriginD, polyMatrixEval_add, polyMatrixEval_term, pow_zero,
    one_smul, pow_one]
  unfold originIntrinsicD1 originIntrinsicD2 originIntrinsicD3
  rw [← originKernelMatrix_smul, ← originKernelMatrix_smul,
    ← originKernelMatrix_add, ← originKernelMatrix_add]
  congr 1
  funext i j
  exact originIntrinsicD_kernel_HS_dictionary ρ σ s i j

theorem hsInverseKernelMatrix_weighted_defect_zero (ρ σ : Fin N → ℝ) (s : ℝ) :
    let D := originKernelMatrix (fun i j => hsInverseKernel (π/vacMix ρ σ)
      ((π/vacMix ρ σ)*xi2 ρ σ/2) (σ i) (σ j) s)
    let O := completionOmega (n := Fin N) (R := ℝ)
    s^3 • (D*O+O*D.transpose) + D*originDensityMatrix ρ*O*D.transpose = 0 := by
  have hm : (π/vacMix ρ σ)*(∑ m, ρ m*(σ m)^2) =
      2*((π/vacMix ρ σ)*xi2 ρ σ/2) := by
    unfold xi2
    ring
  dsimp only
  rw [originKernelMatrix_weighted_omega, originKernelMatrix_transpose,
    originKernelMatrix_mul_omega, omega_mul_originKernelMatrix,
    ← originKernelMatrix_add, ← originKernelMatrix_smul, ← originKernelMatrix_add]
  have he : (fun i j => s^3 •
      (hsInverseKernel (π/vacMix ρ σ) ((π/vacMix ρ σ)*xi2 ρ σ/2) (σ i) (σ j) s * !![0, 1; -1, 0] +
        !![0, 1; -1, 0] * (hsInverseKernel (π/vacMix ρ σ)
          ((π/vacMix ρ σ)*xi2 ρ σ/2) (σ j) (σ i) s).transpose) +
      originJetIntegral (nonlinearDensityFunctional ρ) (fun m =>
        hsInverseKernel (π/vacMix ρ σ) ((π/vacMix ρ σ)*xi2 ρ σ/2) (σ i) (σ m) s * !![0, 1; -1, 0] *
          (hsInverseKernel (π/vacMix ρ σ) ((π/vacMix ρ σ)*xi2 ρ σ/2) (σ j) (σ m) s).transpose)) =
        (fun _ _ => 0) := by
    funext i j
    exact hsInverseKernel_weighted_defect_zero _ _ s ρ σ hm i j
  rw [he, originKernelMatrix_zero]

theorem originIntrinsicDPolynomial_defect_zero (ρ σ : Fin N → ℝ) :
    let D := polyOriginD (originIntrinsicD1 ρ σ) (originIntrinsicD2 ρ σ) (originIntrinsicD3 ρ σ)
    let O := polyMatrixTerm 0 (completionOmega (n := Fin N) (R := ℝ))
    (X^3 : Polynomial ℝ) • (D*O+O*D.transpose) +
      D*polyMatrixTerm 0 (originDensityMatrix ρ)*O*D.transpose = 0 := by
  dsimp only
  apply Matrix.ext
  intro i j
  apply Polynomial.funext
  intro s
  have he := hsInverseKernelMatrix_weighted_defect_zero ρ σ s
  have hd := originIntrinsicDPolynomial_eval_dictionary ρ σ s
  have hh : polyMatrixEval s
      ((X^3 : Polynomial ℝ) •
          (polyOriginD (originIntrinsicD1 ρ σ) (originIntrinsicD2 ρ σ) (originIntrinsicD3 ρ σ) *
              polyMatrixTerm 0 (completionOmega (n := Fin N) (R := ℝ)) +
            polyMatrixTerm 0 (completionOmega (n := Fin N) (R := ℝ)) *
              (polyOriginD (originIntrinsicD1 ρ σ) (originIntrinsicD2 ρ σ) (originIntrinsicD3 ρ σ)).transpose) +
        polyOriginD (originIntrinsicD1 ρ σ) (originIntrinsicD2 ρ σ) (originIntrinsicD3 ρ σ) *
          polyMatrixTerm 0 (originDensityMatrix ρ) *
          polyMatrixTerm 0 (completionOmega (n := Fin N) (R := ℝ)) *
          (polyOriginD (originIntrinsicD1 ρ σ) (originIntrinsicD2 ρ σ) (originIntrinsicD3 ρ σ)).transpose) = 0 := by
    simp only [polyMatrixEval_add, polyMatrixEval_mul, polyMatrixEval_transpose,
      polyMatrixEval_smul, polyMatrixEval_term, pow_zero, one_smul, Polynomial.eval_pow,
      Polynomial.eval_X, hd]
    exact he
  simpa [polyMatrixEval] using congrFun (congrFun hh i) j

end FMSA.ExactMSA.MultiTailMixture
