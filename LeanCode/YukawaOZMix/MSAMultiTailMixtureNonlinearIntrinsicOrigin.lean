import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearIntrinsicKernel

/-! Origin normalization in unscaled species kernels; zero-density rows
retain the full identities. -/
noncomputable section
open Real MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

def originIntrinsicH3 {ι : Type*} [Fintype ι] (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) :=
  originKernelMatrix (fun _ j => originJetH3 (amplitudeA z ρ σ Dt G j))
def originIntrinsicH2 {ι : Type*} [Fintype ι] (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) :=
  originKernelMatrix (fun i j => originJetH2 (σ i) (amplitudeA z ρ σ Dt G j)
    (nonlinearB z ρ σ Dt G j))
def originIntrinsicH1 {ι : Type*} [Fintype ι] (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) :=
  originKernelMatrix (fun i j => originJetH1 (σ i) (nonlinearB z ρ σ Dt G j)
    (nonlinearOriginCmoment z ρ σ Dt G 0 i j))
def originIntrinsicH0 {ι : Type*} [Fintype ι] (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) :=
  originKernelMatrix (fun i j => originJetH0 (nonlinearOriginCmoment z ρ σ Dt G 1 i j)
    (nonlinearOriginWmoment z ρ Dt G 1 i j))
def originIntrinsicHp1 {ι : Type*} [Fintype ι] (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) :=
  originKernelMatrix (fun i j => originJetHplus1 (nonlinearOriginCmoment z ρ σ Dt G 2 i j)
    (nonlinearOriginWmoment z ρ Dt G 2 i j))
def originIntrinsicHp2 {ι : Type*} [Fintype ι] (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) :=
  originKernelMatrix (fun i j => originJetHplus2 (nonlinearOriginCmoment z ρ σ Dt G 3 i j)
    (nonlinearOriginWmoment z ρ Dt G 3 i j))
def originIntrinsicHp3 {ι : Type*} [Fintype ι] (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) :=
  originKernelMatrix (fun i j => originJetHplus1 (nonlinearOriginCmoment z ρ σ Dt G 4 i j)
    (nonlinearOriginWmoment z ρ Dt G 4 i j))
def originIntrinsicD1 (ρ σ : Fin N → ℝ) :=
  originKernelMatrix (fun i j => originJetD1 (Real.pi/vacMix ρ σ) (σ i) (σ j))
def originIntrinsicD2 (ρ σ : Fin N → ℝ) :=
  originKernelMatrix (fun i j => originJetD2 (Real.pi/vacMix ρ σ)
    (xi2 ρ σ) (σ i) (σ j))
def originIntrinsicD3 (ρ σ : Fin N → ℝ) :=
  originKernelMatrix (fun i _ => originJetD3 (Real.pi/vacMix ρ σ)
    (xi2 ρ σ) (σ i))

theorem originIntrinsic_highest_products_zero {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    originIntrinsicD3 ρ σ * originDensityMatrix ρ * originIntrinsicH3 z ρ σ Dt G = 0 ∧
    originIntrinsicD2 ρ σ * originDensityMatrix ρ * originIntrinsicH3 z ρ σ Dt G +
      originIntrinsicD3 ρ σ * originDensityMatrix ρ * originIntrinsicH2 z ρ σ Dt G = 0 ∧
    originIntrinsicD1 ρ σ * originDensityMatrix ρ * originIntrinsicH3 z ρ σ Dt G +
      originIntrinsicD2 ρ σ * originDensityMatrix ρ * originIntrinsicH2 z ρ σ Dt G +
      originIntrinsicD3 ρ σ * originDensityMatrix ρ * originIntrinsicH1 z ρ σ Dt G = 0 := by
  have h (i m j : Fin N) := originJet_highest_three_products_zero
    (Real.pi/vacMix ρ σ) (xi2 ρ σ) (σ i) (σ m)
    (amplitudeA z ρ σ Dt G j) (nonlinearB z ρ σ Dt G j)
    (nonlinearOriginCmoment z ρ σ Dt G 0 m j)
  unfold originIntrinsicD1 originIntrinsicD2 originIntrinsicD3 originIntrinsicH1 originIntrinsicH2 originIntrinsicH3
  simp only [originKernelMatrix_weighted_mul]
  constructor
  · have hh (i j : Fin N) := (h i i j).1
    simp_rw [hh]
    rw [originJetIntegral_zero, originKernelMatrix_zero]
  constructor
  · rw [← originKernelMatrix_add]
    have hz : (fun i j => originJetIntegral (nonlinearDensityFunctional ρ)
        (fun m => originJetD2 (Real.pi/vacMix ρ σ) (xi2 ρ σ) (σ i) (σ m) *
          originJetH3 (amplitudeA z ρ σ Dt G j)) +
        originJetIntegral (nonlinearDensityFunctional ρ) (fun m =>
          originJetD3 (Real.pi/vacMix ρ σ) (xi2 ρ σ) (σ i) *
          originJetH2 (σ m) (amplitudeA z ρ σ Dt G j) (nonlinearB z ρ σ Dt G j))) =
        (fun _ _ => 0) := by
      funext i j a b
      simp only [Matrix.add_apply, originJetIntegral, nonlinearDensityFunctional, LinearMap.coe_mk, AddHom.coe_mk,
        ← Finset.sum_add_distrib, ← mul_add]
      simp only [← Matrix.add_apply, (h i _ j).2.1, Matrix.zero_apply, mul_zero,
        Finset.sum_const_zero]
    rw [hz, originKernelMatrix_zero]
  · rw [← originKernelMatrix_add, ← originKernelMatrix_add]
    have hz : (fun i j => originJetIntegral (nonlinearDensityFunctional ρ)
        (fun m => originJetD1 (Real.pi/vacMix ρ σ) (σ i) (σ m) *
          originJetH3 (amplitudeA z ρ σ Dt G j)) +
        originJetIntegral (nonlinearDensityFunctional ρ) (fun m =>
          originJetD2 (Real.pi/vacMix ρ σ) (xi2 ρ σ) (σ i) (σ m) *
          originJetH2 (σ m) (amplitudeA z ρ σ Dt G j) (nonlinearB z ρ σ Dt G j)) +
        originJetIntegral (nonlinearDensityFunctional ρ) (fun m =>
          originJetD3 (Real.pi/vacMix ρ σ) (xi2 ρ σ) (σ i) *
          originJetH1 (σ m) (nonlinearB z ρ σ Dt G j) (nonlinearOriginCmoment z ρ σ Dt G 0 m j))) =
        (fun _ _ => 0) := by
      funext i j a b
      simp only [Matrix.add_apply, originJetIntegral, nonlinearDensityFunctional, LinearMap.coe_mk, AddHom.coe_mk,
        ← Finset.sum_add_distrib, ← mul_add]
      simp only [← Matrix.add_apply, (h i _ j).2.2, Matrix.zero_apply, mul_zero,
        Finset.sum_const_zero]
    rw [hz, originKernelMatrix_zero]

theorem originIntrinsic_third_coefficient_zero {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (hv : vacMix ρ σ ≠ 0) :
    originIntrinsicH3 z ρ σ Dt G + originIntrinsicD3 ρ σ +
      originIntrinsicD1 ρ σ * originDensityMatrix ρ * originIntrinsicH2 z ρ σ Dt G +
      originIntrinsicD2 ρ σ * originDensityMatrix ρ * originIntrinsicH1 z ρ σ Dt G +
      originIntrinsicD3 ρ σ * originDensityMatrix ρ * originIntrinsicH0 z ρ σ Dt G = 0 := by
  unfold originIntrinsicH3 originIntrinsicD3 originIntrinsicD1 originIntrinsicD2 originIntrinsicH2
    originIntrinsicH1 originIntrinsicH0
  simp only [originKernelMatrix_weighted_mul, ← originKernelMatrix_add]
  have hh : (fun i j => originJetH3 (amplitudeA z ρ σ Dt G j) +
      originJetD3 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) +
      originJetIntegral (nonlinearDensityFunctional ρ) (fun m =>
        originJetD1 (π/vacMix ρ σ) (σ i) (σ m) *
          originJetH2 (σ m) (amplitudeA z ρ σ Dt G j) (nonlinearB z ρ σ Dt G j)) +
      originJetIntegral (nonlinearDensityFunctional ρ) (fun m =>
        originJetD2 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) (σ m) *
          originJetH1 (σ m) (nonlinearB z ρ σ Dt G j) (nonlinearOriginCmoment z ρ σ Dt G 0 m j)) +
      originJetIntegral (nonlinearDensityFunctional ρ) (fun m =>
        originJetD3 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) *
          originJetH0 (nonlinearOriginCmoment z ρ σ Dt G 1 m j)
            (nonlinearOriginWmoment z ρ Dt G 1 m j))) = (fun _ _ => 0) := by
    funext i j a b
    have he := congrFun (congrFun
      (nonlinearOrigin_third_coefficient_zero z ρ σ Dt G hz hv i j) a) b
    simp only [Matrix.add_apply, Matrix.zero_apply, originJetIntegral, nonlinearDensityFunctional,
      LinearMap.coe_mk, AddHom.coe_mk, mul_add, Finset.sum_add_distrib] at he ⊢
    linear_combination he
  rw [hh, originKernelMatrix_zero]

theorem originIntrinsic_second_coefficient_zero {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (hv : vacMix ρ σ ≠ 0) :
    originIntrinsicH2 z ρ σ Dt G + originIntrinsicD2 ρ σ +
      originIntrinsicD1 ρ σ * originDensityMatrix ρ * originIntrinsicH1 z ρ σ Dt G +
      originIntrinsicD2 ρ σ * originDensityMatrix ρ * originIntrinsicH0 z ρ σ Dt G +
      originIntrinsicD3 ρ σ * originDensityMatrix ρ * originIntrinsicHp1 z ρ σ Dt G = 0 := by
  unfold originIntrinsicH2 originIntrinsicD2 originIntrinsicD1 originIntrinsicD3 originIntrinsicH1
    originIntrinsicH0 originIntrinsicHp1
  simp only [originKernelMatrix_weighted_mul, ← originKernelMatrix_add]
  have hh : (fun i j => originJetH2 (σ i) (amplitudeA z ρ σ Dt G j) (nonlinearB z ρ σ Dt G j) +
      originJetD2 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) (σ j) +
      originJetIntegral (nonlinearDensityFunctional ρ) (fun m =>
        originJetD1 (π/vacMix ρ σ) (σ i) (σ m) *
          originJetH1 (σ m) (nonlinearB z ρ σ Dt G j) (nonlinearOriginCmoment z ρ σ Dt G 0 m j)) +
      originJetIntegral (nonlinearDensityFunctional ρ) (fun m =>
        originJetD2 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) (σ m) *
          originJetH0 (nonlinearOriginCmoment z ρ σ Dt G 1 m j) (nonlinearOriginWmoment z ρ Dt G 1 m j)) +
      originJetIntegral (nonlinearDensityFunctional ρ) (fun m =>
        originJetD3 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) *
          originJetHplus1 (nonlinearOriginCmoment z ρ σ Dt G 2 m j)
            (nonlinearOriginWmoment z ρ Dt G 2 m j))) = (fun _ _ => 0) := by
    funext i j a b
    have he := congrFun (congrFun
      (nonlinearOrigin_second_coefficient_zero z ρ σ Dt G hz hv i j) a) b
    simp only [Matrix.add_apply, Matrix.zero_apply, originJetIntegral, nonlinearDensityFunctional,
      LinearMap.coe_mk, AddHom.coe_mk, mul_add, Finset.sum_add_distrib] at he ⊢
    linear_combination he
  rw [hh, originKernelMatrix_zero]

def originIntrinsicResidue {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :=
  originKernelMatrix (originActualResidueKernel z ρ σ Dt G)

def originIntrinsicConstant {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :=
  originKernelMatrix (originActualConstantKernel z ρ σ Dt G)

theorem originIntrinsicResidue_expanded {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    originIntrinsicResidue z ρ σ Dt G =
      originIntrinsicH1 z ρ σ Dt G + originIntrinsicD1 ρ σ +
      originIntrinsicD1 ρ σ * originDensityMatrix ρ * originIntrinsicH0 z ρ σ Dt G +
      originIntrinsicD2 ρ σ * originDensityMatrix ρ * originIntrinsicHp1 z ρ σ Dt G +
      originIntrinsicD3 ρ σ * originDensityMatrix ρ * originIntrinsicHp2 z ρ σ Dt G := by
  unfold originIntrinsicResidue originIntrinsicH1 originIntrinsicD1 originIntrinsicD2 originIntrinsicD3
    originIntrinsicH0 originIntrinsicHp1 originIntrinsicHp2
  simp only [originKernelMatrix_weighted_mul, ← originKernelMatrix_add]
  congr 1
  funext i j a b
  simp [originActualResidueKernel, originJetResidueProduct, Matrix.add_apply,
    originJetIntegral, nonlinearDensityFunctional, mul_add, Finset.sum_add_distrib, add_assoc]

theorem originIntrinsicConstant_expanded {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    originIntrinsicConstant z ρ σ Dt G = originIntrinsicH0 z ρ σ Dt G +
      originIntrinsicD1 ρ σ * originDensityMatrix ρ * originIntrinsicHp1 z ρ σ Dt G +
      originIntrinsicD2 ρ σ * originDensityMatrix ρ * originIntrinsicHp2 z ρ σ Dt G +
      originIntrinsicD3 ρ σ * originDensityMatrix ρ * originIntrinsicHp3 z ρ σ Dt G := by
  unfold originIntrinsicConstant originIntrinsicH0 originIntrinsicD1 originIntrinsicD2 originIntrinsicD3
    originIntrinsicHp1 originIntrinsicHp2 originIntrinsicHp3
  simp only [originKernelMatrix_weighted_mul, ← originKernelMatrix_add]
  congr 1
  funext i j a b
  simp [originActualConstantKernel, Matrix.add_apply, originJetIntegral,
    nonlinearDensityFunctional, mul_add, Finset.sum_add_distrib, add_assoc]

theorem originIntrinsicResidue_lagrangian {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) :
    ∃ A : Matrix (Fin N) (Fin N) ℝ,
      originIntrinsicResidue z ρ σ Dt G = completionV (1 : Matrix (Fin N) (Fin N) ℝ)*A*completionU (1 : Matrix (Fin N) (Fin N) ℝ) := by
  refine ⟨Matrix.of (fun i j => originActualResidueKernel z ρ σ Dt G i j 1 0), ?_⟩
  have h := originLift_lagrangian (fun _ => (1 : ℝ))
    (originActualResidueKernel z ρ σ Dt G)
    (fun i j => nonlinearOrigin_residue_lagrangian z ρ σ Dt G hz i j)
  simpa only [Matrix.diagonal_one, originIntrinsicResidue, originIntrinsicConstant, originKernelMatrix] using h

theorem originIntrinsicConstant_projection_zero {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    completionU (1 : Matrix (Fin N) (Fin N) ℝ) * originIntrinsicConstant z ρ σ Dt G *
      completionV (1 : Matrix (Fin N) (Fin N) ℝ) = 0 := by
  have h := originLift_projection_zero (fun _ => (1 : ℝ))
    (originActualConstantKernel z ρ σ Dt G)
    (originActualConstantKernel_projection_zero z ρ σ Dt G)
  simpa only [Matrix.diagonal_one, originIntrinsicResidue, originIntrinsicConstant, originKernelMatrix] using h

end FMSA.ExactMSA.MultiTailMixture
