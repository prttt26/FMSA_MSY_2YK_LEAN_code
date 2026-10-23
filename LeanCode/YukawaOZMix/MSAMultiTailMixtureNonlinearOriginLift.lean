import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearOriginDictionary

/-! Lift block-position kernels to actual species matrices, retaining both
density factors. Multiplication inserts precisely one species-density sum. -/
noncomputable section
open Real MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

def originLift (ρ : Fin N → ℝ)
    (F : Fin N → Fin N → Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  Matrix.fromBlocks
    (fun i j => ρ i*F i j 0 0) (fun i j => ρ i*F i j 0 1*ρ j)
    (fun i j => F i j 1 0) (fun i j => F i j 1 1*ρ j)

theorem originJetIntegral_zero (ρ : Fin N → ℝ) :
    originJetIntegral (nonlinearDensityFunctional ρ) (fun _ => 0) = 0 := by
  ext a b
  change (nonlinearDensityFunctional ρ) 0 = 0
  exact map_zero _

theorem originLift_zero (ρ : Fin N → ℝ) : originLift ρ (fun _ _ => 0) = 0 := by
  ext i j
  cases i <;> cases j <;> simp [originLift, Matrix.fromBlocks]

theorem originLift_add (ρ : Fin N → ℝ)
    (F H : Fin N → Fin N → Matrix (Fin 2) (Fin 2) ℝ) :
    originLift ρ (fun i j => F i j+H i j) = originLift ρ F+originLift ρ H := by
  ext i j
  cases i <;> cases j <;> simp [originLift, Matrix.fromBlocks, mul_add, add_mul]

theorem originLift_smul (ρ : Fin N → ℝ) (s : ℝ)
    (F : Fin N → Fin N → Matrix (Fin 2) (Fin 2) ℝ) :
    originLift ρ (fun i j => s • F i j) = s • originLift ρ F := by
  ext i j
  cases i <;> cases j <;> simp [originLift, Matrix.fromBlocks, smul_eq_mul] <;> ring

theorem originLift_mul (ρ : Fin N → ℝ)
    (F H : Fin N → Fin N → Matrix (Fin 2) (Fin 2) ℝ) :
    originLift ρ F * originLift ρ H =
      originLift ρ (fun i j => originJetIntegral (nonlinearDensityFunctional ρ)
        (fun m => F i m * H m j)) := by
  rw [originLift, originLift, Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j
  all_goals
    simp only [originLift, Matrix.fromBlocks, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
      Matrix.add_apply, Matrix.mul_apply,
      originJetIntegral, nonlinearDensityFunctional, LinearMap.coe_mk, AddHom.coe_mk,
      Fin.sum_univ_two]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring

def originActualH3 {ι : Type*} [Fintype ι] (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) :=
  originLift ρ (fun _ j => originJetH3 (amplitudeA z ρ σ Dt G j))
def originActualH2 {ι : Type*} [Fintype ι] (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) :=
  originLift ρ (fun i j => originJetH2 (σ i) (amplitudeA z ρ σ Dt G j)
    (nonlinearB z ρ σ Dt G j))
def originActualH1 {ι : Type*} [Fintype ι] (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) :=
  originLift ρ (fun i j => originJetH1 (σ i) (nonlinearB z ρ σ Dt G j)
    (nonlinearOriginCmoment z ρ σ Dt G 0 i j))
def originActualH0 {ι : Type*} [Fintype ι] (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) :=
  originLift ρ (fun i j => originJetH0 (nonlinearOriginCmoment z ρ σ Dt G 1 i j)
    (nonlinearOriginWmoment z ρ Dt G 1 i j))
def originActualHp1 {ι : Type*} [Fintype ι] (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) :=
  originLift ρ (fun i j => originJetHplus1 (nonlinearOriginCmoment z ρ σ Dt G 2 i j)
    (nonlinearOriginWmoment z ρ Dt G 2 i j))
def originActualHp2 {ι : Type*} [Fintype ι] (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) :=
  originLift ρ (fun i j => originJetHplus2 (nonlinearOriginCmoment z ρ σ Dt G 3 i j)
    (nonlinearOriginWmoment z ρ Dt G 3 i j))
def originActualHp3 {ι : Type*} [Fintype ι] (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) :=
  originLift ρ (fun i j => originJetHplus1 (nonlinearOriginCmoment z ρ σ Dt G 4 i j)
    (nonlinearOriginWmoment z ρ Dt G 4 i j))
def originActualD1 (ρ σ : Fin N → ℝ) :=
  originLift ρ (fun i j => originJetD1 (Real.pi/vacMix ρ σ) (σ i) (σ j))
def originActualD2 (ρ σ : Fin N → ℝ) :=
  originLift ρ (fun i j => originJetD2 (Real.pi/vacMix ρ σ)
    (xi2 ρ σ) (σ i) (σ j))
def originActualD3 (ρ σ : Fin N → ℝ) :=
  originLift ρ (fun i _ => originJetD3 (Real.pi/vacMix ρ σ)
    (xi2 ρ σ) (σ i))

theorem originActual_highest_products_zero {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    originActualD3 ρ σ * originActualH3 z ρ σ Dt G = 0 ∧
    originActualD2 ρ σ * originActualH3 z ρ σ Dt G +
      originActualD3 ρ σ * originActualH2 z ρ σ Dt G = 0 ∧
    originActualD1 ρ σ * originActualH3 z ρ σ Dt G +
      originActualD2 ρ σ * originActualH2 z ρ σ Dt G +
      originActualD3 ρ σ * originActualH1 z ρ σ Dt G = 0 := by
  have h (i m j : Fin N) := originJet_highest_three_products_zero
    (Real.pi/vacMix ρ σ) (xi2 ρ σ) (σ i) (σ m)
    (amplitudeA z ρ σ Dt G j) (nonlinearB z ρ σ Dt G j)
    (nonlinearOriginCmoment z ρ σ Dt G 0 m j)
  unfold originActualD1 originActualD2 originActualD3 originActualH1 originActualH2 originActualH3
  simp only [originLift_mul]
  constructor
  · have hh (i j : Fin N) := (h i i j).1
    simp_rw [hh]
    rw [originJetIntegral_zero, originLift_zero]
  constructor
  · rw [← originLift_add]
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
    rw [hz, originLift_zero]
  · rw [← originLift_add, ← originLift_add]
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
    rw [hz, originLift_zero]

theorem originActual_third_coefficient_zero {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (hv : vacMix ρ σ ≠ 0) :
    originActualH3 z ρ σ Dt G + originActualD3 ρ σ +
      originActualD1 ρ σ * originActualH2 z ρ σ Dt G +
      originActualD2 ρ σ * originActualH1 z ρ σ Dt G +
      originActualD3 ρ σ * originActualH0 z ρ σ Dt G = 0 := by
  unfold originActualH3 originActualD3 originActualD1 originActualD2 originActualH2
    originActualH1 originActualH0
  simp only [originLift_mul, ← originLift_add]
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
  rw [hh, originLift_zero]

theorem originActual_second_coefficient_zero {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (hv : vacMix ρ σ ≠ 0) :
    originActualH2 z ρ σ Dt G + originActualD2 ρ σ +
      originActualD1 ρ σ * originActualH1 z ρ σ Dt G +
      originActualD2 ρ σ * originActualH0 z ρ σ Dt G +
      originActualD3 ρ σ * originActualHp1 z ρ σ Dt G = 0 := by
  unfold originActualH2 originActualD2 originActualD1 originActualD3 originActualH1
    originActualH0 originActualHp1
  simp only [originLift_mul, ← originLift_add]
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
  rw [hh, originLift_zero]

theorem originLift_lagrangian (ρ : Fin N → ℝ)
    (F : Fin N → Fin N → Matrix (Fin 2) (Fin 2) ℝ)
    (hF : ∀ i j, F i j = !![-F i j 1 0, -F i j 1 0; F i j 1 0, F i j 1 0]) :
    originLift ρ F = completionV (Matrix.diagonal ρ) *
      Matrix.of (fun i j => F i j 1 0) * completionU (Matrix.diagonal ρ) := by
  have h00 (i j : Fin N) : F i j 0 0 = -F i j 1 0 := by
    simpa using congrFun (congrFun (hF i j) 0) 0
  have h01 (i j : Fin N) : F i j 0 1 = -F i j 1 0 := by
    simpa using congrFun (congrFun (hF i j) 0) 1
  have h11 (i j : Fin N) : F i j 1 1 = F i j 1 0 := by
    simpa using congrFun (congrFun (hF i j) 1) 1
  simp only [completionV, completionU, Matrix.fromRows_mul, Matrix.mul_fromCols]
  ext i j
  cases i <;> cases j <;>
    simp [originLift, h00, h01, h11, Matrix.fromBlocks,
      Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem originLift_projection_zero (ρ : Fin N → ℝ)
    (F : Fin N → Fin N → Matrix (Fin 2) (Fin 2) ℝ)
    (hF : ∀ i j, F i j 0 0+F i j 1 0-F i j 0 1-F i j 1 1 = 0) :
    completionU (Matrix.diagonal ρ) * originLift ρ F *
      completionV (Matrix.diagonal ρ) = 0 := by
  simp only [completionU, completionV, originLift, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows, Matrix.one_mul, Matrix.mul_one]
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply]
  linear_combination -ρ i*ρ j*(hF i j)

def originActualResidueKernel {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) (i j : Fin N) :=
  originJetH1 (σ i) (nonlinearB z ρ σ Dt G j) (nonlinearOriginCmoment z ρ σ Dt G 0 i j) +
    originJetD1 (π/vacMix ρ σ) (σ i) (σ j) +
    originJetIntegral (nonlinearDensityFunctional ρ) (fun m =>
      originJetResidueProduct (π/vacMix ρ σ) (xi2 ρ σ) (σ i) (σ m)
        (nonlinearOriginCmoment z ρ σ Dt G 1 m j) (nonlinearOriginCmoment z ρ σ Dt G 2 m j)
        (nonlinearOriginCmoment z ρ σ Dt G 3 m j) (nonlinearOriginWmoment z ρ Dt G 1 m j)
        (nonlinearOriginWmoment z ρ Dt G 2 m j) (nonlinearOriginWmoment z ρ Dt G 3 m j))

def originActualConstantKernel {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) (i j : Fin N) :=
  originJetH0 (nonlinearOriginCmoment z ρ σ Dt G 1 i j) (nonlinearOriginWmoment z ρ Dt G 1 i j) +
    originJetIntegral (nonlinearDensityFunctional ρ) (fun m =>
      originJetD1 (π/vacMix ρ σ) (σ i) (σ m) *
        originJetHplus1 (nonlinearOriginCmoment z ρ σ Dt G 2 m j) (nonlinearOriginWmoment z ρ Dt G 2 m j) +
      originJetD2 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) (σ m) *
        originJetHplus2 (nonlinearOriginCmoment z ρ σ Dt G 3 m j) (nonlinearOriginWmoment z ρ Dt G 3 m j) +
      originJetD3 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) *
        originJetHplus1 (nonlinearOriginCmoment z ρ σ Dt G 4 m j) (nonlinearOriginWmoment z ρ Dt G 4 m j))

def originActualResidue {ι : Type*} [Fintype ι] (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) := originLift ρ (originActualResidueKernel z ρ σ Dt G)

def originActualConstant {ι : Type*} [Fintype ι] (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) :=
  (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) +
    originLift ρ (originActualConstantKernel z ρ σ Dt G)

theorem originActualResidue_expanded {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    originActualResidue z ρ σ Dt G =
      originActualH1 z ρ σ Dt G + originActualD1 ρ σ +
      originActualD1 ρ σ * originActualH0 z ρ σ Dt G +
      originActualD2 ρ σ * originActualHp1 z ρ σ Dt G +
      originActualD3 ρ σ * originActualHp2 z ρ σ Dt G := by
  unfold originActualResidue originActualH1 originActualD1 originActualD2 originActualD3
    originActualH0 originActualHp1 originActualHp2
  simp only [originLift_mul, ← originLift_add]
  congr 1
  funext i j a b
  simp [originActualResidueKernel, originJetResidueProduct, Matrix.add_apply,
    originJetIntegral, nonlinearDensityFunctional, mul_add, Finset.sum_add_distrib, add_assoc]

theorem originActualConstant_expanded {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    originActualConstant z ρ σ Dt G =
      1+originActualH0 z ρ σ Dt G +
      originActualD1 ρ σ * originActualHp1 z ρ σ Dt G +
      originActualD2 ρ σ * originActualHp2 z ρ σ Dt G +
      originActualD3 ρ σ * originActualHp3 z ρ σ Dt G := by
  unfold originActualConstant originActualH0 originActualD1 originActualD2 originActualD3
    originActualHp1 originActualHp2 originActualHp3
  simp only [originLift_mul, add_assoc, ← originLift_add]
  apply congrArg (fun F : Fin N → Fin N → Matrix (Fin 2) (Fin 2) ℝ =>
    (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) + originLift ρ F)
  funext i j a b
  simp [originActualConstantKernel, Matrix.add_apply,
    originJetIntegral, nonlinearDensityFunctional, mul_add, Finset.sum_add_distrib, add_assoc]

theorem originActualResidue_lagrangian {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) :
    ∃ X : Matrix (Fin N) (Fin N) ℝ,
      originActualResidue z ρ σ Dt G =
        completionV (Matrix.diagonal ρ)*X*completionU (Matrix.diagonal ρ) := by
  refine ⟨Matrix.of (fun i j => originActualResidueKernel z ρ σ Dt G i j 1 0), ?_⟩
  apply originLift_lagrangian
  intro i j
  exact nonlinearOrigin_residue_lagrangian z ρ σ Dt G hz i j

theorem originActualConstant_projection_zero {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    completionU (Matrix.diagonal ρ) * originActualConstant z ρ σ Dt G *
      completionV (Matrix.diagonal ρ) = 0 := by
  have h (i j : Fin N) :
      let F := originActualConstantKernel z ρ σ Dt G i j
      F 0 0+F 1 0-F 0 1-F 1 1 = 0 := by
    let K := fun m => originJetD1 (π/vacMix ρ σ) (σ i) (σ m) *
        originJetHplus1 (nonlinearOriginCmoment z ρ σ Dt G 2 m j) (nonlinearOriginWmoment z ρ Dt G 2 m j) +
      originJetD2 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) (σ m) *
        originJetHplus2 (nonlinearOriginCmoment z ρ σ Dt G 3 m j) (nonlinearOriginWmoment z ρ Dt G 3 m j) +
      originJetD3 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) *
        originJetHplus1 (nonlinearOriginCmoment z ρ σ Dt G 4 m j) (nonlinearOriginWmoment z ρ Dt G 4 m j)
    have hp (m : Fin N) : K m 0 0+K m 1 0-K m 0 1-K m 1 1 = 0 := by
      have he := originJet_constant_lagrangian_projection_zero
        (π/vacMix ρ σ) (xi2 ρ σ) (σ i) (σ m) 0
        (nonlinearOriginCmoment z ρ σ Dt G 2 m j)
        (nonlinearOriginCmoment z ρ σ Dt G 3 m j)
        (nonlinearOriginCmoment z ρ σ Dt G 4 m j) 0
        (nonlinearOriginWmoment z ρ Dt G 2 m j)
        (nonlinearOriginWmoment z ρ Dt G 3 m j)
        (nonlinearOriginWmoment z ρ Dt G 4 m j)
      simpa [originJetH0, K] using he
    have hs : (∑ m, ρ m*(K m 0 0+K m 1 0-K m 0 1-K m 1 1)) = 0 := by
      simp only [hp, mul_zero, Finset.sum_const_zero]
    dsimp only
    change (originJetH0 _ _ + originJetIntegral (nonlinearDensityFunctional ρ) K) 0 0 +
      (originJetH0 _ _ + originJetIntegral (nonlinearDensityFunctional ρ) K) 1 0 -
      (originJetH0 _ _ + originJetIntegral (nonlinearDensityFunctional ρ) K) 0 1 -
      (originJetH0 _ _ + originJetIntegral (nonlinearDensityFunctional ρ) K) 1 1 = 0
    simp only [Matrix.add_apply, originJetIntegral, nonlinearDensityFunctional,
      LinearMap.coe_mk, AddHom.coe_mk, mul_add, mul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs ⊢
    simp [originJetH0]
    linear_combination hs
  unfold originActualConstant
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, completionU_mul_completionV,
    originLift_projection_zero ρ _ h, add_zero]

theorem originActualConstantKernel_projection_zero {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N) :
    ∀ i j, let F := originActualConstantKernel z ρ σ Dt G i j
      F 0 0+F 1 0-F 0 1-F 1 1 = 0 := by
  have h (i j : Fin N) :
      let F := originActualConstantKernel z ρ σ Dt G i j
      F 0 0+F 1 0-F 0 1-F 1 1 = 0 := by
    let K := fun m => originJetD1 (π/vacMix ρ σ) (σ i) (σ m) *
        originJetHplus1 (nonlinearOriginCmoment z ρ σ Dt G 2 m j) (nonlinearOriginWmoment z ρ Dt G 2 m j) +
      originJetD2 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) (σ m) *
        originJetHplus2 (nonlinearOriginCmoment z ρ σ Dt G 3 m j) (nonlinearOriginWmoment z ρ Dt G 3 m j) +
      originJetD3 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) *
        originJetHplus1 (nonlinearOriginCmoment z ρ σ Dt G 4 m j) (nonlinearOriginWmoment z ρ Dt G 4 m j)
    have hp (m : Fin N) : K m 0 0+K m 1 0-K m 0 1-K m 1 1 = 0 := by
      have he := originJet_constant_lagrangian_projection_zero
        (π/vacMix ρ σ) (xi2 ρ σ) (σ i) (σ m) 0
        (nonlinearOriginCmoment z ρ σ Dt G 2 m j)
        (nonlinearOriginCmoment z ρ σ Dt G 3 m j)
        (nonlinearOriginCmoment z ρ σ Dt G 4 m j) 0
        (nonlinearOriginWmoment z ρ Dt G 2 m j)
        (nonlinearOriginWmoment z ρ Dt G 3 m j)
        (nonlinearOriginWmoment z ρ Dt G 4 m j)
      simpa [originJetH0, K] using he
    have hs : (∑ m, ρ m*(K m 0 0+K m 1 0-K m 0 1-K m 1 1)) = 0 := by
      simp only [hp, mul_zero, Finset.sum_const_zero]
    dsimp only
    change (originJetH0 _ _ + originJetIntegral (nonlinearDensityFunctional ρ) K) 0 0 +
      (originJetH0 _ _ + originJetIntegral (nonlinearDensityFunctional ρ) K) 1 0 -
      (originJetH0 _ _ + originJetIntegral (nonlinearDensityFunctional ρ) K) 0 1 -
      (originJetH0 _ _ + originJetIntegral (nonlinearDensityFunctional ρ) K) 1 1 = 0
    simp only [Matrix.add_apply, originJetIntegral, nonlinearDensityFunctional,
      LinearMap.coe_mk, AddHom.coe_mk, mul_add, mul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs ⊢
    simp [originJetH0]
    linear_combination hs
  exact h

end FMSA.ExactMSA.MultiTailMixture
