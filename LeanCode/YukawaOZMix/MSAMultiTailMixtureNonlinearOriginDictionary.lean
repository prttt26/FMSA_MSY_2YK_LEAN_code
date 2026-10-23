import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearMoments
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearCompletion
import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearOriginJet

/-! Low-order origin data of the actual BH amplitude dictionary.
No root, contact symmetry, or species-density inverse is used here. -/
noncomputable section
open Real MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def nonlinearOriginMoment (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (j : Fin N) : ℝ :=
  ∑ m, ρ m * ∑ u,
    ((W z ρ Dt G u m j + C z ρ σ Dt G u m j) / (z u)^2 -
      σ m * (W z ρ Dt G u m j - C z ρ σ Dt G u m j) / (2 * z u))

theorem nonlinearOriginMoment_eq_centered_moment
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (j : Fin N) :
    nonlinearOriginMoment z ρ σ Dt G j =
      nonlinearN z ρ σ Dt G j + σ j / 2 * nonlinearM z ρ σ Dt G j := by
  rw [← nonlinearN_tail_centered_moment z ρ σ Dt G hz j]
  unfold nonlinearOriginMoment
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  field_simp [hz u] <;> ring

theorem nonlinearB_origin_moment_dictionary
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (j : Fin N) :
    nonlinearB z ρ σ Dt G j = π / vacMix ρ σ * σ j +
      (2 * (π / vacMix ρ σ)) * nonlinearOriginMoment z ρ σ Dt G j := by
  rw [nonlinearOriginMoment_eq_centered_moment z ρ σ Dt G hz]
  unfold nonlinearB
  ring

theorem amplitudeA_origin_moment_dictionary
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hv : vacMix ρ σ ≠ 0) (j : Fin N) :
    amplitudeA z ρ σ Dt G j =
      (2 * (π / vacMix ρ σ)) * (1 + nonlinearM z ρ σ Dt G j) +
      (π / vacMix ρ σ) * xi2 ρ σ * nonlinearB z ρ σ Dt G j := by
  rw [amplitudeA_moment_dictionary]
  unfold Qppphys nonlinearB
  field_simp [hv]
  ring

/-- This is precisely the coefficient of the possible simple pole in the
Lagrangian projection after removing the HS reference. -/
theorem nonlinearOrigin_projected_pole_coefficient_zero
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (i j : Fin N) :
    -2 * σ i * nonlinearB z ρ σ Dt G j +
      2 * (π / vacMix ρ σ * σ i) * σ j +
      4 * (π / vacMix ρ σ * σ i) * nonlinearOriginMoment z ρ σ Dt G j = 0 := by
  rw [nonlinearB_origin_moment_dictionary z ρ σ Dt G hz]
  ring

def nonlinearDensityFunctional (ρ : Fin N → ℝ) : (Fin N → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ m, ρ m * f m
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring

def nonlinearOriginCmoment (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (p : ℕ) (m j : Fin N) : ℝ :=
  ∑ u, C z ρ σ Dt G u m j / (z u)^p

def nonlinearOriginWmoment (z : ι → ℝ) (ρ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (p : ℕ) (m j : Fin N) : ℝ :=
  ∑ u, W z ρ Dt G u m j / (z u)^p

theorem nonlinearOrigin_mass_functional
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (j : Fin N) :
    nonlinearDensityFunctional ρ (fun m =>
      σ m * nonlinearOriginCmoment z ρ σ Dt G 0 m j +
      nonlinearOriginWmoment z ρ Dt G 1 m j +
      nonlinearOriginCmoment z ρ σ Dt G 1 m j) =
        -nonlinearM z ρ σ Dt G j := by
  rw [← nonlinearM_tail_mass z ρ σ Dt G hz j]
  change (∑ m, ρ m * _) = _
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  simp only [nonlinearOriginCmoment, nonlinearOriginWmoment, pow_zero,
    pow_one, div_one, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem nonlinearOrigin_centered_functional
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (j : Fin N) :
    nonlinearDensityFunctional ρ (fun m =>
      nonlinearOriginWmoment z ρ Dt G 2 m j +
      nonlinearOriginCmoment z ρ σ Dt G 2 m j -
      σ m * (nonlinearOriginWmoment z ρ Dt G 1 m j -
        nonlinearOriginCmoment z ρ σ Dt G 1 m j) / 2) =
        nonlinearOriginMoment z ρ σ Dt G j := by
  change (∑ m, ρ m * _) = _
  unfold nonlinearOriginMoment
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  simp only [nonlinearOriginCmoment, nonlinearOriginWmoment, pow_one,
    Finset.mul_sum, Finset.sum_mul, div_eq_mul_inv,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  field_simp [hz u] <;> ring

/-- The actual BH amplitude dictionary cancels the remaining order-three
origin coefficient of the HS-normalized block kernel. -/
theorem nonlinearOrigin_third_coefficient_zero
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (hv : vacMix ρ σ ≠ 0) (i j : Fin N) :
    originJetH3 (amplitudeA z ρ σ Dt G j) +
      originJetD3 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) +
      originJetIntegral (nonlinearDensityFunctional ρ) (fun m =>
        originJetD1 (π/vacMix ρ σ) (σ i) (σ m) *
          originJetH2 (σ m) (amplitudeA z ρ σ Dt G j) (nonlinearB z ρ σ Dt G j) +
        originJetD2 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) (σ m) *
          originJetH1 (σ m) (nonlinearB z ρ σ Dt G j)
            (nonlinearOriginCmoment z ρ σ Dt G 0 m j) +
        originJetD3 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) *
          originJetH0 (nonlinearOriginCmoment z ρ σ Dt G 1 m j)
            (nonlinearOriginWmoment z ρ Dt G 1 m j)) = 0 := by
  exact originJet_third_coefficient_zero _ _ _ _ _ _ (nonlinearM z ρ σ Dt G j)
    _ _ _ _ rfl (nonlinearOrigin_mass_functional z ρ σ Dt G hz j)
    (amplitudeA_origin_moment_dictionary z ρ σ Dt G hv j)

theorem nonlinearOrigin_second_coefficient_zero
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (hv : vacMix ρ σ ≠ 0) (i j : Fin N) :
    originJetH2 (σ i) (amplitudeA z ρ σ Dt G j) (nonlinearB z ρ σ Dt G j) +
      originJetD2 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) (σ j) +
      originJetIntegral (nonlinearDensityFunctional ρ) (fun m =>
        originJetD1 (π/vacMix ρ σ) (σ i) (σ m) *
          originJetH1 (σ m) (nonlinearB z ρ σ Dt G j)
            (nonlinearOriginCmoment z ρ σ Dt G 0 m j) +
        originJetD2 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) (σ m) *
          originJetH0 (nonlinearOriginCmoment z ρ σ Dt G 1 m j)
            (nonlinearOriginWmoment z ρ Dt G 1 m j) +
        originJetD3 (π/vacMix ρ σ) (xi2 ρ σ) (σ i) *
          originJetHplus1 (nonlinearOriginCmoment z ρ σ Dt G 2 m j)
            (nonlinearOriginWmoment z ρ Dt G 2 m j)) = 0 := by
  exact originJet_second_coefficient_zero _ _ _ _ _ _ _
    (nonlinearM z ρ σ Dt G j) (nonlinearOriginMoment z ρ σ Dt G j)
    _ _ _ _ _ _ rfl (nonlinearOrigin_mass_functional z ρ σ Dt G hz j)
    (nonlinearOrigin_centered_functional z ρ σ Dt G hz j)
    (amplitudeA_origin_moment_dictionary z ρ σ Dt G hv j)
    (nonlinearB_origin_moment_dictionary z ρ σ Dt G hz j)

theorem nonlinearOrigin_residue_lagrangian
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, z u ≠ 0) (i j : Fin N) :
    let F := originJetH1 (σ i) (nonlinearB z ρ σ Dt G j)
        (nonlinearOriginCmoment z ρ σ Dt G 0 i j) +
      originJetD1 (π/vacMix ρ σ) (σ i) (σ j) +
      originJetIntegral (nonlinearDensityFunctional ρ) (fun m =>
        originJetResidueProduct (π/vacMix ρ σ) (xi2 ρ σ) (σ i) (σ m)
          (nonlinearOriginCmoment z ρ σ Dt G 1 m j)
          (nonlinearOriginCmoment z ρ σ Dt G 2 m j)
          (nonlinearOriginCmoment z ρ σ Dt G 3 m j)
          (nonlinearOriginWmoment z ρ Dt G 1 m j)
          (nonlinearOriginWmoment z ρ Dt G 2 m j)
          (nonlinearOriginWmoment z ρ Dt G 3 m j))
    F = !![-F 1 0, -F 1 0; F 1 0, F 1 0] := by
  exact originJet_residue_lagrangian _ _ _ _ _ _
    (nonlinearOriginMoment z ρ σ Dt G j) _ _ _ _ _ _ _ _
    (nonlinearOrigin_centered_functional z ρ σ Dt G hz j)
    (nonlinearB_origin_moment_dictionary z ρ σ Dt G hz j)

end FMSA.ExactMSA.MultiTailMixture
