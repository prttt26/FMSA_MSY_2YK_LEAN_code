import LeanCode.YukawaOZMix.MSAMultiTailMixtureHSPairSymbolAlgebra
import LeanCode.HSMixture.PhysHSMixWindowing

/-! Actual recentered HS coefficient and finite-column moment dictionaries.
These are integrals of the actual row kernel, with the row diameter retained.
They do not assert the reference OZ equation. -/
noncomputable section
open MeasureTheory Set Real
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

theorem hsPair_Q0_decomposition (ρ σ : Fin N → ℝ) (i j : Fin N) :
    Q0phys ρ σ i j = Qppphys ρ σ j j*σ i/2+Real.pi*σ j/vacMix ρ σ := by
  unfold Q0phys Qppphys
  ring

theorem rdfRecenteredHSQ_rank_two (ρ σ : Fin N → ℝ) (i j : Fin N)
    (t : ℝ) (ht : t ≤ σ i) :
    rdfRecenteredHSQ ρ σ i j t =
      (t-σ i)*(Qppphys ρ σ j j*t/2+Real.pi*σ j/vacMix ρ σ) := by
  rw [rdfRecenteredHSQ, min_eq_left ht, hsPair_Q0_decomposition]
  ring

theorem rdfRecenteredHSQ_mass (ρ σ : Fin N → ℝ) (i j : Fin N)
    (hσ : 0 ≤ σ i) :
    (∫ t in (0 : ℝ)..σ i, rdfRecenteredHSQ ρ σ i j t) =
      -Q0phys ρ σ i j*σ i^2/2+Qppphys ρ σ j j*σ i^3/6 := by
  have he : (∫ t in (0 : ℝ)..σ i, rdfRecenteredHSQ ρ σ i j t) =
      ∫ t in (0 : ℝ)..σ i,
        Q0phys ρ σ i j*(t-σ i)+Qppphys ρ σ j j*(t-σ i)^2/2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hσ] at ht
    simp only [rdfRecenteredHSQ, min_eq_left ht.2]
    ring
  rw [he, FMSA.HSMix.baxterQuad_integral]
  ring

theorem rdfRecenteredHSQ_first_moment (ρ σ : Fin N → ℝ) (i j : Fin N)
    (hσ : 0 ≤ σ i) :
    (∫ t in (0 : ℝ)..σ i, t*rdfRecenteredHSQ ρ σ i j t) =
      -Q0phys ρ σ i j*σ i^3/6+Qppphys ρ σ j j*σ i^4/24 := by
  have he : (∫ t in (0 : ℝ)..σ i, t*rdfRecenteredHSQ ρ σ i j t) =
      ∫ t in (0 : ℝ)..σ i,
        t*(Q0phys ρ σ i j*(t-σ i)+Qppphys ρ σ j j*(t-σ i)^2/2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hσ] at ht
    simp only [rdfRecenteredHSQ, min_eq_left ht.2]
    ring
  rw [he, FMSA.HSMix.baxterQuad1_integral]
  ring

theorem rdfRecenteredHSQ_column_mass (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (j : Fin N) :
    (∑ m, ρ m*∫ t in (0 : ℝ)..σ m, rdfRecenteredHSQ ρ σ m j t) =
      -Qppphys ρ σ j j*(∑ m, ρ m*σ m^3)/12-
        (Real.pi*σ j/vacMix ρ σ)*xi2 ρ σ/2 := by
  simp_rw [rdfRecenteredHSQ_mass ρ σ _ j (hσ _), hsPair_Q0_decomposition]
  unfold xi2
  rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem rdfRecenteredHSQ_column_centered_moment (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (j : Fin N) :
    (∑ m, ρ m*((∫ t in (0 : ℝ)..σ m, t*rdfRecenteredHSQ ρ σ m j t)-
      σ m/2*(∫ t in (0 : ℝ)..σ m, rdfRecenteredHSQ ρ σ m j t))) =
      (Real.pi*σ j/vacMix ρ σ)*(∑ m, ρ m*σ m^3)/12 := by
  simp_rw [rdfRecenteredHSQ_mass ρ σ _ j (hσ _),
    rdfRecenteredHSQ_first_moment ρ σ _ j (hσ _), hsPair_Q0_decomposition]
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem rdfRecenteredHSQ_column_mass_identity (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hv : vacMix ρ σ ≠ 0) (j : Fin N) :
    1-(∑ m, ρ m*∫ t in (0 : ℝ)..σ m, rdfRecenteredHSQ ρ σ m j t) =
      Qppphys ρ σ j j/(2*Real.pi) := by
  rw [rdfRecenteredHSQ_column_mass ρ σ hσ j]
  have hm : Real.pi*(∑ m, ρ m*σ m^3)=6*(1-vacMix ρ σ) := by
    unfold vacMix etaMix
    ring
  unfold Qppphys
  field_simp [hv, Real.pi_ne_zero]
  linear_combination 2*(2*vacMix ρ σ+Real.pi*xi2 ρ σ*σ j)*hm

theorem rdfRecenteredHSQ_column_contact_identity (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hv : vacMix ρ σ ≠ 0) (i j : Fin N) :
    edgeHi σ i j+(∑ m, ρ m*((∫ t in (0 : ℝ)..σ m,
      t*rdfRecenteredHSQ ρ σ m i t)-edgeHi σ m j*
        (∫ t in (0 : ℝ)..σ m, rdfRecenteredHSQ ρ σ m i t))) =
      σ i/(2*vacMix ρ σ)+σ j*Qppphys ρ σ i i/(4*Real.pi) := by
  have he : (∑ m, ρ m*((∫ t in (0 : ℝ)..σ m,
      t*rdfRecenteredHSQ ρ σ m i t)-edgeHi σ m j*
        (∫ t in (0 : ℝ)..σ m, rdfRecenteredHSQ ρ σ m i t))) =
      (∑ m, ρ m*((∫ t in (0 : ℝ)..σ m, t*rdfRecenteredHSQ ρ σ m i t)-
        σ m/2*(∫ t in (0 : ℝ)..σ m, rdfRecenteredHSQ ρ σ m i t)))-
      σ j/2*(∑ m, ρ m*∫ t in (0 : ℝ)..σ m, rdfRecenteredHSQ ρ σ m i t) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    unfold edgeHi
    ring
  rw [he, rdfRecenteredHSQ_column_centered_moment ρ σ hσ i]
  have hmass := rdfRecenteredHSQ_column_mass_identity ρ σ hσ hv i
  have hm : Real.pi*(∑ m, ρ m*σ m^3)=6*(1-vacMix ρ σ) := by
    unfold vacMix etaMix
    ring
  unfold edgeHi
  rw [show (∑ m, ρ m*∫ t in (0 : ℝ)..σ m, rdfRecenteredHSQ ρ σ m i t) =
    1-Qppphys ρ σ i i/(2*Real.pi) from by linarith [hmass]]
  rw [show (∑ m, ρ m*σ m^3)=6*(1-vacMix ρ σ)/Real.pi from by
    apply (eq_div_iff Real.pi_ne_zero).mpr
    simpa only [mul_comm] using hm]
  field_simp [hv, Real.pi_ne_zero]
  ring

theorem hsPair_physical_symbol_relation (ρ σ : Fin N → ℝ) :
    (2*Real.pi/vacMix ρ σ)*xi2 ρ σ =
      4*(Real.pi*xi2 ρ σ/(2*vacMix ρ σ)) := by ring

end FMSA.ExactMSA.MultiTailMixture
