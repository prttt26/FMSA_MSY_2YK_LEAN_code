import LeanCode.YukawaOZMix.MSAMultiTailMixtureHSPairMatrixSymbol

/-! Actual Fourier OZ for the pair-contact HS candidate, using the actual
weighted Volterra budget, source transform and physical symbol relation. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0 FMSA.HardSphere
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def rdfHSPairH (ρ σ : Fin N → ℝ) (k : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => (radial_fourier (rdfHSPairCandidate ρ σ i j) k : ℂ))

def hsPairCompletedZ (ρ σ : Fin N → ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  rdfMatrixLaplace (rdfHSPairExterior ρ σ) s+hsPairBackground σ s

theorem rdfReferenceC_eq_pair_HS_symbol (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 < ρ i)
    (hσ : ∀ i, 0 < σ i) (k : ℝ) (hk : k ≠ 0) :
    rdfReferenceC z ρ σ k=hsPairHSBaxterC ρ σ (Complex.I*k) := by
  have hbase (w : ℝ) (hw : w ≠ 0) (a b : Fin N) :
      fourierQ z σ (amplitudeA z ρ σ 0 (baseSeed z ρ σ)) (amplitudeQp z ρ σ 0 (baseSeed z ρ σ))
        (W z ρ 0 (baseSeed z ρ σ)) (C z ρ σ 0 (baseSeed z ρ σ)) w a b =
        complexHSQ ρ σ (Complex.I*w) a b := by
    rw [fourierQ_eq_QhatComplex z hz σ _ _ _ _ (fun i => (hσ i).le) w hw,
      QhatComplex_zero_eq_phase_HS]
    rfl
  ext i j
  rw [rdfReferenceC, Matrix.of_apply,
    ← spectralBaxterC_zero_eq_ordered_radial z ρ σ hz hv hρ hσ k hk i j]
  simp only [spectralBaxterC, fourierQ_conj]
  simp only [hbase k hk, hbase (-k) (neg_ne_zero.mpr hk), Complex.ofReal_neg,
    mul_neg, hsPairHSBaxterC, Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply]
  rw [Matrix.mul_apply (M := complexHSQ ρ σ (Complex.I*k)*Matrix.diagonal (fun i => (ρ i : ℂ)))]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem rdfHSPairH_eq_phase_difference (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 < σ i)
    (δ : ℝ) (hδ : 0 < δ) (hb : rdfWeightedKernelBudget ρ σ δ < 1)
    (k : ℝ) (hk : k ≠ 0) :
    rdfHSPairH ρ σ k=(2*Real.pi/(Complex.I*k)) •
      (rdfPhase σ (-(Complex.I*k))*hsPairCompletedZ ρ σ (-(Complex.I*k))*rdfPhase σ (-(Complex.I*k))-
        rdfPhase σ (Complex.I*k)*hsPairCompletedZ ρ σ (Complex.I*k)*rdfPhase σ (Complex.I*k)) := by
  ext i j
  have hR : 0 < edgeHi σ i j := by unfold edgeHi; linarith [hσ i, hσ j]
  have hm := rdfHSPairMoment_positive_laplace ρ σ i j hR δ hδ hb (-k) (neg_ne_zero.mpr hk)
  simp only [Complex.ofReal_neg, mul_neg, neg_neg] at hm
  simp only [rdfHSPairH, Matrix.of_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  rw [rdfHSPairCandidate_radial_fourier ρ σ i j δ hδ hb k hk,
    rdfHSPairMoment_positive_laplace ρ σ i j hR δ hδ hb k hk, hm]
  simp only [rdfPhase, Matrix.diagonal_mul, Matrix.mul_diagonal, hsPairCompletedZ, Matrix.add_apply]
  have hp := rdfPhase_contact_product σ (-(Complex.I*k)) i j
  have hn := rdfPhase_contact_product σ (Complex.I*k) i j
  simp only [neg_neg] at hp
  rw [← hp, ← hn]
  ring

theorem hsPair_phase_completed_transfer (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 < ρ i)
    (hσ : ∀ i, 0 < σ i) (δ : ℝ) (hδ : 0 < δ)
    (hb : rdfWeightedKernelBudget ρ σ δ < 1) (k : ℝ) (hk : k ≠ 0) :
    rdfReferenceT z ρ σ k*rdfPhase σ (Complex.I*k)*
      hsPairCompletedZ ρ σ (Complex.I*k)*rdfPhase σ (Complex.I*k) =
      complexHSRightFactor ρ σ (-(Complex.I*k))*rdfPhase σ (Complex.I*k)*
        hsPairSourceMoment ρ σ (Complex.I*k)*rdfPhase σ (Complex.I*k) := by
  have hs0 : Complex.I*(k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk)
  have he := rdfHSPairExterior_completed_transfer ρ σ (fun i => (hσ i).le) hv.ne' δ hδ hb
    (Complex.I*k) (by simp) hs0
  change (rdfRecenteredFactor ρ σ (Complex.I*k)).transpose*hsPairCompletedZ ρ σ (Complex.I*k) = _ at he
  rw [rdfReferenceT_phase z hz ρ σ hv hρ hσ k hk]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (rdfRecenteredFactor ρ σ (Complex.I*k)).transpose, he]

theorem rdfHSPairH_actual_Fourier_OZ (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 < ρ i)
    (hσ : ∀ i, 0 < σ i) (δ : ℝ) (hδ : 0 < δ)
    (hb : rdfWeightedKernelBudget ρ σ δ < 1) (k : ℝ) (hk : k ≠ 0) :
    rdfHSPairH ρ σ k = rdfReferenceC z ρ σ k+
      rdfReferenceC z ρ σ k*Matrix.diagonal (fun i => (ρ i : ℂ))*rdfHSPairH ρ σ k := by
  have hs0 : Complex.I*(k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk)
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hminus := hsPair_phase_completed_transfer z hz ρ σ hv hρ hσ δ hδ hb (-k) (neg_ne_zero.mpr hk)
  simp only [rdfReferenceT, rdfReferenceC_neg, Complex.ofReal_neg, mul_neg, neg_neg] at hminus
  change rdfReferenceT z ρ σ k*rdfPhase σ (-(Complex.I*k))*
      hsPairCompletedZ ρ σ (-(Complex.I*k))*rdfPhase σ (-(Complex.I*k)) = _ at hminus
  have hsymbol := hsPairSourceMoment_factor_difference ρ σ (Complex.I*k) hs0
  have hprod : rdfReferenceT z ρ σ k*rdfHSPairH ρ σ k=rdfReferenceC z ρ σ k := by
    rw [rdfHSPairH_eq_phase_difference ρ σ hσ δ hδ hb k hk, Matrix.mul_smul, Matrix.mul_sub]
    simp only [← Matrix.mul_assoc]
    rw [hminus, hsPair_phase_completed_transfer z hz ρ σ hv hρ hσ δ hδ hb k hk]
    have he := congrArg Neg.neg hsymbol
    simp only [neg_sub, neg_smul, neg_div, neg_neg] at he
    rw [he, smul_smul]
    have hc : (2*Real.pi/(Complex.I*k))*(Complex.I*k/(2*Real.pi))=(1 : ℂ) := by
      field_simp [hs0, hp, hkC]
    rw [hc, one_smul, ← rdfReferenceC_eq_pair_HS_symbol z hz ρ σ hv hρ hσ k hk]
  rw [rdfReferenceT, sub_mul, Matrix.one_mul] at hprod
  exact sub_eq_iff_eq_add.mp hprod

end FMSA.ExactMSA.MultiTailMixture
