import LeanCode.YukawaOZMix.MSAMixtureEqualCoreResidues
import LeanCode.YukawaOZMix.MSAMixtureEqualCorePolynomial

/-! Faithful equality of the original five-coefficient equal-diameter DCF
and the checked unequal-diameter convolution formula, at actual BH roots. -/
noncomputable section
open Real MeasureTheory Set MSAMixture FMSA.MatrixQ0 FMSA.ExactMSA.MixLeg3
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ}

private theorem gForm_sub (a b c d e f g A B C D E F G z r : ℝ) :
    MSAMixtureCoreUneq.gForm a b c d e f g z r-
      MSAMixtureCoreUneq.gForm A B C D E F G z r =
    MSAMixtureCoreUneq.gForm (a-A) (b-B) (c-C) (d-D) (e-E) (f-F) (g-G) z r := by
  unfold MSAMixtureCoreUneq.gForm
  ring

private theorem hs_exp_zero (z : ℝ) (ρ σ : Fin N → ℝ) (i j : Fin N) :
    MSAMixtureCoreUneq.cEmo z ρ σ (A0Vec ρ σ) (qp0Mat ρ σ) 0 0 i j=0 ∧
    MSAMixtureCoreUneq.cEpo z ρ σ (A0Vec ρ σ) (qp0Mat ρ σ) 0 0 i j=0 := by
  simp [MSAMixtureCoreUneq.cEmo, MSAMixtureCoreUneq.cEpo]

theorem legacyEqual_core_pointwise (z sig : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hs : 0 < sig) (hσ : ∀ i, σ i = sig)
    (hρ : ∀ i, 0 ≤ ρ i) (hv : 0 < vacMix ρ σ)
    (hr : MixBHRoot z sig ρ σ Gt Dt K) (hK : ∀ i j, K i j = K j i)
    (i j : Fin N) (r : ℝ) (hr0 : 0 < r) :
    matCoreCorrUneq z ρ σ Gt Dt i j r=matMSACoreCorr z ρ σ Gt Dt K i j r := by
  have hsσ : ∀ i, 0 < σ i := fun i => by rw [hσ i]; exact hs
  have hru := MixBHRootUneq_of_MixBHRoot z sig ρ σ Gt Dt K hσ hr
  have h0 := legacyEqual_core_origin_zero z hz ρ σ Gt Dt K sig hs hσ hv.ne' hru hK i j
  have hhs0 := legacyEqual_core_origin_zero z hz ρ σ
    (baseSeed (fun _ : Unit => z) ρ σ ()) 0 0 sig hs hσ hv.ne'
    (legacyHS_root z hz ρ σ hsσ hρ hv) (by intros; rfl) i j
  simp only [AVec_zero_Dt, qpMat_zero_Dt, Wt_zero_Dt, Ct_zero_Dt] at hhs0
  obtain ⟨hem0, hep0⟩ := hs_exp_zero z ρ σ i j
  rw [hem0, hep0] at hhs0
  have hhs3 : MSAMixtureCoreUneq.cC3o z ρ σ (A0Vec ρ σ) (qp0Mat ρ σ) 0 0 i j=0 := by
    have h := legacyC3_zero z sig ρ σ (AVec z ρ σ Gt 0)
      (qpMat z ρ σ Gt 0) (Wt z ρ Gt 0) (Ct z ρ σ Gt 0) hσ
      (qpMat_equalDiam_rows z sig ρ σ Gt 0 hσ) i j
    simpa only [AVec_zero_Dt, qpMat_zero_Dt, Wt_zero_Dt, Ct_zero_Dt] using h
  obtain ⟨hc1,hc2,hc4,hc3⟩ := legacyEqual_poly_coefficients z sig hz.ne' ρ σ Gt Dt K hσ i j
  obtain ⟨hem,hep⟩ := legacyEqual_exp_coefficients z sig hz.ne' ρ σ Gt Dt K hσ hr hK i j
  have hsij : sigMix σ i j=sig := by unfold sigMix; rw [hσ i,hσ j]; ring
  have hehi : edgeHi σ i j=sig := by unfold edgeHi; rw [hσ i,hσ j]; ring
  have hlam : MSAMixtureCoreUneq.lamA σ i j=0 := by
    unfold MSAMixtureCoreUneq.lamA edgeLo
    rw [hσ i,hσ j]
    simp
  have ho : σ j ≤ σ i := by rw [hσ i,hσ j]
  simp only [matCoreCorrUneq, if_pos ho, hehi, matMSACoreCorr, hsij, coreCorrection]
  by_cases hr : r ≤ sig
  · rw [if_pos hr, if_pos hr]
    simp only [MSAMixtureCoreUneq.matCoreUneq, hlam, if_neg (not_le.mpr hr0)]
    rw [← sub_div, gForm_sub, hc1, hc2, hc4, hc3, hhs3, h0, hhs0, hem, hep, hem0, hep0]
    simp only [sub_zero, sub_self, MSAMixtureCoreUneq.gForm, zero_mul, add_zero]
    unfold coshRatio
    have hp : exp (z*(r-sig))=exp (-z*sig)*exp (z*r) := by
      rw [← exp_add]; congr 1; ring
    have hm : exp (-z*(r+sig))=exp (-z*sig)*exp (-z*r) := by
      rw [← exp_add]; congr 1; ring
    rw [hp,hm]
    field_simp [pi_ne_zero,hr0.ne']
    <;> ring
  · rw [if_neg hr, if_neg hr]

theorem legacyEqual_core_ae (z sig : ℝ) (hz : 0 < z) (ρ σ : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hs : 0 < sig) (hσ : ∀ i, σ i = sig)
    (hρ : ∀ i, 0 ≤ ρ i) (hv : 0 < vacMix ρ σ)
    (hr : MixBHRoot z sig ρ σ Gt Dt K) (hK : ∀ i j, K i j = K j i) (i j : Fin N) :
    matCoreCorrUneq z ρ σ Gt Dt i j =ᵐ[volume.restrict (Ioi 0)]
      matMSACoreCorr z ρ σ Gt Dt K i j := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr0
  exact legacyEqual_core_pointwise z sig hz ρ σ Gt Dt K hs hσ hρ hv hr hK i j r hr0

end FMSA.ExactMSA.MultiTailMixture
