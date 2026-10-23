import LeanCode.YukawaOZMix.MSAMultiTailMixtureRDFSpectralOZ
import LeanCode.Analysis.RadialMixtureFirstOrder

/-! Regularity of the actual constructed RDF and certified actual c1.
The final causal Uc L1 condition supplies the global RDF radius moment. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem oddRadialMoment_ae_continuous_off_contact (f : ℝ → ℝ) (a : ℝ)
    (hc : ∀ r, 0 < r → r ≠ a → ContinuousAt f r) :
    ∀ᵐ v, ContinuousAt (FMSA.HardSphere.oddRadialMoment f) v := by
  filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne a, volume.ae_ne (-a)] with v hv hva hvna
  have hp : 0 < |v| := abs_pos.mpr hv
  have hn : |v| ≠ a := by
    rcases le_or_gt 0 v with h | h
    · rwa [abs_of_nonneg h]
    · rw [abs_of_neg h]
      intro hh
      apply hvna
      linarith
  exact Complex.continuous_ofReal.continuousAt.comp
    (continuousAt_id.mul ((hc |v| hp hn).comp continuous_abs.continuousAt))

theorem rdfFirstOrderCausal_measurable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (i j : Fin N) : Measurable (rdfFirstOrderCausal z ρ σ K i j) := by
  have hm : Measurable (fun r => rdfCausalTwoSided z ρ σ K (r-edgeHi σ i j) i j) :=
    (((rdfCausalTwoSided_continuous z ρ σ K).matrix_elem i j).comp
      (continuous_id.sub continuous_const)).measurable
  exact (hm.div (by fun_prop)).indicator measurableSet_Ici

theorem rdfFirstOrderCausal_radius_measurable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (i j : Fin N) : Measurable (fun r => r*rdfFirstOrderCausal z ρ σ K i j r) :=
  measurable_id.mul (rdfFirstOrderCausal_measurable z ρ σ K i j)

theorem rdfFirstOrderCausal_radius_integrable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 < σ i) (K : TailMatrix ι N)
    (hU : ∀ i j, IntegrableOn (fun r => rdfCausalTwoSided z ρ σ K r i j) (Ioi 0))
    (i j : Fin N) : Integrable (fun r => r*rdfFirstOrderCausal z ρ σ K i j r) := by
  apply ((rdfCausalMoment_integrable z ρ σ K hU i j).div_const (2*π)).congr
  filter_upwards with r
  by_cases hr : r=0
  · subst r
    have hR : 0 < edgeHi σ i j := by unfold edgeHi; linarith [hσ i, hσ j]
    rw [rdfCausalMoment, causalShift_eq_zero_below _ _ _ hR]
    simp
  · rw [rdfFirstOrderCausal_eq_moment_div]
    field_simp [hr]

theorem rdfFirstOrderCausal_continuousAt_positive_off_contact (z : ι → ℝ)
    (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) (i j : Fin N) (r : ℝ)
    (hr : 0 < r) (hR : r ≠ edgeHi σ i j) :
    ContinuousAt (rdfFirstOrderCausal z ρ σ K i j) r := by
  rcases lt_or_gt_of_ne hR with hl | hh
  · have he : rdfFirstOrderCausal z ρ σ K i j =ᶠ[𝓝 r] fun _ => 0 := by
      filter_upwards [isOpen_Iio.mem_nhds hl] with x hx
      exact rdfFirstOrderCausal_hardcore z ρ σ K i j x hx
    exact continuousAt_const.congr_of_eventuallyEq he
  · have he : rdfFirstOrderCausal z ρ σ K i j =ᶠ[𝓝 r]
        fun x => rdfCausalTwoSided z ρ σ K (x-edgeHi σ i j) i j/(2*π*x) := by
      filter_upwards [isOpen_Ioi.mem_nhds hh] with x hx
      exact indicator_of_mem (show x ∈ Ici (edgeHi σ i j) from (show edgeHi σ i j < x from hx).le) _
    have hc : ContinuousAt (fun x => rdfCausalTwoSided z ρ σ K (x-edgeHi σ i j) i j/(2*π*x)) r :=
      ((((rdfCausalTwoSided_continuous z ρ σ K).matrix_elem i j).comp
        (continuous_id.sub continuous_const)).continuousAt).div
        (continuousAt_const.mul continuousAt_id) (by positivity)
    exact hc.congr_of_eventuallyEq he

theorem rdfFirstOrderCausal_odd_ae_continuous (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (i j : Fin N) :
    ∀ᵐ v, ContinuousAt (FMSA.HardSphere.oddRadialMoment (rdfFirstOrderCausal z ρ σ K i j)) v :=
  oddRadialMoment_ae_continuous_off_contact _ (edgeHi σ i j)
    (rdfFirstOrderCausal_continuousAt_positive_off_contact z ρ σ K i j)

theorem orderedLinearizedCorrelation_continuousAt_positive_off_contact
    (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (K : TailMatrix ι N)
    (hK : ∀ u i j, K u i j=K u j i) (i j : Fin N) (r : ℝ)
    (hr : 0 < r) (hR : r ≠ edgeHi σ i j) :
    ContinuousAt (orderedLinearizedCorrelation z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j) r := by
  have hc : ContinuousAt (dpCorrelation z ρ σ K i j) r :=
    (dpOddW_continuousAt_positive_off_contact z hz ρ σ hσ K i j r hr hR).div
      (continuousAt_const.mul continuousAt_id) (by positivity)
  have he : orderedLinearizedCorrelation z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j =ᶠ[𝓝 r]
      dpCorrelation z ρ σ K i j := by
    filter_upwards [isOpen_Ioi.mem_nhds hr, eventually_ne_nhds hR] with x hx hxR
    exact orderedLinearizedCorrelation_eq_dpCorrelation z ρ σ K hz hv hρ hσ hK i j x hx hxR
  exact hc.congr_of_eventuallyEq he

theorem orderedLinearizedCorrelation_odd_ae_continuous
    (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (K : TailMatrix ι N)
    (hK : ∀ u i j, K u i j=K u j i) (i j : Fin N) :
    ∀ᵐ v, ContinuousAt (FMSA.HardSphere.oddRadialMoment
      (orderedLinearizedCorrelation z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j)) v :=
  oddRadialMoment_ae_continuous_off_contact _ (edgeHi σ i j)
    (orderedLinearizedCorrelation_continuousAt_positive_off_contact z hz ρ σ hv hρ hσ K hK i j)

end FMSA.ExactMSA.MultiTailMixture
