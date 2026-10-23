import LeanCode.HardSphere.BaxterOzStar
import LeanCode.HardSphere.BaxterDiluteDecay
import LeanCode.Analysis.CausalRenewalBound

/-! A sufficient weighted integral criterion for the actual HS Volterra
solution. This supplies radius L1 without a Wiener--Hopf injectivity axiom. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
namespace FMSA.HardSphere

def baxterWeightedMass (eta sigma rho δ : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), exp (δ*t)*|q0_poly eta sigma rho t|

theorem q0_poly_weighted_integrable {eta sigma rho δ : ℝ} (hs : 0 < sigma) :
    IntegrableOn (fun t => exp (δ*t)*|q0_poly eta sigma rho t|) (Ioi 0) := by
  let f := fun t => exp (δ*t)*|q0_poly eta sigma rho t|
  have hc : Continuous f := (by fun_prop : Continuous (fun t : ℝ => exp (δ*t))).mul
    (q0_poly_continuous eta sigma rho).abs
  have hi : Integrable ((Icc (0 : ℝ) sigma).indicator f) :=
    hc.integrableOn_Icc.integrable_indicator measurableSet_Icc
  apply hi.integrableOn.congr_fun _ measurableSet_Ioi
  intro t ht
  by_cases hh : t ≤ sigma
  · exact indicator_of_mem (show t ∈ Icc (0 : ℝ) sigma from ⟨ht.le, hh⟩) _
  · rw [indicator_of_notMem (show t ∉ Icc (0 : ℝ) sigma from fun h => hh h.2)]
    simp [f, q0_poly_eq_zero_of_ge (not_le.mp hh).le]

theorem baxterForcing_shift_weighted_bounded {eta sigma rho δ : ℝ}
    (hs : 0 < sigma) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, 0 ≤ t →
      exp (δ*t)*|baxterForcing eta sigma rho (t+sigma)| ≤ B := by
  let f := fun t => exp (δ*t)*|baxterForcing eta sigma rho (t+sigma)|
  have hc : Continuous f := (by fun_prop : Continuous (fun t : ℝ => exp (δ*t))).mul
    ((baxterForcing_continuous eta sigma rho).comp (by fun_prop)).abs
  obtain ⟨x, hx, hm⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) sigma).Nonempty from ⟨0, ⟨le_rfl, hs.le⟩⟩) hc.continuousOn
  refine ⟨f x, by dsimp [f]; positivity, ?_⟩
  intro t ht
  by_cases hh : t ≤ sigma
  · exact hm ⟨ht, hh⟩
  · have hz : baxterForcing eta sigma rho (t+sigma)=0 :=
      baxterForcing_eq_zero_of_two_sigma_le hs (by linarith)
    simp only [hz, abs_zero, mul_zero]
    dsimp [f]; positivity

theorem baxterPsiOuter_shift_renewal (eta sigma rho : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    baxterPsiOuter eta sigma rho (r+sigma)=baxterForcing eta sigma rho (r+sigma)+
      ∫ t in (0 : ℝ)..r, q0_poly eta sigma rho (r-t)*baxterPsiOuter eta sigma rho (t+sigma) := by
  rw [baxterPsiOuter_spec (by linarith : sigma ≤ r+sigma)]
  congr 1
  have he := intervalIntegral.integral_comp_add_right
    (fun t => q0_poly eta sigma rho (r+sigma-t)*baxterPsiOuter eta sigma rho t)
    (a := (0 : ℝ)) (b := r) sigma
  simpa only [zero_add, add_sub_add_right_eq_sub] using he.symm

theorem baxterPsiOuter_shift_continuous (eta sigma rho : ℝ) :
    ContinuousOn (fun t => baxterPsiOuter eta sigma rho (t+sigma)) (Ici 0) := by
  apply baxterPsiOuter_continuousOn_Ici.comp
    (by fun_prop : Continuous (fun t : ℝ => t+sigma)).continuousOn
  intro t ht
  change sigma ≤ t+sigma
  change 0 ≤ t at ht
  linarith [ht]

theorem baxterPsiOuter_shift_integrable_of_weighted_budget {eta sigma rho δ : ℝ}
    (hs : 0 < sigma) (hδ : 0 < δ) (hm : baxterWeightedMass eta sigma rho δ < 1) :
    IntegrableOn (fun t => baxterPsiOuter eta sigma rho (t+sigma)) (Ioi 0) := by
  obtain ⟨B, hB, hf⟩ := baxterForcing_shift_weighted_bounded
    (eta := eta) (rho := rho) (δ := δ) hs
  exact FMSA.causal_renewal_integrable_of_weighted_bound hδ
    (q0_poly_continuous eta sigma rho).continuousOn (baxterPsiOuter_shift_continuous eta sigma rho)
    (q0_poly_weighted_integrable hs) (le_refl (baxterWeightedMass eta sigma rho δ)) hm hB hf
    (fun r hr => baxterPsiOuter_shift_renewal eta sigma rho hr)

theorem baxterPsiOuter_integrable_of_weighted_budget {eta sigma rho δ : ℝ}
    (hs : 0 < sigma) (hδ : 0 < δ) (hm : baxterWeightedMass eta sigma rho δ < 1) :
    IntegrableOn (baxterPsiOuter eta sigma rho) (Ioi sigma) := by
  have hi := baxterPsiOuter_shift_integrable_of_weighted_budget hs hδ hm
  have he : (fun t : ℝ => t+sigma) '' Ioi 0=Ioi sigma := by
    ext x
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨t, ht, rfl⟩; linarith
    · intro hx; exact ⟨x-sigma, by linarith, by ring⟩
  rw [← he, (measurePreserving_add_right volume sigma).integrableOn_image
    (MeasurableEquiv.addRight sigma).measurableEmbedding]
  exact hi

theorem baxterPsi_integrable_of_weighted_budget {eta sigma rho δ : ℝ}
    (hs : 0 < sigma) (hδ : 0 < δ) (hm : baxterWeightedMass eta sigma rho δ < 1) :
    Integrable (baxterPsi eta sigma rho) := by
  have ho : IntegrableOn (baxterPsi eta sigma rho) (Ioi sigma) :=
    (baxterPsiOuter_integrable_of_weighted_budget hs hδ hm).congr_fun
      (fun r hr => (baxterPsi_outer hr.le).symm) measurableSet_Ioi
  obtain ⟨C, _, hb⟩ := baxterPsi_bddOn_uIcc (eta := eta) (rho := rho) 0 sigma
  have hc : IntegrableOn (baxterPsi eta sigma rho) (Icc 0 sigma) := by
    apply Measure.integrableOn_of_bounded (M := C) isCompact_Icc.measure_ne_top
      baxterPsi_measurable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [Real.norm_eq_abs]
    exact hb r (by rw [uIcc_of_le hs.le]; exact hr)
  have hp : IntegrableOn (baxterPsi eta sigma rho) (Ici 0) := by
    have he : Icc (0 : ℝ) sigma ∪ Ioi sigma=Ici 0 := by
      ext x; simp only [mem_union, mem_Icc, mem_Ioi, mem_Ici]; constructor
      · rintro (h|h); exact h.1; linarith
      · intro h; rcases le_or_gt x sigma with hh|hh
        exact Or.inl ⟨h, hh⟩
        exact Or.inr hh
    rw [← he]; exact hc.union ho
  have hn : IntegrableOn (baxterPsi eta sigma rho) (Iic 0) := by
    have he : (fun r : ℝ => -r) ⁻¹' Ici 0=Iic 0 := by ext r; simp
    have hi := ((Measure.measurePreserving_neg volume).integrableOn_comp_preimage
      (MeasurableEquiv.neg ℝ).measurableEmbedding).mpr hp
    rw [he] at hi
    have hf : (baxterPsi eta sigma rho ∘ fun r => -r)=fun r => -baxterPsi eta sigma rho r := by
      funext r; exact baxterPsi_odd hs r
    rw [hf] at hi
    simpa using hi.neg
  have he : Ici (0 : ℝ) ∪ Iic 0=univ := by ext r; simp
  exact integrableOn_univ.mp (by rw [← he]; exact hp.union hn)

theorem baxterPsi_div_radius_measurable (eta sigma rho : ℝ) :
    Measurable (fun r => r*(baxterPsi eta sigma rho r/r)) :=
  measurable_id.mul (baxterPsi_measurable.div measurable_id)

theorem baxterPsi_div_radius_integrable_of_weighted_budget {eta sigma rho δ : ℝ}
    (hs : 0 < sigma) (hδ : 0 < δ) (hm : baxterWeightedMass eta sigma rho δ < 1) :
    Integrable (fun r => r*(baxterPsi eta sigma rho r/r)) := by
  apply (baxterPsi_integrable_of_weighted_budget hs hδ hm).congr
  filter_upwards [volume.ae_ne (0 : ℝ)] with r hr
  field_simp [hr]

end FMSA.HardSphere
