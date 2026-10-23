import LeanCode.YukawaOZMix.MSAMultiTailMixtureRDFRegularity
import LeanCode.YukawaOZ.MSAMultiTailRDFMoments

/-! Actual DCF measurability and the additional first-order radius moment
needed for radial OZ Fubini. The latter follows from the certified Yukawa
exterior and the already certified first radius moment on the finite core. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem basisQ_measurable (z : ι → ℝ) (σ : Fin N → ℝ) (b : BasisIndex ι) (i j : Fin N) :
    Measurable (basisQ z σ b i j) := by
  unfold basisQ baxterQ
  apply Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
  apply Measurable.ite (measurableSet_le measurable_id measurable_const) <;> fun_prop

theorem basisPrime_measurable (z : ι → ℝ) (σ : Fin N → ℝ) (b : BasisIndex ι) (i j : Fin N) :
    Measurable (basisPrime z σ b i j) := baxterQ'_measurable _ _ _ _ _ _ _ _

theorem basisConvolution_measurable (z : ι → ℝ) (σ : Fin N → ℝ)
    (b c : BasisIndex ι) (i j l : Fin N) : Measurable (basisConvolution z σ b c i j l) := by
  have hm : Measurable (fun p : ℝ × ℝ => basisPrime z σ b i l (p.2+p.1)*basisQ z σ c j l p.2) :=
    ((basisPrime_measurable z σ b i l).comp (measurable_snd.add measurable_fst)).mul
      ((basisQ_measurable z σ c j l).comp measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem linearizedCorrelation_measurable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G : TailMatrix ι N) (i j : Fin N) : Measurable (linearizedCorrelation z ρ σ D G i j) := by
  unfold linearizedCorrelation
  apply Measurable.div _ (by fun_prop)
  apply Measurable.add
  · apply Measurable.neg
    exact Finset.measurable_sum _ (fun b _ => (basisPrime_measurable z σ b i j).const_mul _)
  · apply Finset.measurable_sum
    intro l _
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro b _
    apply Finset.measurable_sum
    intro c _
    exact (basisConvolution_measurable z σ b c i j l).const_mul _

theorem orderedLinearizedCorrelation_measurable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G : TailMatrix ι N) (i j : Fin N) : Measurable (orderedLinearizedCorrelation z ρ σ D G i j) := by
  unfold orderedLinearizedCorrelation
  split_ifs <;> exact linearizedCorrelation_measurable _ _ _ _ _ _ _

theorem orderedLinearizedCorrelation_radius_measurable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G : TailMatrix ι N) (i j : Fin N) :
    Measurable (fun r => r*orderedLinearizedCorrelation z ρ σ D G i j r) :=
  measurable_id.mul (orderedLinearizedCorrelation_measurable z ρ σ D G i j)

theorem orderedLinearizedCorrelation_exterior (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 ≤ ρ i)
    (hσ : ∀ i, 0 < σ i) (K : TailMatrix ι N)
    (hK : ∀ u i j, K u i j=K u j i) (i j : Fin N) (r : ℝ) (hr : edgeHi σ i j < r) :
    orderedLinearizedCorrelation z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j r =
      ∑ u, K u i j*exp (-z u*(r-edgeHi σ i j))/r := by
  unfold orderedLinearizedCorrelation
  split_ifs
  · exact linearizedCorrelation_exterior z ρ σ K hz hv hρ hσ i j r hr
  · have hR : edgeHi σ j i=edgeHi σ i j := by unfold edgeHi; ring
    rw [linearizedCorrelation_exterior z ρ σ K hz hv hρ hσ j i r (by rwa [hR])]
    simp only [hR, ← hK]

theorem orderedLinearizedCorrelation_second_moment_integrable
    (z : ι → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (K : TailMatrix ι N)
    (hK : ∀ u i j, K u i j=K u j i) (i j : Fin N) :
    IntegrableOn (fun r => r*(r*orderedLinearizedCorrelation z ρ σ (firstOrderDt z ρ σ K)
      (baseSeed z ρ σ) i j r)) (Ioi 0) := by
  let c := orderedLinearizedCorrelation z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j
  let R := edgeHi σ i j
  have hR : 0 < R := by dsimp only [R, edgeHi]; linarith [hσ i, hσ j]
  have hi : IntegrableOn (fun r => r*c r) (Ioi 0) :=
    orderedLinearizedCorrelation_radius_weighted_integrable z ρ σ K hz hv hρ hσ hK i j
  have hic : IntegrableOn (fun r => r*(r*c r)) (Ioc 0 R) := by
    have hb : ∀ᵐ r ∂volume.restrict (Ioc 0 R), ‖r‖ ≤ R := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      simpa only [Real.norm_eq_abs, abs_of_pos hr.1] using hr.2
    have hh : IntegrableOn (fun r => (r*c r)*r) (Ioc 0 R) :=
      (hi.mono_set (fun _ h => h.1)).mul_bdd measurable_id.aestronglyMeasurable hb
    simpa only [mul_comm] using hh
  have hit : IntegrableOn (fun r => r*(r*c r)) (Ioi R) := by
    have he : IntegrableOn (fun r => ∑ u, (K u i j*exp (z u*R))*(r*exp (-z u*r))) (Ioi R) :=
      integrable_finsetSum _ (fun u _ => ((integrableOn_Ioi_id_mul_exp_neg (hz u)).mono_set
        (Ioi_subset_Ioi hR.le)).const_mul _)
    apply he.congr_fun _ measurableSet_Ioi
    intro r hr
    have hr0 : r ≠ 0 := (hR.trans hr).ne'
    dsimp only [c]
    rw [orderedLinearizedCorrelation_exterior z hz ρ σ hv hρ hσ K hK i j r hr]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [show -z u*(r-R)=z u*R+(-z u*r) from by ring, exp_add]
    field_simp [hr0]
  have hunion : Ioc (0 : ℝ) R ∪ Ioi R=Ioi 0 := by
    ext r
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · intro h; rcases h with h | h <;> linarith [hR]
    · intro h; rcases le_or_gt r R with hh | hh
      · exact Or.inl ⟨h, hh⟩
      · exact Or.inr hh
  rw [← hunion]
  exact hic.union hit

theorem correlation_amplitudes_measurable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (p : TailMatrix ι N × TailMatrix ι N)
    (i j : Fin N) : Measurable (correlation z ρ σ (amplitudeA z ρ σ p.1 p.2)
      (amplitudeQp z ρ σ p.1 p.2) (W z ρ p.1 p.2) (C z ρ σ p.1 p.2) i j) := by
  change Measurable (fun r => correlation z ρ σ _ _ _ _ i j r)
  simp_rw [correlation_eq_basis z hz ρ σ hσ p]
  apply Measurable.div _ (by fun_prop)
  apply Measurable.add
  · apply Measurable.neg
    exact Finset.measurable_sum _ (fun b _ => (basisPrime_measurable z σ b i j).const_mul _)
  · apply Finset.measurable_sum
    intro l _
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro b _
    apply Finset.measurable_sum
    intro c _
    exact (basisConvolution_measurable z σ b c i j l).const_mul _

theorem orderedRadialCorrelation_measurable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K Dt G : TailMatrix ι N) (i j : Fin N) :
    Measurable (orderedRadialCorrelation z ρ σ K Dt G i j) := by
  unfold orderedRadialCorrelation
  split_ifs <;> exact correlation_amplitudes_measurable z hz ρ σ hσ (Dt, G) _ _

theorem orderedRadialCorrelation_zero_exterior (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 ≤ ρ i)
    (hσ : ∀ i, 0 < σ i) (i j : Fin N) (r : ℝ) (hr : edgeHi σ i j < r) :
    orderedRadialCorrelation z ρ σ 0 0 (baseSeed z ρ σ) i j r=0 := by
  have hb := baseSeed_isRoot z ρ σ hz hv hρ hσ
  unfold orderedRadialCorrelation
  split_ifs
  · rw [correlation_exterior_of_root z hz ρ σ 0 0 _ (fun i => (hσ i).le) hb i j r hr]
    simp
  · have he : edgeHi σ j i=edgeHi σ i j := by unfold edgeHi; ring
    rw [correlation_exterior_of_root z hz ρ σ 0 0 _ (fun i => (hσ i).le) hb j i r (by rwa [he])]
    simp

theorem orderedRadialCorrelation_zero_second_moment (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 ≤ ρ i)
    (hσ : ∀ i, 0 < σ i) (i j : Fin N)
    (hi : IntegrableOn (fun r => r*orderedRadialCorrelation z ρ σ 0 0 (baseSeed z ρ σ) i j r) (Ioi 0)) :
    IntegrableOn (fun r => r*(r*orderedRadialCorrelation z ρ σ 0 0 (baseSeed z ρ σ) i j r)) (Ioi 0) := by
  let R := edgeHi σ i j
  let c := orderedRadialCorrelation z ρ σ 0 0 (baseSeed z ρ σ) i j
  have hR : 0 < R := by dsimp only [R, edgeHi]; linarith [hσ i, hσ j]
  have hb : ∀ r ∈ Ioi (0 : ℝ), r*c r*min r R = r*(r*c r) := by
    intro r hr
    by_cases hh : r ≤ R
    · rw [min_eq_left hh]; ring
    · have hc : c r=0 := orderedRadialCorrelation_zero_exterior z hz ρ σ hv hρ hσ i j r (not_le.mp hh)
      simp [hc]
  have hi' : IntegrableOn (fun r => (r*c r)*min r R) (Ioi 0) :=
    hi.mul_bdd (by fun_prop) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hr.le hR.le)]
      exact min_le_right _ _)
  exact hi'.congr_fun hb measurableSet_Ioi

end FMSA.ExactMSA.MultiTailMixture
