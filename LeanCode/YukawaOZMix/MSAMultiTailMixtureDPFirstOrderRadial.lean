import LeanCode.YukawaOZMix.MSAMultiTailMixtureDPIdentification

/-! Actual first-order radial DCF Fourier identification. No core symmetry
or independently supplied DP identification premise remains at first order. -/
noncomputable section
open MeasureTheory Real Set Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators FourierTransform
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem dpPrimitive_tendsto_zero (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j = K u j i) (i j : Fin N) :
    Tendsto (dpPrimitive z ρ σ K i j) atTop (𝓝 0) := by
  apply (linearizedPrimitiveReal_tendsto_zero z ρ σ K hz hv hρ hσ i j).congr'
  filter_upwards [eventually_gt_atTop (edgeLo σ i j)] with r hr
  exact linearizedPrimitiveReal_eq_dpPrimitive_off_edge z ρ σ K hz hv hρ hσ hK i j r (ne_of_gt hr)

theorem dpPrimitive_cosine_eq_sine (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j = K u j i) (i j : Fin N) (k : ℝ) (hk : k ≠ 0) :
    (∫ r in Ioi (0 : ℝ), dpPrimitive z ρ σ K i j r*cos (k*r)) =
      (1/k)*∫ r in Ioi (0 : ℝ), dpOddW z ρ σ K i j r*sin (k*r) := by
  have hp := dpPrimitive_integrable z ρ σ K hz hv hρ hσ hK i j
  have hvint := dpOddW_integrable z hz ρ σ (fun i => (hσ i).le) K i j
  have hcos : Integrable (fun r => dpPrimitive z ρ σ K i j r*cos (k*r)) :=
    hp.mul_bdd (by fun_prop) (Eventually.of_forall (fun r => by
      simpa only [Real.norm_eq_abs] using abs_cos_le_one (k*r)))
  have hsin : Integrable (fun r => dpOddW z ρ σ K i j r*sin (k*r)) :=
    hvint.mul_bdd (by fun_prop) (Eventually.of_forall (fun r => by
      simpa only [Real.norm_eq_abs] using abs_sin_le_one (k*r)))
  apply FMSA.Analysis.cosine_of_one_contact _ _ (edgeHi σ i j) k
    (by unfold edgeHi; linarith [hσ i, hσ j]) hk
    (dpPrimitive_continuous z hz ρ σ (fun i => (hσ i).le) K i j)
    (fun r hr hrR => dpPrimitive_hasDerivAt_positive_off_contact z hz ρ σ hσ K i j r hr hrR)
    (dpPrimitive_tendsto_zero z ρ σ K hz hv hρ hσ hK i j)
    hcos.integrableOn hsin.integrableOn

/-- Actual Fourier integral of the independent radial DP correlation equals
the actual first-order Baxter spectral coefficient. -/
theorem linearizedSpectralC_eq_radial_dpCorrelation (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j = K u j i) (i j : Fin N) (k : ℝ) (hk : k ≠ 0) :
    linearizedSpectralC z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) k i j =
      (FMSA.HardSphere.radial_fourier (dpCorrelation z ρ σ K i j) k : ℂ) := by
  let P := linearizedPrimitiveReal z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j
  have hi := linearizedPrimitiveReal_complex_integrable z hz ρ σ (fun i => (hσ i).le)
    (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j
  have heven : (fun r => (P (-r) : ℂ)) =ᵐ[volume] fun r => (P r : ℂ) := by
    filter_upwards [linearizedPrimitiveReal_ae_even z ρ σ K hz hv hρ hσ hK i j] with r hr
    exact congrArg Complex.ofReal hr
  have hzW : FMSA.MixtureBaxter.zOfW (k/(2*π)) = Complex.I*k := by
    unfold FMSA.MixtureBaxter.zOfW
    push_cast
    field_simp
  have hf := fourier_of_ae_even (fun r => (P r : ℂ)) heven hi (k/(2*π))
  rw [FMSA.MixtureBaxter.fourier_eq_zOfW, hzW] at hf
  have hcos : (∫ r in Ioi (0 : ℝ), (cos (2*π*r*(k/(2*π))) : ℂ)*(P r : ℂ)) =
      Complex.ofReal (∫ r in Ioi (0 : ℝ), dpPrimitive z ρ σ K i j r*cos (k*r)) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae
      (linearizedPrimitiveReal_ae_eq_dpPrimitive z ρ σ K hz hv hρ hσ hK i j)] with r hr
    have he : 2*π*r*(k/(2*π)) = k*r := by field_simp
    dsimp only [P]
    rw [he, hr]
    push_cast
    ring
  have hfP := linearizedPrimitiveReal_fourier z hz ρ σ (fun i => (hσ i).le)
    (firstOrderDt z ρ σ K) (baseSeed z ρ σ) k i j
  rw [linearizedSpectralPrimitive_eq_spectralC z hz ρ σ (fun i => (hσ i).le)] at hfP
  change (∫ r : ℝ, (P r : ℂ)*Complex.exp (-(Complex.I*k)*r)) = _ at hfP
  simp only [neg_mul] at hfP
  rw [← hfP, hf, hcos, dpPrimitive_cosine_eq_sine z ρ σ K hz hv hρ hσ hK i j k hk]
  have he : (∫ r in Ioi (0 : ℝ), dpOddW z ρ σ K i j r*sin (k*r)) =
      2*π*(∫ r in Ioi (0 : ℝ), r*dpCorrelation z ρ σ K i j r*sin (k*r)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr0 : 0 < r := hr
    unfold dpCorrelation dpOddW
    field_simp [hr0.ne']
  rw [he, FMSA.HardSphere.radial_fourier]
  push_cast
  ring

theorem linearizedSpectralC_eq_actual_ordered_radial (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j = K u j i) (i j : Fin N) (horder : σ j ≤ σ i)
    (k : ℝ) (hk : k ≠ 0) :
    linearizedSpectralC z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) k i j =
      (FMSA.HardSphere.radial_fourier
        (linearizedCorrelation z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j) k : ℂ) := by
  rw [linearizedSpectralC_eq_radial_dpCorrelation z ρ σ K hz hv hρ hσ hK i j k hk]
  unfold FMSA.HardSphere.radial_fourier
  congr 2
  apply integral_congr_ae
  filter_upwards [linearizedCorrelation_ae_eq_dpCorrelation_ordered z ρ σ K hz hv hρ hσ hK i j horder]
    with r hr
  rw [hr]

/-- Canonical physical pair representative: put the larger diameter in the
row of the actual BH radial formula. Equal diameters retain the given row. -/
def orderedLinearizedCorrelation (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (D G0 : TailMatrix ι N) (i j : Fin N) : ℝ → ℝ :=
  if σ j ≤ σ i then linearizedCorrelation z ρ σ D G0 i j
    else linearizedCorrelation z ρ σ D G0 j i

theorem orderedLinearizedCorrelation_eq_dpCorrelation (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j = K u j i) (i j : Fin N)
    (r : ℝ) (hr : 0 < r) (hrR : r ≠ edgeHi σ i j) :
    orderedLinearizedCorrelation z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j r =
      dpCorrelation z ρ σ K i j r := by
  unfold orderedLinearizedCorrelation
  split_ifs with ho
  · exact linearizedCorrelation_eq_dpCorrelation_ordered z ρ σ K hz hv hρ hσ hK i j ho r hr hrR
  · have hrR' : r ≠ edgeHi σ j i := by simpa only [edgeHi, add_comm] using hrR
    rw [linearizedCorrelation_eq_dpCorrelation_ordered z ρ σ K hz hv hρ hσ hK j i
      (le_of_not_ge ho) r hr hrR', dpCorrelation_symmetric z hz ρ σ (fun i => (hσ i).le) K hK j i r]

theorem orderedLinearizedCorrelation_ae_eq_dpCorrelation (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j = K u j i) (i j : Fin N) :
    orderedLinearizedCorrelation z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j =ᵐ[volume.restrict (Ioi 0)]
      dpCorrelation z ρ σ K i j := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    ae_restrict_of_ae (volume.ae_ne (edgeHi σ i j))] with r hr hrR
  exact orderedLinearizedCorrelation_eq_dpCorrelation z ρ σ K hz hv hρ hσ hK i j r hr hrR

theorem linearizedSpectralC_eq_all_pairs_ordered_radial (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j = K u j i) (i j : Fin N) (k : ℝ) (hk : k ≠ 0) :
    linearizedSpectralC z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) k i j =
      (FMSA.HardSphere.radial_fourier
        (orderedLinearizedCorrelation z ρ σ (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j) k : ℂ) := by
  rw [linearizedSpectralC_eq_radial_dpCorrelation z ρ σ K hz hv hρ hσ hK i j k hk]
  unfold FMSA.HardSphere.radial_fourier
  congr 2
  apply integral_congr_ae
  filter_upwards [orderedLinearizedCorrelation_ae_eq_dpCorrelation z ρ σ K hz hv hρ hσ hK i j]
    with r hr
  rw [hr]

theorem dpCorrelation_radius_weighted_integrable (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K : TailMatrix ι N) (i j : Fin N) :
    IntegrableOn (fun r => r*dpCorrelation z ρ σ K i j r) (Ioi 0) := by
  apply ((dpOddW_integrable z hz ρ σ hσ K i j).div_const (2*π)).integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr0 : 0 < r := hr
  unfold dpCorrelation dpOddW
  field_simp [hr0.ne']

theorem orderedLinearizedCorrelation_radius_weighted_integrable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hv : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hK : ∀ u i j, K u i j = K u j i) (i j : Fin N) :
    IntegrableOn (fun r => r*orderedLinearizedCorrelation z ρ σ
      (firstOrderDt z ρ σ K) (baseSeed z ρ σ) i j r) (Ioi 0) := by
  apply (dpCorrelation_radius_weighted_integrable z hz ρ σ (fun i => (hσ i).le) K i j).congr
  filter_upwards [orderedLinearizedCorrelation_ae_eq_dpCorrelation z ρ σ K hz hv hρ hσ hK i j]
    with r hr
  rw [hr]

end FMSA.ExactMSA.MultiTailMixture
