import LeanCode.YukawaOZMix.MSAMultiTailMixtureRDFCausalFourier
import LeanCode.Analysis.RadialOZReconstruction

/-! The actual radial first-order RDF of the causal construction: weighted
L1 and its genuine radial Fourier integral, retaining the actual decay
premise on the constructed two-sided Volterra solution. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def causalFull (f : ℝ → ℝ) : ℝ → ℝ := (Ici 0).indicator f
def causalShift (f : ℝ → ℝ) (a : ℝ) (r : ℝ) : ℝ := causalFull f (r-a)

theorem causalFull_integrable (f : ℝ → ℝ) (hi : IntegrableOn f (Ioi 0)) :
    Integrable (causalFull f) :=
  ((integrableOn_Ici_iff_integrableOn_Ioi).mpr hi).integrable_indicator measurableSet_Ici

theorem causalShift_integrable (f : ℝ → ℝ) (hi : IntegrableOn f (Ioi 0)) (a : ℝ) :
    Integrable (causalShift f a) := by
  have he := (measurePreserving_add_right volume (-a)).integrable_comp_of_integrable
    (causalFull_integrable f hi)
  convert! he using 1 <;> funext r <;> simp [causalShift, Function.comp_def, sub_eq_add_neg]

theorem causalFull_complex_laplace (f : ℝ → ℝ) (s : ℂ) :
    (∫ r : ℝ, (causalFull f r : ℂ)*Complex.exp (-s*r)) = FMSA.causalComplexLaplace f s := by
  have he : (fun r : ℝ => (causalFull f r : ℂ)*Complex.exp (-s*r)) =
      (Ici 0).indicator (fun r => (f r : ℂ)*Complex.exp (-s*r)) := by
    funext r
    by_cases hr : r ∈ Ici (0 : ℝ) <;> simp [causalFull, hr]
  rw [he, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  rfl

theorem causalShift_complex_laplace (f : ℝ → ℝ) (a : ℝ) (s : ℂ) :
    (∫ r : ℝ, (causalShift f a r : ℂ)*Complex.exp (-s*r)) =
      Complex.exp (-s*a)*FMSA.causalComplexLaplace f s := by
  have he := FMSA.MixtureBaxter.laplace_shift_neg (fun r => (causalFull f r : ℂ)) a s
  simp only [← neg_mul] at he
  rw [causalFull_complex_laplace] at he
  exact he

theorem causalShift_eq_zero_below (f : ℝ → ℝ) (a r : ℝ) (hr : r < a) :
    causalShift f a r = 0 := by
  exact indicator_of_notMem (show r-a ∉ Ici (0 : ℝ) from not_le.mpr (sub_neg.mpr hr)) _

theorem causalShift_positive_complex_laplace (f : ℝ → ℝ) (a : ℝ) (ha : 0 < a) (s : ℂ) :
    (∫ r in Ioi (0 : ℝ), (causalShift f a r : ℂ)*Complex.exp (-s*r)) =
      Complex.exp (-s*a)*FMSA.causalComplexLaplace f s := by
  rw [← causalShift_complex_laplace f a s]
  have he : (Ioi 0).indicator (fun r : ℝ => (causalShift f a r : ℂ)*Complex.exp (-s*r)) =
      fun r : ℝ => (causalShift f a r : ℂ)*Complex.exp (-s*r) := by
    funext r
    by_cases hr : 0 < r
    · exact indicator_of_mem hr _
    · rw [indicator_of_notMem (show r ∉ Ioi (0 : ℝ) from hr), causalShift_eq_zero_below f a r (by linarith)]
      simp
  rw [← integral_indicator measurableSet_Ioi, he]

def rdfCausalMoment (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (i j : Fin N) : ℝ → ℝ :=
  causalShift (fun t => rdfCausalTwoSided z ρ σ K t i j) (edgeHi σ i j)

theorem rdfFirstOrderCausal_eq_moment_div (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (i j : Fin N) (r : ℝ) :
    rdfFirstOrderCausal z ρ σ K i j r = rdfCausalMoment z ρ σ K i j r/(2*π*r) := by
  unfold rdfFirstOrderCausal rdfCausalMoment causalShift causalFull
  by_cases hr : edgeHi σ i j ≤ r
  · simp only [indicator_of_mem (mem_Ici.mpr hr),
      indicator_of_mem (mem_Ici.mpr (sub_nonneg.mpr hr))]
  · simp only [indicator_of_notMem (show r ∉ Ici (edgeHi σ i j) from hr),
      indicator_of_notMem (show r-edgeHi σ i j ∉ Ici (0 : ℝ) from fun h => hr (sub_nonneg.mp h)), zero_div]

theorem rdfCausalMoment_integrable (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N)
    (hU : ∀ i j, IntegrableOn (fun r => rdfCausalTwoSided z ρ σ K r i j) (Ioi 0))
    (i j : Fin N) : Integrable (rdfCausalMoment z ρ σ K i j) :=
  causalShift_integrable _ (hU i j) _

theorem rdfFirstOrderCausal_radius_weighted_integrable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N)
    (hU : ∀ i j, IntegrableOn (fun r => rdfCausalTwoSided z ρ σ K r i j) (Ioi 0))
    (i j : Fin N) : IntegrableOn (fun r => r*rdfFirstOrderCausal z ρ σ K i j r) (Ioi 0) := by
  apply ((rdfCausalMoment_integrable z ρ σ K hU i j).div_const (2*π)).integrableOn.congr_fun
    _ measurableSet_Ioi
  intro r hr
  have hr0 : 0 < r := hr
  dsimp only
  rw [rdfFirstOrderCausal_eq_moment_div]
  field_simp [hr0.ne']

theorem complex_axis_exp_difference (k r : ℝ) :
    Complex.exp ((Complex.I*k)*r)-Complex.exp (-(Complex.I*k)*r) =
      2*Complex.I*(sin (k*r) : ℂ) := by
  have hp : (Complex.I*(k : ℂ))*(r : ℂ) = ((k*r : ℝ) : ℂ)*Complex.I := by push_cast; ring
  have hn : -(Complex.I*(k : ℂ))*(r : ℂ) = ((-(k*r) : ℝ) : ℂ)*Complex.I := by push_cast; ring
  rw [hp, hn, Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-- Actual positive-radius RDF Fourier integral, as the difference of the
actual causal moment transforms. -/
theorem rdfFirstOrderCausal_radial_fourier (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 < σ i) (K : TailMatrix ι N)
    (hU : ∀ i j, IntegrableOn (fun r => rdfCausalTwoSided z ρ σ K r i j) (Ioi 0))
    (i j : Fin N) (k : ℝ) (hk : k ≠ 0) :
    (FMSA.HardSphere.radial_fourier (rdfFirstOrderCausal z ρ σ K i j) k : ℂ) =
      (Complex.exp ((Complex.I*k)*(edgeHi σ i j : ℂ))*
          rdfMatrixLaplace (rdfCausalTwoSided z ρ σ K) (-(Complex.I*k)) i j-
        Complex.exp (-(Complex.I*k)*(edgeHi σ i j : ℂ))*
          rdfMatrixLaplace (rdfCausalTwoSided z ρ σ K) (Complex.I*k) i j)/(Complex.I*k) := by
  have hR : 0 < edgeHi σ i j := by unfold edgeHi; linarith [hσ i, hσ j]
  let U := rdfCausalMoment z ρ σ K i j
  have hi := rdfCausalMoment_integrable z ρ σ K hU i j
  have hpos := (real_axis_weighted_integrable U hi (-k)).integrableOn (s := Ioi 0)
  have hneg := (real_axis_weighted_integrable U hi k).integrableOn (s := Ioi 0)
  simp only [Complex.ofReal_neg, mul_neg, neg_neg] at hpos
  have he : (∫ r in Ioi (0 : ℝ), (U r : ℂ)*Complex.exp ((Complex.I*k)*r))-
      (∫ r in Ioi (0 : ℝ), (U r : ℂ)*Complex.exp (-(Complex.I*k)*r)) =
        2*Complex.I*Complex.ofReal (∫ r in Ioi (0 : ℝ), U r*sin (k*r)) := by
    rw [← integral_sub hpos hneg, ← integral_complex_ofReal, ← integral_const_mul]
    apply integral_congr_ae (Eventually.of_forall _)
    intro r
    rw [← mul_sub, complex_axis_exp_difference]
    push_cast
    ring
  have hFTpos := causalShift_positive_complex_laplace
    (fun t => rdfCausalTwoSided z ρ σ K t i j) (edgeHi σ i j) hR (-(Complex.I*k))
  have hFTneg := causalShift_positive_complex_laplace
    (fun t => rdfCausalTwoSided z ρ σ K t i j) (edgeHi σ i j) hR (Complex.I*k)
  simp only [neg_neg] at hFTpos
  change (∫ r in Ioi (0 : ℝ), (U r : ℂ)*Complex.exp ((Complex.I*k)*r)) = _ at hFTpos
  change (∫ r in Ioi (0 : ℝ), (U r : ℂ)*Complex.exp (-(Complex.I*k)*r)) = _ at hFTneg
  rw [hFTpos, hFTneg] at he
  have hradius : (∫ r in Ioi (0 : ℝ), r*rdfFirstOrderCausal z ρ σ K i j r*sin (k*r)) =
      (1/(2*π))*∫ r in Ioi (0 : ℝ), U r*sin (k*r) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr0 : 0 < r := hr
    dsimp only
    rw [rdfFirstOrderCausal_eq_moment_div]
    dsimp only [U]
    field_simp [hr0.ne']
  unfold FMSA.HardSphere.radial_fourier
  rw [hradius]
  change _ = _
  change _ = _ at he
  simp only [rdfMatrixLaplace, Matrix.of_apply]
  have hs : Complex.I*(k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk)
  push_cast
  apply (eq_div_iff hs).mpr
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hpC : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  linear_combination (norm := skip) -he
  field_simp [hkC, hpC]
  ring

end FMSA.ExactMSA.MultiTailMixture
