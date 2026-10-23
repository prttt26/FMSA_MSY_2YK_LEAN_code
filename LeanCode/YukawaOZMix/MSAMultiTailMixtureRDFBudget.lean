import LeanCode.YukawaOZMix.MSAMultiTailMixtureRDFCertificate
import LeanCode.Analysis.MatrixCausalRenewalBound

/-! Explicit sufficient weighted integral budget for the actual two-sided
mixture Volterra construction. No all-state or necessary-condition claim. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0 FMSA.HardSphere
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def rdfWeightedKernelBudget (ρ σ : Fin N → ℝ) (δ : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), exp (δ*t)*FMSA.matrixAbsSum (rdfCausalKernel ρ σ t)

def rdfSourceAbsBudget (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) : ℝ :=
  ∑ i, ∑ j, ∑ u, |dpBareAmplitude z ρ σ K u i j|

theorem rdfCausalKernel_weighted_entry_integrable (ρ σ : Fin N → ℝ) (δ : ℝ) (i j : Fin N) :
    IntegrableOn (fun t => exp (δ*t)*|rdfCausalKernel ρ σ t i j|) (Ioi 0) := by
  let f := fun t => exp (δ*t)*|rdfCausalKernel ρ σ t i j|
  have hc : Continuous f := (by fun_prop : Continuous (fun t : ℝ => exp (δ*t))).mul
    ((rdfCausalKernel_continuous ρ σ).matrix_elem i j).abs
  have hi : Integrable ((Icc (0 : ℝ) (max (σ i) 0)).indicator f) :=
    (hc.integrableOn_Icc).integrable_indicator measurableSet_Icc
  apply hi.integrableOn.congr_fun _ measurableSet_Ioi
  intro t ht
  by_cases hh : t ≤ max (σ i) 0
  · exact indicator_of_mem (show t ∈ Icc (0 : ℝ) (max (σ i) 0) from ⟨ht.le, hh⟩) _
  · have hs : σ i ≤ t := le_trans (le_max_left _ _) (not_le.mp hh).le
    rw [indicator_of_notMem (show t ∉ Icc (0 : ℝ) (max (σ i) 0) from fun h => hh h.2)]
    simp [f, rdfCausalKernel, rdfRecenteredHSQ, min_eq_right hs]

theorem rdfCausalKernel_weighted_absSum_integrable (ρ σ : Fin N → ℝ) (δ : ℝ) :
    IntegrableOn (fun t => exp (δ*t)*FMSA.matrixAbsSum (rdfCausalKernel ρ σ t)) (Ioi 0) := by
  have hi : IntegrableOn (fun t => ∑ i, ∑ j, exp (δ*t)*|rdfCausalKernel ρ σ t i j|) (Ioi 0) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      rdfCausalKernel_weighted_entry_integrable ρ σ δ i j))
  simpa only [FMSA.matrixAbsSum, Finset.mul_sum] using hi

theorem rdfSourceAbsBudget_nonneg (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) :
    0 ≤ rdfSourceAbsBudget z ρ σ K := by unfold rdfSourceAbsBudget; positivity

theorem rdfCausalSource_weighted_absSum_bound (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (δ : ℝ) (hzδ : ∀ u, δ ≤ z u) (r : ℝ) (hr : 0 ≤ r) :
    exp (δ*r)*FMSA.matrixAbsSum (rdfCausalSource z ρ σ K r) ≤ rdfSourceAbsBudget z ρ σ K := by
  have hb (i j : Fin N) : exp (δ*r)*|rdfCausalSource z ρ σ K r i j| ≤
      ∑ u, |dpBareAmplitude z ρ σ K u i j| := by
    unfold rdfCausalSource
    simp only [Matrix.of_apply]
    calc
      _ ≤ exp (δ*r)*(∑ u, |dpBareAmplitude z ρ σ K u i j*exp (-z u*r)|) :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (exp_pos _).le
      _ = ∑ u, |dpBareAmplitude z ρ σ K u i j| *exp ((δ-z u)*r) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        rw [abs_mul, abs_of_pos (exp_pos _)]
        have he : exp (δ*r)*exp (-z u*r)=exp ((δ-z u)*r) := by
          rw [← exp_add]; congr 1; ring
        linear_combination |dpBareAmplitude z ρ σ K u i j| *he
      _ ≤ _ := Finset.sum_le_sum (fun u _ => mul_le_of_le_one_right (abs_nonneg _)
        (exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hzδ u)) hr)))
  simp only [FMSA.matrixAbsSum, rdfSourceAbsBudget, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j))

theorem rdfCausalLeft_weighted_absSum_bound (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (δ : ℝ) (hzδ : ∀ u, δ ≤ z u)
    (hbudget : rdfWeightedKernelBudget ρ σ δ < 1) (r : ℝ) (hr : 0 ≤ r) :
    exp (δ*r)*FMSA.matrixAbsSum (rdfCausalLeft z ρ σ K r) ≤
      rdfSourceAbsBudget z ρ σ K/(1-rdfWeightedKernelBudget ρ σ δ) := by
  apply FMSA.matrixRenewal_weighted_absSum_bound
    (fun t => (rdfCausalKernel ρ σ t).transpose) (rdfCausalSource z ρ σ K)
    (rdfCausalLeft z ρ σ K) (rdfCausalKernelTranspose_continuous ρ σ)
    (rdfCausalLeft_continuous z ρ σ K) δ (rdfWeightedKernelBudget ρ σ δ) (rdfSourceAbsBudget z ρ σ K)
    (by simpa only [FMSA.matrixAbsSum_transpose] using rdfCausalKernel_weighted_absSum_integrable ρ σ δ)
    (by simp only [FMSA.matrixAbsSum_transpose, rdfWeightedKernelBudget]; exact le_refl _)
    hbudget (rdfSourceAbsBudget_nonneg z ρ σ K)
    (rdfCausalSource_weighted_absSum_bound z ρ σ K δ hzδ) _ r hr
  intro i j t ht
  exact rdfCausalLeft_renewal z ρ σ K i j t ht

theorem rdfCausalTwoSided_weighted_absSum_bound (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (δ : ℝ) (hzδ : ∀ u, δ ≤ z u)
    (hbudget : rdfWeightedKernelBudget ρ σ δ < 1) (r : ℝ) (hr : 0 ≤ r) :
    exp (δ*r)*FMSA.matrixAbsSum (rdfCausalTwoSided z ρ σ K r) ≤
      rdfSourceAbsBudget z ρ σ K/(1-rdfWeightedKernelBudget ρ σ δ)^2 := by
  have h := FMSA.matrixRenewal_weighted_absSum_bound
    (fun t => (rdfCausalKernel ρ σ t).transpose) (fun t => (rdfCausalLeft z ρ σ K t).transpose)
    (fun t => (rdfCausalTwoSided z ρ σ K t).transpose) (rdfCausalKernelTranspose_continuous ρ σ)
    (continuous_matrix (fun i j => (rdfCausalTwoSided_continuous z ρ σ K).matrix_elem j i))
    δ (rdfWeightedKernelBudget ρ σ δ) (rdfSourceAbsBudget z ρ σ K/(1-rdfWeightedKernelBudget ρ σ δ))
    (by simpa only [FMSA.matrixAbsSum_transpose] using rdfCausalKernel_weighted_absSum_integrable ρ σ δ)
    (by simp only [FMSA.matrixAbsSum_transpose, rdfWeightedKernelBudget]; exact le_refl _)
    hbudget (div_nonneg (rdfSourceAbsBudget_nonneg z ρ σ K) (by linarith))
    (fun t ht => by simpa only [FMSA.matrixAbsSum_transpose] using
      rdfCausalLeft_weighted_absSum_bound z ρ σ K δ hzδ hbudget t ht) (fun i j t ht => by
      have he := rdfCausalTwoSided_renewal z ρ σ K j i t ht
      simpa only [Matrix.transpose_apply, mul_comm] using he) r hr
  simpa only [FMSA.matrixAbsSum_transpose, div_div, pow_two] using h

/-- The actual constructed Uc is L1 under an explicit, sufficient budget.
Only delta>0, delta<=each tail rate, and the actual weighted kernel mass<1
are needed. The criterion is not claimed necessary or valid at all states. -/
theorem rdfCausalTwoSided_integrable_of_weighted_budget (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (δ : ℝ) (hδ : 0 < δ) (hzδ : ∀ u, δ ≤ z u)
    (hbudget : rdfWeightedKernelBudget ρ σ δ < 1) (i j : Fin N) :
    IntegrableOn (fun r => rdfCausalTwoSided z ρ σ K r i j) (Ioi 0) := by
  let B := rdfSourceAbsBudget z ρ σ K/(1-rdfWeightedKernelBudget ρ σ δ)^2
  have hi : IntegrableOn (fun t => B*exp (-δ*t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -δ < 0) 0).const_mul _
  apply hi.mono' ((rdfCausalTwoSided_continuous z ρ σ K).matrix_elem i j).measurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs]
  have hb := rdfCausalTwoSided_weighted_absSum_bound z ρ σ K δ hzδ hbudget t ht.le
  have he : exp (δ*t)*exp (-δ*t)=1 := by rw [← exp_add]; simp
  calc
    _ ≤ FMSA.matrixAbsSum (rdfCausalTwoSided z ρ σ K t) := FMSA.matrixAbsSum_entry_le _ i j
    _ = (exp (δ*t)*FMSA.matrixAbsSum (rdfCausalTwoSided z ρ σ K t))*exp (-δ*t) := by
      linear_combination -FMSA.matrixAbsSum (rdfCausalTwoSided z ρ σ K t)*he
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (exp_pos _).le

theorem rdfCausalKernel_weighted_entry_integral_window (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (δ : ℝ) (i j : Fin N) :
    (∫ t in Ioi (0 : ℝ), exp (δ*t)*|rdfCausalKernel ρ σ t i j|) =
      ∫ t in (0 : ℝ)..σ i, exp (δ*t)*
        |ρ i*(Q0phys ρ σ i j*(t-σ i)+Qppphys ρ σ j j/2*(t-σ i)^2)| := by
  let f := fun t => exp (δ*t)*|rdfCausalKernel ρ σ t i j|
  have he : (Ioi (0 : ℝ)).indicator f=(Ioc (0 : ℝ) (σ i)).indicator f := by
    funext t
    by_cases ht : 0 < t
    · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
      by_cases hs : t ≤ σ i
      · rw [indicator_of_mem (show t ∈ Ioc (0 : ℝ) (σ i) from ⟨ht, hs⟩)]
      · rw [indicator_of_notMem (show t ∉ Ioc (0 : ℝ) (σ i) from fun h => hs h.2)]
        simp [f, rdfCausalKernel, rdfRecenteredHSQ, min_eq_right (not_le.mp hs).le]
    · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht),
        indicator_of_notMem (show t ∉ Ioc (0 : ℝ) (σ i) from fun h => ht h.1)]
  calc
    _ = ∫ t : ℝ, (Ioi (0 : ℝ)).indicator f t := (integral_indicator measurableSet_Ioi).symm
    _ = ∫ t in Ioc (0 : ℝ) (σ i), f t := by rw [he, integral_indicator measurableSet_Ioc]
    _ = ∫ t in (0 : ℝ)..σ i, f t := (intervalIntegral.integral_of_le (hσ i)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le (hσ i)]
      intro t ht
      simp only [f, rdfCausalKernel, Matrix.of_apply, rdfRecenteredHSQ, min_eq_left ht.2]

/-- The sufficient budget is an explicit finite sum of finite-interval
polynomial/exponential integrals, with the real left density retained. -/
theorem rdfWeightedKernelBudget_eq_finite_windows (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (δ : ℝ) :
    rdfWeightedKernelBudget ρ σ δ = ∑ i, ∑ j,
      ∫ t in (0 : ℝ)..σ i, exp (δ*t)*
        |ρ i*(Q0phys ρ σ i j*(t-σ i)+Qppphys ρ σ j j/2*(t-σ i)^2)| := by
  unfold rdfWeightedKernelBudget
  simp only [FMSA.matrixAbsSum, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    rdfCausalKernel_weighted_entry_integrable ρ σ δ i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => rdfCausalKernel_weighted_entry_integrable ρ σ δ i j)]
  exact Finset.sum_congr rfl (fun j _ => rdfCausalKernel_weighted_entry_integral_window ρ σ hσ δ i j)

theorem firstOrderMixtureRDF_certificate_of_weighted_budget (z : ι → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hv : 0 < vacMix ρ σ) (hρ : ∀ i, 0 < ρ i)
    (hσ : ∀ i, 0 < σ i) (K : TailMatrix ι N)
    (hK : ∀ u i j, K u i j=K u j i)
    (δ : ℝ) (hδ : 0 < δ) (hzδ : ∀ u, δ ≤ z u) (hbudget : rdfWeightedKernelBudget ρ σ δ < 1)
    (h0 : Fin N → Fin N → ℝ → ℝ) (href : ValidRadialHSReference z ρ σ h0) :
    (∀ i j r, r < edgeHi σ i j → rdfFirstOrderCausal z ρ σ K i j r=0) ∧
    (∀ τ i j r, 0 < r → r < edgeHi σ i j → h0 i j r+τ*rdfFirstOrderCausal z ρ σ K i j r = -1) ∧
    (∀ i j, rdfFirstOrderCausal z ρ σ K i j =ᵐ[volume.restrict (Ioi 0)]
      fun r => rdfActualC1 z ρ σ K i j r+
        radialMixtureConv (rdfActualHS z ρ σ) (rdfFirstOrderCausal z ρ σ K) ρ i j r+
          radialMixtureConv (rdfActualC1 z ρ σ K) h0 ρ i j r) :=
  firstOrderMixtureRDF_certificate z hz ρ σ hv hρ hσ K hK
    (rdfCausalTwoSided_integrable_of_weighted_budget z ρ σ K δ hδ hzδ hbudget) h0 href

end FMSA.ExactMSA.MultiTailMixture
