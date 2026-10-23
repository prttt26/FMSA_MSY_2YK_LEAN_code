import LeanCode.YukawaOZ.MSAMultiTailRDFOZ
import LeanCode.YukawaOZ.MSAMultiTailCore
import LeanCode.Analysis.RadialConvolutionContinuity

/-! Regularity and actual weighted moments needed for real-space OZ inversion. -/
noncomputable section
open MeasureTheory Set Filter Topology Real
open FMSA.HardSphere
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTail
variable {ι : Type*} [Fintype ι]

theorem qPrime_measurable (xi : ℝ) (z Dt G : ι → ℝ) : Measurable (qPrime xi z Dt G) := by
  have hc : Continuous (qPrimeCore xi z Dt G) := by unfold qPrimeCore; fun_prop
  have ht : Continuous (qPrimeTail xi z Dt G) := by unfold qPrimeTail; fun_prop
  exact measurable_const.ite (measurableSet_Iio) (hc.measurable.ite measurableSet_Iic ht.measurable)

theorem convolution_measurable (xi : ℝ) (z Dt G : ι → ℝ) :
    Measurable (convolution xi z Dt G) := by
  have hqc : Continuous (qCore xi z Dt G) := by unfold qCore; fun_prop
  have hqt : Continuous (qTail xi z Dt G) := by unfold qTail; fun_prop
  have hc : Measurable (fun p : ℝ × ℝ => qPrime xi z Dt G (p.2 + p.1) * qCore xi z Dt G p.2) :=
    ((qPrime_measurable xi z Dt G).comp (measurable_snd.add measurable_fst)).mul
      (hqc.measurable.comp measurable_snd)
  have ht : Measurable (fun p : ℝ × ℝ => qPrime xi z Dt G (p.2 + p.1) * qTail xi z Dt G p.2) :=
    ((qPrime_measurable xi z Dt G).comp (measurable_snd.add measurable_fst)).mul
      (hqt.measurable.comp measurable_snd)
  have hi := hc.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))
  have hj := ht.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (1 : ℝ)))
  unfold convolution
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  exact hi.measurable.add hj.measurable

theorem correlation_measurable (xi : ℝ) (z Dt G : ι → ℝ) :
    Measurable (correlation xi z Dt G) := by
  unfold correlation
  exact ((qPrime_measurable xi z Dt G).neg.add
    ((convolution_measurable xi z Dt G).const_mul _)).div (by fun_prop)

def cCoreMoment (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) : ℝ :=
  (-qPrimeCore xi z Dt G r + rhoOf xi * closedConvolution xi z Dt G r) / (2 * Real.pi)

theorem cCoreMoment_continuous (xi : ℝ) (z Dt G : ι → ℝ) :
    Continuous (cCoreMoment xi z Dt G) := by
  have hc := (closedConvolution_contDiff xi z Dt G).continuous
  unfold cCoreMoment
  have hq : Continuous (qPrimeCore xi z Dt G) := by unfold qPrimeCore; fun_prop
  exact (hq.neg.add (hc.const_mul _)).div_const _

theorem correlation_core_moment (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    r * correlation xi z Dt G r = cCoreMoment xi z Dt G r := by
  rw [correlation_core_eq_closed xi z Dt G hz hr hr1]
  unfold closedCorrelation cCoreMoment
  field_simp [hr.ne', Real.pi_ne_zero]

theorem correlation_weight_integrable (xi : ℝ) (z K Dt G : ι → ℝ)
    (hz : ∀ u, 0 < z u) (hroot : IsRoot xi z K Dt G)
    (w : ℝ → ℝ) (hw : Continuous w)
    (ht : ∀ u, IntegrableOn (fun r => exp (-z u * r) * w r) (Ioi 1)) :
    IntegrableOn (fun r => (r * correlation xi z Dt G r) * w r) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one]
  apply IntegrableOn.union
  · have hi : IntegrableOn (fun r => cCoreMoment xi z Dt G r * w r) (Ioc 0 1) :=
      ((cCoreMoment_continuous xi z Dt G).mul hw).integrableOn_Ioc
    refine hi.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc, (volume.restrict (Ioc (0 : ℝ) 1)).ae_ne 1]
      with r hr hn
    rw [correlation_core_moment xi z Dt G hz hr.1 (lt_of_le_of_ne hr.2 hn)]
  · have hi : IntegrableOn (fun r => ∑ u, (K u * exp (z u)) * (exp (-z u * r) * w r))
        (Ioi 1) := integrable_finsetSum _ (fun u _ => (ht u).const_mul _)
    refine hi.congr_fun ?_ measurableSet_Ioi
    intro r hr
    change 1 < r at hr
    change (∑ u, (K u * exp (z u)) * (exp (-z u * r) * w r)) =
      (r * correlation xi z Dt G r) * w r
    rw [correlation_exterior_of_root xi z K Dt G hz hroot hr, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    rw [show -z u * (r - 1) = z u + -z u * r by ring, exp_add]
    field_simp [show r ≠ 0 by linarith]

theorem correlation_moment_integrable (xi : ℝ) (z K Dt G : ι → ℝ)
    (hz : ∀ u, 0 < z u) (hroot : IsRoot xi z K Dt G) :
    IntegrableOn (fun r => r * correlation xi z Dt G r) (Ioi 0) := by
  simpa only [mul_one] using correlation_weight_integrable xi z K Dt G hz hroot
    (fun _ => 1) continuous_const (fun u => by
      simpa only [mul_one] using integrableOn_exp_mul_Ioi (neg_neg_of_pos (hz u)) 1)

theorem correlation_first_moment_integrable (xi : ℝ) (z K Dt G : ι → ℝ)
    (hz : ∀ u, 0 < z u) (hroot : IsRoot xi z K Dt G) :
    IntegrableOn (fun r => r * (r * correlation xi z Dt G r)) (Ioi 0) := by
  have hi := correlation_weight_integrable xi z K Dt G hz hroot (fun r => r) continuous_id
    (fun u => by
      simpa only [mul_comm] using (integrableOn_Ioi_id_mul_exp_neg (hz u)).mono_set
        (Ioi_subset_Ioi zero_le_one))
  simpa only [mul_comm] using hi

theorem correlation_odd_ae_continuous (xi : ℝ) (z K Dt G : ι → ℝ)
    (hz : ∀ u, 0 < z u) (hroot : IsRoot xi z K Dt G) :
    ∀ᵐ v, ContinuousAt (oddRadialMoment (correlation xi z Dt G)) v := by
  apply oddRadialMoment_ae_continuous_of_junction
  · exact (correlation_contDiffOn_core xi z Dt G hz).continuousOn
  · have hc : ContinuousOn (fun r => (∑ u, K u * exp (-z u * (r - 1))) / r) (Ioi 1) := by
      apply ContinuousOn.div (by fun_prop) continuous_id.continuousOn
      intro r hr; change r ≠ 0; change 1 < r at hr; linarith
    apply hc.congr
    intro r hr
    change correlation xi z Dt G r = (∑ u, K u * exp (-z u * (r - 1))) / r
    rw [correlation_exterior_of_root xi z K Dt G hz hroot hr, Finset.sum_div]

theorem reconstructedH_moment (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) :
    r * reconstructedH xi z Dt G r = rdfRadialMoment xi z Dt G r := by
  by_cases hr : r = 0
  · subst r; simp [rdfRadialMoment_zero xi z Dt G le_rfl]
  · unfold reconstructedH; field_simp

theorem reconstructedH_moment_measurable (xi : ℝ) (z Dt G : ι → ℝ) :
    Measurable (fun r => r * reconstructedH xi z Dt G r) := by
  have hc : Continuous (fun r => rdfExcess xi z Dt G (max 0 r)) :=
    (rdfExcess_continuousOn xi z Dt G).comp_continuous
      (continuous_const.max continuous_id) (fun r => le_max_left 0 r)
  have hs : Measurable (excessSupported xi z Dt G) := by
    convert hc.measurable.indicator (measurableSet_Ioi (a := (0 : ℝ))) using 1
    funext r
    by_cases hr : r ∈ Ioi (0 : ℝ)
    · have hrl : 0 < r := hr
      simp only [excessSupported, indicator_of_mem hr, max_eq_right hrl.le]
    · simp only [excessSupported, indicator_of_notMem hr]
  simp_rw [reconstructedH_moment]
  exact ((measurable_id.neg).indicator measurableSet_Ioc).add
    (hs.comp (measurable_id.sub measurable_const))

theorem reconstructedH_odd_ae_continuous (xi : ℝ) (z Dt G : ι → ℝ) :
    ∀ᵐ v, ContinuousAt (oddRadialMoment (reconstructedH xi z Dt G)) v := by
  apply oddRadialMoment_ae_continuous_of_junction
  · apply (continuous_const (y := (-1 : ℝ))).continuousOn.congr
    intro r hr
    exact reconstructedH_core xi z Dt G hr.1 hr.2
  · have hc : Continuous (fun r => causalMoment xi z Dt G (max 0 (r - 1))) :=
      (causalMoment_continuousOn xi z Dt G).comp_continuous (by fun_prop)
        (fun r => le_max_left 0 (r - 1))
    have he : ContinuousOn (fun r => causalMoment xi z Dt G (max 0 (r - 1)) / r - 1) (Ioi 1) :=
      (hc.continuousOn.div continuous_id.continuousOn
        (fun r hr => by change r ≠ 0; change 1 < r at hr; linarith)).sub continuous_const.continuousOn
    apply he.congr
    intro r hr
    change 1 < r at hr
    rw [reconstructedH_exterior xi z Dt G hr]
    simp only [candidateRDF, if_neg (not_lt_of_ge hr.le), max_eq_right (by linarith : 0 ≤ r - 1)]

end FMSA.ExactMSA.MultiTail
