import LeanCode.YukawaOZ.MSAMultiTailRDFGlobal
import LeanCode.YukawaOZ.MSAMultiTailRDFMoments
import LeanCode.Analysis.CausalRenewalBound

/-! Decay of the actual constructed RDF excess under an explicit weighted
kernel budget. No hard-core OZ conclusion is assumed in the decay proof. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators

namespace FMSA.ExactMSA.MultiTail
variable {ι : Type*} [Fintype ι]

theorem q_weight_integrableOn (xi : ℝ) (z Dt G : ι → ℝ) (h : ℝ → ℝ)
    (hc : Continuous h)
    (ht : ∀ u, IntegrableOn (fun r => exp (-z u * r) * h r) (Ioi 1)) :
    IntegrableOn (fun r => q xi z Dt G r * h r) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  apply IntegrableOn.union
  · refine ((qRight_continuous xi z Dt G).mul hc).integrableOn_Ioc.congr_fun
      (fun r hr => ?_) measurableSet_Ioc
    change qRight xi z Dt G r * h r = q xi z Dt G r * h r
    rw [qRight_eq_q xi z Dt G hr.1.le]
  · have he : (fun r => qTail xi z Dt G r * h r) =
        fun r => ∑ u, (W xi z Dt G u + C xi z Dt G u * exp (z u)) *
          (exp (-z u * r) * h r) := by
      funext r
      rw [qTail_decomposition, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      unfold tailQ
      ring
    have hi : IntegrableOn (fun r => qTail xi z Dt G r * h r) (Ioi 1) := by
      rw [he]
      exact integrable_finsetSum _ (fun u _ => (ht u).const_mul _)
    refine hi.congr_fun (fun r hr => ?_) measurableSet_Ioi
    dsimp only
    change 1 < r at hr
    rw [q, if_neg (by linarith [hr] : ¬ r < 0), if_neg (not_le.mpr hr)]

theorem q_background_convolution (xi : ℝ) (z Dt G : ι → ℝ)
    (hz : ∀ u, 0 < z u) {r : ℝ} (hr : 1 ≤ r) :
    (∫ t in (0 : ℝ)..r, q xi z Dt G t * (r - t + 1)) =
      (r + 1) * qMoment0 xi z Dt G - qMoment1 xi z Dt G -
        ∑ u, (W xi z Dt G u + C xi z Dt G u * exp (z u)) *
          exp (-z u * r) * (1 / z u - 1 / (z u) ^ 2) := by
  have hqid := q_weight_integrableOn xi z Dt G (fun t => t) continuous_id
    (fun u => by simpa only [mul_comm] using
      (integrableOn_Ioi_id_mul_exp_neg (hz u)).mono_set (Ioi_subset_Ioi zero_le_one))
  have hq0 : IntegrableOn (q xi z Dt G) (Ioi 0) := (q_integrable xi z Dt G hz).integrableOn
  have hwhole : IntegrableOn (fun t => q xi z Dt G t * (r - t + 1)) (Ioi 0) := by
    have he : (fun t => q xi z Dt G t * (r - t + 1)) =
        fun t => (r + 1) * q xi z Dt G t - q xi z Dt G t * t := by funext t; ring
    rw [he]
    exact (hq0.const_mul _).sub hqid
  have hfull : (∫ t in Ioi (0 : ℝ), q xi z Dt G t * (r - t + 1)) =
      (r + 1) * qMoment0 xi z Dt G - qMoment1 xi z Dt G := by
    have he : (fun t => q xi z Dt G t * (r - t + 1)) =
        fun t => (r + 1) * q xi z Dt G t - q xi z Dt G t * t := by funext t; ring
    rw [he, integral_sub (hq0.const_mul _) hqid, integral_const_mul,
      ← qMoment0_eq_integral xi z Dt G hz, ← qMoment1_eq_integral xi z Dt G hz]
  have htail : (∫ t in Ioi r, q xi z Dt G t * (r - t + 1)) =
      ∑ u, (W xi z Dt G u + C xi z Dt G u * exp (z u)) *
        exp (-z u * r) * (1 / z u - 1 / (z u) ^ 2) := by
    have ht (u : ι) : IntegrableOn (fun t => exp (-z u * t) * (r - t + 1)) (Ioi r) := by
      have he : (fun t => exp (-z u * t) * (r - t + 1)) =
          fun t => (r + 1) * exp (-z u * t) - t * exp (-z u * t) := by funext t; ring
      rw [he]
      exact ((integrableOn_exp_mul_Ioi (by linarith [hz u] : -z u < 0) r).const_mul _).sub
        ((integrableOn_Ioi_id_mul_exp_neg (hz u)).mono_set (Ioi_subset_Ioi (by linarith)))
    have he : (∫ t in Ioi r, q xi z Dt G t * (r - t + 1)) =
        ∫ t in Ioi r, ∑ u, (W xi z Dt G u + C xi z Dt G u * exp (z u)) *
          (exp (-z u * t) * (r - t + 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      change r < t at ht
      rw [q, if_neg (by linarith : ¬ t < 0), if_neg (by linarith : ¬ t ≤ 1),
        qTail_decomposition, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      unfold tailQ
      ring
    rw [he, integral_finsetSum _ (fun u _ => (ht u).const_mul _)]
    apply Finset.sum_congr rfl
    intro u _
    rw [integral_const_mul]
    have ep : (fun t => exp (-z u * t) * (r - t + 1)) =
        fun t => (r + 1) * exp (-z u * t) - t * exp (-z u * t) := by funext t; ring
    rw [ep, integral_sub
      ((integrableOn_exp_mul_Ioi (by linarith [hz u] : -z u < 0) r).const_mul _)
      ((integrableOn_Ioi_id_mul_exp_neg (hz u)).mono_set (Ioi_subset_Ioi (by linarith))),
      integral_const_mul, integral_exp_mul_Ioi (by linarith [hz u] : -z u < 0),
      exp_first_Ioi (z u) r (hz u)]
    ring
  have hb : IntervalIntegrable (fun t => q xi z Dt G t * (r - t + 1)) volume 0 r := by
    refine (((qRight_continuous xi z Dt G).mul
      (by fun_prop : Continuous (fun t : ℝ => r - t + 1))).intervalIntegrable 0 r).congr
      (fun t ht => ?_)
    rw [uIoc_of_le (by linarith : (0 : ℝ) ≤ r)] at ht
    change qRight xi z Dt G t * (r - t + 1) = q xi z Dt G t * (r - t + 1)
    rw [qRight_eq_q xi z Dt G ht.1.le]
  have he := intervalIntegral.integral_interval_add_Ioi' hb
    (hwhole.mono_set (Ioi_subset_Ioi (by linarith : (0 : ℝ) ≤ r)))
  rw [hfull, htail] at he
  linear_combination he

def rdfExcess (xi : ℝ) (z Dt G : ι → ℝ) (u : ℝ) : ℝ :=
  causalMoment xi z Dt G u - (u + 1)

def excessSource (xi : ℝ) (z Dt G : ι → ℝ) (u : ℝ) : ℝ :=
  gsource xi z Dt G u / (2 * π) - (u + 1) +
    rhoOf xi * ∫ t in (0 : ℝ)..u, qRight xi z Dt G (u - t) * (t + 1)

theorem excessSource_continuous (xi : ℝ) (z Dt G : ι → ℝ) :
    Continuous (excessSource xi z Dt G) := by
  unfold excessSource
  apply Continuous.add
  · exact ((gsource_continuous xi z Dt G).div_const _).sub (by fun_prop)
  · apply Continuous.const_mul
    have hq : Continuous (fun p : ℝ × ℝ => qRight xi z Dt G (p.1 - p.2)) :=
      (qRight_continuous xi z Dt G).comp (by fun_prop)
    have hp : Continuous (fun p : ℝ × ℝ => p.2 + 1) := by fun_prop
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (hq.mul hp) continuous_id

def excessTail (xi : ℝ) (z Dt G : ι → ℝ) (u : ι) : ℝ :=
  z u * C xi z Dt G u / (2 * π) - rhoOf xi *
    (W xi z Dt G u + C xi z Dt G u * exp (z u)) * (1 / z u - 1 / (z u) ^ 2)

theorem excessSource_tail (xi : ℝ) (z Dt G : ι → ℝ)
    (hxi : 1 - xi ≠ 0) (hz : ∀ u, 0 < z u) {r : ℝ} (hr : 1 ≤ r) :
    excessSource xi z Dt G r = ∑ u, excessTail xi z Dt G u * exp (-z u * r) := by
  have he : (∫ t in (0 : ℝ)..r, qRight xi z Dt G (r - t) * (t + 1)) =
      ∫ t in (0 : ℝ)..r, q xi z Dt G t * (r - t + 1) := by
    calc
      _ = ∫ t in (0 : ℝ)..r, (fun t => qRight xi z Dt G t * (r - t + 1)) (r - t) := by
        apply intervalIntegral.integral_congr
        intro t _; dsimp only; congr 1; ring
      _ = ∫ t in (0 : ℝ)..r, qRight xi z Dt G t * (r - t + 1) := by
        simpa using intervalIntegral.integral_comp_sub_left
          (f := fun t => qRight xi z Dt G t * (r - t + 1)) (a := (0 : ℝ)) (b := r) r
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ r)] at ht
        dsimp only
        rw [qRight_eq_q xi z Dt G ht.1]
  unfold excessSource
  rw [he, q_background_convolution xi z Dt G hz hr]
  have hn := rdf_background_normalization xi z Dt G hxi (fun u => (hz u).ne')
  unfold gsource
  rw [add_div, add_div, Finset.sum_div]
  have hρ : rhoOf xi * ((r + 1) * qMoment0 xi z Dt G - qMoment1 xi z Dt G -
      ∑ u, (W xi z Dt G u + C xi z Dt G u * exp (z u)) *
        exp (-z u * r) * (1 / z u - 1 / (z u) ^ 2)) =
      rhoOf xi * ((r + 1) * qMoment0 xi z Dt G - qMoment1 xi z Dt G) -
        ∑ u, rhoOf xi * ((W xi z Dt G u + C xi z Dt G u * exp (z u)) *
          exp (-z u * r) * (1 / z u - 1 / (z u) ^ 2)) := by
    rw [← Finset.mul_sum]; ring
  rw [hρ]
  have hsum : (∑ u, z u * C xi z Dt G u * exp (-z u * r) / (2 * π)) -
      (∑ u, rhoOf xi * ((W xi z Dt G u + C xi z Dt G u * exp (z u)) *
        exp (-z u * r) * (1 / z u - 1 / (z u) ^ 2))) =
      ∑ u, excessTail xi z Dt G u * exp (-z u * r) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _; unfold excessTail; ring
  linear_combination r * hn.1 + hn.2 + hsum

theorem rdfExcess_continuousOn (xi : ℝ) (z Dt G : ι → ℝ) :
    ContinuousOn (rdfExcess xi z Dt G) (Ici 0) :=
  (causalMoment_continuousOn xi z Dt G).sub (by fun_prop)

theorem rdfExcess_renewal (xi : ℝ) (z Dt G : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    rdfExcess xi z Dt G r = excessSource xi z Dt G r +
      ∫ t in (0 : ℝ)..r, (rhoOf xi * qRight xi z Dt G (r - t)) * rdfExcess xi z Dt G t := by
  let yext := fun t => causalMoment xi z Dt G (max 0 t) - (t + 1)
  have hyext : Continuous yext :=
    ((causalMoment_continuousOn xi z Dt G).comp_continuous
      (continuous_const.max continuous_id) (fun t => le_max_left 0 t)).sub (by fun_prop)
  have hi1 : IntervalIntegrable (fun t =>
      (rhoOf xi * qRight xi z Dt G (r - t)) * rdfExcess xi z Dt G t) volume 0 r := by
    have hc : Continuous (fun t => (rhoOf xi * qRight xi z Dt G (r - t)) * yext t) :=
      (((qRight_continuous xi z Dt G).comp
        (by fun_prop : Continuous (fun t : ℝ => r - t))).const_mul (rhoOf xi)).mul hyext
    refine (hc.intervalIntegrable 0 r).congr
      (fun t ht => ?_)
    rw [uIoc_of_le hr] at ht
    dsimp [yext, rdfExcess]
    rw [max_eq_right ht.1.le]
  have hi2 : IntervalIntegrable (fun t =>
      rhoOf xi * (qRight xi z Dt G (r - t) * (t + 1))) volume 0 r := by
    apply Continuous.intervalIntegrable
    exact ((((qRight_continuous xi z Dt G).comp
      (continuous_const.sub continuous_id)).mul (by fun_prop)).const_mul _)
  have he : (∫ t in (0 : ℝ)..r, rhoOf xi * q xi z Dt G (r - t) * causalMoment xi z Dt G t) =
      (∫ t in (0 : ℝ)..r, (rhoOf xi * qRight xi z Dt G (r - t)) * rdfExcess xi z Dt G t) +
        rhoOf xi * (∫ t in (0 : ℝ)..r, qRight xi z Dt G (r - t) * (t + 1)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hi1 hi2]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hr] at ht
    dsimp only
    rw [qRight_eq_q xi z Dt G (by linarith [ht.2])]
    unfold rdfExcess
    ring
  change causalMoment xi z Dt G r - (r + 1) = excessSource xi z Dt G r + _
  rw [causalMoment_renewal xi z Dt G hr, he]
  unfold excessSource
  ring

theorem excessSource_weighted_bounded (xi : ℝ) (z Dt G : ι → ℝ)
    (hxi : 1 - xi ≠ 0) (hz : ∀ u, 0 < z u) {δ : ℝ} (hδz : ∀ u, δ ≤ z u) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r, 0 ≤ r → exp (δ * r) * |excessSource xi z Dt G r| ≤ B := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (((by fun_prop : Continuous (fun r : ℝ => exp (δ * r))).mul
      (excessSource_continuous xi z Dt G)).continuousOn (s := Icc 0 1))
  let S := ∑ u, |excessTail xi z Dt G u|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨max C 0 + S, by positivity, fun r hr => ?_⟩
  by_cases hr1 : r ≤ 1
  · have hb := hC r ⟨hr, hr1⟩
    change ‖exp (δ * r) * excessSource xi z Dt G r‖ ≤ C at hb
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)] at hb
    exact hb.trans (by dsimp only [S]; linarith [le_max_left C 0])
  · rw [excessSource_tail xi z Dt G hxi hz (le_of_not_ge hr1)]
    have he (u : ι) : exp (δ * r) * exp (-z u * r) ≤ 1 := by
      rw [← exp_add]
      apply exp_le_one_iff.mpr
      nlinarith [hδz u]
    have hsum : exp (δ * r) * |∑ u, excessTail xi z Dt G u * exp (-z u * r)| ≤ S := by
      have hn : |∑ u, excessTail xi z Dt G u * exp (-z u * r)| ≤
          ∑ u, |excessTail xi z Dt G u * exp (-z u * r)| := by
        simpa only [Real.norm_eq_abs] using norm_sum_le Finset.univ
          (fun u => excessTail xi z Dt G u * exp (-z u * r))
      calc
        _ ≤ exp (δ * r) * (∑ u, |excessTail xi z Dt G u * exp (-z u * r)|) :=
          mul_le_mul_of_nonneg_left hn (exp_pos _).le
        _ = ∑ u, exp (δ * r) * |excessTail xi z Dt G u * exp (-z u * r)| := Finset.mul_sum _ _ _
        _ ≤ S := by
          apply Finset.sum_le_sum
          intro u _
          rw [abs_mul, abs_of_pos (exp_pos _)]
          calc exp (δ * r) * (|excessTail xi z Dt G u| * exp (-z u * r)) =
                |excessTail xi z Dt G u| * (exp (δ * r) * exp (-z u * r)) := by ring
            _ ≤ |excessTail xi z Dt G u| := by
              simpa using mul_le_mul_of_nonneg_left (he u) (abs_nonneg _)
    exact hsum.trans (by linarith [le_max_right C 0])

def weightedKernelBudget (xi : ℝ) (z Dt G : ι → ℝ) (δ : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), exp (δ * t) * |rhoOf xi * q xi z Dt G t|

theorem weightedKernel_integrable (xi : ℝ) (z Dt G : ι → ℝ)
    {δ : ℝ} (hδz : ∀ u, δ < z u) :
    IntegrableOn (fun t => exp (δ * t) * |rhoOf xi * qRight xi z Dt G t|) (Ioi 0) := by
  have hi := q_weight_integrableOn xi z Dt G (fun t => exp (δ * t)) (by fun_prop)
    (fun u => by
      have he : (fun t => exp (-z u * t) * exp (δ * t)) = fun t => exp ((δ - z u) * t) := by
        funext t; rw [← exp_add]; congr 1; ring
      rw [he]
      exact integrableOn_exp_mul_Ioi (by linarith [hδz u]) 1)
  have hab : IntegrableOn (fun t => |rhoOf xi * (q xi z Dt G t * exp (δ * t))|) (Ioi 0) :=
    (hi.const_mul (rhoOf xi)).abs
  refine hab.congr_fun (fun t ht => ?_) measurableSet_Ioi
  dsimp only
  rw [qRight_eq_q xi z Dt G ht.le, abs_mul, abs_mul, abs_of_pos (exp_pos _), abs_mul]
  ring

/-- Actual exponential decay and L1 of y(u)-(u+1), constructed from the BH
kernel and source. Only an explicit kernel budget below one is assumed. -/
theorem rdfExcess_decay_of_small_budget (xi : ℝ) (z Dt G : ι → ℝ)
    (hxi : 1 - xi ≠ 0) (hz : ∀ u, 0 < z u) {δ : ℝ}
    (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hsmall : weightedKernelBudget xi z Dt G δ < 1) :
    IntegrableOn (rdfExcess xi z Dt G) (Ioi 0) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ r, 0 ≤ r →
        exp (δ * r) * |rdfExcess xi z Dt G r| ≤ B / (1 - weightedKernelBudget xi z Dt G δ) := by
  obtain ⟨B, hB, hforce⟩ := excessSource_weighted_bounded xi z Dt G hxi hz (fun u => (hδz u).le)
  have hm : (∫ t in Ioi (0 : ℝ), exp (δ * t) * |rhoOf xi * qRight xi z Dt G t|) ≤
      weightedKernelBudget xi z Dt G δ := by
    apply le_of_eq
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only [weightedKernelBudget]
    rw [qRight_eq_q xi z Dt G ht.le]
  have hq := (qRight_continuous xi z Dt G).const_mul (rhoOf xi)
  have hy := rdfExcess_continuousOn xi z Dt G
  have heq := fun r hr => rdfExcess_renewal xi z Dt G (r := r) hr
  have hi := weightedKernel_integrable xi z Dt G hδz
  exact ⟨causal_renewal_integrable_of_weighted_bound hδ hq.continuousOn hy hi hm hsmall hB hforce heq,
    B, hB, fun r hr => causal_renewal_weighted_bound hq.continuousOn hy hi hm hsmall hB hforce heq hr⟩

theorem causalMoment_weighted_integrable_of_excess (xi : ℝ) (z Dt G : ι → ℝ)
    (he : IntegrableOn (rdfExcess xi z Dt G) (Ioi 0)) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u => exp (-s * u) * causalMoment xi z Dt G u) (Ioi 0) := by
  have hie : IntegrableOn (fun u => rdfExcess xi z Dt G u * exp (-s * u)) (Ioi 0) :=
    he.mul_bdd (by apply Continuous.aestronglyMeasurable; fun_prop)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          change 0 < u at hu
          rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
          exact exp_le_one_iff.mpr (by nlinarith [hu]))
  have hib : IntegrableOn (fun u => u * exp (-s * u) + exp (-s * u)) (Ioi 0) :=
    (integrableOn_Ioi_id_mul_exp_neg hs).add
      (integrableOn_exp_mul_Ioi (by linarith : -s < 0) 0)
  refine (hie.add hib).congr_fun (fun u _ => ?_) measurableSet_Ioi
  change rdfExcess xi z Dt G u * exp (-s * u) + (u * exp (-s * u) + exp (-s * u)) = _
  dsimp only [rdfExcess]
  ring

/-- Small budget supplies the L1 premise at every positive Laplace rate. -/
theorem causalMoment_laplace_of_small_budget (xi : ℝ) (z Dt G : ι → ℝ)
    (hxi : 1 - xi ≠ 0) (hz : ∀ u, 0 < z u) {δ : ℝ}
    (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hsmall : weightedKernelBudget xi z Dt G δ < 1) {s : ℝ} (hs : 0 < s) :
    2 * π * causalLaplace xi z Dt G s * factor xi z Dt G s = secondRHS xi z Dt G s :=
  causalMoment_laplace_identity xi z Dt G hz hs
    (causalMoment_weighted_integrable_of_excess xi z Dt G
      (rdfExcess_decay_of_small_budget xi z Dt G hxi hz hδ hδz hsmall).1 hs)

end FMSA.ExactMSA.MultiTail
