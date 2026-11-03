import MSAConvergence.YukawaConvolutionTest

/-! Exact core correction converting the honest smoothed test pairing into
the positive-radius Yukawa moment. No root-dependent error bound is used. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
namespace FMSA.Convergence.YukawaTestMoments
open FMSA.HardSphere FMSA.Convergence.YukawaConvolutionTest

def coreCorrection (s R t : ℝ) : ℝ :=
  |t| *smoothed s R |t|-exteriorCoefficient s R*|t| *exp (-s*|t|)

private theorem correction_outside (s R : ℝ) (hR : 0 < R) (t : ℝ) (ht : R ≤ |t|) :
    coreCorrection s R t=0 := by
  rw [coreCorrection,smoothed_exterior s R hR |t| ht]
  ring

/-- The fixed core correction is continuous, including r=0. -/
theorem core_correction_continuous (s R : ℝ) (hs : 0 < s) (hR : 0 < R) :
    Continuous (coreCorrection s R) := by
  have hc := (smoothed_L1_L2 s R hs hR).2.2
  unfold coreCorrection
  exact (continuous_abs.mul (hc.comp continuous_abs)).sub (by fun_prop)

/-- The correction supplies its own compact support and honest L1. -/
theorem core_correction_integrable (s R : ℝ) (hs : 0 < s) (hR : 0 < R) :
    Integrable (coreCorrection s R) := by
  have hsupp : Function.support (coreCorrection s R) ⊆ Icc (-R) R := by
    intro t ht
    by_contra hn
    exact ht (correction_outside s R hR t (lt_of_not_ge (fun h => hn (abs_le.mp h))).le)
  exact (core_correction_continuous s R hs hR).integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hsupp isClosed_Icc))

private theorem even_moment_integrable (f : ℝ → ℝ) (hi : Integrable (oddRadialMoment f))
    (s : ℝ) (hs : 0 < s) : Integrable (fun t : ℝ => |t| *f |t| *exp (-s*|t|)) := by
  have hp := oddRadialMoment_positive_integrable hi
  have he : IntegrableOn (fun t => t*f t*exp (-s*t)) (Ioi 0) := by
    refine hp.mul_bdd (c := 1) (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.mpr (by nlinarith [show 0 < t from ht])
  let m := (Ioi (0 : ℝ)).indicator (fun t => t*f t*exp (-s*t))
  have hm : Integrable m := he.integrable_indicator measurableSet_Ioi
  apply (hm.add hm.comp_neg).congr
  apply ae_of_all
  intro t
  rcases lt_trichotomy t 0 with hn|rfl|hp
  · simp only [Pi.add_apply,m,indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from not_lt.mpr hn.le),
      indicator_of_mem (show -t ∈ Ioi (0 : ℝ) from neg_pos.mpr hn),zero_add,abs_of_neg hn]
  · simp [m]
  · simp only [Pi.add_apply,m,indicator_of_mem (show t ∈ Ioi (0 : ℝ) from hp),
      indicator_of_notMem (show -t ∉ Ioi (0 : ℝ) from not_lt.mpr (neg_nonpos.mpr hp.le)),
      add_zero,abs_of_pos hp]

/-- Exact pairing-to-moment identity. The test agrees with Yukawa outside
R; inside R the ACTUAL hard-core value f=-1 fixes the correction completely. -/
theorem core_pairing_eq_yukawa_moment (s R : ℝ) (hs : 0 < s) (hR : 0 < R)
    (f : ℝ → ℝ) (hi : Integrable (oddRadialMoment f))
    (hcore : ∀ r : ℝ, 0 < r → r < R → f r= -1) :
    (∫ r : ℝ, r^2*f |r| *radialTest s R |r|) =
      2*exteriorCoefficient s R*(∫ r in Ioi (0 : ℝ), r*f r*exp (-s*r))-
        ∫ r : ℝ, coreCorrection s R r := by
  have hpoint (r : ℝ) : r^2*f |r| *radialTest s R |r| =
      exteriorCoefficient s R*(|r| *f |r| *exp (-s*|r|))-coreCorrection s R r := by
    by_cases hr : r=0
    · simp [hr,coreCorrection]
    have hcancel : r^2*radialTest s R |r| = |r| *smoothed s R |r| := by
      rw [← sq_abs r,radialTest]
      field_simp [(abs_pos.mpr hr).ne']
    have hc : f |r| *coreCorrection s R r= -coreCorrection s R r := by
      by_cases ht : |r| < R
      · rw [hcore |r| (abs_pos.mpr hr) ht]
        ring
      · rw [correction_outside s R hR r (not_lt.mp ht)]
        ring
    rw [show r^2*f |r| *radialTest s R |r|=f |r| *(r^2*radialTest s R |r|) by ring,hcancel]
    dsimp only [coreCorrection] at hc ⊢
    linear_combination hc
  have hwhole : Integrable (fun r : ℝ => |r| *f |r| *exp (-s*|r|)) := even_moment_integrable f hi s hs
  have hq := core_correction_integrable s R hs hR
  simp_rw [hpoint]
  rw [integral_sub (hwhole.const_mul _) hq,integral_const_mul,
    integral_comp_abs (f := fun r => r*f r*exp (-s*r))]
  ring

end FMSA.Convergence.YukawaTestMoments
/-- info: 'FMSA.Convergence.YukawaTestMoments.core_correction_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.YukawaTestMoments.core_correction_continuous
/-- info: 'FMSA.Convergence.YukawaTestMoments.core_correction_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.YukawaTestMoments.core_correction_integrable
/-- info: 'FMSA.Convergence.YukawaTestMoments.core_pairing_eq_yukawa_moment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.YukawaTestMoments.core_pairing_eq_yukawa_moment
