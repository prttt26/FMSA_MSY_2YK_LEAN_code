import FMSAPaper.MixedRateWindows

/-! Mixed-rate convolution with the actual constant-core/exponential-tail shape. -/
noncomputable section
open MeasureTheory Set Real

namespace FMSA.Paper.MixedRatePlateau

open MixedRateTails MixedRateWindows

def plateau (w b c t : ℝ) : ℝ := box b c t + tail w c t

theorem plateau_piecewise (w b c t : ℝ) (hbc : b <= c) :
    plateau w b c t = if t < b then 0 else if t < c then 1 else exp (-w * (t - c)) := by
  by_cases hb : t < b
  · have hc : t < c := hb.trans_le hbc
    simp [plateau, box, tail, hb, hc, not_le.mpr hb]
  · by_cases hc : t < c
    · have hm : t ∈ Ico b c := ⟨le_of_not_gt hb, hc⟩
      simp [plateau, box, tail, hb, hc, indicator_of_mem hm]
    · simp [plateau, box, tail, hb, hc]

theorem tail_tail_integrable (z w a b r : ℝ) (hz : 0 < z) (hw : 0 < w) :
    Integrable (fun t : ℝ => tail z a (t + r) * tail w b t) := by
  rw [product_tail_indicator, integrable_indicator_iff measurableSet_Ici,
    integrableOn_Ici_iff_integrableOn_Ioi]
  have he (t : ℝ) : exp (-z * (t + r - a) - w * (t - b)) =
      exp (-z * (r - a) + w * b) * exp (-(z + w) * t) := by
    rw [← exp_add]
    congr 1
    ring
  simp_rw [he]
  exact (integrableOn_exp_mul_Ioi (by linarith : -(z + w) < 0) _).const_mul _

theorem tail_box_integrable (z a b c r : ℝ) :
    Integrable (fun t : ℝ => tail z a (t + r) * box b c t) := by
  rw [tail_box_indicator, integrable_indicator_iff measurableSet_Ico]
  have hc : Continuous (fun t : ℝ => exp (-z * (t + r - a))) := by fun_prop
  exact hc.continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self

theorem tail_plateau_overlap_split (z w a b c r : ℝ) (hz : 0 < z) (hw : 0 < w) :
    (∫ t : ℝ, tail z a (t + r) * plateau w b c t) =
      (∫ t : ℝ, tail z a (t + r) * box b c t) +
      (∫ t : ℝ, tail z a (t + r) * tail w c t) := by
  simp_rw [plateau, mul_add]
  exact integral_add (tail_box_integrable z a b c r) (tail_tail_integrable z w a c r hz hw)

theorem tail_plateau_overlap_left (z w a b c r : ℝ) (hz : 0 < z) (hw : 0 < w)
    (hr : r <= a - c) :
    (∫ t : ℝ, tail z a (t + r) * plateau w b c t) =
      (exp (w * (c - a)) / (z + w)) * exp (w * r) := by
  rw [tail_plateau_overlap_split z w a b c r hz hw, tail_box_overlap_left z a b c r hr,
    tail_overlap_left z w a c r hz hw hr, zero_add]

theorem tail_plateau_overlap_middle (z w a b c r : ℝ) (hz : 0 < z) (hw : 0 < w)
    (hrlo : a - c <= r) (hrhi : r <= a - b) :
    (∫ t : ℝ, tail z a (t + r) * plateau w b c t) =
      1 / z + (exp (z * (a - c)) * (1 / (z + w) - 1 / z)) * exp (-z * r) := by
  rw [tail_plateau_overlap_split z w a b c r hz hw,
    tail_box_overlap_middle z a b c r hz hrlo hrhi, tail_overlap_right z w a c r hz hw hrlo]
  ring

theorem tail_plateau_overlap_right (z w a b c r : ℝ) (hz : 0 < z) (hw : 0 < w)
    (hbc : b <= c) (hr : a - b <= r) :
    (∫ t : ℝ, tail z a (t + r) * plateau w b c t) =
      ((exp (z * (a - b)) - exp (z * (a - c))) / z +
        exp (z * (a - c)) / (z + w)) * exp (-z * r) := by
  rw [tail_plateau_overlap_split z w a b c r hz hw,
    tail_box_overlap_right z a b c r hz hbc hr,
    tail_overlap_right z w a c r hz hw (by linarith)]
  ring

end FMSA.Paper.MixedRatePlateau

/-- info: 'FMSA.Paper.MixedRatePlateau.plateau_piecewise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRatePlateau.plateau_piecewise

/-- info: 'FMSA.Paper.MixedRatePlateau.tail_tail_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRatePlateau.tail_tail_integrable

/-- info: 'FMSA.Paper.MixedRatePlateau.tail_box_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRatePlateau.tail_box_integrable

/-- info: 'FMSA.Paper.MixedRatePlateau.tail_plateau_overlap_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRatePlateau.tail_plateau_overlap_split

/-- info: 'FMSA.Paper.MixedRatePlateau.tail_plateau_overlap_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRatePlateau.tail_plateau_overlap_left

/-- info: 'FMSA.Paper.MixedRatePlateau.tail_plateau_overlap_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRatePlateau.tail_plateau_overlap_middle

/-- info: 'FMSA.Paper.MixedRatePlateau.tail_plateau_overlap_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRatePlateau.tail_plateau_overlap_right
