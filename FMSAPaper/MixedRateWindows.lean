import FMSAPaper.MixedRateTails

/-! Exact finite-window overlap for the constant part of a Baxter C mode. -/
noncomputable section
open MeasureTheory Set Real

namespace FMSA.Paper.MixedRateWindows

open MixedRateTails

def box (a b : ℝ) : ℝ → ℝ := (Ico a b).indicator (fun _ => 1)

theorem tail_box_indicator (z a b c r : ℝ) :
    (fun t => tail z a (t + r) * box b c t) =
      (Ico (max (a - r) b) c).indicator (fun t => exp (-z * (t + r - a))) := by
  funext t
  by_cases h : t ∈ Ico (max (a - r) b) c
  · have hb : t ∈ Ico b c := ⟨(max_le_iff.mp h.1).2, h.2⟩
    have ha : ¬t + r < a := by have := (max_le_iff.mp h.1).1; linarith
    simp only [tail, if_neg ha, box, indicator_of_mem hb, indicator_of_mem h, mul_one]
  · rw [indicator_of_notMem h]
    by_cases hb : t ∈ Ico b c
    · have ha : t + r < a := by
        by_contra hh
        apply h
        exact ⟨max_le (by linarith) hb.1, hb.2⟩
      simp [tail, ha]
    · simp [box, indicator_of_notMem hb]

theorem integral_shifted_exp (z a r l h : ℝ) (hz : 0 < z) :
    (∫ t in l..h, exp (-z * (t + r - a))) =
      (exp (-z * (l + r - a)) - exp (-z * (h + r - a))) / z := by
  have he (t : ℝ) : exp (-z * (t + r - a)) = exp (-z * (r - a)) * exp (-z * t) := by
    rw [← exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,
    ExactMSA.Breakpoint.integral_exp_linear l h (-z) (neg_ne_zero.mpr hz.ne')]
  rw [div_neg]
  ring

theorem tail_box_overlap (z a b c r : ℝ) (hz : 0 < z)
    (h : max (a - r) b <= c) :
    (∫ t : ℝ, tail z a (t + r) * box b c t) =
      (exp (-z * (max (a - r) b + r - a)) - exp (-z * (c + r - a))) / z := by
  rw [tail_box_indicator, integral_indicator measurableSet_Ico,
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le h]
  exact integral_shifted_exp z a r _ _ hz

theorem tail_box_overlap_left (z a b c r : ℝ) (hr : r <= a - c) :
    (∫ t : ℝ, tail z a (t + r) * box b c t) = 0 := by
  rw [tail_box_indicator]
  have h : c <= max (a - r) b := (by linarith : c <= a - r).trans (le_max_left _ _)
  simp [Ico_eq_empty_of_le h]

theorem tail_box_overlap_middle (z a b c r : ℝ) (hz : 0 < z)
    (hrlo : a - c <= r) (hrhi : r <= a - b) :
    (∫ t : ℝ, tail z a (t + r) * box b c t) =
      1 / z - (exp (z * (a - c)) / z) * exp (-z * r) := by
  have hab : b <= a - r := by linarith
  rw [tail_box_overlap z a b c r hz (max_le (by linarith) (by linarith)), max_eq_left hab]
  rw [show -z * (a - r + r - a) = 0 by ring, exp_zero,
    show -z * (c + r - a) = z * (a - c) + -z * r by ring, exp_add]
  ring

theorem tail_box_overlap_right (z a b c r : ℝ) (hz : 0 < z)
    (hbc : b <= c) (hr : a - b <= r) :
    (∫ t : ℝ, tail z a (t + r) * box b c t) =
      ((exp (z * (a - b)) - exp (z * (a - c))) / z) * exp (-z * r) := by
  have hab : a - r <= b := by linarith
  rw [tail_box_overlap z a b c r hz (by rw [max_eq_right hab]; exact hbc), max_eq_right hab]
  rw [show -z * (b + r - a) = z * (a - b) + -z * r by ring,
    show -z * (c + r - a) = z * (a - c) + -z * r by ring, exp_add, exp_add]
  ring

end FMSA.Paper.MixedRateWindows

/-- info: 'FMSA.Paper.MixedRateWindows.tail_box_indicator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateWindows.tail_box_indicator

/-- info: 'FMSA.Paper.MixedRateWindows.integral_shifted_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateWindows.integral_shifted_exp

/-- info: 'FMSA.Paper.MixedRateWindows.tail_box_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateWindows.tail_box_overlap

/-- info: 'FMSA.Paper.MixedRateWindows.tail_box_overlap_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateWindows.tail_box_overlap_left

/-- info: 'FMSA.Paper.MixedRateWindows.tail_box_overlap_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateWindows.tail_box_overlap_middle

/-- info: 'FMSA.Paper.MixedRateWindows.tail_box_overlap_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateWindows.tail_box_overlap_right
