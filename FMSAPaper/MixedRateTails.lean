import LeanCode.YukawaOZMix.MSAMultiTailMixtureBaxter

/-! Exact mixed-rate exponential overlap integrals. The only denominator is
z+w, so coincident positive rates cause no exceptional case. -/
noncomputable section
open MeasureTheory Set Real

namespace FMSA.Paper.MixedRateTails

def tail (z a t : ℝ) : ℝ := if t < a then 0 else exp (-z * (t - a))

theorem product_tail_indicator (z w a b r : ℝ) :
    (fun t => tail z a (t + r) * tail w b t) =
      (Ici (max (a - r) b)).indicator
        (fun t => exp (-z * (t + r - a) - w * (t - b))) := by
  funext t
  by_cases h : max (a - r) b <= t
  · have ha : ¬t + r < a := by have := (max_le_iff.mp h).1; linarith
    have hb : ¬t < b := not_lt.mpr (max_le_iff.mp h).2
    have hm : t ∈ Ici (max (a - r) b) := h
    rw [indicator_of_mem hm]
    simp only [tail, if_neg ha, if_neg hb, ← exp_add]
    congr 1
    ring
  · have hout : t ∉ Ici (max (a - r) b) := h
    rw [indicator_of_notMem hout]
    unfold tail
    split_ifs <;> try simp
    exfalso
    apply h
    exact max_le (by linarith) (by linarith)

theorem exp_pair_integral (z w a b r c : ℝ) (hz : 0 < z) (hw : 0 < w) :
    (∫ t in Ioi c, exp (-z * (t + r - a) - w * (t - b))) =
      exp (-z * (c + r - a) - w * (c - b)) / (z + w) := by
  have he (t : ℝ) : exp (-z * (t + r - a) - w * (t - b)) =
      exp (-z * (r - a) + w * b) * exp (-(z + w) * t) := by
    rw [← exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -(z + w) < 0) c]
  simp only [neg_div_neg_eq]
  ring

theorem tail_overlap (z w a b r : ℝ) (hz : 0 < z) (hw : 0 < w) :
    (∫ t : ℝ, tail z a (t + r) * tail w b t) =
      exp (-z * (max (a - r) b + r - a) - w * (max (a - r) b - b)) / (z + w) := by
  rw [product_tail_indicator, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  exact exp_pair_integral z w a b r _ hz hw

/-- On the right of its sole knot a-b, the overlap is a constant times e^-zr. -/
theorem tail_overlap_right (z w a b r : ℝ) (hz : 0 < z) (hw : 0 < w)
    (hr : a - b <= r) :
    (∫ t : ℝ, tail z a (t + r) * tail w b t) =
      (exp (z * (a - b)) / (z + w)) * exp (-z * r) := by
  rw [tail_overlap z w a b r hz hw, max_eq_right (by linarith)]
  rw [show -z * (b + r - a) - w * (b - b) = z * (a - b) + -z * r by ring, exp_add]
  ring

/-- On the left of that knot, the rate is +w. No sum/difference rate survives
in the radial variable, even though the integration rate is z+w. -/
theorem tail_overlap_left (z w a b r : ℝ) (hz : 0 < z) (hw : 0 < w)
    (hr : r <= a - b) :
    (∫ t : ℝ, tail z a (t + r) * tail w b t) =
      (exp (w * (b - a)) / (z + w)) * exp (w * r) := by
  rw [tail_overlap z w a b r hz hw, max_eq_left (by linarith)]
  rw [show -z * (a - r + r - a) - w * (a - r - b) =
    w * (b - a) + w * r by ring, exp_add]
  ring

end FMSA.Paper.MixedRateTails

/-- info: 'FMSA.Paper.MixedRateTails.product_tail_indicator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateTails.product_tail_indicator

/-- info: 'FMSA.Paper.MixedRateTails.exp_pair_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateTails.exp_pair_integral

/-- info: 'FMSA.Paper.MixedRateTails.tail_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateTails.tail_overlap

/-- info: 'FMSA.Paper.MixedRateTails.tail_overlap_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateTails.tail_overlap_right

/-- info: 'FMSA.Paper.MixedRateTails.tail_overlap_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.MixedRateTails.tail_overlap_left
