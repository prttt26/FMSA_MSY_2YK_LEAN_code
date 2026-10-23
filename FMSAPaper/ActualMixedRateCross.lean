import FMSAPaper.MixedRateCross

/-! Actual unequal-diameter Baxter exponential cross blocks: fixed spatial
span on both positive core regions, including coincident positive rates. -/
noncomputable section
open MeasureTheory Set Real Filter

namespace FMSA.Paper.ActualMixedRateCross

open MixedRateTails MixedRatePlateau MixedRateCross
open ExactMSA.Breakpoint MSAMixture MSAMixtureCoreUneq
variable {N : ℕ}

theorem pure_factor_formula (z : ℝ) (sigma : Fin N → ℝ)
    (W C : Fin N → Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i) (i j : Fin N) (t : ℝ) :
    baxterQ z sigma 0 0 W C i j t =
      W i j * tail z (edgeLo sigma i j) t +
      C i j * plateau z (edgeLo sigma i j) (edgeHi sigma i j) t := by
  have hLH : edgeLo sigma i j <= edgeHi sigma i j := by unfold edgeLo edgeHi; linarith [hsigma i]
  rw [plateau_piecewise _ _ _ _ hLH]
  by_cases hl : t < edgeLo sigma i j
  · simp [baxterQ, tail, hl]
  · by_cases hh : t < edgeHi sigma i j
    · simp [baxterQ, tail, hl, hh, hh.le]
    · by_cases he : t = edgeHi sigma i j
      · subst t
        simp [baxterQ, tail, hl]
      · have ht : edgeHi sigma i j < t := lt_of_le_of_ne (le_of_not_gt hh) (Ne.symm he)
        simp [baxterQ, tail, hl, hh, not_le.mpr ht]

theorem pure_prime_formula (z : ℝ) (sigma : Fin N → ℝ)
    (W C : Fin N → Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i) (i j : Fin N) (t : ℝ)
    (ht : t ≠ edgeHi sigma i j) :
    baxterQ' z sigma 0 0 W C i j t =
      -z * W i j * tail z (edgeLo sigma i j) t -
      z * C i j * tail z (edgeHi sigma i j) t := by
  have hLH : edgeLo sigma i j <= edgeHi sigma i j := by unfold edgeLo edgeHi; linarith [hsigma i]
  by_cases hl : t < edgeLo sigma i j
  · simp [baxterQ', tail, hl, hl.trans_le hLH]
  · by_cases hh : t < edgeHi sigma i j
    · simp [baxterQ', tail, hl, hh, hh.le]
    · have hgt : edgeHi sigma i j < t := lt_of_le_of_ne (le_of_not_gt hh) (Ne.symm ht)
      simp [baxterQ', tail, hl, hh, not_le.mpr hgt]

theorem actual_cross_eq (z w : ℝ) (sigma : Fin N → ℝ)
    (W C V D : Fin N → Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (i j l : Fin N) (r : ℝ) :
    (∫ t : ℝ, baxterQ' z sigma 0 0 W C i l (t + r) * baxterQ w sigma 0 0 V D j l t) =
      cross z w (edgeLo sigma i l) (edgeHi sigma i l) (edgeLo sigma j l) (edgeHi sigma j l)
        (W i l) (C i l) (V j l) (D j l) r := by
  unfold cross
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (edgeHi sigma i l - r)] with t ht
  rw [pure_prime_formula z sigma W C hsigma i l (t + r) (by intro h; apply ht; linarith),
    pure_factor_formula w sigma V D hsigma j l t]

theorem actual_cross_inner_fixed_span (z w : ℝ) (hz : 0 < z) (hw : 0 < w)
    (sigma : Fin N → ℝ) (W C V D : Fin N → Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (i j l : Fin N) (horder : sigma j <= sigma i) :
    ∃ cm cp : ℝ, ∀ r ∈ Ioo (0 : ℝ) (lamA sigma i j),
      (∫ t : ℝ, baxterQ' z sigma 0 0 W C i l (t + r) * baxterQ w sigma 0 0 V D j l t) =
        cm * exp (-z * r) + cp * exp (w * r) := by
  have hLH : edgeLo sigma j l <= edgeHi sigma j l := by unfold edgeLo edgeHi; linarith [hsigma j]
  obtain ⟨cm, cp, hc⟩ := cross_inner_fixed_span z w
    (edgeLo sigma i l) (edgeHi sigma i l) (edgeLo sigma j l) (edgeHi sigma j l)
    (W i l) (C i l) (V j l) (D j l) hz hw hLH
  refine ⟨cm, cp, fun r hr => ?_⟩
  rw [actual_cross_eq z w sigma W C V D hsigma i j l r]
  apply hc
  · unfold edgeLo
    linarith [hr.1]
  · have hm := hr.2
    rw [lamA_eq_of_le sigma i j horder] at hm
    unfold edgeHi
    linarith

theorem actual_cross_outer_fixed_span (z w : ℝ) (hz : 0 < z) (hw : 0 < w)
    (sigma : Fin N → ℝ) (W C V D : Fin N → Fin N → ℝ) (hsigma : ∀ i, 0 <= sigma i)
    (i j l : Fin N) (horder : sigma j <= sigma i) :
    ∃ c0 cm cp : ℝ, ∀ r ∈ Ioo (lamA sigma i j) (edgeHi sigma i j),
      (∫ t : ℝ, baxterQ' z sigma 0 0 W C i l (t + r) * baxterQ w sigma 0 0 V D j l t) =
        c0 + cm * exp (-z * r) + cp * exp (w * r) := by
  have hLH : edgeLo sigma j l <= edgeHi sigma j l := by unfold edgeLo edgeHi; linarith [hsigma j]
  obtain ⟨c0, cm, cp, hc⟩ := cross_middle_fixed_span z w
    (edgeLo sigma i l) (edgeHi sigma i l) (edgeLo sigma j l) (edgeHi sigma j l)
    (W i l) (C i l) (V j l) (D j l) hz hw hLH
  refine ⟨c0, cm, cp, fun r hr => ?_⟩
  rw [actual_cross_eq z w sigma W C V D hsigma i j l r]
  have hm := hr.1
  rw [lamA_eq_of_le sigma i j horder] at hm
  have hR := hr.2
  unfold edgeHi at hR
  apply hc
  · unfold edgeLo
    linarith
  · unfold edgeHi
    linarith
  · unfold edgeHi edgeLo
    linarith

end FMSA.Paper.ActualMixedRateCross

/-- info: 'FMSA.Paper.ActualMixedRateCross.pure_factor_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualMixedRateCross.pure_factor_formula

/-- info: 'FMSA.Paper.ActualMixedRateCross.pure_prime_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualMixedRateCross.pure_prime_formula

/-- info: 'FMSA.Paper.ActualMixedRateCross.actual_cross_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualMixedRateCross.actual_cross_eq

/-- info: 'FMSA.Paper.ActualMixedRateCross.actual_cross_inner_fixed_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualMixedRateCross.actual_cross_inner_fixed_span

/-- info: 'FMSA.Paper.ActualMixedRateCross.actual_cross_outer_fixed_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Paper.ActualMixedRateCross.actual_cross_outer_fixed_span
