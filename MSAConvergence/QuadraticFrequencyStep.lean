import MSAConvergence.ScalarFourierTail

/-! A sharp quadratic remainder and whole-interval nonvanishing from
actual first/second derivatives. The factor1/2 is proved by a quadratic
barrier comparison; no integral remainder identity is assumed. -/
noncomputable section
open Set Real
namespace FMSA.Convergence.QuadraticFrequencyStep
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem quadratic_remainder (f D DD : ℝ → E) (a b L : ℝ)
    (hF : ∀ t ∈ Icc a b, HasDerivAt f (D t) t)
    (hD : ∀ t ∈ Icc a b, HasDerivAt D (DD t) t)
    (hL : ∀ t ∈ Icc a b, ‖DD t‖ ≤ L) :
    ∀ t ∈ Icc a b, ‖f t-f a-(t-a) • D a‖ ≤ L*(t-a)^2/2 := by
  have hDbound : ∀ t ∈ Icc a b, ‖D t-D a‖ ≤ L*(t-a) :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t ht => (hD t ht).hasDerivWithinAt)
      (fun t ht => hL t (Ico_subset_Icc_self ht))
  let err : ℝ → E := fun t => f t-f a-(t-a) • D a
  let barrier : ℝ → ℝ := fun t => L*(t-a)^2/2
  have herr (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt err (D t-D a) t := by
    have hlinear := ((hasDerivAt_id t).sub_const a).smul_const (D a)
    simpa only [err,one_smul,Pi.sub_apply,id_eq] using ((hF t ht).sub_const (f a)).fun_sub hlinear
  have hbarrier (t : ℝ) : HasDerivAt barrier (L*(t-a)) t := by
    have h := (((hasDerivAt_id t).sub_const a).pow 2).const_mul L |>.div_const 2
    exact h.congr_deriv (by dsimp; ring)
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun t ht => (herr t ht).continuousAt.continuousWithinAt)
    (fun t ht => (herr t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (show ‖err a‖ ≤ barrier a by simp [err,barrier]) hbarrier
    (fun t ht => hDbound t (Ico_subset_Icc_self ht))
  intro t ht
  exact h ht

theorem interval_nonzero (f D DD : ℝ → E) (a h L m d : ℝ)
    (hh : 0 ≤ h)
    (hF : ∀ t ∈ Icc a (a+h), HasDerivAt f (D t) t)
    (hD : ∀ t ∈ Icc a (a+h), HasDerivAt D (DD t) t)
    (hL : ∀ t ∈ Icc a (a+h), ‖DD t‖ ≤ L)
    (hm : m ≤ ‖f a‖) (hd : ‖D a‖ ≤ d)
    (hbudget : 0 < m-d*h-L*h^2/2) : ∀ t ∈ Icc a (a+h), f t ≠ 0 := by
  intro t ht hzero
  have hL0 : 0 ≤ L := (norm_nonneg (DD a)).trans (hL a ⟨le_rfl,by linarith⟩)
  have hu0 : 0 ≤ t-a := sub_nonneg.mpr ht.1
  have huh : t-a ≤ h := by linarith [ht.2]
  have hquad := quadratic_remainder f D DD a (a+h) L hF hD hL t ht
  have hpert : ‖f t-f a‖ ≤ (t-a)*‖D a‖+L*(t-a)^2/2 := by
    have he : f t-f a = (t-a) • D a+(f t-f a-(t-a) • D a) := by abel
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hu0]
    exact add_le_add le_rfl hquad
  have hbound : (t-a)*‖D a‖+L*(t-a)^2/2 ≤ h*d+L*h^2/2 := by
    gcongr
  have hnorm : ‖f a‖ ≤ h*d+L*h^2/2 := by
    simpa only [hzero,zero_sub,norm_neg] using hpert.trans hbound
  nlinarith

/-- info: 'FMSA.Convergence.QuadraticFrequencyStep.quadratic_remainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.QuadraticFrequencyStep.quadratic_remainder
/-- info: 'FMSA.Convergence.QuadraticFrequencyStep.interval_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.QuadraticFrequencyStep.interval_nonzero
end FMSA.Convergence.QuadraticFrequencyStep
