import MSAConvergence.PureFluidRFormalDispersion

set_option linter.style.header false

/-! Coefficientwise control of the explicit odd-part dispersion
series. This does not assert positivity of the r node coefficients. -/
noncomputable section
open MvPowerSeries Finsupp
namespace FMSA.Convergence.PureFluidROddCoeffSign
open FMSA.Convergence.PureFluidRFormalDispersion
variable {T : Type*} [Fintype T] [DecidableEq T]

def linearTheta (c : T → ℝ) : MvPowerSeries T ℝ :=
  ∑ t, C (c t) * X t

def geometricTheta (c : T → ℝ) : MvPowerSeries T ℝ :=
  (1 - linearTheta c)⁻¹

omit [DecidableEq T] in
theorem linearTheta_constantCoeff_zero (c : T → ℝ) :
    MvPowerSeries.constantCoeff (linearTheta c) = 0 := by
  classical
  simp [linearTheta, MvPowerSeries.constantCoeff_X]

omit [DecidableEq T] in
theorem geometricTheta_fixed_point (c : T → ℝ) :
    geometricTheta c = 1 + linearTheta c * geometricTheta c := by
  have hconst : MvPowerSeries.constantCoeff (1 - linearTheta c) = 1 := by
    rw [map_sub, map_one, linearTheta_constantCoeff_zero]
    ring
  have hmul : (1 - linearTheta c) * geometricTheta c = 1 := by
    unfold geometricTheta
    apply MvPowerSeries.mul_inv_cancel
    rw [hconst]
    exact one_ne_zero
  linear_combination hmul

omit [DecidableEq T] in
theorem coeff_X_mul_geometric_nonneg_of_lower_degree
    (c : T → ℝ) (t : T) (m : T →₀ ℕ)
    (hprev : ∀ d, d.degree < m.degree →
      0 ≤ MvPowerSeries.coeff d (geometricTheta c)) :
    0 ≤ MvPowerSeries.coeff m (X t * geometricTheta c) := by
  classical
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  split_ifs with hle
  · let e : T →₀ ℕ := Finsupp.single t 1
    have hdecomp : e + (m-e) = m := add_tsub_cancel_of_le hle
    have hdeg : (m-e).degree < m.degree := by
      have heq : m.degree = 1 + (m-e).degree := by
        calc
          m.degree = (e+(m-e)).degree := by rw [hdecomp]
          _ = 1+(m-e).degree := by simp [e]
      omega
    simpa only [one_mul] using hprev (m-e) hdeg
  · exact le_refl 0

/-- Every coefficient of the inverse of one minus a nonnegative linear
multivariate theta series is nonnegative. -/
theorem geometricTheta_coeff_nonneg
    (c : T → ℝ) (hc : ∀ t, 0 ≤ c t) :
    ∀ m : T →₀ ℕ, 0 ≤ MvPowerSeries.coeff m (geometricTheta c) := by
  classical
  have hmain : ∀ n : ℕ, ∀ m : T →₀ ℕ, m.degree = n →
      0 ≤ MvPowerSeries.coeff m (geometricTheta c) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro m hm
      have hprev : ∀ d, d.degree < m.degree →
          0 ≤ MvPowerSeries.coeff d (geometricTheta c) := by
        intro d hd
        exact ih d.degree (by omega) d rfl
      rw [geometricTheta_fixed_point]
      simp only [map_add, linearTheta, Finset.sum_mul, map_sum]
      apply add_nonneg
      · rw [MvPowerSeries.coeff_one]
        split_ifs <;> norm_num
      · apply Finset.sum_nonneg
        intro t _
        rw [mul_assoc, MvPowerSeries.coeff_C_mul]
        exact mul_nonneg (hc t)
          (coeff_X_mul_geometric_nonneg_of_lower_degree c t m hprev)
  intro m
  exact hmain m.degree m rfl

theorem physical_dispersion_inverse_coeff_nonneg
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (x : ℝ) (hx : 0 ≤ x) (hsmall : ∀ t, x < z t) :
    ∀ m : T →₀ ℕ,
      0 ≤ MvPowerSeries.coeff m
        ((1 - ∑ t, C (2 * z t / ((z t)^2 - x^2)) * X t)⁻¹) := by
  have hc (t : T) : 0 ≤ 2 * z t / ((z t)^2 - x^2) := by
    have hleft : 0 < z t - x := sub_pos.mpr (hsmall t)
    have hright : 0 < z t + x := add_pos_of_pos_of_nonneg (hz t) hx
    have hden : 0 < (z t)^2 - x^2 := by
      nlinarith [mul_pos hleft hright]
    exact div_nonneg (mul_nonneg (by norm_num) (hz t).le) hden.le
  simpa only [geometricTheta, linearTheta] using
    geometricTheta_coeff_nonneg
      (fun t => 2 * z t / ((z t)^2 - x^2)) hc

/-- At a positive frequency below every positive rate, every
nonconstant theta coefficient of the formal r odd part is nonpositive.
This is not a sign claim for the individual r node series. -/
theorem physical_formal_R_odd_coeff_nonpos
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (x : ℝ) (hx : 0 ≤ x) (hsmall : ∀ t, x < z t)
    (m : T →₀ ℕ) (hm : m ≠ 0) :
    MvPowerSeries.coeff m
      (physicalFormalR z x - physicalFormalR z (-x)) ≤ 0 := by
  have hplus : ∀ t, x + z t ≠ 0 := by
    intro t
    exact (add_pos_of_nonneg_of_pos hx (hz t)).ne'
  have hminus : ∀ t, z t - x ≠ 0 := by
    intro t
    exact (sub_pos.mpr (hsmall t)).ne'
  rw [physical_formal_R_odd_dispersion z hz x hplus hminus]
  rw [MvPowerSeries.coeff_C_mul]
  simp only [map_sub, MvPowerSeries.coeff_one, if_neg hm, zero_sub]
  exact mul_nonpos_of_nonneg_of_nonpos hx
    (neg_nonpos.mpr (physical_dispersion_inverse_coeff_nonneg
      z hz x hx hsmall m))

end FMSA.Convergence.PureFluidROddCoeffSign

/-- info: 'FMSA.Convergence.PureFluidROddCoeffSign.linearTheta_constantCoeff_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidROddCoeffSign.linearTheta_constantCoeff_zero
/-- info: 'FMSA.Convergence.PureFluidROddCoeffSign.geometricTheta_fixed_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidROddCoeffSign.geometricTheta_fixed_point
/-- info: 'FMSA.Convergence.PureFluidROddCoeffSign.coeff_X_mul_geometric_nonneg_of_lower_degree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidROddCoeffSign.coeff_X_mul_geometric_nonneg_of_lower_degree
/-- info: 'FMSA.Convergence.PureFluidROddCoeffSign.geometricTheta_coeff_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidROddCoeffSign.geometricTheta_coeff_nonneg
/-- info: 'FMSA.Convergence.PureFluidROddCoeffSign.physical_dispersion_inverse_coeff_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidROddCoeffSign.physical_dispersion_inverse_coeff_nonneg
/-- info: 'FMSA.Convergence.PureFluidROddCoeffSign.physical_formal_R_odd_coeff_nonpos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidROddCoeffSign.physical_formal_R_odd_coeff_nonpos
