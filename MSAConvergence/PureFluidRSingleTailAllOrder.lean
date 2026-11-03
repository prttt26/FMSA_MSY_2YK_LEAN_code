import MSAConvergence.PureFluidRSquarefreePoleSpan
import MSAConvergence.PureFluidHFormalSolution

set_option linter.style.header false

/-! All-order repeated-index positivity for a single Yukawa tail. -/
noncomputable section
open MvPowerSeries
namespace FMSA.Convergence.PureFluidRSingleTailAllOrder
open FMSA.Convergence.PureFluidRFormalSolution
open FMSA.Convergence.PureFluidHFormalSolution
open FMSA.Convergence.PureFluidRFormalDispersion
variable {T : Type*} [Unique T] [Fintype T] [DecidableEq T]

/-- In the one-tail formal system, the H and r node equations imply
the exact cancellation H(z-R)=z at every formal order. -/
theorem single_tail_H_mul_z_sub_R
    (z : T → ℝ) (t : T) :
    physicalH z t * (C (z t) - RSeries z t) = C (z t) := by
  have hH := HSeries_system (fun s u : T => (z s + z u)⁻¹) t
  have hR := RSeries_system z t
  change physicalH z t = 1 + ∑ u,
    C ((z t + z u)⁻¹) *
      (X u * (physicalH z t * physicalH z u)) at hH
  change RSeries z t = ∑ u,
    C ((z t + z u)⁻¹) *
      (X u * ((physicalH z t * physicalH z u) *
        (C (z u) - RSeries z u))) at hR
  simp only [Finset.univ_unique, Finset.sum_singleton] at hH hR
  have htd : t = default := Unique.eq_default t
  subst t
  let A : MvPowerSeries T ℝ :=
    C ((z default + z default)⁻¹) *
      (X default * (physicalH z default * physicalH z default))
  have hHa : physicalH z default = 1 + A := hH
  have hRa : RSeries z default = A *
      (C (z default) - RSeries z default) := by
    dsimp [A]
    calc
      _ = C ((z default + z default)⁻¹) *
        (X default * ((physicalH z default * physicalH z default) *
          (C (z default) - RSeries z default))) := hR
      _ = _ := by ring
  linear_combination (C (z default) - RSeries z default) * hHa - hRa

/-- The single-tail off-node r series has a positive-coefficient
resolvent recurrence after the H/r node cancellation. -/
theorem single_tail_physicalFormalR_fixed_point
    (z : T → ℝ) (x : ℝ) (t : T) :
    physicalFormalR z x = C ((x + z t)⁻¹) *
      (X t * (C (z t) + physicalH z t * physicalFormalR z x)) := by
  have ht : t = default := Unique.eq_default t
  subst t
  have h := physicalFormalR_series_recursion z x
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  calc
    physicalFormalR z x = C ((x + z default)⁻¹) *
      (X default * physicalH z default *
        (C (z default) - RSeries z default + physicalFormalR z x)) := h
    _ = C ((x + z default)⁻¹) *
      (X default *
        (physicalH z default * (C (z default) - RSeries z default) +
          physicalH z default * physicalFormalR z x)) := by ring
    _ = _ := by rw [single_tail_H_mul_z_sub_R]

/-- With one positive-rate Yukawa tail, every repeated-index
coefficient of the off-node formal r coordinate is nonnegative at
every nonnegative real frequency. -/
theorem single_tail_physicalFormalR_coeff_nonneg
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (x : ℝ) (hx : 0 ≤ x) :
    ∀ m : T →₀ ℕ,
      0 ≤ MvPowerSeries.coeff m (physicalFormalR z x) := by
  classical
  have hH (d : T →₀ ℕ) :
      0 ≤ MvPowerSeries.coeff d (physicalH z default) := by
    simpa only [physicalH, one_div] using
      physical_HSeries_coeff_nonneg z hz default d
  have hmain : ∀ n : ℕ, ∀ m : T →₀ ℕ, m.degree = n →
      0 ≤ MvPowerSeries.coeff m (physicalFormalR z x) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro m hm
      rw [single_tail_physicalFormalR_fixed_point z x default]
      rw [MvPowerSeries.coeff_C_mul]
      apply mul_nonneg
      · exact inv_nonneg.mpr (add_pos_of_nonneg_of_pos hx (hz default)).le
      · rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
        split_ifs with hle
        · rw [one_mul, map_add]
          apply add_nonneg
          · rw [MvPowerSeries.coeff_C]
            split_ifs
            · exact (hz default).le
            · exact le_refl 0
          · rw [MvPowerSeries.coeff_mul]
            apply Finset.sum_nonneg
            intro p hp
            have hd :=
              (antidiagonal_degree_lt_of_single_le m default hle p hp).2
            exact mul_nonneg (hH p.1)
              (ih p.2.degree (by omega) p.2 rfl)
        · exact le_refl 0
  intro m
  exact hmain m.degree m rfl

/-- The independently recursive one-tail r-node series has
nonnegative coefficients at every multivariate monomial, including
all repeated powers of its sole tail variable. -/
theorem single_tail_RSeries_coeff_nonneg
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (t : T) (m : T →₀ ℕ) :
    0 ≤ MvPowerSeries.coeff m (RSeries z t) := by
  rw [← physicalFormalR_at_node z t]
  exact single_tail_physicalFormalR_coeff_nonneg z hz (z t) (hz t).le m

end FMSA.Convergence.PureFluidRSingleTailAllOrder
/-- info: 'FMSA.Convergence.PureFluidRSingleTailAllOrder.single_tail_H_mul_z_sub_R' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSingleTailAllOrder.single_tail_H_mul_z_sub_R
/-- info: 'FMSA.Convergence.PureFluidRSingleTailAllOrder.single_tail_physicalFormalR_fixed_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSingleTailAllOrder.single_tail_physicalFormalR_fixed_point
/-- info: 'FMSA.Convergence.PureFluidRSingleTailAllOrder.single_tail_physicalFormalR_coeff_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSingleTailAllOrder.single_tail_physicalFormalR_coeff_nonneg
/-- info: 'FMSA.Convergence.PureFluidRSingleTailAllOrder.single_tail_RSeries_coeff_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRSingleTailAllOrder.single_tail_RSeries_coeff_nonneg
