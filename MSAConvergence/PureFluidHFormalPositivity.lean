import MSAConvergence.PureFluidHDispersion
import Mathlib.RingTheory.MvPowerSeries.Basic

set_option linter.style.header false

/-! Coefficientwise positivity for any formal solution of the finite
Chandrasekhar H node system with nonnegative kernel. -/
noncomputable section
open MvPowerSeries Finsupp
namespace FMSA.Convergence.PureFluidHFormalPositivity
variable {T : Type*} [Fintype T]

/-- The denominator-free form of the finite H node equation. -/
def HNodeSystem (c : T → T → ℝ) (H : T → MvPowerSeries T ℝ) : Prop :=
  ∀ s, H s = 1 + ∑ t, MvPowerSeries.C (c s t) *
    (MvPowerSeries.X t * (H s * H t))

omit [Fintype T] in
/-- Multiplication by one formal variable makes the coefficient at a
monomial depend only on coefficients of strictly lower total degree. -/
theorem coeff_X_mul_two_nonneg_of_lower_degree
    (H : T → MvPowerSeries T ℝ) (s t : T) (m : T →₀ ℕ)
    (hprev : ∀ u d, d.degree < m.degree →
      0 ≤ MvPowerSeries.coeff d (H u)) :
    0 ≤ MvPowerSeries.coeff m
      (MvPowerSeries.X t * (H s * H t)) := by
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
    rw [one_mul, MvPowerSeries.coeff_mul]
    apply Finset.sum_nonneg
    intro p hp
    have hpadd : p.1 + p.2 = m-e := by
      simpa only [Finset.mem_antidiagonal] using hp
    have hdeg_left : p.1.degree ≤ (m-e).degree := by
      rw [← hpadd, map_add]
      exact Nat.le_add_right _ _
    have hdeg_right : p.2.degree ≤ (m-e).degree := by
      rw [← hpadd, map_add]
      exact Nat.le_add_left _ _
    exact mul_nonneg
      (hprev s p.1 (lt_of_le_of_lt hdeg_left hdeg))
      (hprev t p.2 (lt_of_le_of_lt hdeg_right hdeg))
  · exact le_refl 0

/-- Every formal solution of the finite H equation has nonnegative
multivariate coefficients when each node kernel coefficient is nonnegative.
Existence and identification with the actual analytic MSA germ are separate. -/
theorem h_node_system_coeff_nonneg
    (c : T → T → ℝ) (H : T → MvPowerSeries T ℝ)
    (hc : ∀ s t, 0 ≤ c s t) (hsys : HNodeSystem c H) :
    ∀ s m, 0 ≤ MvPowerSeries.coeff m (H s) := by
  classical
  have hmain : ∀ n : ℕ, ∀ m : T →₀ ℕ, m.degree = n →
      ∀ s, 0 ≤ MvPowerSeries.coeff m (H s) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro m hm s
      have hprev : ∀ u d, d.degree < m.degree →
          0 ≤ MvPowerSeries.coeff d (H u) := by
        intro u d hd
        exact ih d.degree (by omega) d rfl u
      rw [hsys s]
      simp only [map_add, map_sum]
      apply add_nonneg
      · rw [MvPowerSeries.coeff_one]
        split_ifs <;> norm_num
      · apply Finset.sum_nonneg
        intro t _
        rw [MvPowerSeries.coeff_C_mul]
        exact mul_nonneg (hc s t)
          (coeff_X_mul_two_nonneg_of_lower_degree H s t m hprev)
  intro s m
  exact hmain m.degree m rfl s

/-- The actual positive-rate node kernel is nonnegative, so any formal
solution of its finite H system has nonnegative mixed coefficients. -/
theorem physical_h_node_coeff_nonneg
    (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (H : T → MvPowerSeries T ℝ)
    (hsys : HNodeSystem (fun s t => 1/(z s+z t)) H) :
    ∀ s m, 0 ≤ MvPowerSeries.coeff m (H s) := by
  apply h_node_system_coeff_nonneg
    (fun s t => 1/(z s+z t)) H ?_ hsys
  intro s t
  exact div_nonneg (by norm_num) (add_pos (hz s) (hz t)).le

end FMSA.Convergence.PureFluidHFormalPositivity
/-- info: 'FMSA.Convergence.PureFluidHFormalPositivity.coeff_X_mul_two_nonneg_of_lower_degree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHFormalPositivity.coeff_X_mul_two_nonneg_of_lower_degree
/-- info: 'FMSA.Convergence.PureFluidHFormalPositivity.h_node_system_coeff_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHFormalPositivity.h_node_system_coeff_nonneg
/-- info: 'FMSA.Convergence.PureFluidHFormalPositivity.physical_h_node_coeff_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHFormalPositivity.physical_h_node_coeff_nonneg
