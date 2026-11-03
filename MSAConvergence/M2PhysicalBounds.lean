import MSAConvergence.BHPolynomialJacobian
import Mathlib.Analysis.Real.Pi.Bounds

/-! Kernel-checked numerical constants for the ACTUAL M2 physical data.
Pi and exponentials retain their exact real meanings. Rational candidate
endpoints are verified by ordinary kernel proofs, with ordinary kernel arithmetic. -/
noncomputable section
namespace FMSA.Convergence.M2PhysicalBounds
open Real
open scoped BigOperators
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Existing rigorous twenty-decimal Real.pi bounds, weakened to closed intervals. -/
theorem pi_interval :
    (314159265358979323846 : ℝ)/10^20 ≤ Real.pi ∧ Real.pi ≤ (314159265358979323847 : ℝ)/10^20 := by
  constructor <;> linarith [Real.pi_gt_d20,Real.pi_lt_d20]

/-- Exact reciprocal bounds, with Real.pi positivity proved rather than assumed. -/
theorem inverse_pi_interval :
    (10^20 : ℝ)/314159265358979323847 ≤ Real.pi⁻¹ ∧
      Real.pi⁻¹ ≤ (10^20 : ℝ)/314159265358979323846 := by
  have h1 := one_div_le_one_div_of_le Real.pi_pos pi_interval.2
  have h2 := one_div_le_one_div_of_le
    (by norm_num : (0 : ℝ) < 314159265358979323846/10^20) pi_interval.1
  constructor
  · simpa only [one_div,inv_div] using h1
  · simpa only [one_div,inv_div] using h2

/-- Finite exponential Taylor series with rigorous remainder; all arithmetic
is checked by norm_num and linarith in the ordinary Lean kernel. -/
theorem exp_seed_interval :
    (548811636094026432628 : ℝ)/10^21 ≤ exp (-(3/5 : ℝ)) ∧
      exp (-(3/5 : ℝ)) ≤ (548811636094026432629 : ℝ)/10^21 := by
  have h := Real.exp_bound (x := -(3/5 : ℝ)) (n := 20) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rw [abs_sub_le_iff] at h
  constructor <;> linarith [h.1,h.2]

/-- The same seed encloses EVERY nonnegative integral multiple, with no
interval-oracle hypothesis. -/
theorem exp_seed_multiple (n : ℕ) :
    ((548811636094026432628 : ℝ)/10^21)^n ≤ exp ((n : ℝ)*(-(3/5 : ℝ))) ∧
      exp ((n : ℝ)*(-(3/5 : ℝ))) ≤ ((548811636094026432629 : ℝ)/10^21)^n := by
  rw [Real.exp_nat_mul]
  exact ⟨pow_le_pow_left₀ (by norm_num) exp_seed_interval.1 n,
    pow_le_pow_left₀ (Real.exp_pos _).le exp_seed_interval.2 n⟩

/-- Exact 21-decimal outward enclosure of the M2 exponential with multiplier 3. -/
theorem exp_multiple_3 :
    ((20662361027698317287 : ℝ) / 125000000000000000000) ≤ exp ((-9 : ℝ) / 5) ∧ exp ((-9 : ℝ) / 5) ≤ ((82649444110793269149 : ℝ) / 500000000000000000000) := by
  have h := exp_seed_multiple 3
  norm_num at h
  constructor <;> linarith [h.1,h.2]

/-- Exact 21-decimal outward enclosure of the M2 exponential with multiplier 6. -/
theorem exp_multiple_6 :
    ((27323722447292560801 : ℝ) / 1000000000000000000000) ≤ exp ((-18 : ℝ) / 5) ∧ exp ((-18 : ℝ) / 5) ≤ ((13661861223646280401 : ℝ) / 500000000000000000000) := by
  have h := exp_seed_multiple 6
  norm_num at h
  constructor <;> linarith [h.1,h.2]

/-- Exact 21-decimal outward enclosure of the M2 exponential with multiplier 20. -/
theorem exp_multiple_20 :
    ((6144212353328209 : ℝ) / 1000000000000000000000) ≤ exp ((-12 : ℝ) / 1) ∧ exp ((-12 : ℝ) / 1) ≤ ((614421235332821 : ℝ) / 100000000000000000000) := by
  have h := exp_seed_multiple 20
  norm_num at h
  constructor <;> linarith [h.1,h.2]

/-- Exact 21-decimal outward enclosure of the M2 exponential with multiplier 23. -/
theorem exp_multiple_23 :
    ((101563147100249 : ℝ) / 100000000000000000000) ≤ exp ((-69 : ℝ) / 5) ∧ exp ((-69 : ℝ) / 5) ≤ ((1015631471002491 : ℝ) / 1000000000000000000000) := by
  have h := exp_seed_multiple 23
  norm_num at h
  constructor <;> linarith [h.1,h.2]

/-- Exact 21-decimal outward enclosure of the M2 exponential with multiplier 40. -/
theorem exp_multiple_40 :
    ((18875672721 : ℝ) / 500000000000000000000) ≤ exp ((-24 : ℝ) / 1) ∧ exp ((-24 : ℝ) / 1) ≤ ((37751345443 : ℝ) / 1000000000000000000000) := by
  have h := exp_seed_multiple 40
  norm_num at h
  constructor <;> linarith [h.1,h.2]

end FMSA.Convergence.M2PhysicalBounds

/-- info: 'FMSA.Convergence.M2PhysicalBounds.pi_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2PhysicalBounds.pi_interval

/-- info: 'FMSA.Convergence.M2PhysicalBounds.inverse_pi_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2PhysicalBounds.inverse_pi_interval

/-- info: 'FMSA.Convergence.M2PhysicalBounds.exp_seed_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2PhysicalBounds.exp_seed_interval

/-- info: 'FMSA.Convergence.M2PhysicalBounds.exp_seed_multiple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2PhysicalBounds.exp_seed_multiple

/-- info: 'FMSA.Convergence.M2PhysicalBounds.exp_multiple_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2PhysicalBounds.exp_multiple_3

/-- info: 'FMSA.Convergence.M2PhysicalBounds.exp_multiple_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2PhysicalBounds.exp_multiple_6

/-- info: 'FMSA.Convergence.M2PhysicalBounds.exp_multiple_20' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2PhysicalBounds.exp_multiple_20

/-- info: 'FMSA.Convergence.M2PhysicalBounds.exp_multiple_23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2PhysicalBounds.exp_multiple_23

/-- info: 'FMSA.Convergence.M2PhysicalBounds.exp_multiple_40' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2PhysicalBounds.exp_multiple_40
