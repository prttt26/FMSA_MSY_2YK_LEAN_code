import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Kernel-checked real constants for the original eta49/100 M3 control.
Only static Mathlib imports; no assumed interval oracle. -/
noncomputable section
namespace FMSA.Convergence.M3PhysicalBounds
open Real
open scoped BigOperators
set_option maxRecDepth 4096

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

set_option maxHeartbeats 1000000 in
-- Exact factorial and high-power rational arithmetic needs the larger budget.
/-- Finite exponential Taylor series with rigorous remainder; all arithmetic
is checked by norm_num and linarith in the ordinary Lean kernel. -/
theorem exp_seed_interval :
    (606530659712633423603 : ℝ)/10^21 ≤ exp (-(1/2 : ℝ)) ∧
      exp (-(1/2 : ℝ)) ≤ (606530659712633423604 : ℝ)/10^21 := by
  have h := Real.exp_bound (x := -(1/2 : ℝ)) (n := 20) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  rw [abs_sub_le_iff] at h
  constructor <;> linarith [h.1,h.2]

set_option maxHeartbeats 1000000 in
-- Exact factorial and high-power rational arithmetic needs the larger budget.
/-- The same seed encloses EVERY nonnegative integral multiple, with no
interval-oracle hypothesis. -/
theorem exp_seed_multiple (n : ℕ) :
    ((606530659712633423603 : ℝ)/10^21)^n ≤ exp ((n : ℝ)*(-(1/2 : ℝ))) ∧
      exp ((n : ℝ)*(-(1/2 : ℝ))) ≤ ((606530659712633423604 : ℝ)/10^21)^n := by
  rw [Real.exp_nat_mul]
  exact ⟨pow_le_pow_left₀ (by norm_num) exp_seed_interval.1 n,
    pow_le_pow_left₀ (Real.exp_pos _).le exp_seed_interval.2 n⟩

/-- The exact physical density is positive, with no numerical premise. -/
theorem density_pos : 0 < (147 : ℝ)/(50*Real.pi) := by positivity

/-- Literal exact density bounds from the proved pi interval. -/
theorem density_interval :
    (147 : ℝ)/50*((10^20 : ℝ)/314159265358979323847) ≤ (147 : ℝ)/(50*Real.pi) ∧
      (147 : ℝ)/(50*Real.pi) ≤ (147 : ℝ)/50*((10^20 : ℝ)/314159265358979323846) := by
  have heq : (147 : ℝ)/(50*Real.pi) = (147/50 : ℝ)*Real.pi⁻¹ := by ring
  rw [heq]
  exact ⟨mul_le_mul_of_nonneg_left inverse_pi_interval.1 (by norm_num),
    mul_le_mul_of_nonneg_left inverse_pi_interval.2 (by norm_num)⟩

set_option maxHeartbeats 1000000 in
-- Exact factorial and high-power rational arithmetic needs the larger budget.
/-- Outward rational bounds for exp(-7), derived from exact rational seed powers. -/
theorem exp_multiple_14 :
    (911881965554516207 : ℝ)/10^21 ≤ exp (-(7 : ℝ)) ∧
      exp (-(7 : ℝ)) ≤ (911881965554516209 : ℝ)/10^21 := by
  have h := exp_seed_multiple 14
  norm_num at h
  constructor <;> linarith [h.1,h.2]

set_option maxHeartbeats 1000000 in
-- Exact factorial and high-power rational arithmetic needs the larger budget.
/-- Outward rational bounds for exp(-14), derived from exact rational seed powers. -/
theorem exp_multiple_28 :
    (831528719103567 : ℝ)/10^21 ≤ exp (-(14 : ℝ)) ∧
      exp (-(14 : ℝ)) ≤ (831528719103568 : ℝ)/10^21 := by
  have h := exp_seed_multiple 28
  norm_num at h
  constructor <;> linarith [h.1,h.2]

set_option maxHeartbeats 1000000 in
-- Exact factorial and high-power rational arithmetic needs the larger budget.
/-- Outward rational bounds for exp(-21), derived from exact rational seed powers. -/
theorem exp_multiple_42 :
    (758256042791 : ℝ)/10^21 ≤ exp (-(21 : ℝ)) ∧
      exp (-(21 : ℝ)) ≤ (758256042792 : ℝ)/10^21 := by
  have h := exp_seed_multiple 42
  norm_num at h
  constructor <;> linarith [h.1,h.2]

set_option maxHeartbeats 1000000 in
-- Exact factorial and high-power rational arithmetic needs the larger budget.
/-- Outward rational bounds for exp(-28), derived from exact rational seed powers. -/
theorem exp_multiple_56 :
    (691440010 : ℝ)/10^21 ≤ exp (-(28 : ℝ)) ∧
      exp (-(28 : ℝ)) ≤ (691440011 : ℝ)/10^21 := by
  have h := exp_seed_multiple 56
  norm_num at h
  constructor <;> linarith [h.1,h.2]

/-- info: 'FMSA.Convergence.M3PhysicalBounds.pi_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3PhysicalBounds.pi_interval
/-- info: 'FMSA.Convergence.M3PhysicalBounds.inverse_pi_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3PhysicalBounds.inverse_pi_interval
/-- info: 'FMSA.Convergence.M3PhysicalBounds.exp_seed_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3PhysicalBounds.exp_seed_interval
/-- info: 'FMSA.Convergence.M3PhysicalBounds.exp_seed_multiple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3PhysicalBounds.exp_seed_multiple
/-- info: 'FMSA.Convergence.M3PhysicalBounds.density_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3PhysicalBounds.density_pos
/-- info: 'FMSA.Convergence.M3PhysicalBounds.density_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3PhysicalBounds.density_interval
/-- info: 'FMSA.Convergence.M3PhysicalBounds.exp_multiple_14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3PhysicalBounds.exp_multiple_14
/-- info: 'FMSA.Convergence.M3PhysicalBounds.exp_multiple_28' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3PhysicalBounds.exp_multiple_28
/-- info: 'FMSA.Convergence.M3PhysicalBounds.exp_multiple_42' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3PhysicalBounds.exp_multiple_42
/-- info: 'FMSA.Convergence.M3PhysicalBounds.exp_multiple_56' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M3PhysicalBounds.exp_multiple_56
end FMSA.Convergence.M3PhysicalBounds
