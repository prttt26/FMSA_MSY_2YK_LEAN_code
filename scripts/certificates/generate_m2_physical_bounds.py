#!/usr/bin/env python3
"""Emit kernel proofs of exact rational Real.pi/inverse-Real.pi/exp bounds for M2.

Only rational arithmetic chooses decimal endpoints; every numerical claim is
proved by Lean from mathlib's Real.pi bounds and finite exponential-series remainder.
Prints an unguarded proof body; exact guards follow actual compiler queries.
"""
from fractions import Fraction as Q

def literal(q):
    q=Q(q)
    return f'(({q.numerator} : ℝ) / {q.denominator})'

lo=Q(548811636094026432628,10**21)
hi=Q(548811636094026432629,10**21)
print('''import MSAConvergence.BHPolynomialJacobian
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
''')
for n in [3,6,20,23,40]:
    low=Q((lo**n*10**21).__floor__(),10**21)
    high=Q((hi**n*10**21).__ceil__(),10**21)
    arg=literal(-Q(3*n,5))
    print(f'''/-- Exact 21-decimal outward enclosure of the M2 exponential with multiplier {n}. -/
theorem exp_multiple_{n} :
    {literal(low)} ≤ exp {arg} ∧ exp {arg} ≤ {literal(high)} := by
  have h := exp_seed_multiple {n}
  norm_num at h
  constructor <;> linarith [h.1,h.2]
''')
print('end FMSA.Convergence.M2PhysicalBounds')
