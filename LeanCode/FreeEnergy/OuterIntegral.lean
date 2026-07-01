/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Task F.1 — Outer-Core Free Energy Integral (Closed Form)

**Source:** FMSA free energy calculation, Yukawa outer-core region

For the Yukawa outer-core DCF `c^(1)(r) = K · exp(-z·(r-d)) / r` for `r > d`, the
first-order energy contribution to the free energy is:

    4π ∫_d^∞ c^(1)(r) · r^2 dr
      = 4π ∫_d^∞ K · r · exp(-z·(r-d)) dr
      = 4π · K · (d/z + 1/z^2)

**Derivation:** Substitute `u = r - d`:
    ∫_0^∞ (u + d) · exp(-zu) du = ∫_0^∞ u·exp(-zu) du + d·∫_0^∞ exp(-zu) du = 1/z^2 + d/z.

**Antiderivative:** `G(r) = -exp(-z·(r-d)) · (r/z + 1/z^2)` satisfies `G'(r) = r·exp(-z·(r-d))`.
  - `G(d) = -(d/z + 1/z^2)`
  - `G(r) → 0` as `r → +∞`  (exponential decay dominates linear growth)
  - Improper FTC: `∫_d^∞ G'(r) dr = 0 - G(d) = d/z + 1/z^2`
-/

open MeasureTheory Real Set Filter intervalIntegral

namespace FMSA.FreeEnergy

/-! ### HasDerivAt lemma for the antiderivative -/

/-- `HasDerivAt` for `x ↦ exp(-z·(x - d))` via the chain rule. -/
private lemma hasDerivAt_exp_neg_mul_sub {z d r : ℝ} :
    HasDerivAt (fun x => Real.exp (-z * (x - d))) (Real.exp (-z * (r - d)) * -z) r := by
  have h : HasDerivAt (fun x => -z * (x - d)) (-z) r := by
    have h1 : HasDerivAt (fun x => x - d) 1 r := (hasDerivAt_id r).sub_const d
    have h2 := h1.const_mul (-z)
    simp only [mul_one] at h2
    exact h2
  simpa using h.exp

/-- Antiderivative of `r · exp(-z·(r-d))` is `-exp(-z·(r-d)) · (r/z + 1/z^2)`.

Proof: by product rule,
  `G'(r) = z·exp(-z(r-d))·(r/z+1/z^2) - exp(-z(r-d))·(1/z) = r·exp(-z(r-d))`. -/
private lemma outer_antideriv_hasDerivAt {z d : ℝ} (hz : z ≠ 0) (r : ℝ) :
    HasDerivAt (fun r => -Real.exp (-z * (r - d)) * (r / z + 1 / z ^ 2))
               (r * Real.exp (-z * (r - d))) r := by
  -- E(x) = -exp(-z*(x-d)), E'(r) = z*exp(-z*(r-d))
  have hE : HasDerivAt (fun x => -Real.exp (-z * (x - d))) (z * Real.exp (-z * (r - d))) r :=
    (hasDerivAt_exp_neg_mul_sub (z := z) (d := d) (r := r) |>.neg).congr_deriv (by ring)
  -- A(x) = x/z + 1/z^2, A'(r) = 1/z
  have hA : HasDerivAt (fun x => x / z + 1 / z ^ 2) (1 / z) r := by
    have h := ((hasDerivAt_id r).div_const z).add (hasDerivAt_const r (1 / z ^ 2))
    simp only [id_eq, add_zero] at h
    exact h
  -- Product rule: (E*A)'(r) = E'*A + E*A' = z*exp*(r/z+1/z^2) + (-exp)/z = r*exp
  refine (hE.mul hA).congr_deriv ?_
  field_simp [hz]
  ring

/-! ### Limit at +∞ -/

/-- The antiderivative `G(r) = -exp(-z·(r-d))·(r/z+1/z^2)` tends to 0 as `r → +∞`.

**Proof:** Factor `exp(-z*(r-d)) = exp(z*d) * exp(-z*r)`, then decompose as a sum of
two terms each tending to 0 via `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`. -/
private lemma outer_antideriv_tendsto_zero {z d : ℝ} (hz : 0 < z) :
    Tendsto (fun r => -Real.exp (-z * (r - d)) * (r / z + 1 / z ^ 2)) atTop (nhds 0) := by
  have hz' : z ≠ 0 := hz.ne'
  -- Rewrite: -exp(-z*(r-d)) * (r/z + 1/z^2) = C1 * (r * exp(-z*r)) + C2 * exp(-z*r)
  have hrw : ∀ r : ℝ, -Real.exp (-z * (r - d)) * (r / z + 1 / z ^ 2) =
      -(Real.exp (z * d) / z) * (r * Real.exp (-z * r)) +
      -(Real.exp (z * d) / z ^ 2) * Real.exp (-z * r) := by
    intro r
    rw [show -z * (r - d) = z * d + (-z) * r from by ring, Real.exp_add]
    field_simp [hz']
    ring
  simp_rw [hrw]
  rw [show (0 : ℝ) = -(Real.exp (z * d) / z) * 0 + -(Real.exp (z * d) / z ^ 2) * 0 from by ring]
  apply Tendsto.add
  · apply tendsto_const_nhds.mul
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 z hz
    simp only [Real.rpow_one] at h
    exact h
  · apply tendsto_const_nhds.mul
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 z hz
    simp only [Real.rpow_zero, one_mul] at h
    exact h

/-! ### Integrability -/

/-- The integrand `r ↦ r · exp(-z·(r-d))` is integrable on `Set.Ioi d` for `z > 0`.

**Proof:** Split at `c = max d 0 + 1` (which is > d and > 0). On the compact part `Ioc d c`,
use continuity. On `Ioi c`, use the antiderivative `G(r) = exp(-z*(r-d)) * (r/z + 1/z^2)`,
which has nonpositive derivative `-(r*exp(-z*(r-d)))` for `r > c > 0` and tends to 0. -/
lemma outer_integrable {z d : ℝ} (hz : 0 < z) :
    IntegrableOn (fun r => r * Real.exp (-z * (r - d))) (Set.Ioi d) := by
  have hz' : z ≠ 0 := hz.ne'
  have hcont : Continuous (fun r => r * Real.exp (-z * (r - d))) := by fun_prop
  -- Split at c = max d 0 + 1 (satisfies c > d and c > 0)
  let c := max d 0 + 1
  have hdc : d <= c := by linarith [le_max_left d 0]
  have hc0 : 0 < c := by linarith [le_max_right d 0]
  rw [show Set.Ioi d = Set.Ioc d c ∪ Set.Ioi c from (Ioc_union_Ioi_eq_Ioi hdc).symm]
  apply IntegrableOn.union
  · -- Compact part: continuous on Ioc d c ⊆ Icc d c
    exact hcont.integrableOn_Ioc
  · -- Infinite part: Ioi c where r > c > 0
    -- Use antiderivative g(r) = exp(-z*(r-d)) * (r/z + 1/z^2)
    -- with derivative g'(r) = -(r * exp(-z*(r-d))) ≤ 0 for r > c > 0
    have hint_neg : IntegrableOn (fun r => -(r * Real.exp (-z * (r - d)))) (Set.Ioi c) := by
      apply integrableOn_Ioi_deriv_of_nonpos'
        (g := fun r => Real.exp (-z * (r - d)) * (r / z + 1 / z ^ 2))
        (a := c) (l := 0)
      · -- HasDerivAt g (g'(x)) x for x ∈ Ici c
        intro x _
        have hE : HasDerivAt (fun r => Real.exp (-z * (r - d))) (Real.exp (-z * (x - d)) * -z) x :=
          hasDerivAt_exp_neg_mul_sub
        have hA : HasDerivAt (fun r => r / z + 1 / z ^ 2) (1 / z) x := by
          have h := ((hasDerivAt_id x).div_const z).add (hasDerivAt_const x (1 / z ^ 2))
          simp only [id_eq, add_zero] at h; exact h
        exact (hE.mul hA).congr_deriv (by field_simp [hz']; ring)
      · -- g'(r) = -(r * exp) ≤ 0 for r ∈ Ioi c (r > c > 0)
        intro x hx
        simp only [neg_nonpos]
        exact mul_nonneg (le_of_lt (lt_trans hc0 hx)) (Real.exp_nonneg _)
      · -- g(r) = exp * A → 0 as r → ∞  (note: outer_antideriv_tendsto_zero proves -exp*A → 0)
        have key : (fun r : ℝ => Real.exp (-z * (r - d)) * (r / z + 1 / z ^ 2)) =
                   (fun r => -(-Real.exp (-z * (r - d)) * (r / z + 1 / z ^ 2))) := by
          ext r; ring
        rw [key]
        have h := (outer_antideriv_tendsto_zero (d := d) hz).neg
        rwa [neg_zero] at h
    exact hint_neg.neg.congr_fun (fun r _ => neg_neg _) measurableSet_Ioi

/-! ### Main theorem -/

/-- **Task F.1 — Outer-core free energy integral:**
For `z > 0`, the Yukawa outer-core energy integral satisfies:
    `∫_d^∞ K · r · exp(-z·(r-d)) dr = K · (d/z + 1/z^2)`

**Proof strategy:** FTC for improper integrals using antiderivative
  `G(r) = -exp(-z·(r-d)) · (r/z + 1/z^2)`,
where `G(d) = -(d/z+1/z^2)` and `G(r) → 0`, so the integral equals `0 - G(d) = d/z + 1/z^2`. -/
theorem outer_core_integral {K z d : ℝ} (hz : 0 < z) :
    ∫ r in Set.Ioi d, K * (r * Real.exp (-z * (r - d))) = K * (d / z + 1 / z ^ 2) := by
  have hz' : z ≠ 0 := hz.ne'
  rw [MeasureTheory.integral_const_mul]
  congr 1
  -- Apply FTC for improper integral: ∫_d^∞ G'(r) dr = lim G - G(d)
  have hcont : ContinuousWithinAt (fun r => -Real.exp (-z * (r - d)) * (r / z + 1 / z ^ 2))
      (Set.Ici d) d :=
    (by fun_prop : Continuous (fun r =>
      -Real.exp (-z * (r - d)) * (r / z + 1 / z ^ 2))).continuousAt.continuousWithinAt
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont
      (fun x _ => outer_antideriv_hasDerivAt hz' x)
      (outer_integrable hz)
      (outer_antideriv_tendsto_zero hz)]
  -- Goal: 0 - G(d) = d/z + 1/z^2  where G(d) = -exp(-z*(d-d))*(d/z+1/z^2)
  simp only [sub_self, mul_zero, Real.exp_zero]
  ring

/-- **Corollary:** The `4π`-weighted free energy contribution from the outer core. -/
theorem outer_core_free_energy {K z d : ℝ} (hz : 0 < z) :
    4 * Real.pi * ∫ r in Set.Ioi d, K * (r * Real.exp (-z * (r - d))) =
    4 * Real.pi * K * (d / z + 1 / z ^ 2) := by
  rw [outer_core_integral hz]; ring

end FMSA.FreeEnergy
