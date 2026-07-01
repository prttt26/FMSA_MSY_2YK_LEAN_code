/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# I1 and I2 Antiderivative Identities ([chsY] Eqs. 38–39)  (Tasks 1.1, 1.2)

**Statements:** For `z ≠ 0`:
```
I1 : ∫0^ell (alpha - v) · exp(z·v) dv
       = (alpha-ell)·exp(zell)/z + (exp(zell)-1)/z^2 - alpha/z

I2 : ∫0^ell (alpha - v)^2 · exp(z·v) dv
       = (alpha-ell)^2·exp(zell)/z + 2(alpha-ell)·exp(zell)/z^2 + 2·exp(zell)/z^3
         - alpha^2/z - 2alpha/z^2 - 2/z^3
```

**Antiderivatives (verified by differentiation):**
```
F1(v) = ((alpha-v)/z + 1/z^2) · exp(z·v)
         F1'(v) = (-1/z + (alpha-v)/z·z + 1/z^2·z)·exp(zv) = (alpha-v)·exp(zv)  ✓

F2(v) = ((alpha-v)^2/z + 2(alpha-v)/z^2 + 2/z^3) · exp(z·v)
         F2'(v) = (-2(alpha-v)/z - 2/z^2 + (alpha-v)^2 + 2(alpha-v)/z + 2/z^2)·exp(zv)
                = (alpha-v)^2·exp(zv)  ✓
```

**Proofs:** FTC via `intervalIntegral.integral_eq_sub_of_hasDerivAt`.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open MeasureTheory intervalIntegral Real

namespace FMSA.DCF

/-! ## Shared helper -/

/-- `HasDerivAt` for `v ↦ exp(z·v)`: derivative is `exp(z·v)·z`. -/
private lemma hasDerivAt_exp_mul {z r : ℝ} :
    HasDerivAt (fun v => Real.exp (z * v)) (Real.exp (z * r) * z) r := by
  have h : HasDerivAt (fun v => z * v) z r := by
    simpa using (hasDerivAt_id r).const_mul z
  exact h.exp

/-! ## Task 1.1 — I1 ([chsY] Eq. 38) -/

/-- Antiderivative of `(alpha - v) · exp(z·v)` is `((alpha-v)/z + 1/z^2) · exp(z·v)`. -/
private lemma I1_hasDerivAt {alpha z : ℝ} (hz : z ≠ 0) (v : ℝ) :
    HasDerivAt (fun v => ((alpha - v) / z + 1 / z ^ 2) * Real.exp (z * v))
               ((alpha - v) * Real.exp (z * v)) v := by
  -- A(v) = (alpha-v)/z + 1/z^2, A'(v) = -1/z.
  -- Build as -(v/z) + (alpha/z + 1/z^2) to avoid HasDerivAt.sub Pi/instance issues.
  have hA : HasDerivAt (fun v => (alpha - v) / z + 1 / z ^ 2) (-1 / z) v := by
    -- .neg.add gives Pi-form; use congr_of_eventuallyEq with explicit type to fix function,
    -- then congr_deriv to fix derivative -(1/z) → -1/z.
    have h := ((hasDerivAt_id v).div_const z).neg.add
              (hasDerivAt_const v (alpha / z + 1 / z ^ 2))
    simp only [add_zero] at h
    have h' : HasDerivAt (fun v => (alpha - v) / z + 1 / z ^ 2) (-(1 / z)) v :=
      h.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun w => by
          simp only [Pi.neg_apply, Pi.add_apply, Function.id_def]; ring)
    exact h'.congr_deriv (by ring)
  -- (A·E)' = A'·E + A·E' = (alpha-v)·exp(zv)
  exact (hA.mul hasDerivAt_exp_mul).congr_deriv (by field_simp [hz]; ring)

/-- **[chsY] Eq. 38 — Task 1.1:**
`∫0^ell (alpha - v) · exp(z·v) dv = (alpha-ell)·exp(zell)/z + (exp(zell)-1)/z^2 - alpha/z` -/
theorem I1_formula {alpha z ell : ℝ} (hz : z ≠ 0) :
    ∫ v in (0 : ℝ)..ell, (alpha - v) * Real.exp (z * v) =
    (alpha - ell) * Real.exp (z * ell) / z + (Real.exp (z * ell) - 1) / z ^ 2 - alpha / z := by
  have hint : IntervalIntegrable (fun v => (alpha - v) * Real.exp (z * v)) volume 0 ell :=
    ((continuous_const.sub continuous_id).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 ell
  rw [integral_eq_sub_of_hasDerivAt (fun v _ => I1_hasDerivAt hz v) hint]
  simp only [mul_zero, Real.exp_zero, mul_one, sub_zero]
  field_simp [hz]
  ring

/-! ## Task 1.2 — I2 ([chsY] Eq. 39) -/

/-- Antiderivative of `(alpha - v)^2 · exp(z·v)` is `((alpha-v)^2/z + 2(alpha-v)/z^2 + 2/z^3) · exp(z·v)`. -/
private lemma I2_hasDerivAt {alpha z : ℝ} (hz : z ≠ 0) (v : ℝ) :
    HasDerivAt (fun v => ((alpha - v) ^ 2 / z + 2 * (alpha - v) / z ^ 2 + 2 / z ^ 3) * Real.exp (z * v))
               ((alpha - v) ^ 2 * Real.exp (z * v)) v := by
  -- d/dv (alpha - v) = -1
  have h_sub : HasDerivAt (fun v => alpha - v) (-1 : ℝ) v := by
    have h := (hasDerivAt_id v).neg.add (hasDerivAt_const v alpha)
    simp only [add_zero] at h
    exact h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun w => by
        simp only [Pi.neg_apply, Pi.add_apply, Function.id_def]; ring)
  -- d/dv (alpha - v)^2 = -2(alpha - v), via chain rule
  have h_sq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * (alpha - v)) (alpha - v) := by
    have h := hasDerivAt_pow (𝕜 := ℝ) 2 (alpha - v)
    simpa [pow_one, Nat.cast_ofNat] using h
  have h_sq_comp : HasDerivAt (fun v => (alpha - v) ^ 2) (-2 * (alpha - v)) v :=
    (h_sq.comp v h_sub).congr_deriv (by ring)
  -- A1(v) = (alpha-v)^2/z, A1'(v) = -2(alpha-v)/z
  have hA1 : HasDerivAt (fun v => (alpha - v) ^ 2 / z) (-2 * (alpha - v) / z) v :=
    h_sq_comp.div_const z
  -- A2(v) = 2(alpha-v)/z^2, A2'(v) = -2/z^2
  have hA2 : HasDerivAt (fun v => 2 * (alpha - v) / z ^ 2) (-2 / z ^ 2) v :=
    ((h_sub.const_mul (2 : ℝ)).div_const (z ^ 2)).congr_deriv (by ring)
  -- A3(v) = 2/z^3 (constant), A3' = 0
  have hA3 : HasDerivAt (fun _ : ℝ => (2 : ℝ) / z ^ 3) 0 v := hasDerivAt_const v _
  -- A(v) = A1 + A2 + A3, A'(v) = -2(alpha-v)/z - 2/z^2
  have hA : HasDerivAt (fun v => (alpha - v) ^ 2 / z + 2 * (alpha - v) / z ^ 2 + 2 / z ^ 3)
      (-2 * (alpha - v) / z - 2 / z ^ 2) v :=
    ((hA1.add hA2).add hA3).congr_deriv (by ring)
  -- (A·E)' = A'·E + A·E' = (alpha-v)^2·exp(zv)
  exact (hA.mul hasDerivAt_exp_mul).congr_deriv (by field_simp [hz]; ring)

/-- **[chsY] Eq. 39 — Task 1.2:**
`∫0^ell (alpha - v)^2 · exp(z·v) dv`
`  = (alpha-ell)^2·exp(zell)/z + 2(alpha-ell)·exp(zell)/z^2 + 2·exp(zell)/z^3 - alpha^2/z - 2alpha/z^2 - 2/z^3` -/
theorem I2_formula {alpha z ell : ℝ} (hz : z ≠ 0) :
    ∫ v in (0 : ℝ)..ell, (alpha - v) ^ 2 * Real.exp (z * v) =
    (alpha - ell) ^ 2 * Real.exp (z * ell) / z + 2 * (alpha - ell) * Real.exp (z * ell) / z ^ 2
    + 2 * Real.exp (z * ell) / z ^ 3 - alpha ^ 2 / z - 2 * alpha / z ^ 2 - 2 / z ^ 3 := by
  have hint : IntervalIntegrable (fun v => (alpha - v) ^ 2 * Real.exp (z * v)) volume 0 ell :=
    (((continuous_const.sub continuous_id).pow 2).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 ell
  rw [integral_eq_sub_of_hasDerivAt (fun v _ => I2_hasDerivAt hz v) hint]
  simp only [mul_zero, Real.exp_zero, mul_one, sub_zero]
  field_simp [hz]
  ring

/-! ## Task 1.3 — I1 and I2 vanish at ell = 0 -/

/-- **[chsY] Task 1.3:** `I1(0, alpha, z) = 0` for all `alpha`, `z`.
The integration interval is empty, so the integral vanishes regardless of `alpha` and `z`.
This guarantees Terms II and III in [chsY] Eq. 41 contribute nothing when `r = R_aj` exactly
(the step function boundary case). -/
theorem I1_at_zero {alpha z : ℝ} :
    ∫ v in (0 : ℝ)..(0 : ℝ), (alpha - v) * Real.exp (z * v) = 0 :=
  integral_same

/-- **[chsY] Task 1.3:** `I2(0, alpha, z) = 0` for all `alpha`, `z`.
The integration interval is empty, so the integral vanishes regardless of `alpha` and `z`. -/
theorem I2_at_zero {alpha z : ℝ} :
    ∫ v in (0 : ℝ)..(0 : ℝ), (alpha - v) ^ 2 * Real.exp (z * v) = 0 :=
  integral_same

end FMSA.DCF