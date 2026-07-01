/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Task 4.3 — Does `(1 + A(z))^2 = 1 - g(z)^2`?  (Root cause of the HSY origin spike)

## Background

In FMSA_chsY, the r → 0 contribution from each Yukawa tail t is
```
r·c1_chsY(r → 0) = K_t · (1 + A_t(z_t))^2 · exp(+z_t · sigma)
```
In FMSA_pure, the same limit gives
```
r·c1_pure(r → 0) = K_t · (1 - g_t^2) · exp(+z_t · sigma) - K_t · a_t^2 · exp(-z_t · sigma) + …
```
where:
  `A(z) = 1/Q̂(z) - 1`          (propagator, Baxter Q-function inverse)
  `g(z) = S(z) / ((1-eta)^2 z^3 Q̂(z))`   ([chsY] Eq. 52)

and the single-component Baxter Q-function (PY hard spheres) is
  `Q̂(z) = (S(z) + 12eta · L(z) · exp(-z·sigma)) / ((1-eta)^2 z^3)`

with polynomial pieces (diameter sigma, packing fraction eta = πrhosigma^3/6):
  `S(z) = (1-eta)^2z^3 + 6eta(1-eta)z^2 + 18eta^2z - 12eta(1+2eta)`
  `L(z) = (1+eta/2)z + (1+2eta)`

The two r → 0 formulas agree **only if** `(1 + A(z))^2 = 1 - g(z)^2`.

## Algebraic reduction

Let `D := (1-eta)^2z^3 Q̂(z) = S(z) + 12eta L(z) exp(-z·sigma)`. Then:
  `(1+A)^2  = (1-eta)^4z^6 / D^2`
  `1 - g^2  = (D^2 - S^2) / D^2 = 12eta L exp(-zsigma) · (2S + 12eta L exp(-zsigma)) / D^2`

Clearing D^2 ≠ 0, the identity `(1+A)^2 = 1-g^2` is equivalent to:
```
  (1-eta)^4 z^6  =  12eta · L(z) · exp(-z·sigma) · (2·S(z) + 12eta · L(z) · exp(-z·sigma))    (*)
```

## Main result

**(*) is FALSE.**  Explicit counterexample: eta = 3/4, z = 1, sigma = 1.

Left side of (*):  `(1 - 3/4)^4 · 1^6 = 1/256 > 0`.

Right side of (*) sign analysis (let `e := exp(-1)`):
  - `L(1) = 31/8 > 0`, so `A := (279/8)·e > 0`
  - `S(1) = -179/16`, so `2·S(1) = -179/8`
  - `exp(1) ≥ 1+1 = 2` (standard bound) ⟹ `e = exp(-1) ≤ 1/2`
  - `B := 2·S(1) + (279/8)·e ≤ -179/8 + 279/16 = -79/16 < 0`
  - Right side = A · B = (positive) · (negative) < 0

Therefore  `1/256 = LHS > 0 > RHS`, and (*) fails.

**Physical consequence:** FMSA_chsY replaces `1 - g^2` by `(1+A)^2` in the r → 0 limit.
Since `(1+A)^2 > 0` always while `1-g^2` can be negative, FMSA_chsY overestimates
c1(r → 0), creating the observed large positive spike as r → 0.
-/

set_option linter.unusedSimpArgs false
set_option linter.style.whitespace false

namespace FMSA.OriginCheck

open Real

/-! ### Auxiliary: exp(-1) ≤ 1/2 from the standard bound exp(x) ≥ 1+x -/

/-- From `exp 1 ≥ 1 + 1 = 2` (which is `add_one_le_exp` at x = 1)
    and `exp(-1) · exp(1) = 1`, we get `exp(-1) ≤ 1/2`. -/
private lemma exp_neg_one_le_half : Real.exp (-1) <= 1 / 2 := by
  have h2 : (2 : ℝ) <= Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpos : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  have hmul : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith

/-! ### Main falsification theorem -/

/-- **Task 4.3 (falsified):** The identity `(1 + A(z))^2 = 1 - g(z)^2`, which is
required for FMSA_chsY to agree with FMSA_pure at r → 0, is **false**.

The algebraically equivalent condition — after clearing denominators — is
```
  (1-eta)^4z^6 = 12eta·L(z)·exp(-z·sigma)·(2·S(z) + 12eta·L(z)·exp(-z·sigma))
```
The counterexample eta = 3/4, z = 1, sigma = 1 gives LHS = 1/256 > 0 while RHS < 0. -/
theorem identity_one_plus_A_sq_ne_one_minus_g_sq :
    ∃ (eta sigma z : ℝ), eta ∈ Set.Ioo 0 1 ∧ 0 < sigma ∧ 0 < z ∧
    let S := (1-eta)^2*z^3 + 6*eta*(1-eta)*z^2 + 18*eta^2*z - 12*eta*(1+2*eta)
    let L := (1+eta/2)*z + (1+2*eta)
    (1-eta)^4 * z^6 ≠
      12*eta*L * Real.exp (-z*sigma) * (2*S + 12*eta*L * Real.exp (-z*sigma)) := by
  -- Provide the counterexample (eta, sigma, z) = (3/4, 1, 1)
  refine ⟨3/4, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  -- β-reduce the let bindings with the concrete values
  simp only []
  -- Abbreviate exp(-1·1) = exp(-1) as e for readability
  set e := Real.exp (-(1 : ℝ) * 1) with he_def
  -- exp bound: e ≤ 1/2
  have he_pos : (0 : ℝ) < e := Real.exp_pos _
  have he_le : e <= 1 / 2 := by
    have : e = Real.exp (-1) := by rw [he_def]; norm_num
    rw [this]; exact exp_neg_one_le_half
  -- Rational evaluations of S, L, LHS, and coefficient at (3/4, 1, 1)
  have hS : (1 - (3/4 : ℝ))^2 * 1^3 + 6*(3/4)*(1-3/4)*1^2 + 18*(3/4)^2*1
            - 12*(3/4)*(1+2*(3/4)) = -179/16 := by norm_num
  have hL : (1 + (3/4 : ℝ)/2)*1 + (1 + 2*(3/4)) = 31/8 := by norm_num
  have hLHS : (1 - (3/4 : ℝ))^4 * 1^6 = 1/256 := by norm_num
  have hcoeff : (12 : ℝ) * (3/4) * (31/8) = 279/8 := by norm_num
  -- Assume the identity holds; we derive a contradiction
  intro h
  -- Rewrite the rational S and L in h, then the LHS and coefficient
  rw [hS, hL] at h
  rw [hLHS, hcoeff] at h
  -- After rewrites, h states:  1/256 = (279/8)·e · (2·(-179/16) + (279/8)·e)
  -- Sign analysis of the right side:
  --   A := (279/8)·e > 0   (both factors positive)
  have hA : (0 : ℝ) < (279/8) * e := by positivity
  --   B := 2·(-179/16) + (279/8)·e ≤ -79/16 < 0
  --     because (279/8)·e ≤ (279/8)·(1/2) = 279/16,
  --     and 2·(-179/16) + 279/16 = -358/16 + 279/16 = -79/16
  have hB : 2 * (-179/16 : ℝ) + (279/8) * e <= -79/16 := by nlinarith
  have hB_neg : 2 * (-179/16 : ℝ) + (279/8) * e < 0 := by linarith
  -- Therefore RHS = A · B < 0
  have hrhs_neg : (279/8 : ℝ) * e * (2 * (-179/16) + (279/8) * e) < 0 :=
    mul_neg_of_pos_of_neg hA hB_neg
  -- But h says LHS = RHS, i.e. 1/256 = (negative): contradiction since 1/256 > 0
  linarith [h.le]

end FMSA.OriginCheck