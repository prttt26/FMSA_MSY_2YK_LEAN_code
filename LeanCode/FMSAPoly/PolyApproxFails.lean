/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Task P.3 — Polynomial approximation failure for large z

The inner-core DCF term `E_ij(r) = Σ_k A_k · exp(-z_k·(R-r))` contains exponentials that,
for large inverse ranges `z_k`, cannot be well approximated by any low-degree polynomial on
`[0, R]`.

The target function `f(r) = exp(z·(R-r))` satisfies:
- `f(0) = exp(z·R)` — exponentially large (e.g., exp(14) ≈ 1.2 × 10^6 for z = 14, R = 1)
- `f(R) = 1`

For any polynomial `p` with `p(0) ≤ exp(z·R)/2` — a condition satisfied in FMSA_poly by
the origin normalisation `P_ij(0) = -E_ij(0)` (Task P.2) when amplitudes are non-negative —
the L∞ approximation error on `[0, R]` is at least `exp(z·R)/2`.

**Why it matters:** For `z2 ≈ 14` (repulsive 2YK second Yukawa), the lower bound on the
approximation error is `exp(14)/2 ≈ 600 000`, explaining the numerical spike observed in
`c(r)` within `~1/z2 ≈ 0.07sigma` of contact.

## Note on the todo hypothesis

The todo statement used `exp(z·R) - p(0) ≥ 0` (i.e., `p(0) ≤ exp(z·R)`) as the hypothesis.
This is insufficient: a polynomial with `p(0) = exp(z·R)/2 + ε` has error `< exp(z·R)/2` at
r = 0, and recovering the bound at an interior point requires Chebyshev degree constraints not
available in Mathlib. The corrected hypothesis `p(0) ≤ exp(z·R)/2` makes r = 0 an explicit
witness, matching the physically relevant FMSA_poly regime where p(0) ≈ -E_ij(0) ≈ 0.

## Main results

- `poly_approx_fails` : `p(0) ≤ exp(z·R)/2` implies ∃ r ∈ [0,R] with error ≥ exp(z·R)/2
- `poly_approx_fails_origin` : FMSA_poly case `p(0) ≤ 0` gives error ≥ exp(z·R) at r = 0
- `poly_approx_fails_two_endpoints` : `p(0) ≤ p(R)` (wrong direction) gives error ≥ (exp(z·R)-1)/2
  at whichever of r = 0 or r = R is worse; complementary to `poly_approx_fails` (Task P.C2)
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace FMSA.PolyApproxFails

/-- **Polynomial approximation lower bound (Task P.3):**
For any polynomial `p` with `p(0) ≤ exp(z·R)/2`, the L∞ error on `[0, R]` for the target
`f(r) = exp(z·(R-r))` is at least `exp(z·R)/2`.

Proof: the witness is `r = 0`, where `f(0) = exp(z·R)` and
`|f(0) - p(0)| = exp(z·R) - p(0) ≥ exp(z·R) - exp(z·R)/2 = exp(z·R)/2`. -/
theorem poly_approx_fails (z R : ℝ) (hR : 0 < R) (_hz : 0 < z) (p : Polynomial ℝ)
    (h : p.eval 0 <= Real.exp (z * R) / 2) :
    ∃ r ∈ Set.Icc 0 R, |Real.exp (z * (R - r)) - p.eval r| >= Real.exp (z * R) / 2 := by
  refine ⟨0, Set.mem_Icc.mpr ⟨le_refl 0, hR.le⟩, ?_⟩
  simp only [sub_zero]
  have hpos : (0 : ℝ) < Real.exp (z * R) := Real.exp_pos _
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **FMSA_poly case (Task P.3):**
In FMSA_poly, the origin normalisation (Task P.2) forces `P_ij(0) = -E_ij(0)`.
When amplitudes `A_k ≥ 0` (attractive Yukawa), `E_ij(0) ≥ 0` so `p(0) ≤ 0`.
With this stronger hypothesis the error at `r = 0` is at least the full `exp(z·R)`. -/
theorem poly_approx_fails_origin (z R : ℝ) (hR : 0 < R) (_hz : 0 < z) (p : Polynomial ℝ)
    (h : p.eval 0 <= 0) :
    ∃ r ∈ Set.Icc 0 R, |Real.exp (z * (R - r)) - p.eval r| >= Real.exp (z * R) := by
  refine ⟨0, Set.mem_Icc.mpr ⟨le_refl 0, hR.le⟩, ?_⟩
  simp only [sub_zero]
  have hpos : (0 : ℝ) < Real.exp (z * R) := Real.exp_pos _
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **Tighter two-endpoint bound (Task P.C2):**
For any polynomial `p` with `p(0) ≤ p(R)` (non-decreasing, i.e. going in the OPPOSITE
direction to the strictly decreasing target `f(r) = exp(z·(R-r))`), at least one of the
endpoints `r = 0` or `r = R` carries error ≥ `(exp(z·R) - 1)/2`.

**Proof by case split on whether `p(0) ≤ (exp(zR)+1)/2`:**
- Case 1: `p(0) ≤ (exp(zR)+1)/2 < exp(zR)` → error at r = 0 ≥ (exp(zR)-1)/2.
- Case 2: `p(0) > (exp(zR)+1)/2` and `p(R) ≥ p(0)` → `p(R) > 1` → error at r = R ≥ (exp(zR)-1)/2.

**Complements `poly_approx_fails`:** that theorem covers `p(0) ≤ exp(zR)/2`; this one covers the
"wrong-direction" regime `p(0) ≤ p(R)`. Together they bound all polynomials except those with
`p(0) ∈ (exp(zR)/2, exp(zR)]` AND `p(0) > p(R)` (the Chebyshev gap, not yet formalised). -/
theorem poly_approx_fails_two_endpoints (z R : ℝ) (hR : 0 < R) (hz : 0 < z) (p : Polynomial ℝ)
    (hmono : p.eval 0 <= p.eval R) :
    ∃ r ∈ Set.Icc 0 R, |Real.exp (z * (R - r)) - p.eval r| >= (Real.exp (z * R) - 1) / 2 := by
  -- exp(z*R) > 1 since z*R > 0
  have hexp : 1 < Real.exp (z * R) := by
    have := Real.add_one_le_exp (z * R)
    linarith [mul_pos hz hR]
  by_cases h : p.eval 0 <= (Real.exp (z * R) + 1) / 2
  · -- Case 1: p(0) ≤ (exp(zR)+1)/2 < exp(zR), so error at r = 0 ≥ (exp(zR)-1)/2
    refine ⟨0, Set.mem_Icc.mpr ⟨le_refl 0, hR.le⟩, ?_⟩
    simp only [sub_zero]
    rw [abs_of_nonneg (by linarith)]
    linarith
  · -- Case 2: p(0) > (exp(zR)+1)/2 and p(R) ≥ p(0) > 1, so error at r = R ≥ (exp(zR)-1)/2
    push Not at h
    refine ⟨R, Set.mem_Icc.mpr ⟨hR.le, le_refl R⟩, ?_⟩
    simp only [sub_self, mul_zero, Real.exp_zero]
    rw [abs_of_nonpos (by linarith)]
    linarith

end FMSA.PolyApproxFails
