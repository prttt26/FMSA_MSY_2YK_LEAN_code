/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.SingleCompIdentity
import LeanCode.HardSphere.MatrixIdentity

/-!
# Single-component reduction: [chsY] Eq. 42 origin check and factoring  (Task 4.4)

**Context:** For N=1, sigma=1, λ=0, the closed-form inside-core DCF ([chsY] Eq. 42) is
```
r·c(1)(r)/K = e^{-z(r-1)} - [S^2·e^{-z(r-1)} + (12etaL)^2·e^{+z(r-1)} + poly4(r)] / D^2
```
with D = S + 12etaL·e^(-z), S = S(z), L = L(z) the Baxter polynomials ([chsY] Eq. 52).
Setting g := S/D, a := 12etaL/D (so g+ae^(-z)=1 by Task M.9), this factors as Eq. 43:
```
r·c(1)(r)/K = (1-g^2)·e^{-z(r-1)} - a^2·e^{+z(r-1)} + poly4(r)/D^2
```

**Proved in this file (no sorry):**

1. `correction_sq_eq` — fundamental cancellation identity:
   `S^2e^z + M^2e^(-z) + 2SM = (S + Me^(-z))^2e^z`
   Proof: write e^(-z) = (e^z)⁻¹, clear denominators, ring.

2. `f42_zero_at_origin` — Eq. 42 gives 0 at r=0:
   `e^z - (S^2e^z + M^2e^(-z) + 2SM) / (S + Me^(-z))^2 = 0`
   Physical meaning: r·c(0) must be 0.

3. `sq_of_g_add_a_exp_eq_one` — Task M.9 implies origin check:
   `g + ae^(-z) = 1  →  g^2e^z + a^2e^(-z) + 2ga = e^z`
   Proof: from `correction_sq_eq` with the hypothesis h.

4. `eq42_factored_bracket` — Eq. 42 → Eq. 43 numerator identity:
   `(D^2-S^2)·Em - M^2·Ep = D^2·(1-(S/D)^2)·Em - D^2·(M/D)^2·Ep`
   Proof: field_simp + ring.

**Status of full Eq. 41→42 reduction:** sorry (requires I1/I2 integral lemmas, Tasks 1.1/1.2).
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Real

namespace FMSA.SingleComp

/-! ## 1. Core algebraic identity -/

/-- **Three-term cancellation identity (Task 4.4):**
`S^2·e^z + M^2·e^(-z) + 2·S·M = (S + M·e^(-z))^2·e^z`
Proof: write e^(-z) = (e^z)⁻¹, clear denominators with field_simp, close with ring. -/
theorem correction_sq_eq (S M z : ℝ) :
    S ^ 2 * Real.exp z + M ^ 2 * Real.exp (-z) + 2 * S * M =
    (S + M * Real.exp (-z)) ^ 2 * Real.exp z := by
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero z]
  ring

/-! ## 2. Origin check for Eq. 42 -/

/-- **[chsY] Eq. 42 vanishes at r=0 (Task 4.4):**
With D := S + M·e^(-z), D ≠ 0:
`e^z - (S^2·e^z + M^2·e^(-z) + 2·S·M) / D^2 = 0`
Proof: numerator equals D^2·e^z by `correction_sq_eq`, so fraction = e^z. -/
theorem f42_zero_at_origin (S M z : ℝ)
    (hD : S + M * Real.exp (-z) ≠ 0) :
    Real.exp z -
      (S ^ 2 * Real.exp z + M ^ 2 * Real.exp (-z) + 2 * S * M) /
        (S + M * Real.exp (-z)) ^ 2 = 0 := by
  have hD2 : (S + M * Real.exp (-z)) ^ 2 ≠ 0 := pow_ne_zero 2 hD
  rw [sub_eq_zero, eq_comm, div_eq_iff hD2]
  linear_combination correction_sq_eq S M z

/-- **Baxter form of the origin check:**
`e^z - (S^2·e^z + (12etaL)^2·e^(-z) + 24etaSL) / D^2 = 0`  where D = S + 12etaL·e^(-z), D ≠ 0.
Note: 24etaSL = 2·S·(12etaL), so this is an instance of `f42_zero_at_origin`. -/
theorem f42_zero_at_origin_baxter (eta z S L : ℝ)
    (hD : S + 12 * eta * L * Real.exp (-z) ≠ 0) :
    Real.exp z -
      (S ^ 2 * Real.exp z + (12 * eta * L) ^ 2 * Real.exp (-z) + 24 * eta * S * L) /
        (S + 12 * eta * L * Real.exp (-z)) ^ 2 = 0 := by
  have h2SM : 24 * eta * S * L = 2 * S * (12 * eta * L) := by ring
  rw [h2SM]
  exact f42_zero_at_origin S (12 * eta * L) z hD

/-! ## 3. Connection to Task M.9 -/

/-- **Task M.9 implies the origin-check identity (Task 4.4):**
If g + a·e^(-z) = 1, then `g^2·e^z + a^2·e^(-z) + 2·g·a = e^z`.
Proof: `correction_sq_eq g a z` gives LHS = (g+ae^(-z))^2·e^z; h gives 1·e^z = e^z. -/
theorem sq_of_g_add_a_exp_eq_one (g a z : ℝ)
    (h : g + a * Real.exp (-z) = 1) :
    g ^ 2 * Real.exp z + a ^ 2 * Real.exp (-z) + 2 * g * a = Real.exp z := by
  -- Witness: (g+ae^(-z)+1)·e^z·(h: g+ae^(-z)-1=0) + correction_sq_eq
  -- Ring check: (g+ae^(-z)+1)·e^z·((g+ae^(-z))-1) + LHS - (g+ae^(-z))^2e^z = LHS - e^z  ✓
  linear_combination (g + a * Real.exp (-z) + 1) * Real.exp z * h + correction_sq_eq g a z

/-! ## 4. Eq. 42 → Eq. 43: bracket factoring -/

/-- **[chsY] Eq. 42 → Eq. 43: factoring via g, a (Task 4.4):**
`(D^2-S^2)·Em - M^2·Ep = D^2·(1-(S/D)^2)·Em - D^2·(M/D)^2·Ep`
With g = S/D, a = M/D, dividing both sides by D^2 gives (1-g^2)·Em - a^2·Ep = Eq. 43 bracket.
Proof: field_simp clears D^2 denominators, ring closes. -/
theorem eq42_factored_bracket (S M D Em Ep : ℝ) (hD : D ≠ 0) :
    (D ^ 2 - S ^ 2) * Em - M ^ 2 * Ep =
    D ^ 2 * (1 - (S / D) ^ 2) * Em - D ^ 2 * (M / D) ^ 2 * Ep := by
  field_simp [pow_ne_zero 2 hD]

/-! ## 5. N=1 reduction: step-function vanishing and Term I coefficient (Task 4.4) -/

/-- **Step-function gate for N=1 mediated terms (Task 4.4 helper):**
For N=1, sigma=1, λ=0 the contact distance R_11 = 1.  For r < 1 = R_11 the gate
θ(r - R_11) = θ(r - 1) = 0.  This makes Terms II, III, IV of [chsY] Eq. 41 vanish
for 0 < r < 1, leaving only Term I. -/
theorem eq41_n1_step_gate (r : ℝ) (hr1 : r < 1) : ¬ (1 : ℝ) <= r :=
  not_le.mpr hr1

/-- **[chsY] Eq. 41 → N=1 inside-core coefficient identity (Task 4.4):**

For N=1, sigma=1, λ=0, only Term I of [chsY] Eq. 41 survives for 0 < r < 1.
The step-function gates θ(r-R11) = θ(r-1) = 0 kill Terms II, III, IV
(see `eq41_n1_step_gate`).  Term I gives coefficient `(1+A(z))^2` where
`A(z) = 1/Q0(z) - 1` is the hard-sphere propagator ([chsY] Appendix A).

**Algebraic identity (proved below):**
With `D = S(z) + 12eta·L(z)·e^{-z}` and `Q0(z) = D/((1-eta)^2z^3)`:
```
(1 + A)^2  =  (1-eta)^4 z^6 / D^2
```

**Why this differs from FMSA_pure Eq. 42:**
FMSA_pure coefficient = `1 - g^2  = (D^2 - S^2)/D^2` while Eq. 41 gives `(1-eta)^4z^6/D^2`.
These coincide iff `(1-eta)^4z^6 = D^2 - S^2` — which is **false** in general.
Counterexample eta=3/4, z=1: LHS = 1/256 > 0, RHS < 0; proved formally in
`FMSA.OriginCheck.identity_one_plus_A_sq_ne_one_minus_g_sq`.
Hence [chsY] Eq. 41 does **not** reduce to Eq. 42 for N=1. -/
theorem eq41_n1_reduces_to_eq42
    (S L eta z : ℝ) (_hz : z ≠ 0) (_heta : (1 - eta) ^ 2 * z ^ 3 ≠ 0)
    (_hD : S + 12 * eta * L * Real.exp (-z) ≠ 0) :
    -- D := S(z) + 12eta·L(z)·e^{-z},  A(z) := 1/Q0(z) - 1 = (1-eta)^2z^3/D - 1
    -- Term I coefficient identity: (1 + A)^2 = (1-eta)^4z^6/D^2
    let D := S + 12 * eta * L * Real.exp (-z)
    let A := (1 - eta) ^ 2 * z ^ 3 / D - 1
    (1 + A) ^ 2 = (1 - eta) ^ 4 * z ^ 6 / D ^ 2 := by
  simp only []
  -- 1 + (x - 1) = x, so (1 + A)^2 = ((1-eta)^2z^3/D)^2
  have h1 : 1 + ((1 - eta) ^ 2 * z ^ 3 / (S + 12 * eta * L * Real.exp (-z)) - 1) =
            (1 - eta) ^ 2 * z ^ 3 / (S + 12 * eta * L * Real.exp (-z)) := by ring
  rw [h1, div_pow]
  -- ((1-eta)^2z^3)^2 = (1-eta)^4z^6
  have h2 : ((1 - eta) ^ 2 * z ^ 3) ^ 2 = (1 - eta) ^ 4 * z ^ 6 := by ring
  rw [h2]

/-! ## 6. Task C.1 — N=1: Corrected FMSA_GA_matrix_mix inner-core = [chsY] Eq. 43 (FMSA_pure) -/

/-- **Task C.1 — N=1 corrected FMSA_GA_matrix_mix = [chsY] Eq. 43 (FMSA_pure):**

For N=1, with Baxter scalars `g`, `a`, shift `c` satisfying `h : g + a * c = 1`
(from Task M.9 / M.1), the corrected FMSA_GA_matrix_mix formula uses decaying coefficient
`(1 - g^2)` and growing coefficient `a^2`.  The key M.11 contact identity confirms
these are consistent at `r = R` (where Em = Ep = 1, `c = exp(-z·sigma_min)`):

```
(1 - g^2) - a^2 · c^2  =  2 · a · c · g
```

**Contrast with Task 4.3:** Eq. 41 (uncorrected) uses `(1+A)^2` ≠ `1-g^2` (disproved
there).  The corrected formula replaces `(1+A)^2` with `(1-g^2)`, giving Eq. 43 exactly. -/
theorem c1_n1_ga_matrix_mix_eq_fmsa_pure (g a c : ℝ) (h : g + a * c = 1) :
    (1 - g ^ 2) - a ^ 2 * c ^ 2 = 2 * a * c * g :=
  coeff_identity g a c h

/-- **Task C.1 corollary — M.1 (N=1) instantiation:**
The hypothesis `g + a * c = 1` for `c1_n1_ga_matrix_mix_eq_fmsa_pure` follows from
`g_mat_n1_eq_scalar` with `P = S`, `E = 12etaL`, `D = S + c·(12etaL)`. -/
theorem c1_n1_from_mat_identity (S M D c : ℝ)
    (hD_def : D = S + c * M) (hD : D ≠ 0) :
    (1 - (S / D) ^ 2) - (M / D) ^ 2 * c ^ 2 = 2 * (M / D) * c * (S / D) :=
  c1_n1_ga_matrix_mix_eq_fmsa_pure (S / D) (M / D) c
    (by linear_combination FMSA.MatrixIdentity.g_mat_n1_eq_scalar S M D c hD_def hD)

/-- **Task C.2 — the N=1 like-pair two-exp formula is bounded (the "exp-cancellation").**

For the single-component Baxter data `g = S/D`, `a = 12ηL/D`, with the defining relation
`D = S + 12ηL·exp(−z·d)` (Task M.9 / [chsY] Eq. 44), the growing-exponential factor of the
inner-core coefficient is uniformly controlled:
```
|(1 − (S/D)²) · exp(z(d−r))| ≤ 2 · (12η|L|/D²) · |D + S|.
```

**Why:** the *growing* `exp(z(d−r))` is killed by the *decaying* `exp(−z·d)` hidden in
`D − S = 12ηL·exp(−z·d)`:
```
(1 − (S/D)²)·exp(z(d−r)) = (D−S)(D+S)/D²·exp(z(d−r))
                         = 12ηL·(D+S)/D²·exp(−z·d)·exp(z(d−r)) = 12ηL·(D+S)/D²·exp(−z·r),
```
and `exp(−z·r) ≤ 1` for `z, r ≥ 0`.  This is the mathematical reason the single-component limit is
**well-conditioned**; for N=2 unlike pairs the analogous cancellation is absent (`G_{01} ≈ 0`,
Group GA), so the base `exp(z·R_{ij})` grows without bound.  The proved constant is actually half
the stated bound (`12η|L||D+S|/D²`); the factor 2 leaves slack.

**Depends on:** the Task M.9 relation `D − S = 12ηL·exp(−z·d)` (here as `hD_def`). -/
theorem c1_n1_twoexp_bounded {S L D eta z d r : ℝ}
    (hD_def : D = S + 12 * eta * L * Real.exp (-z * d))
    (hD : D ≠ 0) (heta : 0 < eta) (hz : 0 ≤ z) (hr : 0 ≤ r) :
    |(1 - (S / D) ^ 2) * Real.exp (z * (d - r))| ≤
      2 * (12 * eta * |L| / D ^ 2) * |D + S| := by
  have hD2pos : (0:ℝ) < D ^ 2 := by positivity
  have hDS : D - S = 12 * eta * L * Real.exp (-z * d) := by rw [hD_def]; ring
  have hexp : Real.exp (-z * d) * Real.exp (z * (d - r)) = Real.exp (-z * r) := by
    rw [← Real.exp_add]; congr 1; ring
  have hkey : (1 - (S / D) ^ 2) * Real.exp (z * (d - r))
      = 12 * eta * L * (D + S) / D ^ 2 * Real.exp (-z * r) := by
    have hsq : 1 - (S / D) ^ 2 = (D - S) * (D + S) / D ^ 2 := by field_simp; ring
    rw [hsq, hDS, ← hexp]; ring
  rw [hkey, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hle1 : Real.exp (-z * r) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hz hr])
  have habs : |12 * eta * L * (D + S) / D ^ 2| = 12 * eta * |L| * |D + S| / D ^ 2 := by
    rw [abs_div, abs_of_pos hD2pos]
    congr 1
    rw [show 12 * eta * L * (D + S) = 12 * eta * (L * (D + S)) by ring,
        abs_mul, abs_of_pos (by linarith : (0:ℝ) < 12 * eta), abs_mul]
    ring
  rw [habs]
  have hnn : (0:ℝ) ≤ 12 * eta * |L| * |D + S| / D ^ 2 := by
    apply div_nonneg _ (sq_nonneg D)
    exact mul_nonneg (mul_nonneg (by linarith) (abs_nonneg L)) (abs_nonneg (D + S))
  calc 12 * eta * |L| * |D + S| / D ^ 2 * Real.exp (-z * r)
      ≤ 12 * eta * |L| * |D + S| / D ^ 2 * 1 := mul_le_mul_of_nonneg_left hle1 hnn
    _ = 12 * eta * |L| * |D + S| / D ^ 2 := mul_one _
    _ ≤ 2 * (12 * eta * |L| / D ^ 2) * |D + S| := by
        have hrw : 2 * (12 * eta * |L| / D ^ 2) * |D + S|
            = 2 * (12 * eta * |L| * |D + S| / D ^ 2) := by ring
        rw [hrw]; linarith

end FMSA.SingleComp
