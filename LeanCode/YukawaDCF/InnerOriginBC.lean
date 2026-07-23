/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HardSphere.SingleCompReduction
import LeanCode.HardSphere.SingleCompIdentity
import LeanCode.YukawaDCF.I1I2Integrals

/-!
# Task GAP.4 — FMSA_GA_matrix_mix origin BC is automatic: `lim_{r→0} r·c^(1)(r) = 0`

For the FMSA_GA_matrix_mix inner-core formula ([chsY] Eq. 41 → 42), the origin boundary condition
`lim_{r→0} r·c^(1)_ij(r) = 0` is satisfied **automatically** — no explicit normalisation
parameter choice is needed.  This contrasts sharply with FMSA_poly (Task P.2), which
requires explicitly setting `p_0 = -E_ij(0)`.

## Structure of [chsY] Eq. 42 at r = 0

At r = 0, the full formula decomposes as:

```
r·c^(1)(r)|_{r=0} = Term_I(0) + Term_II(0) + Term_III(0) + p_0
```

| Term | Value at r = 0 | Why |
|------|----------------|-----|
| Term I | `K*(1-g^2)*exp(z)` | decaying exponential `exp(-z*(r-R))` at r=0 gives `exp(z)` |
| Term II | `0` | involves `I_1(0,...) = 0` (Task 1.3 / `I1_at_zero`) |
| Term III | `0` | involves `I_2(0,...) = 0` (Task 1.3 / `I2_at_zero`) |
| p_0 | `-2*K*g*a` | Baxter-forced: equals `K*a^2*exp(-z) - K*(1-g^2)*exp(z)` |

The polynomial constant `p_0 = -2*K*g*a` is algebraically determined by the Baxter Q-matrix
factorization.  It follows from `g + a*exp(-z) = 1` (Task M.9) via
`sq_of_g_add_a_exp_eq_one` (Task 4.4): `g^2*exp(z) + a^2*exp(-z) + 2*g*a = exp(z)`.

## Contrast with FMSA_poly (Task P.2)

In FMSA_poly, the polynomial constant must be **explicitly imposed** as
`p_0 = -E_ij(0) = -Σ_k A_k * exp(-z_k * R)` (Task P.2: `origin_finiteness`).
This is a normalization *choice*, not a structural consequence.

In FMSA_GA_matrix_mix, `p_0` is *uniquely forced* by the Baxter factorization:
```
p_0 = K*a^2*exp(-z) - K*(1-g^2)*exp(z) = -2*K*g*a
```
No separate normalization step is required or permitted.

## Results

| Statement | Status |
|---|---|
| `origin_termI1_vanish_at_zero` | proved — `I_1(0,...) = 0` (Term II vanishes) |
| `origin_termI2_vanish_at_zero` | proved — `I_2(0,...) = 0` (Term III vanishes) |
| `origin_polynomial_constant` | proved — non-polynomial part of Eq. 42 at r=0 equals `2*K*g*a` |
| `origin_bc_abstract` | proved — abstract: Term_I + 0 + 0 + p_0 = 0 |
| `origin_bc_concrete` | proved — full Eq. 42 at r=0 is 0 |
-/

open Real intervalIntegral

namespace FMSA.MixturePoly

/-! ### Terms II and III vanish at r = 0 -/

/-- **Task GAP.4 helper — Term II vanishes at r = 0:**

The integral `I_1(0, alpha, z) = ∫_0^0 (alpha - v)*exp(z*v) dv = 0` (Task 1.3),
so Term II of [chsY] Eq. 41 contributes zero at r = 0. -/
lemma origin_termI1_vanish_at_zero (alpha z : ℝ) :
    ∫ v in (0 : ℝ)..(0 : ℝ), (alpha - v) * Real.exp (z * v) = 0 :=
  FMSA.DCF.I1_at_zero

/-- **Task GAP.4 helper — Term III vanishes at r = 0:**

The integral `I_2(0, alpha, z) = ∫_0^0 (alpha-v)^2*exp(z*v) dv = 0` (Task 1.3),
so Term III of [chsY] Eq. 41 contributes zero at r = 0. -/
lemma origin_termI2_vanish_at_zero (alpha z : ℝ) :
    ∫ v in (0 : ℝ)..(0 : ℝ), (alpha - v) ^ 2 * Real.exp (z * v) = 0 :=
  FMSA.DCF.I2_at_zero

/-! ### Polynomial constant is algebraically forced -/

/-- **Task GAP.4 — Polynomial constant identity:**

The non-polynomial part of [chsY] Eq. 42 at r = 0 equals `2*K*g*a`, where
`g = S/D`, `a = 12*eta*L/D`, and `g + a*exp(-z) = 1` (Task M.9).

Equivalently, the Baxter-forced polynomial constant is `p_0 = -2*K*g*a`:
this is what makes the full formula vanish at r = 0.

Proof: rearranges to `g^2*exp(z) + a^2*exp(-z) + 2*g*a = exp(z)`,
which is `sq_of_g_add_a_exp_eq_one` (Task 4.4). -/
theorem origin_polynomial_constant (g a z K : ℝ)
    (h : g + a * Real.exp (-z) = 1) :
    K * (1 - g ^ 2) * Real.exp z - K * a ^ 2 * Real.exp (-z) = 2 * K * g * a := by
  linear_combination -K * FMSA.SingleComp.sq_of_g_add_a_exp_eq_one g a z h

/-! ### Abstract and concrete GAP.4 theorems -/

/-- **Task GAP.4 (abstract form).**

⚠ **Content-free scaffolding (vacuity audit 2026-07-17).** `term_i`, `p0` are arbitrary reals;
the conclusion is the hypothesis `h_cancel` with two literal `+ 0`s inserted (the "Terms II/III
vanish" are hard-coded numerals here, **not** the `origin_termI1_vanish_at_zero`/`origin_termI2_vanish_at_zero`
lemmas). This asserts nothing about any physical object and **must not** be cited as GAP.4's content.
GAP.4's real content is carried by the concrete siblings `origin_bc_concrete`
(below) and `origin_bc_baxter`, which do the actual algebra via
`sq_of_g_add_a_exp_eq_one`. Kept as an illustrative shape only; no production-path licensing. -/
theorem origin_bc_abstract (term_i p0 : ℝ)
    (h_cancel : term_i + p0 = 0) :
    term_i + 0 + 0 + p0 = 0 := by linarith

/-- **Task GAP.4 — FMSA_GA_matrix_mix origin BC is automatic (N=1 / single-component):**

For the single-component FMSA_GA_matrix_mix formula ([chsY] Eq. 42) with Baxter scalars
`g`, `a` satisfying `g + a * exp(-z) = 1` (Task M.9), and polynomial constant
`p_0 = -2 * K * g * a` (Baxter-forced), the full formula at r = 0 vanishes:

```
K*(1-g^2)*exp(z) - K*a^2*exp(-z) + p_0 = 0
```

**No explicit normalisation is needed:** `p_0` is uniquely determined by the Baxter
structure.  FMSA_poly (Task P.2) must instead impose `p_0 = -E_ij(0)` by hand. -/
theorem origin_bc_concrete (g a z K : ℝ)
    (h : g + a * Real.exp (-z) = 1) :
    K * (1 - g ^ 2) * Real.exp z - K * a ^ 2 * Real.exp (-z) +
      (-(2 * K * g * a)) = 0 := by
  linear_combination -K * FMSA.SingleComp.sq_of_g_add_a_exp_eq_one g a z h

/-- **Task GAP.4 (Baxter form):**

Concrete instantiation with `S`, `M` (Baxter polynomial values) and `D = S + M*exp(-z)`,
setting `g = S/D`, `a = M/D`.  The polynomial constant is `p_0 = -2*K*S*M/D^2`. -/
theorem origin_bc_baxter (S M z K : ℝ)
    (hD : S + M * Real.exp (-z) ≠ 0) :
    let D := S + M * Real.exp (-z)
    K * (1 - (S / D) ^ 2) * Real.exp z - K * (M / D) ^ 2 * Real.exp (-z) +
      (-(2 * K * (S / D) * (M / D))) = 0 := by
  simp only []
  apply origin_bc_concrete
  field_simp [hD]

end FMSA.MixturePoly
