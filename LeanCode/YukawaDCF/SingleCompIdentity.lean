/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Identity g + a·exp(-z) = 1  ([chsY] Eq. 44, Task 4.2)

**Statement:** For the single-component Baxter Q-function at the Yukawa pole z:
```
g(z) + a(z) · exp(-z) = 1
```
with definitions from [chsY] Eq. 52 and 44:
```
S(z) = (1-eta)^2z^3 + 6eta(1-eta)z^2 + 18eta^2z - 12eta(1+2eta)
L(z) = (1+eta/2)z + (1+2eta)
D(z) := S(z) + 12eta·L(z)·exp(-z)   [= (1-eta)^2z^3·Q0(z)]
g(z) := S(z) / D(z)
a(z) := 12eta·L(z) / D(z)
```

**Proof:** Purely algebraic.
```
g + a·e^{-z} = S/D + (12etaL/D)·e^{-z}
             = (S + 12etaL·e^{-z}) / D
             = D / D  = 1
```
The only hypothesis is D ≠ 0 (i.e., Q0(z) ≠ 0 at the Yukawa pole).

**Physical meaning:** [chsY] Eq. 44. This identity encodes continuity of c^(1)(r) at the
contact distance r = sigma.  Together with the disproof of (1+A)^2 = 1-g^2 (Task 4.3), it shows
that FMSA_chsY and FMSA_pure use incompatible inner-core coefficients for like pairs.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Real

namespace FMSA.SingleComp

/-- **[chsY] Eq. 44 (abstract form):**
For any S, L, D, eta, z with D = S + 12etaL·exp(-z) and D ≠ 0:
```
S / D + 12etaL / D · exp(-z) = 1
```
Proof: trivially (S + 12etaLe^{-z}) / D = D / D = 1. -/
theorem g_add_a_mul_exp_eq_one {S L D eta z : ℝ}
    (hD_def : D = S + 12 * eta * L * Real.exp (-z))
    (hD : D ≠ 0) :
    S / D + 12 * eta * L / D * Real.exp (-z) = 1 := by
  have hnum : S + 12 * eta * L * Real.exp (-z) = D := hD_def.symm
  rw [div_mul_eq_mul_div, ← add_div, hnum, div_self hD]

/-- **[chsY] Eq. 44 (explicit Baxter Q-function form):**
With S(z), L(z) from [chsY] Eq. 52 and D(z) := S(z) + 12eta·L(z)·exp(-z),
if D(z) ≠ 0 then g(z) + a(z)·exp(-z) = 1. -/
theorem g_add_a_mul_exp_eq_one_baxter (eta z : ℝ)
    (hD : (1 - eta) ^ 2 * z ^ 3 + 6 * eta * (1 - eta) * z ^ 2 +
          18 * eta ^ 2 * z - 12 * eta * (1 + 2 * eta) +
          12 * eta * ((1 + eta / 2) * z + (1 + 2 * eta)) * Real.exp (-z) ≠ 0) :
    let S := (1 - eta) ^ 2 * z ^ 3 + 6 * eta * (1 - eta) * z ^ 2 +
             18 * eta ^ 2 * z - 12 * eta * (1 + 2 * eta)
    let L := (1 + eta / 2) * z + (1 + 2 * eta)
    let D := S + 12 * eta * L * Real.exp (-z)
    S / D + 12 * eta * L / D * Real.exp (-z) = 1 := by
  simp only []
  exact g_add_a_mul_exp_eq_one rfl hD

/-- **Task B.3 — Coefficient algebra identity (abstract form):**
From `g + a * c = 1`, deduce `(1 - g^2) - a^2c^2 = 2·a·c·g`.

Physical reading: with `c = exp(-z)`, `g = S/D`, `a = 12etaL/D` (Task 4.2), this
decomposes the FMSA_GA_matrix_mix inner-core coefficient into decaying + growing exponential pieces
whose sum at r = R equals the physical contact value. Required by Task C.1. -/
theorem coeff_identity (g a c : ℝ) (h : g + a * c = 1) :
    (1 - g ^ 2) - a ^ 2 * c ^ 2 = 2 * a * c * g := by
  have hg : g = 1 - a * c := by linarith
  rw [hg]; ring

/-- **Task B.3 — Corollary (Baxter Q-function form):**
With Baxter g = S/D and a = 12etaL/D satisfying `g_add_a_mul_exp_eq_one`,
the coefficient identity holds for c = exp(-z). -/
theorem coeff_identity_baxter {S L D eta z : ℝ}
    (hD_def : D = S + 12 * eta * L * Real.exp (-z))
    (hD : D ≠ 0) :
    (1 - (S / D) ^ 2) - (12 * eta * L / D) ^ 2 * Real.exp (-z) ^ 2 =
    2 * (12 * eta * L / D) * Real.exp (-z) * (S / D) := by
  have h1 : S / D + 12 * eta * L / D * Real.exp (-z) = 1 :=
    g_add_a_mul_exp_eq_one hD_def hD
  exact coeff_identity _ _ _ h1

end FMSA.SingleComp