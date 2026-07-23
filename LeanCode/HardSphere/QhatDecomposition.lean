/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Task M.10 — Concrete Q̂0 = P̂ + Ê · exp(-z · sigma_min)  (scalar entry identity)

Each (i,j) entry of the multi-component Baxter matrix Q̂0 in FMSA FMSA_GA_matrix_mix satisfies:
```
Q̂0_{ij}(z) = delta_{ij} - rho · exp(-lam·z) · [Q' · p1(sigma,z) + Q'' · p2(sigma,z)]
```
where `rho = √(rhoirhoj)`, `lam = λij = (sigmaj-sigmai)/2`, and:
```
p1(sigma,z) = (1-zsigma - exp(-zsigma)) / z^2     [= -φ1_shifted from Task 2.3, ex-B.1]
p2(sigma,z) = (1-zsigma + (zsigma)^2/2 - exp(-zsigma)) / z^3
```

This file proves the decomposition Q̂0_{ij} = P̂_{ij} + Ê_{ij} · exp(-z · sigma_min) where:
```
P̂_{ij} = delta_{ij} - rho · exp(-λz) · [Q'·(1-zsigma)/z^2 + Q''·(1-zsigma+(zsigma)^2/2)/z^3]
Ê_{ij}  = rho · exp(-z·(R-sigma_min)) · (Q'/z^2 + Q''/z^3)
```
with `R = lam + sigma` (i.e., Rij = λij + sigmai = (sigmai+sigmaj)/2).

**Key exp identity:** `exp(-λz) · exp(-zsigma) = exp(-zR) = exp(-z(R-sigma_min)) · exp(-zsigma_min)`
follows from `lam + sigma = R` via `← Real.exp_add` + `linear_combination`.

**Physical role (Task M.1):** This supplies the concrete `hD_def : D = P + c • E`
hypothesis for `g_mat_add_a_mat_exp_eq_one`, with `D = Q̂0`, `c = exp(-z·sigma_min)`.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Real

namespace FMSA.HardSphere

/-- **Task M.10 — Q̂0 entry decomposition (scalar):**
```
Q̂0_{ij} = P̂_{ij} + Ê_{ij} · exp(-z · sigma_min)
```
Parameters: `z` (Yukawa pole, `≠ 0`), `sigma` (diameter sigmai), `lam = (sigmaj-sigmai)/2`,
`R = (sigmai+sigmaj)/2` (contact), `sigma_min`, `rho = √(rhoirhoj)`,
`Q'`, `Q''`, `delta` (Kronecker deltaij).
Hypothesis `hR : lam + sigma = R` encodes the contact-distance identity Rij = λij + sigmai. -/
theorem qhat_entry_decomp
    (z sigma lam R sigma_min rho Q' Q'' delta : ℝ) (hz : z ≠ 0) (hR : lam + sigma = R) :
    delta - rho * exp (-(lam * z)) *
        (Q' * ((1 - z * sigma - exp (-(z * sigma))) / z ^ 2) +
         Q'' * ((1 - z * sigma + (z * sigma) ^ 2 / 2 - exp (-(z * sigma))) / z ^ 3))
    = (delta - rho * exp (-(lam * z)) *
           (Q' * ((1 - z * sigma) / z ^ 2) +
            Q'' * ((1 - z * sigma + (z * sigma) ^ 2 / 2) / z ^ 3)))
    + rho * exp (-(z * (R - sigma_min))) * (Q' / z ^ 2 + Q'' / z ^ 3) *
      exp (-(z * sigma_min)) := by
  -- Step 1: key exp identity: exp(-λz)·exp(-zsigma) = exp(-z(R-sigma_min))·exp(-zsigma_min)
  -- follows from lam + sigma = R via exp_add
  have hexp : exp (-(lam * z)) * exp (-(z * sigma)) =
              exp (-(z * (R - sigma_min))) * exp (-(z * sigma_min)) := by
    rw [← exp_add, ← exp_add]
    congr 1; linear_combination -z * hR
  -- Step 2: factor exp(-zsigma) out of the p1/p2 terms (pure algebra, no exp arithmetic)
  have h : delta - rho * exp (-(lam * z)) *
        (Q' * ((1 - z * sigma - exp (-(z * sigma))) / z ^ 2) +
         Q'' * ((1 - z * sigma + (z * sigma) ^ 2 / 2 - exp (-(z * sigma))) / z ^ 3))
      = (delta - rho * exp (-(lam * z)) *
             (Q' * ((1 - z * sigma) / z ^ 2) +
              Q'' * ((1 - z * sigma + (z * sigma) ^ 2 / 2) / z ^ 3)))
        + rho * (exp (-(lam * z)) * exp (-(z * sigma))) * (Q' / z ^ 2 + Q'' / z ^ 3) := by
    field_simp [pow_ne_zero 2 hz, pow_ne_zero 3 hz]; ring
  -- Step 3: substitute hexp into h and rearrange by ring
  rw [h, hexp]; ring

end FMSA.HardSphere
