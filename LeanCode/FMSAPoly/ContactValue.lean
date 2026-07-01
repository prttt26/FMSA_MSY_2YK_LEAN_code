/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.FMSAPoly.EijStructure

/-!
# Task P.4 — E_ij contact value matches outer-core MSA at r = R_ij

In FMSA, the outer-core DCF for r > R_ij is given by the MSA closure:
```
c_outer(r) = Σ_t K_t · exp(-z_t·(r - R)) / r
```
At r = R each exponential factor equals 1, giving `c_outer(R) = Σ_t K_t / R`.

The inner-core DCF (FMSA_poly) is `(E_ij(r) + P_ij(r)) / r`. Continuity at contact
requires the inner and outer values to agree at r = R:
```
(E_ij(R) + P_ij(R)) / R  =  Σ_t K_t / R
→  E_ij(R) + P_ij(R)  =  Σ_t K_t
```
From Task P.1, `E_ij(R) = Σ_k A_k` (`eij_at_contact`), so exact contact matching pins:
```
P_ij(R)  =  Σ_t K_t - Σ_k A_k
```

## Why it matters

When `Σ K_t < 0` (repulsive net tail) and `Σ A_k > 0`, the polynomial must take a
large negative value at R.  Combined with the origin constraint `P_ij(0) = -E_ij(0) ≤ 0`
(Task P.2) and the polynomial approximation failure (Task P.3), P_ij is forced to make
large excursions across `[0, R]` — impossible without a sharp feature near R that a
low-degree polynomial cannot reproduce.

## Main results

- `outer_dcf_at_contact` : outer-core DCF at r = R collapses to `Σ K_t / R`
- `contact_matching`     : inner = outer ↔ `E_ij(R) + P_ij(R) = Σ K_t`
- `contact_poly_value`   : under matching, `P_ij(R) = Σ K_t - Σ A_k` (by P.1)
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open FMSA.EijStructure

namespace FMSA.ContactValue

section

variable {n : ℕ} (A z K : Fin n → ℝ) (R : ℝ)

/-- **Outer-core DCF at contact (Task P.4):**
The MSA outer-core DCF `c_outer(r) = Σ_t K_t · exp(-z_t·(r-R)) / r` evaluates at r = R to
`Σ_t K_t / R`, because each exponential factor `exp(-z_t · 0) = 1`. -/
theorem outer_dcf_at_contact :
    ∑ t : Fin n, K t * Real.exp (-(z t) * (R - R)) / R = ∑ t : Fin n, K t / R := by
  simp [sub_self, mul_zero, Real.exp_zero]

/-- **Contact matching condition (Task P.4):**
Inner and outer DCFs agree at r = R (i.e. `(E_ij(R) + P(R)) / R = Σ K_t / R`)
if and only if `E_ij(R) + P(R) = Σ K_t`.

Proof: cancel R (nonzero) from both sides. -/
theorem contact_matching (hR : 0 < R) (P : Polynomial ℝ) :
    (eij A z R R + P.eval R) / R = ∑ t : Fin n, K t / R ↔
    eij A z R R + P.eval R = ∑ t : Fin n, K t := by
  rw [← Finset.sum_div]
  exact div_left_inj' (ne_of_gt hR)

/-- **Polynomial contact value (Task P.4):**
If contact matching holds and `E_ij(R) = Σ A_k` (Task P.1), then
`P_ij(R) = Σ_t K_t - Σ_k A_k`.

This pins the polynomial value at the right endpoint.  When `Σ K_t < 0` and `Σ A_k > 0`,
P_ij must take a large negative value at R — combined with the origin constraint
`P_ij(0) ≤ 0` (Task P.2) this forces the polynomial to make large excursions on `[0, R]`. -/
theorem contact_poly_value (P : Polynomial ℝ)
    (h : eij A z R R + P.eval R = ∑ t : Fin n, K t) :
    P.eval R = ∑ t : Fin n, K t - ∑ k : Fin n, A k := by
  rw [eij_at_contact] at h
  linarith

end

end FMSA.ContactValue
