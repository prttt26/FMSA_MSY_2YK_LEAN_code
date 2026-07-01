/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.FMSAPoly.SingleCompReduction

/-!
# Task 4.1 — Single-component b_ij formula: N=1 case of [chsY] Eq. 24

**Physical context.** In the multi-species Wiener–Hopf solution [chsY], the Fourier
transform of the inner-core first-order DCF can be written as a sum over species pairs
(m, n) and Yukawa tails t:

    T_S(k)_ij = Σ_{t,m,n} K_{mn}^t · (1 + A_{im}(z^t)) · (1 + A_{nj}(z^t)) / (ik + z^t)

where `A` is the MSA propagator matrix (the `a` matrix in `amat_scalar`).  For a
single species (N = 1) and single tail, the only non-zero index combination is
i = j = m = n = 0, so the double sum collapses to one term.

**Proved in this file (no sorry):**

1. `b_general` — the abstract double-sum definition of `b_ij` for N species.

2. `b_n1_collapse` — for N=1, `Σ_{m n : Fin 1}` reduces to a single evaluation:
   the result is `K · (1 + A)^2 / (s + z)`.  Proof: `Fin.sum_univ_one` × 2, then `ring`.

3. `a_n1_one_plus_eq_Qinv` — for N=1, the definition `A = Q̂⁻¹ - 1` gives `1 + A = Q̂⁻¹`.
   Proof: `ring`.

4. `b_n1_baxter_formula` — connecting Task 4.1 to the concrete Baxter A(z):
   with A = (1-eta)^2z^3/D - 1 (from [chsY] Appendix A / `eq41_n1_reduces_to_eq42`),
   the collapsed formula becomes `K · (1-eta)^4z^6 / (D^2 · (s+z))`.
   Proof: `eq41_n1_reduces_to_eq42` + `b_n1_collapse` + `ring`.

**Key Lean fact used:** `Fin.sum_univ_one : ∀ f : Fin 1 → alpha, ∑ i, f i = f 0`.
-/

namespace FMSA.Task4_1

/-! ## 1. Abstract multi-species b_ij definition -/

/-- **[chsY] Eq. 24 (one tail, abstract N).** The pole-residue amplitude at wavevector s:

    b_ij(s) = Σ_{m n : Fin N} K_{mn} · (1 + A_{im}) · (1 + A_{nj}) / (s + z)

where `K : Fin N → Fin N → ℝ` are the Yukawa amplitudes,
`A : Fin N → Fin N → ℝ` is the MSA propagator matrix at the pole `z`, and `s` is
the Laplace / Fourier variable. -/
noncomputable def b_general {N : ℕ} (K A : Fin N → Fin N → ℝ)
    (z s : ℝ) (i j : Fin N) : ℝ :=
  ∑ m : Fin N, ∑ n : Fin N,
    K m n * (1 + A i m) * (1 + A n j) / (s + z)

/-! ## 2. N=1 collapse -/

/-- **Task 4.1 main result (abstract form):** For N=1, the double sum in `b_general`
has only one term (m = n = 0).  It evaluates to `K · (1 + A)^2 / (s + z)`.

Proof: `Fin.sum_univ_one` collapses both sums to index 0, then `ring` closes the goal
`K · (1+A) · (1+A) / (s+z) = K · (1+A)^2 / (s+z)`. -/
theorem b_n1_collapse (K A : Fin 1 → Fin 1 → ℝ) (z s : ℝ) :
    b_general K A z s 0 0 =
    K 0 0 * (1 + A 0 0) ^ 2 / (s + z) := by
  simp only [b_general, Fin.sum_univ_one]
  ring

/-! ## 3. Connection to A = Q̂⁻¹ - 1 -/

/-- **A-matrix entry for N=1:** From the definition `A_ij = (Q̂⁻¹)_{ij} · exp(λ_{ij}·z) - delta_{ij}`,
for i = j = 0 with λ_00 = 0 (equal-species pair), `A_00 = Q̂⁻¹ - 1`.
The immediate consequence is `1 + A_00 = Q̂⁻¹`. -/
theorem a_n1_one_plus_eq_Qinv (Q : ℝ) :
    let A00 := Q⁻¹ - 1
    1 + A00 = Q⁻¹ := by
  simp

/-- **Squared form:** `(1 + A_00)^2 = Q̂(z)⁻^2`. -/
theorem a_n1_one_plus_sq (Q : ℝ) :
    let A00 := Q⁻¹ - 1
    (1 + A00) ^ 2 = Q⁻¹ ^ 2 := by
  simp; ring

/-! ## 4. Concrete Baxter form -/

/-- **Task 4.1 (concrete Baxter form):** With the FMSA single-component Baxter factor
`Q̂(z) = D / ((1-eta)^2z^3)` where `D = S(z) + 12eta·L(z)·e^{-z}`, the N=1 `b_00` formula
evaluates to:

    b_00(s) = K · (1 + A(z))^2 / (s + z) = K · (1-eta)^4z^6 / (D^2 · (s + z))

Here `A(z) = (1-eta)^2z^3/D - 1` is the propagator from [chsY] Appendix A,
proved in `FMSA.SingleComp.eq41_n1_reduces_to_eq42`.

Proof: substitute the constant K and A into `b_n1_collapse`, then use
`eq41_n1_reduces_to_eq42` to rewrite `(1 + A)^2`. -/
theorem b_n1_baxter_formula (K S L eta z s : ℝ)
    (hz : z ≠ 0) (heta : (1 - eta) ^ 2 * z ^ 3 ≠ 0)
    (hD : S + 12 * eta * L * Real.exp (-z) ≠ 0) :
    let D   := S + 12 * eta * L * Real.exp (-z)
    let A00 := (1 - eta) ^ 2 * z ^ 3 / D - 1
    b_general (fun _ _ => K) (fun _ _ => A00) z s 0 0 =
    K * ((1 - eta) ^ 4 * z ^ 6 / (S + 12 * eta * L * Real.exp (-z)) ^ 2) / (s + z) := by
  simp only []
  -- Step 1: collapse the N=1 double sum
  rw [b_n1_collapse]
  -- Step 2: use (1 + A00)^2 = (1-eta)^4z^6/D^2 from SingleCompReduction
  have hA_sq := FMSA.SingleComp.eq41_n1_reduces_to_eq42 S L eta z hz heta hD
  simp only [] at hA_sq
  -- hA_sq : (1 + ((1-eta)^2*z^3/D - 1))^2 = (1-eta)^4*z^6/D^2
  -- Goal: K * (1 + ((1-eta)^2*z^3/D - 1))^2 / (s+z) = K * ((1-eta)^4*z^6/D^2) / (s+z)
  rw [hA_sq]

end FMSA.Task4_1
