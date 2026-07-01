/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.FMSAPoly.EijStructure

/-!
# Task F.2 / F.2a — Inner-Core Free Energy Integral (Closed Form)

**Source:** FMSA E_ij decomposition (FMSA_poly inner-core region)

For the E_ij contribution to `c^(1)(r)` on `[0, R]`:
    `E_ij(r) = Σ_t A_ij(z_t) · exp(z_t · (r - R))`

The first-order free energy inner-core integral is:
    `∫_0^R E_ij(r) · r dr = Σ_t A_ij(z_t) · [R/z_t - 1/z_t^2 + exp(-z_t·R)/z_t^2]`

**Derivation for each term:**
    `∫_0^R r · exp(z·(r-R)) dr`
      `= exp(-zR) · ∫_0^R r · exp(z·r) dr`
      `= exp(-zR) · [(R/z - 1/z^2)·exp(zR) + 1/z^2]`
      `= R/z - 1/z^2 + exp(-zR)/z^2`

**Antiderivative for ∫ r·exp(zr) dr:** `F(r) = (r/z - 1/z^2)·exp(zr)`, `F'(r) = r·exp(zr)`.
-/

open MeasureTheory intervalIntegral Real Set

namespace FMSA.FreeEnergy

/-! ### HasDerivAt lemma for the antiderivative -/

/-- Antiderivative of `r · exp(z·r)` is `(r/z - 1/z^2) · exp(z·r)`.

Verification: `d/dr [(r/z-1/z^2)·exp(zr)] = (1/z)·exp(zr) + (r/z-1/z^2)·z·exp(zr)`
`= exp(zr)·(1/z + z·r/z - z/z^2) = exp(zr)·(1/z + r - 1/z) = r·exp(zr)`. ✓ -/
private lemma hasDerivAt_r_exp_mul_antideriv {z : ℝ} (hz : z ≠ 0) (r : ℝ) :
    HasDerivAt (fun r => (r / z - 1 / z ^ 2) * Real.exp (z * r))
               (r * Real.exp (z * r)) r := by
  -- E(r) = exp(z·r), E'(r) = exp(z·r)·z
  have hE : HasDerivAt (fun r => Real.exp (z * r)) (Real.exp (z * r) * z) r := by
    have h : HasDerivAt (fun r => z * r) z r := by
      simpa using (hasDerivAt_id r).const_mul z
    exact h.exp
  -- A(r) = r/z - 1/z^2, A'(r) = 1/z
  have hA : HasDerivAt (fun r => r / z - 1 / z ^ 2) (1 / z) r := by
    have h := (hasDerivAt_id r).div_const z |>.sub (hasDerivAt_const r (1 / z ^ 2))
    simpa using h
  -- Product rule: F' = A'·E + A·E' = r·exp(zr)
  exact (hA.mul hE).congr_deriv (by field_simp [hz]; ring)

/-! ### Integral formula for ∫_0^R r·exp(zr) dr -/

/-- **∫_0^R r · exp(z·r) dr = (R/z - 1/z^2)·exp(zR) + 1/z^2** for `z ≠ 0`.

Proved by FTC: antiderivative is `F(r) = (r/z - 1/z^2)·exp(zr)`, `F(R) - F(0) = result`. -/
theorem integral_r_exp_mul {z R : ℝ} (hz : z ≠ 0) :
    ∫ r in (0 : ℝ)..R, r * Real.exp (z * r) =
    (R / z - 1 / z ^ 2) * Real.exp (z * R) + 1 / z ^ 2 := by
  have hint : IntervalIntegrable (fun r => r * Real.exp (z * r)) volume 0 R := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => hasDerivAt_r_exp_mul_antideriv hz r) hint]
  simp only [mul_zero, Real.exp_zero, mul_one, zero_div, zero_sub]
  field_simp [hz]
  ring

/-! ### Key single-term formula -/

/-- **∫_0^R r · exp(z·(r-R)) dr = R/z - 1/z^2 + exp(-zR)/z^2** for `z ≠ 0`.

This is the key building block for the inner-core free energy integral.

**Proof:** Factor out `exp(-zR)`:
  `exp(z·(r-R)) = exp(-zR)·exp(zr)`, then `integral_r_exp_mul` and algebra. -/
theorem integral_r_exp_shifted {z R : ℝ} (hz : z ≠ 0) :
    ∫ r in (0 : ℝ)..R, r * Real.exp (z * (r - R)) =
    R / z - 1 / z ^ 2 + Real.exp (-z * R) / z ^ 2 := by
  have hfactor : ∀ r : ℝ, Real.exp (z * (r - R)) = Real.exp (-z * R) * Real.exp (z * r) := by
    intro r; rw [← Real.exp_add]; congr 1; ring
  -- Rewrite integrand, then pull out the constant exp(-zR)
  have hrw : ∀ r : ℝ, r * Real.exp (z * (r - R)) = Real.exp (-z * R) * (r * Real.exp (z * r)) := by
    intro r; rw [hfactor]; ring
  simp_rw [hrw]
  rw [intervalIntegral.integral_const_mul, integral_r_exp_mul hz]
  -- Goal: exp(-zR) * ((R/z - 1/z^2)*exp(zR) + 1/z^2) = R/z - 1/z^2 + exp(-zR)/z^2
  -- Key: exp(-zR) * exp(zR) = 1
  have hexp1 : Real.exp (-(z * R)) * Real.exp (z * R) = 1 := by
    rw [← Real.exp_add, show -(z * R) + z * R = 0 from by ring, Real.exp_zero]
  have hmul : z * R * Real.exp (-(z * R)) * Real.exp (z * R) = z * R := by
    calc z * R * Real.exp (-(z * R)) * Real.exp (z * R)
        = z * R * (Real.exp (-(z * R)) * Real.exp (z * R)) := by ring
      _ = z * R * 1 := by rw [hexp1]
      _ = z * R := by ring
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero _ hz
  have hzR : Real.exp (-z * R) = Real.exp (-(z * R)) := by ring_nf
  field_simp [hz]
  linarith

/-! ### Main theorem: single-term inner-core integral -/

/-- **Task F.2 — Inner-core free energy integral (single Yukawa term):**

For a single exponential `A · exp(z·(r-R))` on `[0, R]`:
    `∫_0^R A · r · exp(z·(r-R)) dr = A · (R/z - 1/z^2 + exp(-zR)/z^2)` -/
theorem inner_core_single_term_integral {A z R : ℝ} (hz : z ≠ 0) :
    ∫ r in (0 : ℝ)..R, A * (r * Real.exp (z * (r - R))) =
    A * (R / z - 1 / z ^ 2 + Real.exp (-z * R) / z ^ 2) := by
  rw [intervalIntegral.integral_const_mul, integral_r_exp_shifted hz]

/-! ### Full E_ij sum integral -/

/-- **Task F.2 — Inner-core free energy integral (full E_ij):**

For `E_ij(r) = Σ_{t=1}^N A_t · exp(z_t · (r-R))`:
    `∫_0^R E_ij(r) · r dr = Σ_t A_t · (R/z_t - 1/z_t^2 + exp(-z_t·R)/z_t^2)` -/
theorem inner_core_eij_integral {n : ℕ} (A z : Fin n → ℝ) (R : ℝ)
    (hz : ∀ t, z t ≠ 0) :
    ∫ r in (0 : ℝ)..R,
      (∑ t : Fin n, A t * Real.exp (z t * (r - R))) * r =
    ∑ t : Fin n, A t * (R / z t - 1 / z t ^ 2 + Real.exp (-z t * R) / z t ^ 2) := by
  -- Strategy: swap sum and integral, then apply inner_core_single_term_integral to each term.
  -- Step 1: (Σ A_t exp(z_t(r-R))) * r = Σ (A_t * (r * exp(z_t(r-R))))
  -- Step 2: ∫ Σ ... = Σ ∫ ... (interchange by integral_finsetSum)
  -- Step 3: Each term by inner_core_single_term_integral
  have hrw : ∀ r : ℝ,
      (∑ t : Fin n, A t * Real.exp (z t * (r - R))) * r =
      ∑ t : Fin n, A t * (r * Real.exp (z t * (r - R))) := by
    intro r; simp_rw [Finset.sum_mul]; congr 1; ext t; ring
  simp_rw [hrw]
  rw [intervalIntegral.integral_finsetSum (fun t _ => by
    apply Continuous.intervalIntegrable
    apply Continuous.mul continuous_const
    apply Continuous.mul continuous_id
    exact Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const)))]
  congr 1; ext t
  exact inner_core_single_term_integral (hz t)

/-! ### Task F.2a — Inner-core free energy via eij (FMSA_GA_matrix_mix) -/

/-- **Task F.2a — Inner-core free energy integral using `eij` (FMSA_GA_matrix_mix, no sorry):**

Connects the `EijStructure.eij` definition to the FMSA_GA_matrix_mix inner-core free energy:
    `∫_0^R eij(A, z, R, r) · r dr = Σ_k A_k · (R/z_k - 1/z_k^2 + exp(-z_k·R)/z_k^2)`

**Key step:** `eij A z R r = Σ_k A_k · exp(-z_k·(R-r)) = Σ_k A_k · exp(z_k·(r-R))`,
which matches the `inner_core_eij_integral` integrand exactly after `ring`. -/
theorem eij_inner_integral {n : ℕ} (A z : Fin n → ℝ) (R : ℝ)
    (hz : ∀ t, z t ≠ 0) :
    ∫ r in (0 : ℝ)..R, FMSA.EijStructure.eij A z R r * r =
    ∑ t : Fin n, A t * (R / z t - 1 / z t ^ 2 + Real.exp (-z t * R) / z t ^ 2) := by
  -- Rewrite eij to match inner_core_eij_integral: -(z k)*(R-r) = z k*(r-R)
  have hrw : ∀ r : ℝ,
      FMSA.EijStructure.eij A z R r * r =
      (∑ t : Fin n, A t * Real.exp (z t * (r - R))) * r := fun r => by
    unfold FMSA.EijStructure.eij
    congr 1
    apply Finset.sum_congr rfl; intro k _
    congr 1; congr 1; ring
  simp_rw [hrw]
  exact inner_core_eij_integral A z R hz

end FMSA.FreeEnergy
