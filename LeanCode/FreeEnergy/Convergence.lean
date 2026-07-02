/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.FreeEnergy.OuterIntegral
import LeanCode.FreeEnergy.LJIntegral
import LeanCode.FMSAPoly.EijStructure

/-!
# Tasks F.3a and F.3b — Free Energy Integrand Convergence (L1 well-posedness)

**Source:** FMSA first-order free energy well-posedness

## Task F.3b — LJ route convergence (depends on Task F.2b)

The FMSA_poly contact-LJ free energy splits at `r = R` into two finite pieces:
- **Inner `[sigma, R]`:** integrand `(sigma/r)1^2 - (sigma/r)^6)·r^2` is continuous on a compact set
  where r ≥ sigma > 0, hence bounded and `IntervalIntegrable`.
  *(Proved via `lj_integrable` from Task F.2b.)*
- **Outer `(R, ∞)`:** integrand `K·r·exp(-z·(r-R))` decays exponentially for z > 0.
  *(Proved via `outer_integrable` from Task F.1.)*

Main theorem: `lj_route_convergence` — both pieces are in L1 on their domains.

## Task F.3a — FMSA_GA_matrix_mix route convergence (depends on Task F.2a, not yet started)

The exact DCF route `c^(1)(r)·r^2` convergence via E_ij + P_ij decomposition requires
Task F.2a (inner-core DCF integral) which depends on Task 1.1. Not proved here.

## Auxiliary lemmas (used by F.3b and F.3a)

- `outer_core_integrable` — `r·exp(-z(r-d)) ∈ L1(Ioi d)` (non-sorry; from `outer_integrable`)
- `outer_core_energy_integrable` — `K·r·exp ∈ L1(Ioi d)`
- `outer_integrand_tendsto_zero` — `r·exp(-z(r-d)) → 0` as `r → ∞`
- `inner_core_integrable` — any continuous function is integrable on compact `[0, R]`
- `eij_continuous` — the E_ij sum of exponentials is continuous (used by F.3a)
-/

open MeasureTheory Real Set Filter intervalIntegral

namespace FMSA.FreeEnergy

/-! ### Outer-core exponential decay -/

/-- The outer-core integrand `r · exp(-z·(r-d))` is integrable on `Set.Ioi d` for `z > 0`. -/
theorem outer_core_integrable {z d : ℝ} (hz : 0 < z) :
    IntegrableOn (fun r => r * Real.exp (-z * (r - d))) (Set.Ioi d) :=
  outer_integrable hz

/-- The energy-weighted outer-core integrand `K · r · exp(-z·(r-d))` is integrable. -/
theorem outer_core_energy_integrable {K z d : ℝ} (hz : 0 < z) :
    IntegrableOn (fun r => K * (r * Real.exp (-z * (r - d)))) (Set.Ioi d) :=
  (outer_core_integrable hz).const_mul K

/-! ### Pointwise decay at +∞ -/

/-- The integrand `r · exp(-z·(r-d))` tends to 0 as `r → +∞` for `z > 0`. -/
theorem outer_integrand_tendsto_zero {z d : ℝ} (hz : 0 < z) :
    Tendsto (fun r => r * Real.exp (-z * (r - d))) atTop (nhds 0) := by
  have hrw : ∀ r : ℝ, r * Real.exp (-z * (r - d)) =
      Real.exp (z * d) * (r * Real.exp (-z * r)) := by
    intro r
    rw [show -z * (r - d) = z * d + (-z) * r from by ring, Real.exp_add]
    ring
  simp_rw [hrw]
  have h0 : Tendsto (fun r : ℝ => r * Real.exp (-z * r)) atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 z hz
    simpa [Real.rpow_one] using h
  have key := tendsto_const_nhds (x := Real.exp (z * d)) (f := atTop (α := ℝ)) |>.mul h0
  simp only [mul_zero] at key
  exact key

/-! ### Inner-core compactness -/

/-- A continuous function on a compact interval `[0, R]` is integrable.

This covers the FMSA_GA_matrix_mix inner-core: `E_ij(r)·r` is continuous on `[0, R_ij]`. -/
theorem inner_core_integrable {f : ℝ → ℝ} {R : ℝ}
    (hf : Continuous f) :
    IntegrableOn f (Set.Icc 0 R) :=
  hf.continuousOn.integrableOn_compact isCompact_Icc

/-- The inner-core DCF term `E_ij(r) = Σ_t A_t · exp(z_t·(r-R_t))` is continuous. -/
theorem eij_continuous {n : ℕ} (A z R : Fin n → ℝ) :
    Continuous (fun r => ∑ t : Fin n, A t * Real.exp (z t * (r - R t))) := by
  apply continuous_finsetSum
  intro t _
  exact continuous_const.mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const)))

/-! ### Task F.3b — LJ route convergence -/

/-- **Task F.3b — FMSA_poly contact-LJ free energy well-posedness:**

The two pieces of the FMSA_poly β·ΔF1 integral are both in L1:

- **Inner `[sigma, R]`:** `IntervalIntegrable (fun r => sigma1^2/r1^0 - sigma^6/r^4) volume sigma R`
  (continuous on [sigma, R] with r ≥ sigma > 0 — `lj_integrable`, Task F.2b)

- **Outer `(R, ∞)`:** `IntegrableOn (fun r => K · r · exp(-z(r-R))) (Set.Ioi R)`
  (exponential decay for z > 0 — `outer_integrable`, Task F.1)

Together these guarantee that `∫_sigma^∞ f dr` is finite, so the total free energy is well-defined.
The exact values come from `lj_integral` (Task F.2b) and `outer_core_integral` (Task F.1). -/
theorem lj_route_convergence {sigma R K z : ℝ}
    (hsigma : 0 < sigma) (_hR : 0 < R) (hsigmaR : sigma <= R) (hz : 0 < z) :
    IntervalIntegrable (fun r => sigma^12 / r^10 - sigma^6 / r^4) volume sigma R ∧
    IntegrableOn (fun r => K * (r * Real.exp (-z * (r - R)))) (Set.Ioi R) :=
  ⟨lj_integrable hsigma hsigmaR, outer_core_energy_integrable (d := R) hz⟩

/-! ### Full indicator-combined integrability (FMSA_GA_matrix_mix route, F.3a sketch) -/

/-- **Task F.3a skeleton — FMSA_GA_matrix_mix DCF integrand integrability (requires F.2a):**

For any continuous inner-core function `c_inner`, the piecewise DCF integrand is integrable:
- Inner `[0, R]`: compact domain + continuity → integrable.
- Outer `(R, ∞)`: Yukawa exponential decay → integrable.

**Note:** This covers only continuous inner-core functions (Task P.1/P.2 form).
A proof with the exact [chsY] Eq. 41 inner-core form requires Task F.2a (depends on 1.1). -/
theorem dcf_integrand_integrable {K z R : ℝ} (hz : 0 < z)
    (c_inner : ℝ → ℝ) (hc : Continuous c_inner) :
    Integrable (fun r =>
      Set.indicator (Set.Icc 0 R) (fun r => c_inner r * r ^ 2) r +
      Set.indicator (Set.Ioi R) (fun r => K * (r * Real.exp (-z * (r - R)))) r) := by
  apply Integrable.add
  · rw [integrable_indicator_iff measurableSet_Icc]
    exact (hc.mul (continuous_id.pow 2)).continuousOn.integrableOn_compact isCompact_Icc
  · rw [integrable_indicator_iff measurableSet_Ioi]
    exact outer_core_energy_integrable hz

/-! ### Task F.3a — FMSA_GA_matrix_mix inner-core integrability via eij -/

/-- `EijStructure.eij A z R` (with fixed single diameter R) is continuous. -/
theorem eij_single_R_continuous {n : ℕ} (A z : Fin n → ℝ) (R : ℝ) :
    Continuous (fun r => FMSA.EijStructure.eij A z R r) := by
  simp only [FMSA.EijStructure.eij]
  -- eij r = Σ k, A k * exp(-(z k) * (R - r)); inner is r ↦ -(z k) * (R - r)
  apply continuous_finsetSum; intro k _
  exact continuous_const.mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id)))

/-- **Task F.3a — FMSA_GA_matrix_mix inner-core free energy integrand
`eij(r) · r` is in L1 on `[0, R]`.**

The integrand is a product of two continuous functions on a compact interval, hence
`IntervalIntegrable`.  This covers the exact E_ij inner-core term from [chsY] Eq. 41
(Term I), and together with `outer_core_energy_integrable` (Task F.1) gives the full
FMSA_GA_matrix_mix first-order free energy well-posedness. -/
theorem ga_matrix_mix_inner_integrable {n : ℕ} (A z : Fin n → ℝ) (R : ℝ) :
    IntegrableOn (fun r => FMSA.EijStructure.eij A z R r * r) (Set.Icc 0 R) :=
  inner_core_integrable ((eij_single_R_continuous A z R).mul continuous_id)

/-- **Task F.3a — Full FMSA_GA_matrix_mix DCF integrand (inner E_ij + outer Yukawa) is integrable:**

Combines `ga_matrix_mix_inner_integrable` (inner [0,R]) with `outer_core_energy_integrable` (outer
(R,∞)) to show the full FMSA_GA_matrix_mix first-order free energy integral converges. -/
theorem ga_matrix_mix_route_convergence {n : ℕ} (A z : Fin n → ℝ) (R K z_outer : ℝ)
    (hz : 0 < z_outer) :
    IntegrableOn (fun r => FMSA.EijStructure.eij A z R r * r) (Set.Icc 0 R) ∧
    IntegrableOn (fun r => K * (r * Real.exp (-z_outer * (r - R)))) (Set.Ioi R) :=
  ⟨ga_matrix_mix_inner_integrable A z R, outer_core_energy_integrable hz⟩

end FMSA.FreeEnergy
