/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterOzStar
import LeanCode.HardSphere.OzBaxterFixedPt
import LeanCode.HardSphere.BaxterExteriorRegularityGeneral

/-!
# Exterior "derivative bundle" of `baxter_exterior_regularity` — obstruction at the contact point

The 6th top-level conjunct of the theorem `baxter_exterior_regularity` (`OzCoreClosure.lean`) is a
derivative bundle `∃ g', (6a) ∧ … ∧ (6j)` about `ozBaxterFixedPt`.  Its first clause is

  `(6a)  ∀ r ∈ Ici σ, HasDerivAt (ozBaxterFixedPt eta sigma rho) (g' r) r`.

This file records a **rigorous obstruction**: clause `(6a)` is *false* at the endpoint `r = σ`,
because `ozBaxterFixedPt` has a genuine jump there.  Concretely

  `ozBaxterFixedPt σ = baxterPsiOuter σ / σ = baxterForcing σ / σ > 0`,

whereas `ozBaxterFixedPt` is `-1` on all of `(-∞, σ)` (its definitional core value).  A function
with a jump discontinuity is not differentiable there (`HasDerivAt ⇒ ContinuousAt`), so no `g' σ`
can satisfy `(6a)` at `σ`.  Hence the bundle cannot be assembled as a theorem *as stated*, and it
cannot be truthfully axiomatized either.

The closed form (verified numerically) is `baxterForcing σ = σ·η·(5-2η)/(2(1-η)²)`, always
positive for the physical range `η ∈ (0,1)`; here we only need positivity, which follows from the
strict positivity of the integrand `q0_poly(σ-s)·(-s) = s²·(μ - ν·s/2)` on `(0,σ)`
(`μ := ρ·q_prime_py`, `ν := ρ·q_doubleprime_py`, with `μ - ν·σ/2 = ρπσ/(1-η) > 0`).

## Results
* `baxterForcing_sigma_pos` — `0 < baxterForcing σ`.
* `ozBaxterFixedPt_sigma_pos` — `0 < ozBaxterFixedPt σ` (contact value, above the core `-1`).
* `ozBaxterFixedPt_apply_lt` — `ozBaxterFixedPt r = -1` for `r < σ`.
* `ozBaxterFixedPt_not_continuousAt_sigma` — `¬ ContinuousAt ozBaxterFixedPt σ`.
* `ozBaxterFixedPt_deriv_bundle_endpoint_false` — clause `(6a)` is unsatisfiable
  (`¬ ∃ g', ∀ r ∈ Ici σ, HasDerivAt ozBaxterFixedPt (g' r) r`).
-/

open MeasureTheory Set Real Filter Topology

namespace FMSA.HardSphere

noncomputable section

/-- `ozBaxterFixedPt` is measurable (`-1` below `σ`, `baxterPsi/·` above), reusing
`baxterPsi_measurable`.  A reusable primitive for the exterior integrability clauses. -/
theorem ozBaxterFixedPt_measurable {eta sigma rho : ℝ} :
    Measurable (ozBaxterFixedPt eta sigma rho) := by
  unfold ozBaxterFixedPt
  exact Measurable.ite measurableSet_Iio measurable_const
    (baxterPsi_measurable.div measurable_id)

/-- The forcing at contact is strictly positive: `0 < baxterForcing σ`.  The integrand
`q0_poly(σ-s)·(-s)` equals `s²·(μ - ν·s/2)` with `μ := ρ·q_prime_py`, `ν := ρ·q_doubleprime_py`;
`μ - ν·s/2 > μ - ν·σ/2 = ρπσ/(1-η) > 0` for `s ∈ (0,σ)`. -/
theorem baxterForcing_sigma_pos {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta_lt : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) : 0 < baxterForcing eta sigma rho sigma := by
  have h1e : (0 : ℝ) < 1 - eta := by linarith
  have hν : 0 < rho * q_doubleprime_py eta := baxterNu_pos heta0 heta_lt hrho
  -- `μ - ν·σ/2 = ρπσ/(1-η) > 0`
  have hμνσ : 0 < rho * q_prime_py eta sigma - rho * q_doubleprime_py eta * sigma / 2 := by
    have heq : rho * q_prime_py eta sigma - rho * q_doubleprime_py eta * sigma / 2
        = rho * Real.pi * sigma / (1 - eta) := by
      unfold q_prime_py q_doubleprime_py
      field_simp
      ring
    rw [heq]; positivity
  unfold baxterForcing
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ ?_ hsigma
  · exact (((q0_poly_continuous eta sigma rho).comp
      (continuous_const.sub continuous_id)).mul continuous_id.neg).intervalIntegrable _ _
  · intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    rw [q0_poly_inner (by linarith : sigma - s ≤ sigma)]
    have hμνs : 0 < rho * q_prime_py eta sigma - rho * q_doubleprime_py eta * s / 2 := by
      have : rho * q_doubleprime_py eta * s < rho * q_doubleprime_py eta * sigma :=
        mul_lt_mul_of_pos_left hs1 hν
      linarith
    rw [show (rho * q_prime_py eta sigma * (sigma - s - sigma)
          + rho * q_doubleprime_py eta * (sigma - s - sigma) ^ 2 / 2) * (-s)
        = s ^ 2 * (rho * q_prime_py eta sigma - rho * q_doubleprime_py eta * s / 2) from by ring]
    exact mul_pos (pow_pos hs0 2) hμνs

/-- `ozBaxterFixedPt r = -1` for `r < σ` (definitional core value). -/
theorem ozBaxterFixedPt_apply_lt {eta sigma rho r : ℝ} (hr : r < sigma) :
    ozBaxterFixedPt eta sigma rho r = -1 := if_pos hr

/-- The contact value of `ozBaxterFixedPt` is strictly positive — in particular `≠ -1`, the core
value it takes just below `σ`. -/
theorem ozBaxterFixedPt_sigma_pos {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta_lt : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) : 0 < ozBaxterFixedPt eta sigma rho sigma := by
  rw [ozBaxterFixedPt_eq_div hsigma hsigma, baxterPsi_outer (le_refl sigma)]
  have hspec := baxterPsiOuter_spec (eta := eta) (sigma := sigma) (rho := rho)
    (r := sigma) (le_refl sigma)
  rw [intervalIntegral.integral_same, add_zero] at hspec
  rw [hspec]
  exact div_pos (baxterForcing_sigma_pos heta0 heta_lt hsigma hrho) hsigma

/-- `ozBaxterFixedPt` is **not** continuous at `σ`: its left limit is the core value `-1`, but its
value at `σ` is strictly positive. -/
theorem ozBaxterFixedPt_not_continuousAt_sigma {eta sigma rho : ℝ} (heta0 : 0 < eta)
    (heta_lt : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho) :
    ¬ ContinuousAt (ozBaxterFixedPt eta sigma rho) sigma := by
  intro hcont
  have hpos := ozBaxterFixedPt_sigma_pos heta0 heta_lt hsigma hrho
  have hL : Tendsto (ozBaxterFixedPt eta sigma rho) (𝓝[<] sigma) (𝓝 (-1)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (ozBaxterFixedPt_apply_lt hr).symm
  have hR : Tendsto (ozBaxterFixedPt eta sigma rho) (𝓝[<] sigma)
      (𝓝 (ozBaxterFixedPt eta sigma rho sigma)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hval := tendsto_nhds_unique hR hL
  rw [hval] at hpos
  linarith

/-- **Obstruction to clause `(6a)` of the exterior derivative bundle.**  There is *no* `g'` making
`ozBaxterFixedPt` differentiable at every `r ∈ Ici σ`, because `HasDerivAt` at `σ` would force
continuity there, which fails (`ozBaxterFixedPt` jumps from `-1` to `baxterForcing σ / σ > 0`). -/
theorem ozBaxterFixedPt_deriv_bundle_endpoint_false {eta sigma rho : ℝ} (heta0 : 0 < eta)
    (heta_lt : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho) :
    ¬ ∃ g' : ℝ → ℝ, ∀ r ∈ Ici sigma, HasDerivAt (ozBaxterFixedPt eta sigma rho) (g' r) r := by
  rintro ⟨g', hg⟩
  exact ozBaxterFixedPt_not_continuousAt_sigma heta0 heta_lt hsigma hrho
    (hg sigma (self_mem_Ici)).continuousAt

end

end FMSA.HardSphere
