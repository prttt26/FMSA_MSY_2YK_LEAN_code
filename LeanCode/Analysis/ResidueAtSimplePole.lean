/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Residue at a simple pole — the elementary limit characterization

**Stability note:** kept in its own file, importing only `Mathlib`, because it is a reuse target
for other, independent work streams (the mixture groups MML/MZERO — `YukawaDCF/MixtureHSPoles.lean`,
`YukawaDCF/YukawaPoleResidue.lean`) that should not need to rebuild alongside the actively-changing
`HardSphere/BaxterResidue.lean` (Group OZFIX), which now only *imports* this file
rather than defining the lemma inline.

No Cauchy integral formula needed: the classical alternative characterization of a simple-pole
residue, `Res_{z0}[f] = lim_{z→z0} (z-z0)·f(z)`, is provable directly from `HasDerivAt`'s own
definition (`hasDerivAt_iff_tendsto_slope`) plus elementary limit algebra (`Filter.Tendsto.inv₀`,
`Filter.Tendsto.mul`) — no circle integrals, no Cauchy's formula, no new Mathlib subsystem needed.
`residue_of_simple_pole` is fully general (`N`, `D : ℂ → ℂ`, `D` merely differentiable with a
simple zero at `z0`), not tied to any specific application.
-/

open Filter Topology

namespace FMSA.Analysis

/-- **Residue at a simple pole, via the elementary limit characterization** — no Cauchy integral
formula needed. For `f = N/D` with `D` having a simple zero at `z0` (`HasDerivAt D D' z0`,
`D z0 = 0`, `D' ≠ 0`) and `N` continuous at `z0`, `(z-z0)·f(z) → N(z0)/D'(z0)` as `z → z0`
(`z ≠ z0`) — the standard alternative definition of `Res_{z0}[f]` for a simple pole. -/
theorem residue_of_simple_pole (N D : ℂ → ℂ) (Dprime : ℂ) (z0 : ℂ) (hD : HasDerivAt D Dprime z0)
    (hDz0 : D z0 = 0) (hDprime : Dprime ≠ 0) (hNcont : ContinuousAt N z0) :
    Tendsto (fun z => (z - z0) * (N z / D z)) (𝓝[≠] z0) (𝓝 (N z0 / Dprime)) := by
  have hslope : Tendsto (slope D z0) (𝓝[≠] z0) (𝓝 Dprime) := hasDerivAt_iff_tendsto_slope.mp hD
  have hinv : Tendsto (fun z => (slope D z0 z)⁻¹) (𝓝[≠] z0) (𝓝 Dprime⁻¹) := hslope.inv₀ hDprime
  have heq : ∀ z ∈ ({z0}ᶜ : Set ℂ), (slope D z0 z)⁻¹ = (z - z0) / D z := by
    intro z _
    rw [slope_def_field, hDz0, sub_zero, inv_div]
  have hinv' : Tendsto (fun z => (z - z0) / D z) (𝓝[≠] z0) (𝓝 Dprime⁻¹) := by
    apply Tendsto.congr' _ hinv
    filter_upwards [self_mem_nhdsWithin] with z hz using heq z hz
  have hN : Tendsto N (𝓝[≠] z0) (𝓝 (N z0)) := hNcont.continuousWithinAt.tendsto
  have hprod := hN.mul hinv'
  have heq2 : ∀ z : ℂ, N z * ((z - z0) / D z) = (z - z0) * (N z / D z) := fun z => by ring
  have hfinal := hprod.congr heq2
  rwa [show N z0 * Dprime⁻¹ = N z0 / Dprime from (div_eq_mul_inv (N z0) Dprime).symm] at hfinal

end FMSA.Analysis
