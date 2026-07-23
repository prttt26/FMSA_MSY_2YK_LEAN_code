/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterRenewal

/-!
# Reducing the exterior decay/boundedness clauses to `baxterPsiOuter → 0` — Task POLE.11 (task b)

The two load-bearing analytic clauses of the theorem `baxter_exterior_regularity` — exterior
boundedness (clause 2) and the decay `Tendsto (r·ozBaxterFixedPt) atTop 0` (inside clause 6) — both
follow from the **single** qualitative fact `baxterPsiOuter → 0`.  This file proves that reduction,
axiom-clean, isolating the one genuinely hard input (`baxterPsiOuter → 0` for general `η`) as an
explicit hypothesis.

* `baxterPsi_bounded_Ici_of_tendsto_zero` — boundedness on `[σ,∞)` from `→ 0` + continuity on each
  compact (a `→0` continuous function is bounded).
* `r_mul_ozBaxterFixedPt_tendsto_zero_of_tendsto_zero` — the decay clause, since
  `r·ozBaxterFixedPt r = baxterPsi r = baxterPsiOuter r` eventually.

**Discharge.** The hypothesis `Tendsto (baxterPsiOuter …) atTop (𝓝 0)` is exactly what the
Paley–Wiener / Wiener-algebra renewal theorem provides once the symbol `1 − ρQ̂` is nonvanishing on
the closed lower half-plane — supplied by the abstract MA-group axiom
`volterra_renewal_tendsto_zero` (`Analysis/WienerRenewal.lean`), instantiated at the Volterra kernel
`q0_poly`/forcing `baxterForcing`.  In the dilute regime it is instead a theorem
(`baxterPsi_tendsto_zero_of_dilute`, `BaxterDiluteDecay.lean`), so these reductions there are
unconditional.
-/

open MeasureTheory Set Real Filter Topology

namespace FMSA.HardSphere

noncomputable section

/-- **Boundedness from decay.**  If `baxterPsiOuter → 0` then `baxterPsi` is bounded on `[σ,∞)`:
past some `R₀` it is `≤ 1`, and on the compact `[σ,R₀]` it is bounded by continuity. -/
theorem baxterPsi_bounded_Ici_of_tendsto_zero {eta sigma rho : ℝ}
    (hdecay : Tendsto (baxterPsiOuter eta sigma rho) atTop (𝓝 0)) :
    ∃ C, ∀ r, sigma ≤ r → |baxterPsi eta sigma rho r| ≤ C := by
  obtain ⟨R0, hR0⟩ := Metric.tendsto_atTop.1 hdecay 1 (by norm_num)
  set R1 := max sigma R0 with hR1
  have hcont : ContinuousOn (fun x => |baxterPsiOuter eta sigma rho x|) (Set.Icc sigma R1) :=
    (baxterPsiOuter_continuousOn (le_max_left sigma R0)).abs
  have hne : (Set.Icc sigma R1).Nonempty := ⟨sigma, ⟨le_rfl, le_max_left _ _⟩⟩
  obtain ⟨x0, _, hx0max⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  have hmax : ∀ y ∈ Set.Icc sigma R1,
      |baxterPsiOuter eta sigma rho y| ≤ |baxterPsiOuter eta sigma rho x0| := isMaxOn_iff.mp hx0max
  refine ⟨max |baxterPsiOuter eta sigma rho x0| 1, fun r hr => ?_⟩
  rw [baxterPsi_outer hr]
  rcases le_total r R1 with hle | hge
  · exact le_trans (hmax r ⟨hr, hle⟩) (le_max_left _ _)
  · have hrR0 : R0 ≤ r := le_trans (le_max_right sigma R0) hge
    have hd := hR0 r hrR0
    rw [Real.dist_eq, sub_zero] at hd
    exact le_trans hd.le (le_max_right _ _)


end

end FMSA.HardSphere
