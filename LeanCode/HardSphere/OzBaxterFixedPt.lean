/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterRenewal

/-!
# `ozBaxterFixedPt` — the Baxter candidate for the OZ exterior fixed point

The definition `ozBaxterFixedPt := if r < σ then -1 else baxterPsi r / r` and the identity
`ozBaxterFixedPt = baxterPsi/·` on `(0,∞)`.  Extracted here (upstream of `OzCoreClosure.lean`) so
that the POLE.11 decay chain (`BaxterDiluteDecay`, `BaxterExteriorDecayReduction`, …), which needs
only this def, does **not** import `OzCoreClosure` — which in turn lets `OzCoreClosure` import the
general-`η` boundedness/decay theorems (`baxterPsi_bounded_Ici`, …) without an import cycle, the
prerequisite for retiring the `baxter_exterior_regularity` axiom (now the theorem
`baxter_exterior_regularity`).
-/

open Set

namespace FMSA.HardSphere

noncomputable section

/-- The Baxter candidate for the OZ fixed point: `-1` inside the core, `baxterPsi r / r` outside.
The core value is forced on *every* `OzFixedPt` by `oz_operator`'s `if r < σ then -1` branch; on the
exterior it is the radial `h` of the constructed Baxter solution `baxterPsi`. -/
def ozBaxterFixedPt (eta sigma rho : ℝ) (r : ℝ) : ℝ :=
  if r < sigma then -1 else baxterPsi eta sigma rho r / r

/-- On `(0,∞)`, `ozBaxterFixedPt = baxterPsi/·`: the core value `-1` is also `baxterPsi(r)/r` there,
since `baxterPsi = -r` on `(-σ,σ)` (`baxterPsi_core`). -/
theorem ozBaxterFixedPt_eq_div {eta sigma rho : ℝ} (hsigma : 0 < sigma) {s : ℝ} (hs : 0 < s) :
    ozBaxterFixedPt eta sigma rho s = baxterPsi eta sigma rho s / s := by
  unfold ozBaxterFixedPt
  rcases lt_or_ge s sigma with h | h
  · rw [if_pos h, baxterPsi_core ⟨by linarith, h⟩]
    field_simp
  · rw [if_neg (not_lt.mpr h)]

end

end FMSA.HardSphere
