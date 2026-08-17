/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Derivatives of `sin (k·x)` and `cos (k·x)`

Two elementary `HasDerivAt` facts used by the radial-Fourier / Wiener-Hopf integrands.  They were
previously duplicated as file-local `private` helpers in `HardSphere/BaxterWienerHopf`,
`HardSphere/RadialFourierCHS` and `YukawaOZMix/RadialFourierQFwd`; homed here (Layer 0) so a single
copy serves all three.
-/

namespace FMSA.Analysis

/-- Derivative of `x ↦ sin (k·x)` at `r`. -/
theorem hasDerivAt_sin_mul {k r : ℝ} :
    HasDerivAt (fun x => Real.sin (k * x)) (Real.cos (k * r) * k) r := by
  have h : HasDerivAt (fun x => k * x) k r := by simpa using (hasDerivAt_id r).const_mul k
  exact h.sin

/-- Derivative of `x ↦ cos (k·x)` at `r`. -/
theorem hasDerivAt_cos_mul {k r : ℝ} :
    HasDerivAt (fun x => Real.cos (k * x)) (-Real.sin (k * r) * k) r := by
  have h : HasDerivAt (fun x => k * x) k r := by simpa using (hasDerivAt_id r).const_mul k
  exact h.cos

end FMSA.Analysis
