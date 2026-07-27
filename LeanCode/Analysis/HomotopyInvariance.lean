/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Homotopy invariance of contour integrals — MA.8, RETIRED to a theorem (2026-07-24)

Group MA (`MATH_AXIOMS.md`), task `MA.8`.  This was the classical **homotopy form of Cauchy's
theorem** (Ahlfors Ch. 4 Thm 16 / Conway IV.6.7): freely-homotopic-through-loops `C¹` loops in an
open `U` give equal contour integrals of a function holomorphic on `U`.  It was pre-placed as a bare
assumption because Mathlib then had **no** homotopy/winding machinery for contour integrals.

## Retirement (2026-07-24)

Mathlib `v4.31.0` has since gained the **Poincaré lemma for `1`-forms**
(`Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean`), including
`ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt` — the curve
integrals of a **closed** `1`-form along two paths joined by a `C²` homotopy agree.  The former
"Mathlib lacks it" gap has therefore **closed** for the `C²` case (only the fully-continuous form is
still WIP upstream, Mathlib issue #24019), so MA.8 is no longer a gap axiom.

The mathematical content now lives, **axiom-free**, in `Analysis/ContourHomotopy.lean`:
`FMSA.Analysis.contourIntegral_holoForm_eq_of_homotopic_loops` (homotopy-invariance through loops)
and `contourIntegral_holoForm_eq_zero_of_nullhomotopic` (Cauchy's theorem, null-homotopic form),
both `#print axioms = {std three}`.  Those are stated in Mathlib's bundled `Path`/`Homotopy`
vocabulary with a `C²` homotopy — which is a **free strengthening** here (MA.8 had **no consumer**,
and its only intended future use, the keyhole-homotopy derivations of the contour-deformation axioms
`MA.1`, constructs smooth homotopies) and is exactly the form Mathlib's Poincaré lemma consumes.

The raw-function axiom (`contourIntegral_eq_of_homotopic_loops`) and its raw null-homotopic corollary
that formerly lived here have been **removed**: both were consumer-less, and their content is the
above theorems.  Only the axiom-free change-of-variables bridge `circleIntegral_eq_unitLoop_integral`
(unit-interval loop form of `∮ z in C(c,R), f z`) is kept, unchanged.
-/

open Set Metric Complex Filter Topology intervalIntegral

noncomputable section

/-- **Bridge to `circleIntegral`**: `∮ z in C(c,R), f z` equals the normalized unit-interval loop
integral for `γ(t) = circleMap c R (2πt)`.  Genuine theorem, no axiom — pure change of variables
(`intervalIntegral.smul_integral_comp_mul_left`).  Kept as a convenience for turning `circleIntegral`
statements into the unit-interval loop form that the homotopy theorems in `ContourHomotopy.lean`
speak about. -/
theorem circleIntegral_eq_unitLoop_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : ℂ → E) (c : ℂ) (R : ℝ) :
    (∮ z in C(c, R), f z) =
      ∫ t in (0:ℝ)..1, ((2 * Real.pi : ℝ) • deriv (circleMap c R) (2 * Real.pi * t)) •
        f (circleMap c R (2 * Real.pi * t)) := by
  rw [circleIntegral]
  have key := intervalIntegral.smul_integral_comp_mul_left
    (fun θ => deriv (circleMap c R) θ • f (circleMap c R θ)) (2 * Real.pi) (a := 0) (b := 1)
  simp only [mul_zero, mul_one] at key
  rw [← key, ← intervalIntegral.integral_smul]
  congr 1
  funext t
  rw [smul_assoc]

end
