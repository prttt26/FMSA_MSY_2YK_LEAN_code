/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Homotopy invariance of the lower-half-plane zero count (argument principle / Hurwitz)

This file states one pure-analysis axiom: **the number of zeros of a holomorphic function in the
open lower half-plane is invariant under a continuous deformation that never lets a zero touch the
boundary.**  It is the standard consequence of the argument principle — the zero count is
`(2πi)⁻¹ ∮ H'/H` over the boundary of a large half-disk, a continuous integer-valued function of the
homotopy parameter, hence locally constant — equivalently Hurwitz's theorem.

## Why it is an axiom

Mathlib (as of this development) has **neither Rouché's theorem nor the parametric/​counting form
of the argument principle** with a *contour construction* (it has `circleIntegral`-based pieces, but
not the homotopy-invariance-of-zero-count package on a bounded region).  This is a genuine *library
gap*, not an effort gap: reconstructing it needs winding-number machinery on a half-disk contour
that is not present.  Per the project's triage policy such gaps are axiomatized abstractly (never as
a domain-specific statement) and cited.

## Statement shape and how each hypothesis rules out a way the count could change

`H t` is a family of entire functions, jointly continuous in `(t, z)` on `[a,b] × ℂ`.  The count of
zeros of `H t` in `{Im z < 0}` cannot change as `t` runs from `a` to `b` because:

* `hbound` — every zero in the **closed** lower half-plane stays inside `‖z‖ < R`: no zero escapes
  to or arrives from infinity, so the count is over the fixed bounded region `{Im z<0} ∩ ball 0 R`;
* `hreal` — `H t` never vanishes on the real axis: a zero cannot cross from the upper into the lower
  half-plane without passing through `Im z = 0`, and none sits on the boundary;
* `hbase` — the count is `0` at `t = a`.

Therefore it is `0` at `t = b`: `H b` is zero-free in the open lower half-plane.  (`H t` is not
identically zero — `hreal` forbids it — so its zeros have positive order and "count `0`" is
genuinely "no zeros".)

This is deliberately specialized to the **lower** half-plane and the **real** boundary axis,
matching the Baxter/Wiener–Hopf use (`MA.14`, `baxter_no_open_lhp_pole_core`), but is otherwise
fully general: `H` is an arbitrary continuous family of entire functions.
-/

open Complex Set

namespace FMSA.Analysis

/-- **Homotopy invariance of open-lower-half-plane zero-freeness** (argument principle / Hurwitz).
See the file docstring for the meaning of each hypothesis. A pure-analysis axiom standing in for the
parametric argument principle, which Mathlib lacks. -/
axiom zeroFree_lowerHalfPlane_of_homotopy
    {H : ℝ → ℂ → ℂ} {a b R : ℝ}
    (hab : a ≤ b) (hR : 0 < R)
    (hcont : ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2) (Set.Icc a b ×ˢ (Set.univ : Set ℂ)))
    (hholo : ∀ t ∈ Set.Icc a b, Differentiable ℂ (H t))
    (hbound : ∀ t ∈ Set.Icc a b, ∀ z : ℂ, z.im ≤ 0 → H t z = 0 → ‖z‖ < R)
    (hreal : ∀ t ∈ Set.Icc a b, ∀ z : ℂ, z.im = 0 → H t z ≠ 0)
    (hbase : ∀ z : ℂ, z.im < 0 → H a z ≠ 0) :
    ∀ z : ℂ, z.im < 0 → H b z ≠ 0

end FMSA.Analysis
