/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Shared coupling calculus and first-order closure comparison

MSA/FMSA first order and the minimal PY/Mayer comparison used by the
foundation's existing FMSA scope gate. HNCB-specific results now live in
Other_Closures/OtherClosures/ClosureExpansions.lean. The original shared
public names, statements and proof bodies are retained.
-/

set_option linter.style.longLine false

open Filter Topology FourierTransform
open scoped Matrix

namespace FMSA.FirstOrderClosure

/-! ## PYE.1 — the first-order closures

The coupling parameter is `s` (the tail is `s·u`); `s = 0` is the pure hard-sphere system, where
`g₀ = g_HS`, `γ₀ = h_HS` and `c₀(r>R) = 0`.  Everything here is one product/chain rule at `s = 0`.
-/

/-- The Mayer factor of the `s`-scaled tail, `f(s) = e^{−β s u} − 1`.  (`u` is the outer pair
potential at the radius under consideration; `β` the inverse temperature.) -/
noncomputable def mayerF (beta u s : ℝ) : ℝ := Real.exp (-(beta * s * u)) - 1

/-- At zero coupling the Mayer factor vanishes — the PY outer DCF has no zeroth-order part,
`c₀(r>R) = 0`. -/
theorem mayerF_zero (beta u : ℝ) : mayerF beta u 0 = 0 := by
  simp [mayerF]

/-- The `s`-linear exponent `−β s u` and its derivative `−βu` (the one calculus input of the whole
closure expansion; kept as a named lemma because both closures need it). -/
theorem hasDerivAt_couplingExponent (beta u : ℝ) :
    HasDerivAt (fun s : ℝ => -(beta * s * u)) (-(beta * 1 * u)) 0 :=
  (((hasDerivAt_id (0 : ℝ)).const_mul beta).mul_const u).neg

/-- `d/ds e^{−β s u}|_{s=0} = −βu`: the Mayer factor is `−βu·s + O(s²)`. -/
theorem hasDerivAt_mayerF (beta u : ℝ) : HasDerivAt (mayerF beta u) (-(beta * u)) 0 := by
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (-(beta * s * u)) - 1)
      (Real.exp (-(beta * 0 * u)) * -(beta * 1 * u)) 0 :=
    (hasDerivAt_couplingExponent beta u).exp.sub_const 1
  have hval : Real.exp (-(beta * 0 * u)) * -(beta * 1 * u) = -(beta * u) := by simp
  rw [hval] at h2
  exact h2

/-- **PYE.1 — the PY closure to first order in the coupling.**  The PY closure
`c(s) = (e^{−β s u} − 1)·y(s)` has first-order coefficient `y₀·(−βu)`: the Mayer factor supplies the
`−βu`, and the cavity function contributes only its zeroth-order value because the factor it
multiplies vanishes at `s = 0`. -/
theorem py_first_order_outer {beta u gHS y1 : ℝ} (y : ℝ → ℝ)
    (hy : HasDerivAt y y1 0) (hy0 : y 0 = gHS) :
    HasDerivAt (fun s => mayerF beta u s * y s) (gHS * -(beta * u)) 0 := by
  have h := (hasDerivAt_mayerF beta u).mul hy
  rw [mayerF_zero, hy0] at h
  rw [show gHS * -(beta * u) = -(beta * u) * gHS + 0 * y1 from by ring]
  exact h

/-- **PYE.1 — `y₀ = g_HS`.**  The cavity function `y = g·e^{βsu}` at zero coupling is the RDF at zero
coupling, i.e. the hard-sphere `g_HS`.  (This is what turns `py_first_order_outer`'s `y₀` into the
`g_HS` of `c₁ = g_HS·(−βu)`.) -/
theorem cavity_zero_coupling {beta u gHS : ℝ} (g y : ℝ → ℝ)
    (hcav : ∀ s, y s = g s * Real.exp (beta * s * u)) (hg0 : g 0 = gHS) :
    y 0 = gHS := by
  rw [hcav 0]; simp [hg0]

/-- **PYE.1 — first-order PY outer, assembled**: `c₁(r>R) = g_HS·(−βu)`, with `g_HS` reached through
the cavity function (`cavity_zero_coupling`). -/
theorem py_first_order_outer_cavity {beta u gHS y1 : ℝ} (g y : ℝ → ℝ)
    (hy : HasDerivAt y y1 0) (hcav : ∀ s, y s = g s * Real.exp (beta * s * u)) (hg0 : g 0 = gHS) :
    HasDerivAt (fun s => mayerF beta u s * y s) (gHS * -(beta * u)) 0 :=
  py_first_order_outer y hy (cavity_zero_coupling g y hcav hg0)

/-- **MSA/FMSA first order is the `y₀ ↦ 1` case**: the bare `−βu`, with no `g_HS` enhancement.  (The
numerics' "FMSA badly undershoots" — `hncb_first_order.md` §3 — is exactly this missing factor.) -/
theorem msa_first_order_outer (beta u : ℝ) :
    HasDerivAt (fun s => mayerF beta u s * (1 : ℝ)) (1 * -(beta * u)) 0 :=
  py_first_order_outer (fun _ => (1 : ℝ)) (hasDerivAt_const 0 1) rfl

end FMSA.FirstOrderClosure
