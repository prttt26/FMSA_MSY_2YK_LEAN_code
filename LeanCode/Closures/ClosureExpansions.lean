/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# First-order closure relations — PY / PYE / HNCB / MSA  (Group PYE.1 / HNCB.1)

The **dependency-free half** of the non-FMSA closure development (split from the core-bound DP map,
`Closures/DPClosureMap.lean`, in the 2026-08 restructure): the Mayer `f`-function, the PY, MSA, and
HNCB (Lado reference-HNC) closures expanded to first order in the coupling, the cavity-function
forms, the bridge coefficient, and the pass-0 collapse of HNCB to first-order PY.  All `HasDerivAt` /
algebra over Mathlib only — no FMSA core dependency, which is why it lives in `Closures/`.
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

/-- The HNCB (Lado reference-HNC) closure at coupling `s`:
`c(s) = exp(−β s u + γ(s) + B_HS) − 1 − γ(s)`, with a **coupling-independent** hard-sphere bridge
`B_HS`. -/
noncomputable def hncbClosure (beta u B : ℝ) (gamma : ℝ → ℝ) (s : ℝ) : ℝ :=
  Real.exp (-(beta * s * u) + gamma s + B) - 1 - gamma s

/-- **The expansion base point is consistent**: `c₀(r>R) = 0`.  At `s = 0` the system is pure hard
sphere, `γ₀ = h_HS` and `exp(γ₀ + B_HS) = g_HS = 1 + h_HS` — which is exactly the hypothesis — so the
zeroth-order outer HNCB DCF vanishes, matching PY's `mayerF_zero`. -/
theorem hncb_outer_zeroth_order_eq_zero {beta u B : ℝ} (gamma : ℝ → ℝ)
    (hbase : Real.exp (gamma 0 + B) = 1 + gamma 0) :
    hncbClosure beta u B gamma 0 = 0 := by
  simp only [hncbClosure, mul_zero, zero_mul, neg_zero, zero_add, hbase]
  ring

/-- **PYE.1 (HNCB side) — the bridge closure to first order.**  `c₁(r>R) = g_HS·(−βu) + h_HS·γ₁`
with `g_HS = exp(γ₀ + B_HS)` and `h_HS = g_HS − 1`: the chain rule on the exponential gives
`g_HS·(−βu + γ₁)` and the explicit `−γ(s)` subtracts one `γ₁`. -/
theorem hncb_first_order_outer {beta u B gHS gamma1 : ℝ} (gamma : ℝ → ℝ)
    (hg : HasDerivAt gamma gamma1 0) (hgHS : Real.exp (gamma 0 + B) = gHS) :
    HasDerivAt (hncbClosure beta u B gamma) (gHS * -(beta * u) + (gHS - 1) * gamma1) 0 := by
  have hlin : HasDerivAt (fun s : ℝ => -(beta * s * u) + gamma s + B)
      (-(beta * 1 * u) + gamma1) 0 := ((hasDerivAt_couplingExponent beta u).add hg).add_const B
  have hval : Real.exp (-(beta * 0 * u) + gamma 0 + B) = gHS := by
    simpa using hgHS
  have h : HasDerivAt (fun s => Real.exp (-(beta * s * u) + gamma s + B) - 1 - gamma s)
      (Real.exp (-(beta * 0 * u) + gamma 0 + B) * (-(beta * 1 * u) + gamma1) - gamma1) 0 :=
    ((hlin.exp).sub_const 1).sub hg
  rw [hval] at h
  have hd : gHS * (-(beta * 1 * u) + gamma1) - gamma1 = gHS * -(beta * u) + (gHS - 1) * gamma1 := by
    ring
  rw [hd] at h
  exact h

/-- **HNCB.1 — the base point, and why `h_HS` is the `γ₁` coefficient.**  The two hypotheses used
above are *not* independent: `hncb_outer_zeroth_order_eq_zero` asks for `exp(γ₀+B) = 1+γ₀` (so that
`c₀(r>R) = 0`) and `hncb_first_order_outer` asks for `exp(γ₀+B) = g_HS`.  Held together they force

    γ₀ = g_HS − 1 = h_HS ,

the physical statement that at zero coupling the indirect correlation *is* the hard-sphere `h_HS`
(the outer `c₀` having vanished) — which is exactly why `hncb_first_order_outer`'s `γ₁` coefficient
comes out as `g_HS − 1 = h_HS` rather than as some independent constant.

Stated so the pair cannot be instantiated inconsistently: a caller supplying both hypotheses gets the
base-point identity and the vanishing zeroth order together.  The `example` below certifies the pair
is inhabited at a `g_HS ≠ 1` point, i.e. that this is not read at the ideal-gas degeneracy. -/
theorem hncb_base_point_gamma_eq {beta u B gHS : ℝ} (gamma : ℝ → ℝ)
    (hbase : Real.exp (gamma 0 + B) = 1 + gamma 0) (hgHS : Real.exp (gamma 0 + B) = gHS) :
    gamma 0 = gHS - 1 ∧ hncbClosure beta u B gamma 0 = 0 :=
  ⟨by rw [hgHS] at hbase; linarith, hncb_outer_zeroth_order_eq_zero gamma hbase⟩

/-- **Non-vacuity of the HNCB base point.**  `γ ≡ 1`, `B_HS = log 2 − 1`, `g_HS = 2` satisfies
`HasDerivAt γ 0 0`, `exp(γ₀+B) = g_HS` *and* `exp(γ₀+B) = 1 + γ₀`, with `g_HS ≠ 1`.  Recorded as an
`example` because this repo has shipped true-but-empty statements before
(`b4_origin_bc_abstract`, `b9_d_ij_nonzero_example`, GAP.8's `poly_coeff_from_laurent`), and the
`g_HS ≠ 1` clause rules out the degenerate reading at the ideal-gas point. -/
example : ∃ (B gHS : ℝ) (gamma : ℝ → ℝ),
    HasDerivAt gamma 0 0 ∧ Real.exp (gamma 0 + B) = gHS ∧
      Real.exp (gamma 0 + B) = 1 + gamma 0 ∧ gHS ≠ 1 := by
  refine ⟨Real.log 2 - 1, 2, fun _ => (1 : ℝ), hasDerivAt_const (0 : ℝ) (1 : ℝ), ?_, ?_, by norm_num⟩
  · change Real.exp ((1 : ℝ) + (Real.log 2 - 1)) = 2
    rw [show (1 : ℝ) + (Real.log 2 - 1) = Real.log 2 from by ring, Real.exp_log (by norm_num)]
  · change Real.exp ((1 : ℝ) + (Real.log 2 - 1)) = 1 + 1
    rw [show (1 : ℝ) + (Real.log 2 - 1) = Real.log 2 from by ring, Real.exp_log (by norm_num)]
    norm_num

/-! ### HNCB.1 — the pivot to the contractive form `c₁ = −βu + B·h₁`

`hncb_first_order_outer` gives the **`exp`-form** coefficient `g_HS·(−βu) + h_HS·γ₁`.  The form the
predictor–corrector actually iterates is the algebraically equivalent

    c₁ = −βu + B·h₁ ,      B := h_HS/g_HS = 1 − 1/g_HS ,

reached by eliminating `γ₁` through the definition of the indirect correlation, `h = γ + c` (so
`γ₁ = h₁ − c₁`), and dividing by `g_HS`.  The two inputs the pivot needs — and the only ones — are
that OZ relation and `g_HS ≠ 0`.

The pivot is not cosmetic: it is what makes the iteration converge.  The `exp` form's own feedback
coefficient on `c₁` is `h_HS = g_HS − 1`, which **exceeds 1 for any moderately dense hard-sphere
fluid** (`g_HS` at contact is ≳ 2), so Picard-iterating it diverges; `B = 1 − 1/g_HS` stays in `[0,1)`
for every `g_HS ≥ 1`.  Both statements are proved below, so the choice of form is recorded as a fact
rather than as a remark.
-/

/-- The contractive bridge coefficient `B = h_HS/g_HS = 1 − 1/g_HS` of the HNCB outer closure. -/
noncomputable def bridgeCoeff (gHS : ℝ) : ℝ := 1 - 1 / gHS

/-- **HNCB.1 ⭐ — the pivot.**  Eliminating `γ₁` from the `exp`-form first-order coefficient
`c₁ = g_HS·(−βu) + h_HS·γ₁` via the OZ relation `h = γ + c` (i.e. `γ₁ = h₁ − c₁`) and dividing by
`g_HS ≠ 0` gives the contractive form `c₁ = −βu + B·h₁`, `B = 1 − 1/g_HS`.

Note `h_HS = g_HS − 1` is *not* an extra hypothesis here: it is already the `γ₁` coefficient produced
by `hncb_first_order_outer`, and `1 + h_HS = g_HS` is what collapses `c₁ + h_HS·c₁` to `g_HS·c₁`. -/
theorem hncb_contractive_pivot {beta u gHS gamma1 h1 c1 : ℝ} (hgHS : gHS ≠ 0)
    (hc1 : c1 = gHS * -(beta * u) + (gHS - 1) * gamma1)
    (hOZ : h1 = gamma1 + c1) :
    c1 = -(beta * u) + bridgeCoeff gHS * h1 := by
  have hgam : gamma1 = h1 - c1 := by linarith
  rw [hgam] at hc1
  unfold bridgeCoeff
  field_simp
  linear_combination hc1

/-- **HNCB.1 — the pivot at the derivative level.**  The HNCB closure's first-order outer
coefficient, written contractively: `HasDerivAt (hncbClosure …) (−βu + B·h₁) 0`, given the OZ
relation for the first-order coefficients and `g_HS ≠ 0`.  This is the form Groups HNCB.2/HNCB.3
iterate. -/
theorem hncb_first_order_outer_contractive {beta u B gHS gamma1 h1 : ℝ} (gamma : ℝ → ℝ)
    (hg : HasDerivAt gamma gamma1 0) (hgHS : Real.exp (gamma 0 + B) = gHS) (hgne : gHS ≠ 0)
    (hOZ : h1 = gamma1 + (gHS * -(beta * u) + (gHS - 1) * gamma1)) :
    HasDerivAt (hncbClosure beta u B gamma) (-(beta * u) + bridgeCoeff gHS * h1) 0 := by
  have h := hncb_first_order_outer (beta := beta) (u := u) gamma hg hgHS
  rwa [hncb_contractive_pivot (beta := beta) (u := u) hgne rfl hOZ] at h

/-- **Why the contractive form is the one to iterate (half 1).**  `B = 1 − 1/g_HS ∈ [0,1)` for every
`g_HS ≥ 1`, so Picard iteration on `c₁ = −βu + B·h₁` contracts. -/
theorem bridgeCoeff_mem_Ico {gHS : ℝ} (h : 1 ≤ gHS) : bridgeCoeff gHS ∈ Set.Ico (0 : ℝ) 1 := by
  have hpos : 0 < gHS := lt_of_lt_of_le one_pos h
  constructor
  · unfold bridgeCoeff
    have : 1 / gHS ≤ 1 := by rw [div_le_one hpos]; exact h
    linarith
  · unfold bridgeCoeff
    have : 0 < 1 / gHS := by positivity
    linarith

/-- **Why the contractive form is the one to iterate (half 2).**  The `exp` form's own feedback
coefficient on `c₁` is `h_HS = g_HS − 1`, which is `≥ 1` as soon as `g_HS ≥ 2` — and `g_HS` at
contact exceeds 2 for any moderately dense hard-sphere fluid.  So iterating
`c₁ = g_HS·(−βu) + h_HS·γ₁` directly is Picard-**unstable** exactly where the theory is used, which
is the reason for the pivot above. -/
theorem exp_form_feedback_ge_one {gHS : ℝ} (h : 2 ≤ gHS) : 1 ≤ gHS - 1 := by linarith

/-- **PYE.1 ⭐ — the Group-PYE identification.**  Setting `γ₁ ≡ 0` (the `pullback_passes = 0` rung,
which drops the indirect correlation) makes the HNCB first-order outer coefficient **equal to PY's**:
both are `g_HS·(−βu)`.  This is the closure-level content of "the no-pull-back construction *is*
first-order PY"; the solver-level content is PYE.3/PYE.4 below. -/
theorem pass_zero_eq_py_first_order {beta u B gHS y1 : ℝ} (gamma y : ℝ → ℝ)
    (hg : HasDerivAt gamma 0 0) (hgHS : Real.exp (gamma 0 + B) = gHS)
    (hy : HasDerivAt y y1 0) (hy0 : y 0 = gHS) :
    HasDerivAt (hncbClosure beta u B gamma) (gHS * -(beta * u)) 0 ∧
      HasDerivAt (fun s => mayerF beta u s * y s) (gHS * -(beta * u)) 0 := by
  refine ⟨?_, py_first_order_outer y hy hy0⟩
  have h := hncb_first_order_outer (beta := beta) (u := u) gamma hg hgHS
  rw [show gHS * -(beta * u) + (gHS - 1) * 0 = gHS * -(beta * u) from by ring] at h
  exact h


end FMSA.FirstOrderClosure
