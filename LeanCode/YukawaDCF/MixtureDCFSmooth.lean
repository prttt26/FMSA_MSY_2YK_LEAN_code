/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaDCF.MixtureClosedForm

/-!
# IB.9 — the first-order inner DCF is smooth (no interior knot) on the open core

The support-geometry half of IB.9 is closed in `MixtureConvolution` (`pbp_breakpoints_subset`: the
only breakpoints are `{±λ_ij, ±R_ij}`, the intermediate species cancel).  This file closes the
analytic half: on each inter-breakpoint interval the DCF is a **finite `poly + exp` closed form**,
hence `ContDiff` — so `λ_ij` is genuinely the only interior knot.

Building on the closed-form assembly of `MixtureClosedForm` (`bConvP_closed_form`,
`intervalIntegral_P_expQuadClosed`, `innerDCF_N1_oddPart`, …), this file supplies:

* `expQuadClosed_outer_eq` — the **outer**-region per-pole term is a *pure exponential*
  `K·e^{−zy}` (the `y`, `y²` coefficients cancel), the missing companion to
  `MixtureClosedForm.expQuadClosed_decomp` (aligned region).
* `outer_perpole_integral` — `∫ P·(outer term)` in closed form (via `integral_quadratic_exppos_conv`).
* `expQuadClosed_contDiff` — every closed-form atom is `ContDiff ℝ ⊤` (by `fun_prop`).

which are the last pieces needed to write `pbpConv` on the core as a closed form, from which the DCF's
`ContDiff` follows by `fun_prop`.

Reads only the frozen `MixtureClosedForm` / `MixtureConvolution` / `Mix` interfaces.
-/

set_option linter.style.longLine false

open FMSA.InnerDecomp FMSA.MixtureConvolution FMSA.MixtureClosedForm
open MeasureTheory Set
open scoped Convolution

namespace FMSA.MixtureDCFSmooth

/-! ### The outer-region per-pole term is a pure exponential -/

/-- **The outer-region `expQuadClosed` collapses to a pure exponential.**  In the outer region the
lower limit of the per-pole integral is the running point `y+L` (not the constant `R`), and the
polynomial part of `expQuadClosed A z R p0 p1 p2 y (y+L) (y+S)` has its `y` and `y²` coefficients
**cancel identically**, leaving `K·e^{−zy}` with a constant `K`.  (Physically: once the compact
`𝒬⁻`-window is fully engulfed, the convolution is just the Yukawa tail times a constant moment of the
window.)  Companion to `MixtureClosedForm.expQuadClosed_decomp` (aligned region). -/
theorem expQuadClosed_outer_eq (A z R L S p0 p1 p2 y : ℝ) :
    expQuadClosed A z R p0 p1 p2 y (y + L) (y + S)
      = A * (Real.exp (z * (R - L)) * (p0/z - p1*L/z - p1/z^2 + p2*L^2/z + 2*p2*L/z^2 + 2*p2/z^3)
             - Real.exp (z * (R - S)) * (p0/z - p1*S/z - p1/z^2 + p2*S^2/z + 2*p2*S/z^2 + 2*p2/z^3))
        * Real.exp (-z * y) := by
  have hS : Real.exp (z * R) * Real.exp (-z * (y + S)) = Real.exp (z * (R - S)) * Real.exp (-z * y) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hL : Real.exp (z * R) * Real.exp (-z * (y + L)) = Real.exp (z * (R - L)) * Real.exp (-z * y) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  unfold expQuadClosed Hn
  linear_combination
    (-A * (p0/z - p1*S/z - p1/z^2 + p2*S^2/z + 2*p2*S/z^2 + 2*p2/z^3)) * hS
    + (A * (p0/z - p1*L/z - p1/z^2 + p2*L^2/z + 2*p2*L/z^2 + 2*p2/z^3)) * hL

/-- Named value of the outer per-pole integral (so the downstream `ContDiff` is `unfold; fun_prop`). -/
noncomputable def outerPerPoleVal (P0 P1 P2 A z R L S p0 p1 p2 x a b : ℝ) : ℝ :=
  (A * (Real.exp (z*(R-L)) * (p0/z - p1*L/z - p1/z^2 + p2*L^2/z + 2*p2*L/z^2 + 2*p2/z^3)
        - Real.exp (z*(R-S)) * (p0/z - p1*S/z - p1/z^2 + p2*S^2/z + 2*p2*S/z^2 + 2*p2/z^3)))
    * Real.exp (-z*x)
    * ((Real.exp (z*b) * (P0/z + P1*(b/z-1/z^2) + P2*(b^2/z-2*b/z^2+2/z^3)))
       - (Real.exp (z*a) * (P0/z + P1*(a/z-1/z^2) + P2*(a^2/z-2*a/z^2+2/z^3))))

/-- `outerPerPoleVal` with `x = r`, `a` constant, `b = r + shift` is `ContDiff ℝ ⊤` in `r`
(a finite `poly · exp`). -/
theorem outerPerPoleVal_contDiff (P0 P1 P2 A z R L S p0 p1 p2 a shift : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun r => outerPerPoleVal P0 P1 P2 A z R L S p0 p1 p2 r a (r + shift)) := by
  unfold outerPerPoleVal; fun_prop

/-- **`∫ P·(outer per-pole term)` in closed form.**  Since the outer term is `K·e^{−z(x−t)}`, the
integral against the quadratic `P = P0+P1t+P2t²` is `K·e^{−zx}·∫ P(t)·e^{zt} dt`, closed by
`integral_quadratic_exppos_conv`.  This is the outer companion to
`MixtureClosedForm.intervalIntegral_P_expQuadClosed` (the aligned per-pole integral). -/
theorem outer_perpole_integral (P0 P1 P2 A z R L S p0 p1 p2 x a b : ℝ) (hz : z ≠ 0) :
    (∫ t in a..b, (P0 + P1*t + P2*t^2)
        * expQuadClosed A z R p0 p1 p2 (x-t) ((x-t)+L) ((x-t)+S))
      = outerPerPoleVal P0 P1 P2 A z R L S p0 p1 p2 x a b := by
  unfold outerPerPoleVal
  rw [show (fun t => (P0 + P1*t + P2*t^2)
            * expQuadClosed A z R p0 p1 p2 (x-t) ((x-t)+L) ((x-t)+S))
      = (fun t => (A * (Real.exp (z*(R-L)) * (p0/z - p1*L/z - p1/z^2 + p2*L^2/z + 2*p2*L/z^2 + 2*p2/z^3)
                       - Real.exp (z*(R-S)) * (p0/z - p1*S/z - p1/z^2 + p2*S^2/z + 2*p2*S/z^2 + 2*p2/z^3)))
                  * Real.exp (-z*x) * ((P0 + P1*t + P2*t^2) * Real.exp (z*t))) from by
    ext t
    rw [expQuadClosed_outer_eq, show -z*(x-t) = -z*x + z*t from by ring, Real.exp_add]; ring]
  rw [intervalIntegral.integral_const_mul, integral_quadratic_exppos_conv _ _ _ _ _ _ hz]

/-- Named value of the aligned per-pole integral = `expQuadClosedPos` atom + the pure-quadratic
residue (closed by `integral_quad_quadReflected`).  So the aligned half is also a finite `poly · exp`
in `r`. -/
noncomputable def alignedPerPoleVal (P0 P1 P2 A z R S p0 p1 p2 x a b : ℝ) : ℝ :=
  expQuadClosedPos (-A * Real.exp (z * (R - S))
      * (p0/z - p1*S/z - p1/z^2 + p2*S^2/z + 2*p2*S/z^2 + 2*p2/z^3)) z 0 P0 P1 P2 x a b
  + A * (let s0 := p0/z - p1*(R/z+1/z^2) + p2*(R^2/z+2*R/z^2+2/z^3)
         let s1 := p1/z - 2*p2*(R/z+1/z^2)
         let s2 := p2/z
         let d0 := P0*(s0+s1*x+s2*x^2)
         let d1 := P0*(-s1-2*s2*x)+P1*(s0+s1*x+s2*x^2)
         let d2 := P0*s2+P1*(-s1-2*s2*x)+P2*(s0+s1*x+s2*x^2)
         let d3 := P1*s2+P2*(-s1-2*s2*x)
         let d4 := P2*s2
         (d0*b + d1*b^2/2 + d2*b^3/3 + d3*b^4/4 + d4*b^5/5)
         - (d0*a + d1*a^2/2 + d2*a^3/3 + d3*a^4/4 + d4*a^5/5))

/-- `alignedPerPoleVal` with `x = r`, `a = r + shift`, `b` constant is `ContDiff ℝ ⊤` in `r`. -/
theorem alignedPerPoleVal_contDiff (P0 P1 P2 A z R S p0 p1 p2 shift b : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun r => alignedPerPoleVal P0 P1 P2 A z R S p0 p1 p2 r (r + shift) b) := by
  unfold alignedPerPoleVal expQuadClosedPos Hp; fun_prop

/-- **`∫ P·(aligned per-pole term)` in closed form** — `intervalIntegral_P_expQuadClosed` (their exp
atom) with the residual pure-quadratic integral closed by `integral_quad_quadReflected`. -/
theorem aligned_perpole_integral (P0 P1 P2 A z R S p0 p1 p2 x a b : ℝ) (hz : z ≠ 0) :
    (∫ t in a..b, (P0 + P1*t + P2*t^2) * expQuadClosed A z R p0 p1 p2 (x-t) R ((x-t)+S))
      = alignedPerPoleVal P0 P1 P2 A z R S p0 p1 p2 x a b := by
  rw [intervalIntegral_P_expQuadClosed P0 P1 P2 A z R S p0 p1 p2 x a b hz,
      integral_quad_quadReflected]
  rfl

/-! ### Every closed-form atom is smooth -/

/-- `expQuadClosed A z R p (·) a (·+u)` is `ContDiff ℝ ⊤` in its evaluation point — it is a finite
`poly · exp`, so `fun_prop` closes it after unfolding.  The engine behind "the DCF is smooth on each
inter-breakpoint interval". -/
theorem expQuadClosed_contDiff (A z R p0 p1 p2 a u : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => expQuadClosed A z R p0 p1 p2 x a (x + u)) := by
  unfold expQuadClosed Hn; fun_prop

/-- `expQuadClosedPos A z R p (·) a (·+u)` is `ContDiff ℝ ⊤` (the `P⋆ℬ` per-pole atom). -/
theorem expQuadClosedPos_contDiff (A z R p0 p1 p2 a u : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => expQuadClosedPos A z R p0 p1 p2 x a (x + u)) := by
  unfold expQuadClosedPos Hp; fun_prop

/-! ### Two of the four N=1 DCF terms are smooth on the core (directly from their closed forms) -/

/-- **`bConvP` (the `ℬ⋆P` term) is `ContDiff` on the open core `(0, R_00)`** (N=1).  On that interval
`bConvP_closed_form` gives it as `Σ_q expQuadClosed`, a finite `poly + exp`, hence smooth. -/
theorem bConvP_contDiffOn {M : ℕ} (X : Mix 1 M) (hz : ∀ q : Fin M, X.zp 0 0 q ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (bConvP X 0 0 0) (Set.Ioo 0 (X.R 0 0)) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ q : Fin M,
      expQuadClosed (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0)
        (2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) * (-X.Q0 0 0 * X.R 0 0 + X.Qpp 0 * X.R 0 0 ^ 2 / 2))
        (2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) * (-X.Q0 0 0 + X.Qpp 0 * X.R 0 0))
        (2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) * (X.Qpp 0 / 2))
        x (X.R 0 0) (x - -(X.R 0 0))) := by
    apply ContDiff.sum
    intro q _
    simpa only [sub_neg_eq_add] using expQuadClosed_contDiff (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0)
      (2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) * (-X.Q0 0 0 * X.R 0 0 + X.Qpp 0 * X.R 0 0 ^ 2 / 2))
      (2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) * (-X.Q0 0 0 + X.Qpp 0 * X.R 0 0))
      (2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) * (X.Qpp 0 / 2)) (X.R 0 0) (X.R 0 0)
  refine hg.contDiffOn.congr ?_
  intro x hx
  rw [Set.mem_Ioo] at hx
  have hlam : X.lam 0 0 = 0 := by simp only [Mix.lam]; ring
  refine bConvP_closed_form X 0 0 0 x hz ?_ ?_
  · rw [hlam]; simp only [neg_zero, sub_zero]; linarith [hx.2]
  · simp only [sub_neg_eq_add]; linarith [hx.1]

/-- **`pConvB` (the `P⋆ℬ` term) is `ContDiff` on the open core `(0, R_00)`** (N=1).  On that interval
`pConvB_closed_form` gives it as `Σ_q expQuadClosedPos`, a finite `poly + exp`, hence smooth. -/
theorem pConvB_contDiffOn {M : ℕ} (X : Mix 1 M) (hz : ∀ q : Fin M, X.zp 0 0 q ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      ((pMixEntry X 0 0) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (bMixEntry X 0 0))
      (Set.Ioo 0 (X.R 0 0)) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ q : Fin M,
      expQuadClosedPos (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0)
        (2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) * (-X.Q0 0 0 * X.R 0 0 + X.Qpp 0 * X.R 0 0 ^ 2 / 2))
        (2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) * (-X.Q0 0 0 + X.Qpp 0 * X.R 0 0))
        (2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) * (X.Qpp 0 / 2))
        x (-(X.R 0 0)) (x - X.R 0 0)) := by
    apply ContDiff.sum
    intro q _
    have h := expQuadClosedPos_contDiff (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0)
      (2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) * (-X.Q0 0 0 * X.R 0 0 + X.Qpp 0 * X.R 0 0 ^ 2 / 2))
      (2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) * (-X.Q0 0 0 + X.Qpp 0 * X.R 0 0))
      (2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) * (X.Qpp 0 / 2)) (-(X.R 0 0)) (-(X.R 0 0))
    simpa only [← sub_eq_add_neg] using h
  refine hg.contDiffOn.congr ?_
  intro x hx
  rw [Set.mem_Ioo] at hx
  have hlam : X.lam 0 0 = 0 := by simp only [Mix.lam]; ring
  refine pConvB_closed_form X 0 0 0 x hz ?_ ?_
  · rw [hlam]; simp only [neg_zero]; linarith [hx.2]
  · linarith [hx.1]

/-! ### Step A — piecewise interval-integrability discharges `pbpConv_eq_intervalIntegral`'s `hint`

The `hint` of `MixtureClosedForm.pbpConv_eq_intervalIntegral` asks for `bConvP` interval-integrability.
`bConvP` is *not* continuous (both convolution kernels jump), and Mathlib's convolution-continuity
lemmas all require a continuous factor — so we do **not** prove continuity.  Instead: split the
integration interval at the jump `t₀ = x−R`; on each half `bConvP(x−t)` **equals** a continuous
closed form (`bConvP_closed_form_outer` / `bConvP_closed_form`), so the integrand is
`IntervalIntegrable` there (`intervalIntegrable_congr_uIoo` + `Continuous.intervalIntegrable`); then
`IntervalIntegrable.trans` glues the two.  Integrability does not care about the jump between halves —
this is "piecewise gluing" for *integrability*, not continuity. -/

/-- The `pbpConv_eq_intervalIntegral` integrand for N=1 (the `𝒬⁻`-window quadratic times `bConvP`). -/
noncomputable def pbpIntegrand {M : ℕ} (X : Mix 1 M) (x t : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0)
    * (X.Q0 0 0 * (-t - X.R 0 0) + X.Qpp 0 * (-t - X.R 0 0) ^ 2 / 2) * bConvP X 0 0 0 (x - t)

/-- OUTER half `[−R, x−R]`: `bConvP(x−t) = Σ_q expQuadClosed(outer)` (continuous) ⇒ integrable. -/
theorem pbpIntegrand_intervalIntegrable_outer {M : ℕ} (X : Mix 1 M)
    (hz : ∀ q : Fin M, X.zp 0 0 q ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    IntervalIntegrable (pbpIntegrand X x) volume (-(X.R 0 0)) (x - X.R 0 0) := by
  have hlam : X.lam 0 0 = 0 := by simp only [Mix.lam]; ring
  refine (intervalIntegrable_congr_uIoo (g := fun t => 2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0)
      * (X.Q0 0 0 * (-t - X.R 0 0) + X.Qpp 0 * (-t - X.R 0 0) ^ 2 / 2) *
      ∑ q : Fin M, expQuadClosed (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0)
        (2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) * (-X.Q0 0 0 * X.R 0 0 + X.Qpp 0 * X.R 0 0 ^ 2 / 2))
        (2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) * (-X.Q0 0 0 + X.Qpp 0 * X.R 0 0))
        (2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) * (X.Qpp 0 / 2))
        (x-t) ((x-t) - -(X.lam 0 0)) ((x-t) - -(X.R 0 0))) ?_).mpr ?_
  · intro t ht
    rw [Set.uIoo_of_le (by linarith : -(X.R 0 0) ≤ x - X.R 0 0), Set.mem_Ioo] at ht
    show pbpIntegrand X x t = _
    unfold pbpIntegrand
    rw [bConvP_closed_form_outer X 0 0 0 (x-t) hz
        (by rw [hlam]; simp only [neg_zero, sub_zero]; linarith [ht.2])
        (by rw [hlam]; simp only [neg_zero, sub_zero]; linarith [X.R_pos 0 0])]
  · apply Continuous.intervalIntegrable
    refine Continuous.mul (by fun_prop) (continuous_finsetSum _ ?_)
    intro q _; unfold expQuadClosed Hn; fun_prop

/-- ALIGNED half `[x−R, 0]`: `bConvP(x−t) = Σ_q expQuadClosed(aligned)` (continuous) ⇒ integrable. -/
theorem pbpIntegrand_intervalIntegrable_aligned {M : ℕ} (X : Mix 1 M)
    (hz : ∀ q : Fin M, X.zp 0 0 q ≠ 0) {x : ℝ} (hx : 0 < x) (hxR : x < X.R 0 0) :
    IntervalIntegrable (pbpIntegrand X x) volume (x - X.R 0 0) 0 := by
  have hlam : X.lam 0 0 = 0 := by simp only [Mix.lam]; ring
  refine (intervalIntegrable_congr_uIoo (g := fun t => 2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0)
      * (X.Q0 0 0 * (-t - X.R 0 0) + X.Qpp 0 * (-t - X.R 0 0) ^ 2 / 2) *
      ∑ q : Fin M, expQuadClosed (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0)
        (2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) * (-X.Q0 0 0 * X.R 0 0 + X.Qpp 0 * X.R 0 0 ^ 2 / 2))
        (2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) * (-X.Q0 0 0 + X.Qpp 0 * X.R 0 0))
        (2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) * (X.Qpp 0 / 2))
        (x-t) (X.R 0 0) ((x-t) - -(X.R 0 0))) ?_).mpr ?_
  · intro t ht
    rw [Set.uIoo_of_le (by linarith : x - X.R 0 0 ≤ 0), Set.mem_Ioo] at ht
    show pbpIntegrand X x t = _
    unfold pbpIntegrand
    rw [bConvP_closed_form X 0 0 0 (x-t) hz
        (by rw [hlam]; simp only [neg_zero, sub_zero]; linarith [ht.2])
        (by simp only [sub_neg_eq_add]; linarith [ht.1])]
  · apply Continuous.intervalIntegrable
    refine Continuous.mul (by fun_prop) (continuous_finsetSum _ ?_)
    intro q _; unfold expQuadClosed Hn; fun_prop

/-- **The `hint`**: `pbpIntegrand` is interval-integrable on the full `[−R, 0]`, by `trans` of the two
halves.  Discharges `pbpConv_eq_intervalIntegral` for N=1. -/
theorem pbpIntegrand_intervalIntegrable {M : ℕ} (X : Mix 1 M)
    (hz : ∀ q : Fin M, X.zp 0 0 q ≠ 0) {x : ℝ} (hx : 0 < x) (hxR : x < X.R 0 0) :
    IntervalIntegrable (pbpIntegrand X x) volume (-(X.R 0 0)) 0 :=
  (pbpIntegrand_intervalIntegrable_outer X hz hx.le).trans
    (pbpIntegrand_intervalIntegrable_aligned X hz hx hxR)

-- reusable: half-integral = Σ per-pole val (outer OR aligned), packaged by a boolean-ish switch
-- OUTER half eval
/-- **Outer half of `pbpConv(r)` in closed form** (N=1, `0<r<R`).  On `t∈[−R, r−R]` the argument
`r−t` lands in the OUTER region (`R ≤ r−t`), where `bConvP(r−t)` is the pure-exponential outer closed
form; term-by-term the P-weighted integral is `outerPerPoleVal` (via `outer_perpole_integral`). -/
theorem pbpConv_outer_half_eq {M:ℕ} (X : Mix 1 M) (hz : ∀ q : Fin M, X.zp 0 0 q ≠ 0) {r:ℝ} (hr0:0<r) (hrR:r<X.R 0 0)
    (G0 G1 G2 : ℝ) (hG0 : G0 = 2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(-X.Q0 0 0*X.R 0 0+X.Qpp 0*X.R 0 0^2/2))
    (hG1 : G1 = 2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(-X.Q0 0 0+X.Qpp 0*X.R 0 0))
    (hG2 : G2 = 2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(X.Qpp 0/2)) :
    (∫ t in (-(X.R 0 0))..(r - X.R 0 0), pbpIntegrand X r t)
      = ∑ q : Fin M, outerPerPoleVal G0 G1 G2 (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0) (X.lam 0 0) (X.R 0 0) G0 G1 G2 r (-(X.R 0 0)) (r - X.R 0 0) := by
  have hlam : X.lam 0 0 = 0 := by simp only [Mix.lam]; ring
  rw [show (∫ t in (-(X.R 0 0))..(r - X.R 0 0), pbpIntegrand X r t)
      = ∑ q : Fin M, ∫ t in (-(X.R 0 0))..(r - X.R 0 0), (G0 + G1*t + G2*t^2)
          * expQuadClosed (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0) G0 G1 G2 ((r-t)) ((r-t) + X.lam 0 0) ((r-t) + X.R 0 0) from ?_]
  · exact Finset.sum_congr rfl fun q _ =>
      outer_perpole_integral G0 G1 G2 (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0) (X.lam 0 0) (X.R 0 0) G0 G1 G2 r (-(X.R 0 0)) (r - X.R 0 0) (hz q)
  · rw [← intervalIntegral.integral_finsetSum]
    · apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith : -(X.R 0 0) ≤ r - X.R 0 0), mem_Icc] at ht
      show pbpIntegrand X r t = _
      unfold pbpIntegrand
      rw [bConvP_closed_form_outer X 0 0 0 (r-t) hz (by rw [hlam]; simp only [neg_zero, sub_zero]; linarith [ht.2]) (by rw [hlam]; simp only [neg_zero, sub_zero]; linarith [X.R_pos 0 0]), Finset.mul_sum]
      apply Finset.sum_congr rfl; intro q _; rw [hG0, hG1, hG2]; simp only [sub_neg_eq_add]; ring
    · intro q _; apply Continuous.intervalIntegrable; unfold expQuadClosed Hn; fun_prop
-- ALIGNED half eval
/-- **Aligned half of `pbpConv(r)` in closed form** (N=1, `0<r<R`).  On `t∈[r−R, 0]` the argument
`r−t∈[0,R]` lands in the ALIGNED region, where `bConvP(r−t)` is the `bConvP_closed_form` quadratic×exp;
term-by-term the P-weighted integral is `alignedPerPoleVal` (via `aligned_perpole_integral`). -/
theorem pbpConv_aligned_half_eq {M:ℕ} (X : Mix 1 M) (hz : ∀ q : Fin M, X.zp 0 0 q ≠ 0) {r:ℝ} (hr0:0<r) (hrR:r<X.R 0 0)
    (G0 G1 G2 : ℝ) (hG0 : G0 = 2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(-X.Q0 0 0*X.R 0 0+X.Qpp 0*X.R 0 0^2/2))
    (hG1 : G1 = 2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(-X.Q0 0 0+X.Qpp 0*X.R 0 0))
    (hG2 : G2 = 2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(X.Qpp 0/2)) :
    (∫ t in (r - X.R 0 0)..0, pbpIntegrand X r t)
      = ∑ q : Fin M, alignedPerPoleVal G0 G1 G2 (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0) (X.R 0 0) G0 G1 G2 r (r - X.R 0 0) 0 := by
  have hlam : X.lam 0 0 = 0 := by simp only [Mix.lam]; ring
  rw [show (∫ t in (r - X.R 0 0)..0, pbpIntegrand X r t)
      = ∑ q : Fin M, ∫ t in (r - X.R 0 0)..0, (G0 + G1*t + G2*t^2)
          * expQuadClosed (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0) G0 G1 G2 ((r-t)) (X.R 0 0) ((r-t) + X.R 0 0) from ?_]
  · exact Finset.sum_congr rfl fun q _ =>
      aligned_perpole_integral G0 G1 G2 (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0) (X.R 0 0) G0 G1 G2 r (r - X.R 0 0) 0 (hz q)
  · rw [← intervalIntegral.integral_finsetSum]
    · apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith : r - X.R 0 0 ≤ 0), mem_Icc] at ht
      show pbpIntegrand X r t = _
      unfold pbpIntegrand
      rw [bConvP_closed_form X 0 0 0 (r-t) hz (by rw [hlam]; simp only [neg_zero, sub_zero]; linarith [ht.1]) (by simp only [sub_neg_eq_add]; linarith [ht.2]), Finset.mul_sum]
      apply Finset.sum_congr rfl; intro q _; rw [hG0, hG1, hG2]; simp only [sub_neg_eq_add]; ring
    · intro q _; apply Continuous.intervalIntegrable; unfold expQuadClosed Hn; fun_prop
/-- **`pbpConv(r)` as a single interval integral of `pbpIntegrand`** (N=1, `0<r<R`), folding the
upper limit `−λ_00 = 0`.  Discharges `pbpConv_eq_intervalIntegral`'s integrability hypothesis via the
piecewise `pbpIntegrand_intervalIntegrable`. -/
theorem pbpConv_eq {M:ℕ} (X : Mix 1 M) (hz : ∀ q : Fin M, X.zp 0 0 q ≠ 0) {r:ℝ} (hr0:0<r) (hrR:r<X.R 0 0) :
    pbpConv X 0 0 0 0 r = ∫ t in (-(X.R 0 0))..0, pbpIntegrand X r t := by
  have hlam : X.lam 0 0 = 0 := by simp only [Mix.lam]; ring
  rw [pbpConv_eq_intervalIntegral X 0 0 0 0 r (by rw [hlam]; linarith [X.R_pos 0 0])
      (by rw [show -(X.lam 0 0) = (0:ℝ) from by rw [hlam]; ring]; exact pbpIntegrand_intervalIntegrable X hz hr0 hrR)]
  rw [show -(X.lam 0 0) = (0:ℝ) from by rw [hlam]; ring]
  rfl
/-- **`pbpConv(r)` (the `P⋆ℬ⋆P` term) is `ContDiff` on the open core `(0,R_00)`** (N=1).  Split at the
jump `t=r−R` into outer + aligned halves, each a finite `Σ_q` of smooth per-pole closed forms
(`outerPerPoleVal` / `alignedPerPoleVal`); no continuity of the (discontinuous) convolution kernels is
needed — only piecewise integrability plus the two closed-form half evaluations. -/
theorem pbpConv_pos_contDiffOn {M:ℕ} (X : Mix 1 M) (hz : ∀ q : Fin M, X.zp 0 0 q ≠ 0) :
    ContDiffOn ℝ (⊤:ℕ∞) (fun r => pbpConv X 0 0 0 0 r) (Ioo 0 (X.R 0 0)) := by
  set G0 := 2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(-X.Q0 0 0*X.R 0 0+X.Qpp 0*X.R 0 0^2/2) with hG0
  set G1 := 2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(-X.Q0 0 0+X.Qpp 0*X.R 0 0) with hG1
  set G2 := 2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(X.Qpp 0/2) with hG2
  have hcd : ContDiff ℝ (⊤:ℕ∞) (fun r =>
      (∑ q : Fin M, outerPerPoleVal G0 G1 G2 (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0) (X.lam 0 0) (X.R 0 0) G0 G1 G2 r (-(X.R 0 0)) (r - X.R 0 0))
      + (∑ q : Fin M, alignedPerPoleVal G0 G1 G2 (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0) (X.R 0 0) G0 G1 G2 r (r - X.R 0 0) 0)) := by
    apply ContDiff.add
    · apply ContDiff.sum; intro q _
      exact outerPerPoleVal_contDiff G0 G1 G2 (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0) (X.lam 0 0) (X.R 0 0) G0 G1 G2 (-(X.R 0 0)) (-(X.R 0 0))
    · apply ContDiff.sum; intro q _
      exact alignedPerPoleVal_contDiff G0 G1 G2 (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0) (X.R 0 0) G0 G1 G2 (-(X.R 0 0)) 0
  refine ContDiffOn.congr hcd.contDiffOn ?_
  intro r hr
  rw [mem_Ioo] at hr
  rw [pbpConv_eq X hz hr.1 hr.2,
      ← intervalIntegral.integral_add_adjacent_intervals
        (pbpIntegrand_intervalIntegrable_outer X hz hr.1.le)
        (pbpIntegrand_intervalIntegrable_aligned X hz hr.1 hr.2),
      pbpConv_outer_half_eq X hz hr.1 hr.2 G0 G1 G2 hG0 hG1 hG2,
      pbpConv_aligned_half_eq X hz hr.1 hr.2 G0 G1 G2 hG0 hG1 hG2]

-- neg-aligned integrability on [-R, -r]
/-- **`pbpIntegrand(−r)` is integrable on the aligned window `[−R, −r]`** (N=1, `0<r<R`).  There
`−r−t∈[0,R−r]` is aligned, so `pbpIntegrand(−r,·)` agrees a.e. with a continuous `poly×Σ_q expQuadClosed`. -/
theorem pbpIntegrand_neg_intervalIntegrable_aligned {M:ℕ} (X : Mix 1 M) (hz : ∀ q : Fin M, X.zp 0 0 q ≠ 0) {r:ℝ} (hr0:0<r) (hrR:r<X.R 0 0) :
    IntervalIntegrable (pbpIntegrand X (-r)) volume (-(X.R 0 0)) (-r) := by
  have hlam : X.lam 0 0 = 0 := by simp only [Mix.lam]; ring
  refine (intervalIntegrable_congr_uIoo (g := fun t => 2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)
      * (X.Q0 0 0*(-t-X.R 0 0)+X.Qpp 0*(-t-X.R 0 0)^2/2) *
      ∑ q : Fin M, expQuadClosed (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0)
        (2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(-X.Q0 0 0*X.R 0 0+X.Qpp 0*X.R 0 0^2/2))
        (2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(-X.Q0 0 0+X.Qpp 0*X.R 0 0))
        (2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(X.Qpp 0/2))
        (-r-t) (X.R 0 0) ((-r-t) - -(X.R 0 0))) ?_).mpr ?_
  · intro t ht
    rw [Set.uIoo_of_le (by linarith : -(X.R 0 0) ≤ -r), mem_Ioo] at ht
    show pbpIntegrand X (-r) t = _
    unfold pbpIntegrand
    rw [bConvP_closed_form X 0 0 0 (-r-t) hz (by rw [hlam]; simp only [neg_zero, sub_zero]; linarith [ht.2]) (by simp only [sub_neg_eq_add]; linarith [ht.2])]
  · apply Continuous.intervalIntegrable
    refine Continuous.mul (by fun_prop) (continuous_finsetSum _ ?_)
    intro q _; unfold expQuadClosed Hn; fun_prop
-- zero part on [-r, 0]
/-- **`pbpIntegrand(−r)` is integrable on `[−r, 0]`, where it vanishes** (N=1, `0<r`).  For `t>−r` the
argument `−r−t<0` is below `bConvP`'s support `[0,∞)`, so the integrand is a.e. `0`. -/
theorem pbpIntegrand_neg_intervalIntegrable_zero {M:ℕ} (X : Mix 1 M) {r:ℝ} (hr0:0<r) :
    IntervalIntegrable (pbpIntegrand X (-r)) volume (-r) 0 := by
  refine (intervalIntegrable_congr_uIoo (g := fun _ => (0:ℝ)) ?_).mpr (by simp)
  intro t ht
  rw [Set.uIoo_of_le (by linarith : -r ≤ (0:ℝ)), mem_Ioo] at ht
  show pbpIntegrand X (-r) t = 0
  unfold pbpIntegrand
  rw [show bConvP X 0 0 0 (-r-t) = 0 from ?_, mul_zero]
  by_contra h
  have := bConvP_support_subset X 0 0 0 (Function.mem_support.mpr h)
  rw [Set.mem_Ici, show X.R 0 0 - X.R 0 0 = (0:ℝ) from by ring] at this
  linarith [ht.1]
/-- **`pbpConv(−r)` aligned window in closed form** (N=1, `0<r<R`).  `∫_{−R}^{−r}` term-by-term is
`Σ_q alignedPerPoleVal(…,−r,−R,−r)` (via `aligned_perpole_integral`); the complementary `∫_{−r}^{0}`
vanishes by support. -/
theorem pbpConv_neg_half_eq {M:ℕ} (X : Mix 1 M) (hz : ∀ q : Fin M, X.zp 0 0 q ≠ 0) {r:ℝ} (hr0:0<r) (hrR:r<X.R 0 0)
    (G0 G1 G2 : ℝ) (hG0 : G0 = 2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(-X.Q0 0 0*X.R 0 0+X.Qpp 0*X.R 0 0^2/2))
    (hG1 : G1 = 2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(-X.Q0 0 0+X.Qpp 0*X.R 0 0))
    (hG2 : G2 = 2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(X.Qpp 0/2)) :
    (∫ t in (-(X.R 0 0))..(-r), pbpIntegrand X (-r) t)
      = ∑ q : Fin M, alignedPerPoleVal G0 G1 G2 (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0) (X.R 0 0) G0 G1 G2 (-r) (-(X.R 0 0)) (-r) := by
  have hlam : X.lam 0 0 = 0 := by simp only [Mix.lam]; ring
  rw [show (∫ t in (-(X.R 0 0))..(-r), pbpIntegrand X (-r) t)
      = ∑ q : Fin M, ∫ t in (-(X.R 0 0))..(-r), (G0 + G1*t + G2*t^2)
          * expQuadClosed (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0) G0 G1 G2 ((-r-t)) (X.R 0 0) ((-r-t) + X.R 0 0) from ?_]
  · exact Finset.sum_congr rfl fun q _ =>
      aligned_perpole_integral G0 G1 G2 (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0) (X.R 0 0) G0 G1 G2 (-r) (-(X.R 0 0)) (-r) (hz q)
  · rw [← intervalIntegral.integral_finsetSum]
    · apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith : -(X.R 0 0) ≤ -r), mem_Icc] at ht
      show pbpIntegrand X (-r) t = _
      unfold pbpIntegrand
      rw [bConvP_closed_form X 0 0 0 (-r-t) hz (by rw [hlam]; simp only [neg_zero, sub_zero]; linarith [ht.2]) (by simp only [sub_neg_eq_add]; linarith [ht.2]), Finset.mul_sum]
      apply Finset.sum_congr rfl; intro q _; rw [hG0, hG1, hG2]; simp only [sub_neg_eq_add]; ring
    · intro q _; apply Continuous.intervalIntegrable; unfold expQuadClosed Hn; fun_prop
/-- **`r ↦ pbpConv(−r)` is `ContDiff` on `(0,R_00)`** (N=1).  For `0<r<R`, `pbpConv(−r)` equals only its
aligned window `Σ_q alignedPerPoleVal(…,−r,−R,−r)` (the `[−r,0]` piece is `0` by support), a finite
`poly+exp` in `r`, hence smooth. -/
theorem pbpConv_neg_contDiffOn {M:ℕ} (X : Mix 1 M) (hz : ∀ q : Fin M, X.zp 0 0 q ≠ 0) :
    ContDiffOn ℝ (⊤:ℕ∞) (fun r => pbpConv X 0 0 0 0 (-r)) (Ioo 0 (X.R 0 0)) := by
  set G0 := 2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(-X.Q0 0 0*X.R 0 0+X.Qpp 0*X.R 0 0^2/2) with hG0
  set G1 := 2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(-X.Q0 0 0+X.Qpp 0*X.R 0 0) with hG1
  set G2 := 2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(X.Qpp 0/2) with hG2
  have hlam : X.lam 0 0 = 0 := by simp only [Mix.lam]; ring
  have hcd : ContDiff ℝ (⊤:ℕ∞) (fun r =>
      ∑ q : Fin M, alignedPerPoleVal G0 G1 G2 (X.cb 0 0 q) (X.zp 0 0 q) (X.R 0 0) (X.R 0 0) G0 G1 G2 (-r) (-(X.R 0 0)) (-r)) := by
    apply ContDiff.sum; intro q _; unfold alignedPerPoleVal expQuadClosedPos Hp; fun_prop
  refine ContDiffOn.congr hcd.contDiffOn ?_
  intro r hr
  rw [mem_Ioo] at hr
  rw [pbpConv_eq_intervalIntegral X 0 0 0 0 (-r) (by rw [hlam]; linarith [X.R_pos 0 0])
      (by rw [show -(X.lam 0 0) = (0:ℝ) from by rw [hlam]; ring]; exact (pbpIntegrand_neg_intervalIntegrable_aligned X hz hr.1 hr.2).trans (pbpIntegrand_neg_intervalIntegrable_zero X hr.1))]
  rw [show -(X.lam 0 0) = (0:ℝ) from by rw [hlam]; ring]
  rw [show (∫ t in (-(X.R 0 0))..0, 2*Real.pi*Real.sqrt (X.ρ 0*X.ρ 0)*(X.Q0 0 0*(-t-X.R 0 0)+X.Qpp 0*(-t-X.R 0 0)^2/2) * bConvP X 0 0 0 (-r-t))
      = ∫ t in (-(X.R 0 0))..0, pbpIntegrand X (-r) t from rfl,
      ← intervalIntegral.integral_add_adjacent_intervals (pbpIntegrand_neg_intervalIntegrable_aligned X hz hr.1 hr.2) (pbpIntegrand_neg_intervalIntegrable_zero X hr.1),
      pbpConv_neg_half_eq X hz hr.1 hr.2 G0 G1 G2 hG0 hG1 hG2]
  have hzero : (∫ t in (-r)..0, pbpIntegrand X (-r) t) = 0 := by
    have h0 : ∀ᵐ t ∂volume, t ∈ Set.uIoc (-r) 0 → pbpIntegrand X (-r) t = (fun _ => (0:ℝ)) t := by
      filter_upwards with t ht
      rw [Set.uIoc_of_le (by linarith : -r ≤ (0:ℝ)), mem_Ioc] at ht
      show pbpIntegrand X (-r) t = 0
      unfold pbpIntegrand
      have hb0 : bConvP X 0 0 0 (-r-t) = 0 := by
        by_contra h
        have := bConvP_support_subset X 0 0 0 (Function.mem_support.mpr h)
        rw [Set.mem_Ici, show X.R 0 0 - X.R 0 0 = (0:ℝ) from by ring] at this
        linarith [ht.1]
      rw [hb0, mul_zero]
    rw [intervalIntegral.integral_congr_ae h0, intervalIntegral.integral_zero]
  rw [hzero, add_zero]

/-- **IB.9 headline — the N=1 first-order inner DCF is smooth on the open core `(0, R_00)`.**  By
`innerDCF_N1_oddPart`, `2π√(ρ²)·r·c₁(r)` equals `−bConvP(r) − (P⋆ℬ)(r) + pbpConv(r) − pbpConv(−r)`.
Each of the four terms is `ContDiffOn ℝ ⊤` on `(0,R_00)` (`bConvP_contDiffOn`, `pConvB_contDiffOn`,
`pbpConv_pos_contDiffOn`, `pbpConv_neg_contDiffOn`), so their combination is `C^∞`.  N=1 has `λ_00 = 0`,
so the only DCF breakpoints `{±λ_ij, ±R_ij}` reduce to `{0, ±R}` and NONE lie in the open core:
the inner DCF has NO interior knot — the numerically observed smoothness, proved. -/
theorem innerDCF_N1_contDiffOn {M : ℕ} (X : Mix 1 M) (hz : ∀ q : Fin M, X.zp 0 0 q ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun r => -bConvP X 0 0 0 r
        - ((pMixEntry X 0 0) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (bMixEntry X 0 0)) r
        + pbpConv X 0 0 0 0 r - pbpConv X 0 0 0 0 (-r)) (Set.Ioo 0 (X.R 0 0)) :=
  (((bConvP_contDiffOn X hz).neg.sub (pConvB_contDiffOn X hz)).add
      (pbpConv_pos_contDiffOn X hz)).sub (pbpConv_neg_contDiffOn X hz)



/-! ### General-index (any N, any species pair) — the term-wise ContDiffOn engine

Each `𝒲_ij` term (`ℬ_in⋆P_jn`, `P_im⋆ℬ_mj`, `P_im⋆ℬ_mn⋆P_jn`) is a finite `poly×exp` with
breakpoints **only** at `{±λ_ij, ±R_ij}` (the intermediate species `m,n` cancel via the signed
contact identity `R_in − λ_jn = R_ij`).  So on the upper subinterval `(λ_ij, R_ij)` every term is a
single smooth piece — no aggregate cancellation is needed. -/

/-- The signed contact identity `R_in − λ_jn = R_ij` (intermediate species `n` cancels). -/
theorem R_sub_lam_eq (X : Mix N M) (i n j : Fin N) : X.R i n - X.lam j n = X.R i j := by
  simp only [Mix.R, Mix.lam]; ring

/-- **General-index `bConvP` is `ContDiff` on its aligned region `(−λ_ij, R_ij)`.**  The two-fold
term `ℬ_in ⋆ P_jn` equals its `bConvP_closed_form` finite `poly×exp` there (no interior breakpoint —
the only edges are `−λ_ij` and `R_ij`), hence `C^∞`. -/
theorem bConvP_contDiffOn_aligned (X : Mix N M) (i n j : Fin N)
    (hz : ∀ q : Fin M, X.zp i n q ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (bConvP X i n j) (Set.Ioo (-(X.lam i j)) (X.R i j)) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ q : Fin M,
      expQuadClosed (X.cb i n q) (X.zp i n q) (X.R i n)
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n * X.R j n + X.Qpp n * X.R j n ^ 2 / 2))
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n + X.Qpp n * X.R j n))
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (X.Qpp n / 2))
        x (X.R i n) (x - -(X.R j n))) := by
    apply ContDiff.sum
    intro q _
    simpa only [sub_neg_eq_add] using expQuadClosed_contDiff (X.cb i n q) (X.zp i n q) (X.R i n)
      (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n * X.R j n + X.Qpp n * X.R j n ^ 2 / 2))
      (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n + X.Qpp n * X.R j n))
      (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (X.Qpp n / 2)) (X.R i n) (X.R j n)
  refine hg.contDiffOn.congr ?_
  intro x hx
  rw [Set.mem_Ioo] at hx
  refine bConvP_closed_form X i n j x hz ?_ ?_
  · -- x - -(lam j n) ≤ R i n  ⟺  x ≤ R i n - lam j n = R i j
    have : x - -(X.lam j n) ≤ X.R i n ↔ x ≤ X.R i j := by
      rw [← R_sub_lam_eq X i n j]; constructor <;> intro h <;> linarith
    rw [this]; linarith [hx.2]
  · -- R i n ≤ x - -(R j n)  ⟺  R i n - R j n ≤ x  ⟺  -lam i j ≤ x
    have hb := bConvP_edge_eq X i n j
    rw [show X.R i n ≤ x - -(X.R j n) ↔ X.R i n - X.R j n ≤ x from by
      constructor <;> intro h <;> linarith, hb]
    linarith [hx.1]

/-- `R_mj − R_im = λ_ij` (the mirror two-fold support-start identity). -/
theorem pConvB_edge_eq (X : Mix N M) (i m j : Fin N) : X.R m j - X.R i m = X.lam i j := by
  simp only [Mix.R, Mix.lam]; ring

/-- **General-index `pConvB` is `ContDiff` on its aligned region `(λ_ij, R_ij)`.** -/
theorem pConvB_contDiffOn_aligned (X : Mix N M) (i m j : Fin N)
    (hz : ∀ q : Fin M, X.zp m j q ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      ((pMixEntry X i m) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (bMixEntry X m j))
      (Set.Ioo (X.lam i j) (X.R i j)) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ q : Fin M,
      expQuadClosedPos (X.cb m j q) (X.zp m j q) (X.R m j)
        (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m) * (-X.Q0 i m * X.R i m + X.Qpp m * X.R i m ^ 2 / 2))
        (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m) * (-X.Q0 i m + X.Qpp m * X.R i m))
        (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m) * (X.Qpp m / 2))
        x (-(X.R i m)) (x - X.R m j)) := by
    apply ContDiff.sum
    intro q _
    have := expQuadClosedPos_contDiff (X.cb m j q) (X.zp m j q) (X.R m j)
      (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m) * (-X.Q0 i m * X.R i m + X.Qpp m * X.R i m ^ 2 / 2))
      (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m) * (-X.Q0 i m + X.Qpp m * X.R i m))
      (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m) * (X.Qpp m / 2)) (-(X.R i m)) (-(X.R m j))
    simpa only [sub_eq_add_neg] using this
  refine hg.contDiffOn.congr ?_
  intro x hx
  rw [Set.mem_Ioo] at hx
  refine pConvB_closed_form X i m j x hz ?_ ?_
  · -- x - R m j ≤ -lam i m  ⟺  x ≤ R m j - lam i m = R i j
    have : X.R m j - X.lam i m = X.R i j := by simp only [Mix.R, Mix.lam]; ring
    linarith [hx.2, this]
  · -- -(R i m) ≤ x - R m j  ⟺  R m j - R i m ≤ x  ⟺  lam i j ≤ x
    have := pConvB_edge_eq X i m j; linarith [hx.1]

/-- `bConvP` vanishes strictly below its support start `−λ_ij`. -/
theorem bConvP_eq_zero_of_lt (X : Mix N M) (i n j : Fin N) {x : ℝ} (hx : x < -(X.lam i j)) :
    bConvP X i n j x = 0 := by
  refine eq_zero_of_lt_support_edge (bConvP_support_subset X i n j) ?_
  rw [bConvP_edge_eq]; exact hx

/-- `pConvB` vanishes strictly below its support start `λ_ij`. -/
theorem pConvB_eq_zero_of_lt (X : Mix N M) (i m j : Fin N) {x : ℝ} (hx : x < X.lam i j) :
    ((pMixEntry X i m) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (bMixEntry X m j)) x = 0 := by
  refine eq_zero_of_lt_support_edge (pConvB_support_subset X i m j) ?_
  rw [pConvB_edge_eq]; exact hx

noncomputable def pbpIntegrandG (X : Mix N M) (i m n j : Fin N) (x t : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m)
    * (X.Q0 i m * (-t - X.R i m) + X.Qpp m * (-t - X.R i m) ^ 2 / 2) * bConvP X m n j (x - t)

theorem pbpIntegrandG_ii_outer (X : Mix N M) (i m n j : Fin N)
    (hz : ∀ q : Fin M, X.zp m n q ≠ 0) {x : ℝ} (hlo : X.lam i j < x) :
    IntervalIntegrable (pbpIntegrandG X i m n j x) volume (-(X.R i m)) (x - X.R m j) := by
  have hwin : -(X.R i m) ≤ x - X.R m j := by
    have : X.R m j - X.R i m = X.lam i j := by simp only [Mix.R, Mix.lam]; ring
    linarith
  refine (intervalIntegrable_congr_uIoo (g := fun t => 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m)
      * (X.Q0 i m * (-t - X.R i m) + X.Qpp m * (-t - X.R i m) ^ 2 / 2) *
      ∑ q : Fin M, expQuadClosed (X.cb m n q) (X.zp m n q) (X.R m n)
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n * X.R j n + X.Qpp n * X.R j n ^ 2 / 2))
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n + X.Qpp n * X.R j n))
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (X.Qpp n / 2))
        (x-t) ((x-t) - -(X.lam j n)) ((x-t) - -(X.R j n))) ?_).mpr ?_
  · intro t ht
    rw [Set.uIoo_of_le hwin, Set.mem_Ioo] at ht
    show pbpIntegrandG X i m n j x t = _
    unfold pbpIntegrandG
    rw [bConvP_closed_form_outer X m n j (x-t) hz
        (by rw [show X.R m n ≤ (x-t) - -(X.lam j n) ↔ X.R m j ≤ x - t from by
              rw [← R_sub_lam_eq X m n j]; constructor <;> intro h <;> linarith]; linarith [ht.2])
        (by have hjn : X.lam j n ≤ X.R j n := by simp only [Mix.lam, Mix.R]; linarith [X.hσ j]
            linarith)]
  · apply Continuous.intervalIntegrable
    refine Continuous.mul (by fun_prop) (continuous_finsetSum _ ?_)
    intro q _; unfold expQuadClosed Hn; fun_prop

theorem pbpIntegrandG_ii_aligned (X : Mix N M) (i m n j : Fin N)
    (hz : ∀ q : Fin M, X.zp m n q ≠ 0) {x : ℝ}
    (hlo : X.lam i j < x) (hhi : x < X.R i j) (hlam0 : 0 ≤ X.lam i j) :
    IntervalIntegrable (pbpIntegrandG X i m n j x) volume (x - X.R m j) (-(X.lam i m)) := by
  have hsplit : x - X.R m j ≤ -(X.lam i m) := by
    have : X.R m j - X.lam i m = X.R i j := by simp only [Mix.R, Mix.lam]; ring
    linarith
  refine (intervalIntegrable_congr_uIoo (g := fun t => 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m)
      * (X.Q0 i m * (-t - X.R i m) + X.Qpp m * (-t - X.R i m) ^ 2 / 2) *
      ∑ q : Fin M, expQuadClosed (X.cb m n q) (X.zp m n q) (X.R m n)
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n * X.R j n + X.Qpp n * X.R j n ^ 2 / 2))
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n + X.Qpp n * X.R j n))
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (X.Qpp n / 2))
        (x-t) (X.R m n) ((x-t) - -(X.R j n))) ?_).mpr ?_
  · intro t ht
    rw [Set.uIoo_of_le hsplit, Set.mem_Ioo] at ht
    show pbpIntegrandG X i m n j x t = _
    unfold pbpIntegrandG
    have hAl : (x-t) - -(X.lam j n) ≤ X.R m n := by
      rw [show (x-t) - -(X.lam j n) ≤ X.R m n ↔ x - t ≤ X.R m j from by
            rw [← R_sub_lam_eq X m n j]; constructor <;> intro h <;> linarith]
      have : X.R m j - X.lam i m = X.R i j := by simp only [Mix.R, Mix.lam]; ring
      linarith [ht.1]
    have hNe : X.R m n ≤ (x-t) - -(X.R j n) := by
      rw [show X.R m n ≤ (x-t) - -(X.R j n) ↔ X.R m n - X.R j n ≤ x - t from by
            constructor <;> intro h <;> linarith, bConvP_edge_eq X m n j]
      have e1 : X.lam m j = (X.σ j - X.σ m)/2 := rfl
      have e2 : X.lam i m = (X.σ m - X.σ i)/2 := rfl
      have e3 : X.lam i j = (X.σ j - X.σ i)/2 := rfl
      linarith [ht.2]
    rw [bConvP_closed_form X m n j (x-t) hz hAl hNe]
  · apply Continuous.intervalIntegrable
    refine Continuous.mul (by fun_prop) (continuous_finsetSum _ ?_)
    intro q _; unfold expQuadClosed Hn; fun_prop


/-- Abbreviation packaging the six reflected-quadratic coefficients of `P_ab` (`= 2π√(ρ_a ρ_b)·q`). -/
theorem pbpConvG_eq (X : Mix N M) (i m n j : Fin N)
    (hz : ∀ q : Fin M, X.zp m n q ≠ 0) {x : ℝ} (hlo : X.lam i j < x) (hhi : x < X.R i j)
    (hlam0 : 0 ≤ X.lam i j) :
    pbpConv X i m n j x
      = ∫ t in (-(X.R i m))..(-(X.lam i m)), pbpIntegrandG X i m n j x t := by
  rw [pbpConv_eq_intervalIntegral X i m n j x (by simp only [Mix.lam, Mix.R]; linarith [X.hσ i])
      ((pbpIntegrandG_ii_outer X i m n j hz hlo).trans
        (pbpIntegrandG_ii_aligned X i m n j hz hlo hhi hlam0))]
  rfl

theorem outerHalfG_eq (X : Mix N M) (i m n j : Fin N)
    (hz : ∀ q : Fin M, X.zp m n q ≠ 0) {x : ℝ}
    (P0 P1 P2 G0 G1 G2 : ℝ)
    (hP0 : P0 = 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(-X.Q0 i m*X.R i m+X.Qpp m*X.R i m^2/2))
    (hP1 : P1 = 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(-X.Q0 i m+X.Qpp m*X.R i m))
    (hP2 : P2 = 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(X.Qpp m/2))
    (hG0 : G0 = 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(-X.Q0 j n*X.R j n+X.Qpp n*X.R j n^2/2))
    (hG1 : G1 = 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(-X.Q0 j n+X.Qpp n*X.R j n))
    (hG2 : G2 = 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(X.Qpp n/2))
    (hlo : X.lam i j < x) :
    (∫ t in (-(X.R i m))..(x - X.R m j), pbpIntegrandG X i m n j x t)
      = ∑ q : Fin M, outerPerPoleVal P0 P1 P2 (X.cb m n q) (X.zp m n q) (X.R m n)
          (X.lam j n) (X.R j n) G0 G1 G2 x (-(X.R i m)) (x - X.R m j) := by
  have hwin : -(X.R i m) ≤ x - X.R m j := by
    have : X.R m j - X.R i m = X.lam i j := by simp only [Mix.R, Mix.lam]; ring
    linarith
  rw [show (∫ t in (-(X.R i m))..(x - X.R m j), pbpIntegrandG X i m n j x t)
      = ∑ q : Fin M, ∫ t in (-(X.R i m))..(x - X.R m j), (P0 + P1*t + P2*t^2)
          * expQuadClosed (X.cb m n q) (X.zp m n q) (X.R m n) G0 G1 G2
              (x-t) ((x-t) + X.lam j n) ((x-t) + X.R j n) from ?_]
  · exact Finset.sum_congr rfl fun q _ =>
      outer_perpole_integral P0 P1 P2 (X.cb m n q) (X.zp m n q) (X.R m n) (X.lam j n) (X.R j n)
        G0 G1 G2 x (-(X.R i m)) (x - X.R m j) (hz q)
  · rw [← intervalIntegral.integral_finsetSum]
    · apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hwin, Set.mem_Icc] at ht
      show pbpIntegrandG X i m n j x t = _
      unfold pbpIntegrandG
      rw [bConvP_closed_form_outer X m n j (x-t) hz
          (by rw [show X.R m n ≤ (x-t) - -(X.lam j n) ↔ X.R m j ≤ x - t from by
                rw [← R_sub_lam_eq X m n j]; constructor <;> intro h <;> linarith]; linarith [ht.2])
          (by have hjn : X.lam j n ≤ X.R j n := by simp only [Mix.lam, Mix.R]; linarith [X.hσ j]
              linarith), Finset.mul_sum]
      apply Finset.sum_congr rfl; intro q _
      rw [hP0, hP1, hP2, hG0, hG1, hG2]; simp only [sub_neg_eq_add]; ring
    · intro q _; apply Continuous.intervalIntegrable; unfold expQuadClosed Hn; fun_prop

theorem alignedHalfG_eq (X : Mix N M) (i m n j : Fin N)
    (hz : ∀ q : Fin M, X.zp m n q ≠ 0) {x : ℝ}
    (P0 P1 P2 G0 G1 G2 : ℝ)
    (hP0 : P0 = 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(-X.Q0 i m*X.R i m+X.Qpp m*X.R i m^2/2))
    (hP1 : P1 = 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(-X.Q0 i m+X.Qpp m*X.R i m))
    (hP2 : P2 = 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(X.Qpp m/2))
    (hG0 : G0 = 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(-X.Q0 j n*X.R j n+X.Qpp n*X.R j n^2/2))
    (hG1 : G1 = 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(-X.Q0 j n+X.Qpp n*X.R j n))
    (hG2 : G2 = 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(X.Qpp n/2))
    (hlo : X.lam i j < x) (hhi : x < X.R i j) (hlam0 : 0 ≤ X.lam i j) :
    (∫ t in (x - X.R m j)..(-(X.lam i m)), pbpIntegrandG X i m n j x t)
      = ∑ q : Fin M, alignedPerPoleVal P0 P1 P2 (X.cb m n q) (X.zp m n q) (X.R m n)
          (X.R j n) G0 G1 G2 x (x - X.R m j) (-(X.lam i m)) := by
  have hsplit : x - X.R m j ≤ -(X.lam i m) := by
    have : X.R m j - X.lam i m = X.R i j := by simp only [Mix.R, Mix.lam]; ring
    linarith
  rw [show (∫ t in (x - X.R m j)..(-(X.lam i m)), pbpIntegrandG X i m n j x t)
      = ∑ q : Fin M, ∫ t in (x - X.R m j)..(-(X.lam i m)), (P0 + P1*t + P2*t^2)
          * expQuadClosed (X.cb m n q) (X.zp m n q) (X.R m n) G0 G1 G2
              (x-t) (X.R m n) ((x-t) + X.R j n) from ?_]
  · exact Finset.sum_congr rfl fun q _ =>
      aligned_perpole_integral P0 P1 P2 (X.cb m n q) (X.zp m n q) (X.R m n) (X.R j n)
        G0 G1 G2 x (x - X.R m j) (-(X.lam i m)) (hz q)
  · rw [← intervalIntegral.integral_finsetSum]
    · apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hsplit, Set.mem_Icc] at ht
      show pbpIntegrandG X i m n j x t = _
      unfold pbpIntegrandG
      have hAl : (x-t) - -(X.lam j n) ≤ X.R m n := by
        rw [show (x-t) - -(X.lam j n) ≤ X.R m n ↔ x - t ≤ X.R m j from by
              rw [← R_sub_lam_eq X m n j]; constructor <;> intro h <;> linarith]
        have : X.R m j - X.lam i m = X.R i j := by simp only [Mix.R, Mix.lam]; ring
        linarith [ht.1]
      have hNe : X.R m n ≤ (x-t) - -(X.R j n) := by
        rw [show X.R m n ≤ (x-t) - -(X.R j n) ↔ X.R m n - X.R j n ≤ x - t from by
              constructor <;> intro h <;> linarith, bConvP_edge_eq X m n j]
        have e1 : X.lam m j = (X.σ j - X.σ m)/2 := rfl
        have e2 : X.lam i m = (X.σ m - X.σ i)/2 := rfl
        have e3 : X.lam i j = (X.σ j - X.σ i)/2 := rfl
        linarith [ht.2]
      rw [bConvP_closed_form X m n j (x-t) hz hAl hNe, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro q _
      rw [hP0, hP1, hP2, hG0, hG1, hG2]; simp only [sub_neg_eq_add]; ring
    · intro q _; apply Continuous.intervalIntegrable; unfold expQuadClosed Hn; fun_prop


/-- **General-index forward `pbpConv X i m n j` is `ContDiff` on `(λ_ij, R_ij)`** (`0 ≤ λ_ij`).
Split the `P_im`-window at `t* = x − R_mj` into outer + aligned halves, each a finite `Σ_q` of the
smooth per-pole closed forms; no interior breakpoint of the term lies in `(λ_ij, R_ij)`. -/
theorem pbpConv_forward_contDiffOn (X : Mix N M) (i m n j : Fin N)
    (hz : ∀ q : Fin M, X.zp m n q ≠ 0) (hlam0 : 0 ≤ X.lam i j) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => pbpConv X i m n j x) (Set.Ioo (X.lam i j) (X.R i j)) := by
  set P0 := 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(-X.Q0 i m*X.R i m+X.Qpp m*X.R i m^2/2) with hP0
  set P1 := 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(-X.Q0 i m+X.Qpp m*X.R i m) with hP1
  set P2 := 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(X.Qpp m/2) with hP2
  set G0 := 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(-X.Q0 j n*X.R j n+X.Qpp n*X.R j n^2/2) with hG0
  set G1 := 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(-X.Q0 j n+X.Qpp n*X.R j n) with hG1
  set G2 := 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(X.Qpp n/2) with hG2
  have hcd : ContDiff ℝ (⊤:ℕ∞) (fun x =>
      (∑ q : Fin M, outerPerPoleVal P0 P1 P2 (X.cb m n q) (X.zp m n q) (X.R m n)
          (X.lam j n) (X.R j n) G0 G1 G2 x (-(X.R i m)) (x - X.R m j))
      + (∑ q : Fin M, alignedPerPoleVal P0 P1 P2 (X.cb m n q) (X.zp m n q) (X.R m n)
          (X.R j n) G0 G1 G2 x (x - X.R m j) (-(X.lam i m)))) := by
    apply ContDiff.add
    · apply ContDiff.sum; intro q _
      exact outerPerPoleVal_contDiff P0 P1 P2 (X.cb m n q) (X.zp m n q) (X.R m n)
        (X.lam j n) (X.R j n) G0 G1 G2 (-(X.R i m)) (-(X.R m j))
    · apply ContDiff.sum; intro q _
      exact alignedPerPoleVal_contDiff P0 P1 P2 (X.cb m n q) (X.zp m n q) (X.R m n)
        (X.R j n) G0 G1 G2 (-(X.R m j)) (-(X.lam i m))
  refine ContDiffOn.congr hcd.contDiffOn ?_
  intro x hx
  rw [Set.mem_Ioo] at hx
  rw [pbpConvG_eq X i m n j hz hx.1 hx.2 hlam0,
      ← intervalIntegral.integral_add_adjacent_intervals
        (pbpIntegrandG_ii_outer X i m n j hz hx.1)
        (pbpIntegrandG_ii_aligned X i m n j hz hx.1 hx.2 hlam0),
      outerHalfG_eq X i m n j hz P0 P1 P2 G0 G1 G2 hP0 hP1 hP2 hG0 hG1 hG2 hx.1,
      alignedHalfG_eq X i m n j hz P0 P1 P2 G0 G1 G2 hP0 hP1 hP2 hG0 hG1 hG2 hx.1 hx.2 hlam0]

theorem pbpIntegrandG_neg_ii_aligned (X : Mix N M) (i m n j : Fin N)
    (hz : ∀ q : Fin M, X.zp m n q ≠ 0) {x : ℝ}
    (hlo : X.lam i j < x) (hhi : x < X.R i j) (hlam0 : 0 ≤ X.lam i j) :
    IntervalIntegrable (pbpIntegrandG X i m n j (-x)) volume (-(X.R i m)) (-x + X.lam m j) := by
  have hwin : -(X.R i m) ≤ -x + X.lam m j := by
    have e3 : X.lam m j = (X.σ j - X.σ m)/2 := rfl
    have er : X.R i m = (X.σ i + X.σ m)/2 := rfl
    have erij : X.R i j = (X.σ i + X.σ j)/2 := rfl
    linarith [hhi]
  refine (intervalIntegrable_congr_uIoo (g := fun t => 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m)
      * (X.Q0 i m * (-t - X.R i m) + X.Qpp m * (-t - X.R i m) ^ 2 / 2) *
      ∑ q : Fin M, expQuadClosed (X.cb m n q) (X.zp m n q) (X.R m n)
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n * X.R j n + X.Qpp n * X.R j n ^ 2 / 2))
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n + X.Qpp n * X.R j n))
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (X.Qpp n / 2))
        (-x-t) (X.R m n) ((-x-t) - -(X.R j n))) ?_).mpr ?_
  · intro t ht
    rw [Set.uIoo_of_le hwin, Set.mem_Ioo] at ht
    show pbpIntegrandG X i m n j (-x) t = _
    unfold pbpIntegrandG
    have hAl : (-x-t) - -(X.lam j n) ≤ X.R m n := by
      rw [show (-x-t) - -(X.lam j n) ≤ X.R m n ↔ -x - t ≤ X.R m j from by
            rw [← R_sub_lam_eq X m n j]; constructor <;> intro h <;> linarith]
      have er : X.R i m = (X.σ i + X.σ m)/2 := rfl
      have erj : X.R m j = (X.σ m + X.σ j)/2 := rfl
      have e4 : X.lam i j = (X.σ j - X.σ i)/2 := rfl
      linarith [ht.1]
    have hNe : X.R m n ≤ (-x-t) - -(X.R j n) := by
      rw [show X.R m n ≤ (-x-t) - -(X.R j n) ↔ X.R m n - X.R j n ≤ -x - t from by
            constructor <;> intro h <;> linarith, bConvP_edge_eq X m n j]
      have e1 : X.lam m j = (X.σ j - X.σ m)/2 := rfl
      linarith [ht.2]
    rw [show (-x-t) = ((-x)-t) from by ring] at hAl hNe ⊢
    rw [bConvP_closed_form X m n j ((-x)-t) hz hAl hNe]
  · apply Continuous.intervalIntegrable
    refine Continuous.mul (by fun_prop) (continuous_finsetSum _ ?_)
    intro q _; unfold expQuadClosed Hn; fun_prop

-- zero window [-x+lam_mj, -lam_im]
theorem pbpIntegrandG_neg_ii_zero (X : Mix N M) (i m n j : Fin N) {x : ℝ}
    (hlo : X.lam i j < x) (hhi : x < X.R i j) :
    IntervalIntegrable (pbpIntegrandG X i m n j (-x)) volume (-x + X.lam m j) (-(X.lam i m)) := by
  have hwin : -x + X.lam m j ≤ -(X.lam i m) := by
    have e2 : X.lam i m = (X.σ m - X.σ i)/2 := rfl
    have e3 : X.lam m j = (X.σ j - X.σ m)/2 := rfl
    have e4 : X.lam i j = (X.σ j - X.σ i)/2 := rfl
    linarith
  refine (intervalIntegrable_congr_uIoo (g := fun _ => (0:ℝ)) ?_).mpr (by simp)
  intro t ht
  rw [Set.uIoo_of_le hwin, Set.mem_Ioo] at ht
  show pbpIntegrandG X i m n j (-x) t = 0
  unfold pbpIntegrandG
  have hb0 : bConvP X m n j (-x - t) = 0 := by
    refine eq_zero_of_lt_support_edge (bConvP_support_subset X m n j) ?_
    rw [bConvP_edge_eq X m n j]
    have e1 : X.lam m j = (X.σ j - X.σ m)/2 := rfl
    linarith [ht.1]
  rw [show (-x - t) = ((-x) - t) from by ring, hb0, mul_zero]


theorem neg_halfG_eq (X : Mix N M) (i m n j : Fin N)
    (hz : ∀ q : Fin M, X.zp m n q ≠ 0) {x : ℝ}
    (hlo : X.lam i j < x) (hhi : x < X.R i j) (hlam0 : 0 ≤ X.lam i j)
    (P0 P1 P2 G0 G1 G2 : ℝ)
    (hP0 : P0 = 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(-X.Q0 i m*X.R i m+X.Qpp m*X.R i m^2/2))
    (hP1 : P1 = 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(-X.Q0 i m+X.Qpp m*X.R i m))
    (hP2 : P2 = 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(X.Qpp m/2))
    (hG0 : G0 = 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(-X.Q0 j n*X.R j n+X.Qpp n*X.R j n^2/2))
    (hG1 : G1 = 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(-X.Q0 j n+X.Qpp n*X.R j n))
    (hG2 : G2 = 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(X.Qpp n/2)) :
    (∫ t in (-(X.R i m))..(-x + X.lam m j), pbpIntegrandG X i m n j (-x) t)
      = ∑ q : Fin M, alignedPerPoleVal P0 P1 P2 (X.cb m n q) (X.zp m n q) (X.R m n)
          (X.R j n) G0 G1 G2 (-x) (-(X.R i m)) (-x + X.lam m j) := by
  have hwin : -(X.R i m) ≤ -x + X.lam m j := by
    have e3 : X.lam m j = (X.σ j - X.σ m)/2 := rfl
    have er : X.R i m = (X.σ i + X.σ m)/2 := rfl
    have erij : X.R i j = (X.σ i + X.σ j)/2 := rfl
    linarith [hhi]
  rw [show (∫ t in (-(X.R i m))..(-x + X.lam m j), pbpIntegrandG X i m n j (-x) t)
      = ∑ q : Fin M, ∫ t in (-(X.R i m))..(-x + X.lam m j), (P0 + P1*t + P2*t^2)
          * expQuadClosed (X.cb m n q) (X.zp m n q) (X.R m n) G0 G1 G2
              ((-x)-t) (X.R m n) (((-x)-t) + X.R j n) from ?_]
  · exact Finset.sum_congr rfl fun q _ =>
      aligned_perpole_integral P0 P1 P2 (X.cb m n q) (X.zp m n q) (X.R m n) (X.R j n)
        G0 G1 G2 (-x) (-(X.R i m)) (-x + X.lam m j) (hz q)
  · rw [← intervalIntegral.integral_finsetSum]
    · apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hwin, Set.mem_Icc] at ht
      show pbpIntegrandG X i m n j (-x) t = _
      unfold pbpIntegrandG
      have hAl : ((-x)-t) - -(X.lam j n) ≤ X.R m n := by
        rw [show ((-x)-t) - -(X.lam j n) ≤ X.R m n ↔ (-x) - t ≤ X.R m j from by
              rw [← R_sub_lam_eq X m n j]; constructor <;> intro h <;> linarith]
        have er : X.R i m = (X.σ i + X.σ m)/2 := rfl
        have erj : X.R m j = (X.σ m + X.σ j)/2 := rfl
        have e4 : X.lam i j = (X.σ j - X.σ i)/2 := rfl
        linarith [ht.1]
      have hNe : X.R m n ≤ ((-x)-t) - -(X.R j n) := by
        rw [show X.R m n ≤ ((-x)-t) - -(X.R j n) ↔ X.R m n - X.R j n ≤ (-x) - t from by
              constructor <;> intro h <;> linarith, bConvP_edge_eq X m n j]
        have e1 : X.lam m j = (X.σ j - X.σ m)/2 := rfl
        linarith [ht.2]
      rw [bConvP_closed_form X m n j ((-x)-t) hz hAl hNe, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro q _
      rw [hP0, hP1, hP2, hG0, hG1, hG2]; simp only [sub_neg_eq_add]; ring
    · intro q _; apply Continuous.intervalIntegrable; unfold expQuadClosed Hn; fun_prop

/-- **General-index reflected `x ↦ pbpConv X i m n j (−x)` is `ContDiff` on `(λ_ij, R_ij)`.**  The
`P_im`-window splits at `t** = −x + λ_mj` into an aligned part (`Σ_q alignedPerPoleVal`) and a part
where `bConvP(−x−t)` vanishes by support (`−x−t < −λ_mj`). -/
theorem pbpConv_reflected_contDiffOn (X : Mix N M) (i m n j : Fin N)
    (hz : ∀ q : Fin M, X.zp m n q ≠ 0) (hlam0 : 0 ≤ X.lam i j) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => pbpConv X i m n j (-x)) (Set.Ioo (X.lam i j) (X.R i j)) := by
  set P0 := 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(-X.Q0 i m*X.R i m+X.Qpp m*X.R i m^2/2) with hP0
  set P1 := 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(-X.Q0 i m+X.Qpp m*X.R i m) with hP1
  set P2 := 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(X.Qpp m/2) with hP2
  set G0 := 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(-X.Q0 j n*X.R j n+X.Qpp n*X.R j n^2/2) with hG0
  set G1 := 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(-X.Q0 j n+X.Qpp n*X.R j n) with hG1
  set G2 := 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(X.Qpp n/2) with hG2
  have hcd : ContDiff ℝ (⊤:ℕ∞) (fun x =>
      ∑ q : Fin M, alignedPerPoleVal P0 P1 P2 (X.cb m n q) (X.zp m n q) (X.R m n)
          (X.R j n) G0 G1 G2 (-x) (-(X.R i m)) (-x + X.lam m j)) := by
    apply ContDiff.sum; intro q _; unfold alignedPerPoleVal expQuadClosedPos Hp; fun_prop
  refine ContDiffOn.congr hcd.contDiffOn ?_
  intro x hx
  rw [Set.mem_Ioo] at hx
  rw [pbpConv_eq_intervalIntegral X i m n j (-x)
      (by simp only [Mix.lam, Mix.R]; linarith [X.hσ i])
      ((pbpIntegrandG_neg_ii_aligned X i m n j hz hx.1 hx.2 hlam0).trans
        (pbpIntegrandG_neg_ii_zero X i m n j hx.1 hx.2))]
  rw [show (∫ t in (-(X.R i m))..(-(X.lam i m)),
        2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(X.Q0 i m*(-t-X.R i m)+X.Qpp m*(-t-X.R i m)^2/2)
          * bConvP X m n j ((-x)-t))
      = ∫ t in (-(X.R i m))..(-(X.lam i m)), pbpIntegrandG X i m n j (-x) t from rfl,
      ← intervalIntegral.integral_add_adjacent_intervals
        (pbpIntegrandG_neg_ii_aligned X i m n j hz hx.1 hx.2 hlam0)
        (pbpIntegrandG_neg_ii_zero X i m n j hx.1 hx.2),
      neg_halfG_eq X i m n j hz hx.1 hx.2 hlam0 P0 P1 P2 G0 G1 G2 hP0 hP1 hP2 hG0 hG1 hG2]
  have hzero : (∫ t in (-x + X.lam m j)..(-(X.lam i m)), pbpIntegrandG X i m n j (-x) t) = 0 := by
    have h0 : ∀ᵐ t ∂volume, t ∈ Set.uIoc (-x + X.lam m j) (-(X.lam i m)) →
        pbpIntegrandG X i m n j (-x) t = (fun _ => (0:ℝ)) t := by
      have hwin : -x + X.lam m j ≤ -(X.lam i m) := by
        have e2 : X.lam i m = (X.σ m - X.σ i)/2 := rfl
        have e3 : X.lam m j = (X.σ j - X.σ m)/2 := rfl
        have e4 : X.lam i j = (X.σ j - X.σ i)/2 := rfl
        linarith [hx.1]
      filter_upwards with t ht
      rw [Set.uIoc_of_le hwin, Set.mem_Ioc] at ht
      show pbpIntegrandG X i m n j (-x) t = 0
      unfold pbpIntegrandG
      have hb0 : bConvP X m n j ((-x) - t) = 0 := by
        refine eq_zero_of_lt_support_edge (bConvP_support_subset X m n j) ?_
        rw [bConvP_edge_eq X m n j]
        have e1 : X.lam m j = (X.σ j - X.σ m)/2 := rfl
        linarith [ht.1]
      rw [hb0, mul_zero]
    rw [intervalIntegral.integral_congr_ae h0, intervalIntegral.integral_zero]
  rw [hzero, add_zero]





/-! ### Lower subinterval `(0, λ_ij)` — the middle-aligned regime (whole window aligned) -/

/-- For `y ∈ (−λ_ij, λ_ij)` the whole `P_im`-window `[−R_im, −λ_im]` maps into `bConvP`'s aligned
region — `pbpIntegrandG` is integrable there with no split. -/
theorem pbpIntegrandG_ii_mid (X : Mix N M) (i m n j : Fin N)
    (hz : ∀ q : Fin M, X.zp m n q ≠ 0) {y : ℝ} (hlo : -(X.lam i j) < y) (hhi : y < X.lam i j) :
    IntervalIntegrable (pbpIntegrandG X i m n j y) volume (-(X.R i m)) (-(X.lam i m)) := by
  have hwin : -(X.R i m) ≤ -(X.lam i m) := by
    have : X.lam i m ≤ X.R i m := by simp only [Mix.lam, Mix.R]; linarith [X.hσ i]
    linarith
  refine (intervalIntegrable_congr_uIoo (g := fun t => 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m)
      * (X.Q0 i m * (-t - X.R i m) + X.Qpp m * (-t - X.R i m) ^ 2 / 2) *
      ∑ q : Fin M, expQuadClosed (X.cb m n q) (X.zp m n q) (X.R m n)
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n * X.R j n + X.Qpp n * X.R j n ^ 2 / 2))
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n + X.Qpp n * X.R j n))
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (X.Qpp n / 2))
        (y-t) (X.R m n) ((y-t) - -(X.R j n))) ?_).mpr ?_
  · intro t ht
    rw [Set.uIoo_of_le hwin, Set.mem_Ioo] at ht
    show pbpIntegrandG X i m n j y t = _
    unfold pbpIntegrandG
    have hAl : (y-t) - -(X.lam j n) ≤ X.R m n := by
      rw [show (y-t) - -(X.lam j n) ≤ X.R m n ↔ y - t ≤ X.R m j from by
            rw [← R_sub_lam_eq X m n j]; constructor <;> intro h <;> linarith]
      have er : X.R i m = (X.σ i + X.σ m)/2 := rfl
      have erj : X.R m j = (X.σ m + X.σ j)/2 := rfl
      have e4 : X.lam i j = (X.σ j - X.σ i)/2 := rfl
      linarith [ht.1]
    have hNe : X.R m n ≤ (y-t) - -(X.R j n) := by
      rw [show X.R m n ≤ (y-t) - -(X.R j n) ↔ X.R m n - X.R j n ≤ y - t from by
            constructor <;> intro h <;> linarith, bConvP_edge_eq X m n j]
      have e1 : X.lam m j = (X.σ j - X.σ m)/2 := rfl
      have e2 : X.lam i m = (X.σ m - X.σ i)/2 := rfl
      have e4 : X.lam i j = (X.σ j - X.σ i)/2 := rfl
      linarith [ht.2]
    rw [bConvP_closed_form X m n j (y-t) hz hAl hNe]
  · apply Continuous.intervalIntegrable
    refine Continuous.mul (by fun_prop) (continuous_finsetSum _ ?_)
    intro q _; unfold expQuadClosed Hn; fun_prop

theorem midHalfG_eq (X : Mix N M) (i m n j : Fin N)
    (hz : ∀ q : Fin M, X.zp m n q ≠ 0) {y : ℝ} (hlo : -(X.lam i j) < y) (hhi : y < X.lam i j)
    (P0 P1 P2 G0 G1 G2 : ℝ)
    (hP0 : P0 = 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(-X.Q0 i m*X.R i m+X.Qpp m*X.R i m^2/2))
    (hP1 : P1 = 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(-X.Q0 i m+X.Qpp m*X.R i m))
    (hP2 : P2 = 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(X.Qpp m/2))
    (hG0 : G0 = 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(-X.Q0 j n*X.R j n+X.Qpp n*X.R j n^2/2))
    (hG1 : G1 = 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(-X.Q0 j n+X.Qpp n*X.R j n))
    (hG2 : G2 = 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(X.Qpp n/2)) :
    (∫ t in (-(X.R i m))..(-(X.lam i m)), pbpIntegrandG X i m n j y t)
      = ∑ q : Fin M, alignedPerPoleVal P0 P1 P2 (X.cb m n q) (X.zp m n q) (X.R m n)
          (X.R j n) G0 G1 G2 y (-(X.R i m)) (-(X.lam i m)) := by
  have hwin : -(X.R i m) ≤ -(X.lam i m) := by
    have : X.lam i m ≤ X.R i m := by simp only [Mix.lam, Mix.R]; linarith [X.hσ i]
    linarith
  rw [show (∫ t in (-(X.R i m))..(-(X.lam i m)), pbpIntegrandG X i m n j y t)
      = ∑ q : Fin M, ∫ t in (-(X.R i m))..(-(X.lam i m)), (P0 + P1*t + P2*t^2)
          * expQuadClosed (X.cb m n q) (X.zp m n q) (X.R m n) G0 G1 G2
              (y-t) (X.R m n) ((y-t) + X.R j n) from ?_]
  · exact Finset.sum_congr rfl fun q _ =>
      aligned_perpole_integral P0 P1 P2 (X.cb m n q) (X.zp m n q) (X.R m n) (X.R j n)
        G0 G1 G2 y (-(X.R i m)) (-(X.lam i m)) (hz q)
  · rw [← intervalIntegral.integral_finsetSum]
    · apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hwin, Set.mem_Icc] at ht
      show pbpIntegrandG X i m n j y t = _
      unfold pbpIntegrandG
      have hAl : (y-t) - -(X.lam j n) ≤ X.R m n := by
        rw [show (y-t) - -(X.lam j n) ≤ X.R m n ↔ y - t ≤ X.R m j from by
              rw [← R_sub_lam_eq X m n j]; constructor <;> intro h <;> linarith]
        have er : X.R i m = (X.σ i + X.σ m)/2 := rfl
        have erj : X.R m j = (X.σ m + X.σ j)/2 := rfl
        have e4 : X.lam i j = (X.σ j - X.σ i)/2 := rfl
        linarith [ht.1]
      have hNe : X.R m n ≤ (y-t) - -(X.R j n) := by
        rw [show X.R m n ≤ (y-t) - -(X.R j n) ↔ X.R m n - X.R j n ≤ y - t from by
              constructor <;> intro h <;> linarith, bConvP_edge_eq X m n j]
        have e1 : X.lam m j = (X.σ j - X.σ m)/2 := rfl
        have e2 : X.lam i m = (X.σ m - X.σ i)/2 := rfl
        have e4 : X.lam i j = (X.σ j - X.σ i)/2 := rfl
        linarith [ht.2]
      rw [bConvP_closed_form X m n j (y-t) hz hAl hNe, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro q _
      rw [hP0, hP1, hP2, hG0, hG1, hG2]; simp only [sub_neg_eq_add]; ring
    · intro q _; apply Continuous.intervalIntegrable; unfold expQuadClosed Hn; fun_prop

/-- **`pbpConv X i m n j` is `ContDiff` on the middle interval `(−λ_ij, λ_ij)`** — there the whole
`P_im`-window is aligned, so `pbpConv` is a single `Σ_q alignedPerPoleVal`, no split, no reflection. -/
theorem pbpConv_contDiffOn_midAligned (X : Mix N M) (i m n j : Fin N)
    (hz : ∀ q : Fin M, X.zp m n q ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => pbpConv X i m n j y) (Set.Ioo (-(X.lam i j)) (X.lam i j)) := by
  set P0 := 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(-X.Q0 i m*X.R i m+X.Qpp m*X.R i m^2/2) with hP0
  set P1 := 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(-X.Q0 i m+X.Qpp m*X.R i m) with hP1
  set P2 := 2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(X.Qpp m/2) with hP2
  set G0 := 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(-X.Q0 j n*X.R j n+X.Qpp n*X.R j n^2/2) with hG0
  set G1 := 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(-X.Q0 j n+X.Qpp n*X.R j n) with hG1
  set G2 := 2*Real.pi*Real.sqrt (X.ρ j*X.ρ n)*(X.Qpp n/2) with hG2
  have hcd : ContDiff ℝ (⊤:ℕ∞) (fun y =>
      ∑ q : Fin M, alignedPerPoleVal P0 P1 P2 (X.cb m n q) (X.zp m n q) (X.R m n)
          (X.R j n) G0 G1 G2 y (-(X.R i m)) (-(X.lam i m))) := by
    apply ContDiff.sum; intro q _; unfold alignedPerPoleVal expQuadClosedPos Hp; fun_prop
  refine ContDiffOn.congr hcd.contDiffOn ?_
  intro y hy
  rw [Set.mem_Ioo] at hy
  rw [pbpConv_eq_intervalIntegral X i m n j y
      (by simp only [Mix.lam, Mix.R]; linarith [X.hσ i])
      (pbpIntegrandG_ii_mid X i m n j hz hy.1 hy.2)]
  rw [show (∫ t in (-(X.R i m))..(-(X.lam i m)),
        2*Real.pi*Real.sqrt (X.ρ i*X.ρ m)*(X.Q0 i m*(-t-X.R i m)+X.Qpp m*(-t-X.R i m)^2/2)
          * bConvP X m n j (y-t))
      = ∫ t in (-(X.R i m))..(-(X.lam i m)), pbpIntegrandG X i m n j y t from rfl,
      midHalfG_eq X i m n j hz hy.1 hy.2 P0 P1 P2 G0 G1 G2 hP0 hP1 hP2 hG0 hG1 hG2]

/-! ### General-N assembly — the `𝒲_ij` double sum and its odd-part DCF -/

/-- **The real-space `𝒲_ij` matrix entry** — `(𝒬⁻ ⋆ ℬ ⋆ (𝒬⁻)ᵀ)_ij`, expanded via `𝒬⁻ = δ − P`
into `ℬ_ij − Σ_n ℬ_in⋆P_jn − Σ_m P_im⋆ℬ_mj + Σ_{m,n} P_im⋆ℬ_mn⋆P_jn` (`fmsa_double_prop._build_closed_form`). -/
noncomputable def Wmix (X : Mix N M) (i j : Fin N) : ℝ → ℝ := fun x =>
  bMixEntry X i j x
    - (∑ n : Fin N, bConvP X i n j x)
    - (∑ m : Fin N, ((pMixEntry X i m) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (bMixEntry X m j)) x)
    + (∑ m : Fin N, ∑ n : Fin N, pbpConv X i m n j x)

/-- **`2π√(ρᵢρⱼ)·r·c^(1)_ij(r) = 𝒲_ij(r) − 𝒲_ij(−r)`** — the first-order inner DCF, odd part. -/
noncomputable def dcfOdd (X : Mix N M) (i j : Fin N) : ℝ → ℝ := fun x => Wmix X i j x - Wmix X i j (-x)

/-- `bMixEntry` vanishes strictly below its support start `R_ij`. -/
theorem bMixEntry_eq_zero_of_lt (X : Mix N M) (i j : Fin N) {x : ℝ} (hx : x < X.R i j) :
    bMixEntry X i j x = 0 := eq_zero_of_lt_support_edge (bMixEntry_support_subset X i j) hx

/-- **General-N inner-DCF smoothness on the UPPER subinterval `(λ_ij, R_ij)` (`0 ≤ λ_ij`).**  Every
term is a finite `poly×exp` there (breakpoints only at `{±λ_ij, ±R_ij}`); the reflected two-fold terms
vanish by support, leaving `−Σ_n ℬ_in⋆P_jn − Σ_m P_im⋆ℬ_mj + Σ_{m,n}[pbpConv(r) − pbpConv(−r)]`,
each `ContDiffOn`.  No aggregate cancellation — the mediated species cancel term-by-term. -/
theorem dcfOdd_contDiffOn_upper (X : Mix N M) (i j : Fin N)
    (hz : ∀ a b : Fin N, ∀ q : Fin M, X.zp a b q ≠ 0) (hlam0 : 0 ≤ X.lam i j) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dcfOdd X i j) (Set.Ioo (X.lam i j) (X.R i j)) := by
  have hsub : Set.Ioo (X.lam i j) (X.R i j) ⊆ Set.Ioo (-(X.lam i j)) (X.R i j) :=
    Set.Ioo_subset_Ioo (by linarith) le_rfl
  have hbc : ContDiffOn ℝ (⊤:ℕ∞) (fun x => ∑ n : Fin N, bConvP X i n j x)
      (Set.Ioo (X.lam i j) (X.R i j)) :=
    ContDiffOn.sum fun n _ => (bConvP_contDiffOn_aligned X i n j (hz i n)).mono hsub
  have hpc : ContDiffOn ℝ (⊤:ℕ∞)
      (fun x => ∑ m : Fin N, ((pMixEntry X i m) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (bMixEntry X m j)) x)
      (Set.Ioo (X.lam i j) (X.R i j)) :=
    ContDiffOn.sum fun m _ => pConvB_contDiffOn_aligned X i m j (hz m j)
  have hpp : ContDiffOn ℝ (⊤:ℕ∞) (fun x => ∑ m : Fin N, ∑ n : Fin N, pbpConv X i m n j x)
      (Set.Ioo (X.lam i j) (X.R i j)) :=
    ContDiffOn.sum fun m _ => ContDiffOn.sum fun n _ =>
      pbpConv_forward_contDiffOn X i m n j (hz m n) hlam0
  have hppn : ContDiffOn ℝ (⊤:ℕ∞) (fun x => ∑ m : Fin N, ∑ n : Fin N, pbpConv X i m n j (-x))
      (Set.Ioo (X.lam i j) (X.R i j)) :=
    ContDiffOn.sum fun m _ => ContDiffOn.sum fun n _ =>
      pbpConv_reflected_contDiffOn X i m n j (hz m n) hlam0
  refine ((hbc.neg.sub hpc).add hpp).sub hppn |>.congr ?_
  intro x hx
  rw [Set.mem_Ioo] at hx
  have hbMx : bMixEntry X i j x = 0 := bMixEntry_eq_zero_of_lt X i j hx.2
  have hbMnx : bMixEntry X i j (-x) = 0 :=
    bMixEntry_eq_zero_of_lt X i j (by linarith [X.R_pos i j] : -x < X.R i j)
  have hbcn : (∑ n : Fin N, bConvP X i n j (-x)) = 0 :=
    Finset.sum_eq_zero fun n _ => bConvP_eq_zero_of_lt X i n j (by linarith [hx.1])
  have hpcn : (∑ m : Fin N, ((pMixEntry X i m) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (bMixEntry X m j)) (-x)) = 0 :=
    Finset.sum_eq_zero fun m _ => pConvB_eq_zero_of_lt X i m j (by linarith [hx.1, hlam0])
  show dcfOdd X i j x = _
  unfold dcfOdd Wmix
  rw [hbMx, hbMnx, hbcn, hpcn]; ring



/-- **General-N inner-DCF smoothness on the LOWER subinterval `(0, λ_ij)`.**  Below the knot the
forward `P⋆ℬ` and both `ℬ_ij` terms vanish by support; the whole `P_im`-window is aligned, so
`pbpConv(±x)` and the reflected `ℬ_in⋆P_jn(−x)` are single smooth pieces.  Empty (hence vacuous) for
like pairs (`λ_ij = 0`); the genuine content is unlike pairs. -/
theorem dcfOdd_contDiffOn_lower (X : Mix N M) (i j : Fin N)
    (hz : ∀ a b : Fin N, ∀ q : Fin M, X.zp a b q ≠ 0) (hlam0 : 0 ≤ X.lam i j) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dcfOdd X i j) (Set.Ioo 0 (X.lam i j)) := by
  have hlamR : X.lam i j ≤ X.R i j := by simp only [Mix.lam, Mix.R]; linarith [X.hσ i]
  have hsub_bc : Set.Ioo (0:ℝ) (X.lam i j) ⊆ Set.Ioo (-(X.lam i j)) (X.R i j) :=
    Set.Ioo_subset_Ioo (by linarith) hlamR
  have hsub_pp : Set.Ioo (0:ℝ) (X.lam i j) ⊆ Set.Ioo (-(X.lam i j)) (X.lam i j) :=
    Set.Ioo_subset_Ioo (by linarith) le_rfl
  have hmap_bc : Set.MapsTo (fun x => -x) (Set.Ioo (0:ℝ) (X.lam i j)) (Set.Ioo (-(X.lam i j)) (X.R i j)) := by
    intro x hx; rw [Set.mem_Ioo] at hx ⊢
    exact ⟨by linarith [hx.2], by linarith [X.R_pos i j, hx.1]⟩
  have hmap_pp : Set.MapsTo (fun x => -x) (Set.Ioo (0:ℝ) (X.lam i j)) (Set.Ioo (-(X.lam i j)) (X.lam i j)) := by
    intro x hx; rw [Set.mem_Ioo] at hx ⊢
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hbc : ContDiffOn ℝ (⊤:ℕ∞) (fun x => ∑ n : Fin N, bConvP X i n j x)
      (Set.Ioo 0 (X.lam i j)) :=
    ContDiffOn.sum fun n _ => (bConvP_contDiffOn_aligned X i n j (hz i n)).mono hsub_bc
  have hbcn : ContDiffOn ℝ (⊤:ℕ∞) (fun x => ∑ n : Fin N, bConvP X i n j (-x))
      (Set.Ioo 0 (X.lam i j)) :=
    ContDiffOn.sum fun n _ =>
      (bConvP_contDiffOn_aligned X i n j (hz i n)).comp contDiff_neg.contDiffOn hmap_bc
  have hpp : ContDiffOn ℝ (⊤:ℕ∞) (fun x => ∑ m : Fin N, ∑ n : Fin N, pbpConv X i m n j x)
      (Set.Ioo 0 (X.lam i j)) :=
    ContDiffOn.sum fun m _ => ContDiffOn.sum fun n _ =>
      (pbpConv_contDiffOn_midAligned X i m n j (hz m n)).mono hsub_pp
  have hppn : ContDiffOn ℝ (⊤:ℕ∞) (fun x => ∑ m : Fin N, ∑ n : Fin N, pbpConv X i m n j (-x))
      (Set.Ioo 0 (X.lam i j)) :=
    ContDiffOn.sum fun m _ => ContDiffOn.sum fun n _ =>
      (pbpConv_contDiffOn_midAligned X i m n j (hz m n)).comp contDiff_neg.contDiffOn hmap_pp
  refine (((hbc.neg.add hbcn).add hpp).sub hppn).congr ?_
  intro x hx
  rw [Set.mem_Ioo] at hx
  have hbMx : bMixEntry X i j x = 0 := bMixEntry_eq_zero_of_lt X i j (by linarith [hlamR])
  have hbMnx : bMixEntry X i j (-x) = 0 :=
    bMixEntry_eq_zero_of_lt X i j (by linarith [X.R_pos i j])
  have hpcx : (∑ m : Fin N, ((pMixEntry X i m) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (bMixEntry X m j)) x) = 0 :=
    Finset.sum_eq_zero fun m _ => pConvB_eq_zero_of_lt X i m j hx.2
  have hpcnx : (∑ m : Fin N, ((pMixEntry X i m) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (bMixEntry X m j)) (-x)) = 0 :=
    Finset.sum_eq_zero fun m _ => pConvB_eq_zero_of_lt X i m j (by linarith [hx.1])
  show dcfOdd X i j x = _
  unfold dcfOdd Wmix
  rw [hbMx, hbMnx, hpcx, hpcnx]; ring

/-- **Capstone — like pairs are smooth on the WHOLE core `(0, R_ii)`.**  For a like pair `λ_ii = 0`,
so the lower subinterval is empty and `dcfOdd_contDiffOn_upper` already covers all of `(0, R_ii)`:
the like-species inner DCF has NO interior knot (for every `N`). -/
theorem dcfOdd_contDiffOn_like (X : Mix N M) (i : Fin N)
    (hz : ∀ a b : Fin N, ∀ q : Fin M, X.zp a b q ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dcfOdd X i i) (Set.Ioo 0 (X.R i i)) := by
  have h0 : X.lam i i = 0 := by simp only [Mix.lam]; ring
  have h := dcfOdd_contDiffOn_upper X i i hz (le_of_eq h0.symm)
  rwa [h0] at h


end FMSA.MixtureDCFSmooth
