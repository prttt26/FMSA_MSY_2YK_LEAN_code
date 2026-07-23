/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Task OZ.18 — Hard-sphere `λ_ij` kink in the White-Bear FMT DCF

`get_HS_FMT` (`fmsa_ga_matrix_mix.py:1142-1212`) evaluates the White-Bear FMT pair DCF
`c^HS_ij(r)`, but first **clamps** `r` up to the size-asymmetry cutoff
`λ = |λ_ij| = |σᵢ − σⱼ|/2 = |Rᵢ − Rⱼ|` when `r < λ` (lines 1163-1165):

```python
lam_cut = abs(self.lambda_ij[i, j])
if lam_cut > 0.0 and r < lam_cut:
    r = lam_cut
```

So for an **unlike** pair the DCF is *constant* (`= F(λ)`) below `λ` and the White-Bear
rational form `F(r)` above.  The two one-sided slopes are `0` (constant piece) and `F'(λ)`
(rational piece); when they differ, `c^HS_ij` has a genuine **C⁰ slope kink** at `λ` — the FMT
realization of the Lebowitz two-piece PY structure.

## What is proved here

The kink is a property of the *clamp*, independent of the specific form of `F`.  We isolate that:

* `clampedBelow F λ r := if r < λ then F λ else F r` — the "clamp to `λ` from below" of any `F`.
* `clampedBelow_continuousAt` : continuous at `λ` whenever `F` is (**C⁰**).
* `clampedBelow_hasDerivWithinAt_Iic` / `_Ici` : the one-sided derivatives at `λ` are exactly
  `0` (below) and `F'(λ)` (above).
* `clampedBelow_not_differentiableAt` : if `F'(λ) ≠ 0` the clamp is **not differentiable** at `λ`
  (a genuine kink), because a two-sided derivative would have to equal both `0` and `F'(λ)`.

Then we instantiate `F` with the faithful White-Bear core `cHS_core` (a rational function of `r`,
mirroring the `-(χ₃·… + χ₂·… + χ₁·… + …)` return of `get_HS_FMT`) and specialize to `λ = |Rᵢ−Rⱼ|`:

* `cHS_FMT_continuousAt` : **C⁰** at the cutoff for unlike pairs (`Rᵢ ≠ Rⱼ`).
* `cHS_FMT_not_differentiableAt` : genuine kink, **conditional on `F'(λ) ≠ 0`**.

## The slope is now in closed form (`hslope` discharged)

**Update (2026-07-16).** `F'(λ) ≠ 0` is *not* an opaque state-point fact after all.  Evaluating the
core slope at the cutoff, **every `χ₃/χ₂/χ₁` contribution cancels identically** (the `χ₃`, `χ₂` and
`χ₁` groups each contribute exactly `0` to `F(λ) − λF'(λ)`, using only `λ² = (Rᵢ−Rⱼ)²`), leaving

    F'(λ) = 2·(χ₂₂ − χ₁/(4π))        (`cHS_core_deriv_at_cutoff`)

— independent of `Rᵢ, Rⱼ, χ₀, χ₂, χ₃`.  Hence the kink hypothesis is *equivalent* to the elementary
scalar condition `χ₂₂ ≠ χ₁/(4π)` (`cHS_core_deriv_at_cutoff_ne_zero_iff`), and the kink itself is
proved from it directly (`cHS_FMT_not_differentiableAt_of_chi`) — no numerical input.

This is sharp, not merely sufficient: the kink genuinely *fails* (the FMT DCF is differentiable at
`λ`) exactly when `χ₂₂ = χ₁/(4π)`, so no unconditional statement is possible.

Status: ✓ DONE — continuity, both one-sided slopes, the closed-form slope, and the kink from
`χ₂₂ ≠ χ₁/(4π)`, all unconditional and axiom-clean.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

open Set

namespace FMSA.HSKink

/-!
## The abstract "clamp from below" and its kink
-/

/-- `F` clamped to its value at `lam` for arguments below `lam`:
`clampedBelow F lam r = F lam` if `r < lam`, else `F r`.
Mirrors the `if r < |λ_ij|: r = |λ_ij|` clamp of `get_HS_FMT`. -/
noncomputable def clampedBelow (F : ℝ → ℝ) (lam : ℝ) : ℝ → ℝ :=
  fun r => if r < lam then F lam else F r

/-- The clamp equals `F ∘ (max · lam)`. -/
theorem clampedBelow_eq_max (F : ℝ → ℝ) (lam r : ℝ) :
    clampedBelow F lam r = F (max r lam) := by
  simp only [clampedBelow]
  by_cases h : r < lam
  · rw [if_pos h, max_eq_right (le_of_lt h)]
  · rw [if_neg h, max_eq_left (not_lt.mp h)]

/-- On `(-∞, lam]` the clamp is the constant `F lam`. -/
theorem clampedBelow_eqOn_Iic (F : ℝ → ℝ) (lam : ℝ) :
    EqOn (clampedBelow F lam) (fun _ => F lam) (Iic lam) := by
  intro r hr
  have hr' : r ≤ lam := hr
  simp only [clampedBelow]
  by_cases h : r < lam
  · rw [if_pos h]
  · have : r = lam := le_antisymm hr' (not_lt.mp h)
    rw [if_neg h, this]

/-- On `[lam, ∞)` the clamp equals `F`. -/
theorem clampedBelow_eqOn_Ici (F : ℝ → ℝ) (lam : ℝ) :
    EqOn (clampedBelow F lam) F (Ici lam) := by
  intro r hr
  have hr' : lam ≤ r := hr
  simp only [clampedBelow]
  rw [if_neg (not_lt.mpr hr')]

/-- **C⁰.** The clamp is continuous at `lam` whenever `F` is. -/
theorem clampedBelow_continuousAt (F : ℝ → ℝ) {lam : ℝ} (hF : ContinuousAt F lam) :
    ContinuousAt (clampedBelow F lam) lam := by
  set m : ℝ → ℝ := fun r => max r lam with hm
  have hmax : ContinuousAt m lam := (continuous_id.max continuous_const).continuousAt
  have hml : m lam = lam := by simp [hm, max_self]
  have hval : ContinuousAt F (m lam) := by rw [hml]; exact hF
  have hcomp : ContinuousAt (F ∘ m) lam := hval.comp hmax
  have heq : clampedBelow F lam = F ∘ m := funext (fun r => clampedBelow_eq_max F lam r)
  rw [heq]; exact hcomp

/-- **Left slope `0`.** The clamp is constant on `Iic lam`, so its within-derivative there is `0`. -/
theorem clampedBelow_hasDerivWithinAt_Iic (F : ℝ → ℝ) (lam : ℝ) :
    HasDerivWithinAt (clampedBelow F lam) 0 (Iic lam) lam :=
  (hasDerivWithinAt_const lam (Iic lam) (F lam)).congr
    (clampedBelow_eqOn_Iic F lam) (clampedBelow_eqOn_Iic F lam self_mem_Iic)

/-- **Right slope `F'(lam)`.** The clamp equals `F` on `Ici lam`. -/
theorem clampedBelow_hasDerivWithinAt_Ici (F : ℝ → ℝ) {lam D : ℝ} (hF : HasDerivAt F D lam) :
    HasDerivWithinAt (clampedBelow F lam) D (Ici lam) lam :=
  (hF.hasDerivWithinAt).congr (clampedBelow_eqOn_Ici F lam) (clampedBelow_eqOn_Ici F lam self_mem_Ici)

/-- **The kink.** If `F` has a nonzero derivative at `lam`, the clamp is *not* differentiable at
`lam`: a two-sided derivative `L` would restrict to `L = 0` on `Iic` and `L = F'(lam)` on `Ici`. -/
theorem clampedBelow_not_differentiableAt (F : ℝ → ℝ) {lam D : ℝ}
    (hF : HasDerivAt F D lam) (hD : D ≠ 0) :
    ¬ DifferentiableAt ℝ (clampedBelow F lam) lam := by
  intro hdiff
  have hL := hdiff.hasDerivAt
  set L := deriv (clampedBelow F lam) lam with hLdef
  have hLIic : HasDerivWithinAt (clampedBelow F lam) L (Iic lam) lam := hL.hasDerivWithinAt
  have hLIci : HasDerivWithinAt (clampedBelow F lam) L (Ici lam) lam := hL.hasDerivWithinAt
  have hs_iic : UniqueDiffWithinAt ℝ (Iic lam) lam := uniqueDiffOn_Iic lam lam self_mem_Iic
  have hs_ici : UniqueDiffWithinAt ℝ (Ici lam) lam := uniqueDiffOn_Ici lam lam self_mem_Ici
  have h0 : L = 0 := by
    rw [← hLIic.derivWithin hs_iic, (clampedBelow_hasDerivWithinAt_Iic F lam).derivWithin hs_iic]
  have hd : L = D := by
    rw [← hLIci.derivWithin hs_ici, (clampedBelow_hasDerivWithinAt_Ici F hF).derivWithin hs_ici]
  exact hD (by rw [← hd, h0])

/-!
## The concrete White-Bear FMT core `F(r)` and its cutoff kink
-/

/-- Polynomial numerator of the core: `cHS_core r = -(cHS_num r)/r - χ0` for `r ≠ 0`.
(The `χ0` argument is carried only to match `cHS_core`'s signature; it is the separated
constant term and does not appear in the numerator.) -/
noncomputable def cHS_num (χ0 χ1 χ2 χ3 χ22 Ri Rj : ℝ) (r : ℝ) : ℝ :=
  χ3 * (Real.pi/6) * (-(3/2)*(Ri^2-Rj^2)^2 + 4*r*(Ri^3+Rj^3) - 3*r^2*(Ri^2+Rj^2) + r^4/2)
  + χ2 * Real.pi * (-(Ri+Rj)*(Ri-Rj)^2 + 2*r*(Ri^2+Rj^2) - r^2*(Ri+Rj))
  + χ1 * (-(1/4)*(Ri-Rj)^2 + (1/2)*r*(Ri+Rj) - (1/4)*r^2)
  + (χ22 - χ1/(4*Real.pi)) * ((Ri-Rj)^2 - r^2)

/-- The White-Bear FMT hard-sphere core `F(r)` (before clamping), mirroring the `return -(…)`
of `get_HS_FMT` (`fmsa_ga_matrix_mix.py:1206-1212`) with `V`, `S`, `Rterm`, `Rprime` inlined and
the density-dependent coefficients `χ₀…χ₃, χ₂₂` taken as parameters. -/
noncomputable def cHS_core (χ0 χ1 χ2 χ3 χ22 Ri Rj : ℝ) (r : ℝ) : ℝ :=
  -(χ3 * (Real.pi/(6*r)) * (-(3/2)*(Ri^2-Rj^2)^2 + 4*r*(Ri^3+Rj^3) - 3*r^2*(Ri^2+Rj^2) + r^4/2)
    + χ2*(Real.pi/r)*(-(Ri+Rj)*(Ri-Rj)^2 + 2*r*(Ri^2+Rj^2) - r^2*(Ri+Rj))
    + χ1*(-(1/4)*(Ri-Rj)^2 + (1/2)*r*(Ri+Rj) - (1/4)*r^2)/r
    + (χ22 - χ1/(4*Real.pi))*(((Ri-Rj)^2 - r^2)/r)
    + χ0)

theorem cHS_num_differentiable (χ0 χ1 χ2 χ3 χ22 Ri Rj : ℝ) :
    Differentiable ℝ (cHS_num χ0 χ1 χ2 χ3 χ22 Ri Rj) := by
  unfold cHS_num; fun_prop

/-- For `r ≠ 0` the core is a single rational function `-(polynomial)/r − χ0`. -/
theorem cHS_core_eq_num (χ0 χ1 χ2 χ3 χ22 Ri Rj : ℝ) {r : ℝ} (hr : r ≠ 0) :
    cHS_core χ0 χ1 χ2 χ3 χ22 Ri Rj r = -(cHS_num χ0 χ1 χ2 χ3 χ22 Ri Rj r)/r - χ0 := by
  simp only [cHS_core, cHS_num]
  field_simp
  ring

/-- The core is differentiable wherever `r ≠ 0` (in particular at the cutoff of an unlike pair). -/
theorem cHS_core_differentiableAt (χ0 χ1 χ2 χ3 χ22 Ri Rj : ℝ) {lam : ℝ} (hlam : lam ≠ 0) :
    DifferentiableAt ℝ (cHS_core χ0 χ1 χ2 χ3 χ22 Ri Rj) lam := by
  have hdiv : DifferentiableAt ℝ
      (fun r => -(cHS_num χ0 χ1 χ2 χ3 χ22 Ri Rj r)/r - χ0) lam := by
    apply DifferentiableAt.sub _ (differentiableAt_const _)
    exact ((cHS_num_differentiable χ0 χ1 χ2 χ3 χ22 Ri Rj lam).neg).div differentiableAt_id hlam
  refine hdiv.congr_of_eventuallyEq ?_
  filter_upwards [eventually_ne_nhds hlam] with r hr
  exact cHS_core_eq_num χ0 χ1 χ2 χ3 χ22 Ri Rj hr

/-- The clamped FMT DCF `c^HS_ij`: the White-Bear core clamped from below at the cutoff
`λ = |Rᵢ − Rⱼ| = |σᵢ − σⱼ|/2`.  Faithful to `get_HS_FMT`. -/
noncomputable def cHS_FMT (χ0 χ1 χ2 χ3 χ22 Ri Rj : ℝ) : ℝ → ℝ :=
  clampedBelow (cHS_core χ0 χ1 χ2 χ3 χ22 Ri Rj) |Ri - Rj|

/-- **OZ.18 (C⁰).** For an unlike pair (`Rᵢ ≠ Rⱼ`), the clamped FMT DCF is continuous at the
cutoff `λ = |Rᵢ − Rⱼ|`. -/
theorem cHS_FMT_continuousAt (χ0 χ1 χ2 χ3 χ22 Ri Rj : ℝ) (hne : Ri ≠ Rj) :
    ContinuousAt (cHS_FMT χ0 χ1 χ2 χ3 χ22 Ri Rj) |Ri - Rj| := by
  have hlam : |Ri - Rj| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hne)
  exact clampedBelow_continuousAt _ (cHS_core_differentiableAt χ0 χ1 χ2 χ3 χ22 Ri Rj hlam).continuousAt

/-- **OZ.18 (left slope `0`).** Below the cutoff the DCF is constant. -/
theorem cHS_FMT_hasDerivWithinAt_Iic (χ0 χ1 χ2 χ3 χ22 Ri Rj : ℝ) :
    HasDerivWithinAt (cHS_FMT χ0 χ1 χ2 χ3 χ22 Ri Rj) 0 (Iic |Ri - Rj|) |Ri - Rj| :=
  clampedBelow_hasDerivWithinAt_Iic _ _

/-- **OZ.18 (right slope `= F'(λ)`).** Above the cutoff the DCF equals the White-Bear core, so its
one-sided derivative there is the core slope. -/
theorem cHS_FMT_hasDerivWithinAt_Ici (χ0 χ1 χ2 χ3 χ22 Ri Rj : ℝ) (hne : Ri ≠ Rj) :
    HasDerivWithinAt (cHS_FMT χ0 χ1 χ2 χ3 χ22 Ri Rj)
      (deriv (cHS_core χ0 χ1 χ2 χ3 χ22 Ri Rj) |Ri - Rj|) (Ici |Ri - Rj|) |Ri - Rj| := by
  have hlam : |Ri - Rj| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hne)
  exact clampedBelow_hasDerivWithinAt_Ici _ (cHS_core_differentiableAt χ0 χ1 χ2 χ3 χ22 Ri Rj hlam).hasDerivAt

/-- **OZ.18 (genuine kink).** For an unlike pair, if the White-Bear core has nonzero slope at the
cutoff, the clamped FMT DCF is **not differentiable** at `λ`: left slope `0` ≠ right slope `F'(λ)`.
Together with `cHS_FMT_continuousAt` this is the genuine C⁰ kink.  (`hslope` is no longer an opaque
numerical input — see `cHS_core_deriv_at_cutoff` below, which evaluates it in closed form, and
`cHS_FMT_not_differentiableAt_of_chi`, which discharges it from `χ₂₂ ≠ χ₁/(4π)`.) -/
theorem cHS_FMT_not_differentiableAt (χ0 χ1 χ2 χ3 χ22 Ri Rj : ℝ) (hne : Ri ≠ Rj)
    (hslope : deriv (cHS_core χ0 χ1 χ2 χ3 χ22 Ri Rj) |Ri - Rj| ≠ 0) :
    ¬ DifferentiableAt ℝ (cHS_FMT χ0 χ1 χ2 χ3 χ22 Ri Rj) |Ri - Rj| := by
  have hlam : |Ri - Rj| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hdiff := cHS_core_differentiableAt χ0 χ1 χ2 χ3 χ22 Ri Rj hlam
  exact clampedBelow_not_differentiableAt _ hdiff.hasDerivAt hslope

/-!
## OZ.18 (slope) — the cutoff slope in closed form: `F'(λ) = 2(χ₂₂ − χ₁/(4π))`

`hslope` is **not** an opaque state-point fact. At the cutoff `r = λ` (where `λ² = (Rᵢ−Rⱼ)²`) the
entire `χ₃/χ₂/χ₁` polynomial structure of the White-Bear core **cancels identically**, leaving

    F'(λ) = 2·(χ₂₂ − χ₁/(4π))

— independent of `Rᵢ, Rⱼ, χ₀, χ₂, χ₃`.  So the kink hypothesis is *equivalent* to the elementary
scalar condition `χ₂₂ ≠ χ₁/(4π)`.
-/

/-- `r⁰`-coefficient of the polynomial `cHS_num`, with the combined coefficient `E = χ₂₂ − χ₁/(4π)`
kept **abstract** (this is what makes the cancellation a clean polynomial identity). -/
noncomputable def chiA0 (χ1 χ2 χ3 E Ri Rj : ℝ) : ℝ :=
  χ3*(Real.pi/6)*(-(3/2)*(Ri^2-Rj^2)^2) + χ2*Real.pi*(-(Ri+Rj)*(Ri-Rj)^2)
  + χ1*(-(1/4)*(Ri-Rj)^2) + E*(Ri-Rj)^2

/-- `r¹`-coefficient of `cHS_num`. -/
noncomputable def chiA1 (χ1 χ2 χ3 Ri Rj : ℝ) : ℝ :=
  χ3*(Real.pi/6)*(4*(Ri^3+Rj^3)) + χ2*Real.pi*(2*(Ri^2+Rj^2)) + χ1*((1/2)*(Ri+Rj))

/-- `r²`-coefficient of `cHS_num` (the `r³` coefficient vanishes). -/
noncomputable def chiA2 (χ1 χ2 χ3 E Ri Rj : ℝ) : ℝ :=
  χ3*(Real.pi/6)*(-3*(Ri^2+Rj^2)) + χ2*Real.pi*(-(Ri+Rj)) + χ1*(-(1/4)) - E

/-- `r⁴`-coefficient of `cHS_num`. -/
noncomputable def chiA4 (χ3 : ℝ) : ℝ := χ3*(Real.pi/12)

/-- Derivative of the Laurent shape `x ↦ -(a₀/x + a₁ + a₂x + a₄x³) − c` at `x = r ≠ 0`. -/
theorem hasDerivAt_neg_laurent (a0 a1 a2 a4 c : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun x : ℝ => -(a0 * x⁻¹ + a1 + a2 * x + a4 * x ^ 3) - c)
      (a0 / r ^ 2 - a2 - 3 * a4 * r ^ 2) r := by
  have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-(r ^ 2)⁻¹) r := hasDerivAt_inv hr
  have h0 : HasDerivAt (fun x : ℝ => a0 * x⁻¹) (a0 * -(r ^ 2)⁻¹) r := hinv.const_mul a0
  have h1 : HasDerivAt (fun x : ℝ => a0 * x⁻¹ + a1) (a0 * -(r ^ 2)⁻¹) r := h0.add_const a1
  have h2 : HasDerivAt (fun x : ℝ => a2 * x) a2 r := by
    simpa using (hasDerivAt_id r).const_mul a2
  have h3 : HasDerivAt (fun x : ℝ => a4 * x ^ 3) (a4 * (3 * r ^ 2)) r := by
    simpa using (hasDerivAt_pow 3 r).const_mul a4
  have hsum := (((h1.add h2).add h3).neg).sub_const c
  have hval : -(a0 * -(r ^ 2)⁻¹ + a2 + a4 * (3 * r ^ 2)) = a0 / r ^ 2 - a2 - 3 * a4 * r ^ 2 := by
    ring
  rwa [hval] at hsum

/-- Away from `r = 0` the core is the Laurent form `-(a₀/r + a₁ + a₂r + a₄r³) − χ₀`. -/
theorem cHS_core_eq_laurent (χ0 χ1 χ2 χ3 χ22 Ri Rj : ℝ) {r : ℝ} (hr : r ≠ 0) :
    cHS_core χ0 χ1 χ2 χ3 χ22 Ri Rj r
      = -(chiA0 χ1 χ2 χ3 (χ22 - χ1/(4*Real.pi)) Ri Rj * r⁻¹ + chiA1 χ1 χ2 χ3 Ri Rj
          + chiA2 χ1 χ2 χ3 (χ22 - χ1/(4*Real.pi)) Ri Rj * r + chiA4 χ3 * r ^ 3) - χ0 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [cHS_core_eq_num _ _ _ _ _ _ _ hr]
  unfold cHS_num chiA0 chiA1 chiA2 chiA4
  field_simp
  ring

/-- **The cancellation.** Whenever `λ² = (Rᵢ−Rⱼ)²`, `a₀ = (2E + a₂ + 3a₄λ²)·λ²` — a polynomial
identity modulo `λ² − (Rᵢ−Rⱼ)²`. This is exactly where the whole `χ₃/χ₂/χ₁` structure cancels. -/
theorem chiA0_eq_of_sq (χ1 χ2 χ3 E Ri Rj lam : ℝ) (hsq : lam ^ 2 = (Ri - Rj) ^ 2) :
    chiA0 χ1 χ2 χ3 E Ri Rj
      = (2*E + chiA2 χ1 χ2 χ3 E Ri Rj + 3 * chiA4 χ3 * lam ^ 2) * lam ^ 2 := by
  unfold chiA0 chiA2 chiA4
  linear_combination (-E + Real.pi*Ri^2*χ3/4 + Real.pi*Ri*Rj*χ3/2 + Real.pi*Ri*χ2
    + Real.pi*Rj^2*χ3/4 + Real.pi*Rj*χ2 + χ1/4 - Real.pi*χ3*lam^2/4) * hsq

/-- The Laurent slope collapses to `2E`: `a₀/λ² − a₂ − 3a₄λ² = 2E` when `λ² = (Rᵢ−Rⱼ)²`. -/
theorem chi_slope_value (χ1 χ2 χ3 E Ri Rj lam : ℝ) (hlam : lam ≠ 0)
    (hsq : lam ^ 2 = (Ri - Rj) ^ 2) :
    chiA0 χ1 χ2 χ3 E Ri Rj / lam ^ 2 - chiA2 χ1 χ2 χ3 E Ri Rj - 3 * chiA4 χ3 * lam ^ 2 = 2*E := by
  have hlam2 : lam ^ 2 ≠ 0 := pow_ne_zero 2 hlam
  rw [chiA0_eq_of_sq χ1 χ2 χ3 E Ri Rj lam hsq]
  field_simp
  ring

/-- **OZ.18 (slope closed form).** At any `lam ≠ 0` with `lam² = (Rᵢ−Rⱼ)²` — in particular at the
cutoff `lam = |Rᵢ−Rⱼ|` — the White-Bear core has derivative exactly `2(χ₂₂ − χ₁/(4π))`. All the
`χ₃/χ₂/χ₁` contributions cancel. -/
theorem cHS_core_hasDerivAt_of_sq (χ0 χ1 χ2 χ3 χ22 Ri Rj lam : ℝ) (hlam : lam ≠ 0)
    (hsq : lam ^ 2 = (Ri - Rj) ^ 2) :
    HasDerivAt (cHS_core χ0 χ1 χ2 χ3 χ22 Ri Rj) (2 * (χ22 - χ1 / (4 * Real.pi))) lam := by
  have heq : cHS_core χ0 χ1 χ2 χ3 χ22 Ri Rj =ᶠ[nhds lam]
      fun x => -(chiA0 χ1 χ2 χ3 (χ22 - χ1/(4*Real.pi)) Ri Rj * x⁻¹ + chiA1 χ1 χ2 χ3 Ri Rj
          + chiA2 χ1 χ2 χ3 (χ22 - χ1/(4*Real.pi)) Ri Rj * x + chiA4 χ3 * x ^ 3) - χ0 := by
    filter_upwards [eventually_ne_nhds hlam] with x hx
    exact cHS_core_eq_laurent χ0 χ1 χ2 χ3 χ22 Ri Rj hx
  have hD := (hasDerivAt_neg_laurent (chiA0 χ1 χ2 χ3 (χ22 - χ1/(4*Real.pi)) Ri Rj)
    (chiA1 χ1 χ2 χ3 Ri Rj) (chiA2 χ1 χ2 χ3 (χ22 - χ1/(4*Real.pi)) Ri Rj) (chiA4 χ3) χ0
    hlam).congr_of_eventuallyEq heq
  rwa [chi_slope_value χ1 χ2 χ3 (χ22 - χ1/(4*Real.pi)) Ri Rj lam hlam hsq] at hD

/-- **OZ.18 (slope closed form at the cutoff).** `F'(|Rᵢ−Rⱼ|) = 2(χ₂₂ − χ₁/(4π))`. -/
theorem cHS_core_deriv_at_cutoff (χ0 χ1 χ2 χ3 χ22 Ri Rj : ℝ) (hne : Ri ≠ Rj) :
    deriv (cHS_core χ0 χ1 χ2 χ3 χ22 Ri Rj) |Ri - Rj| = 2 * (χ22 - χ1 / (4 * Real.pi)) :=
  (cHS_core_hasDerivAt_of_sq χ0 χ1 χ2 χ3 χ22 Ri Rj |Ri - Rj|
    (abs_ne_zero.mpr (sub_ne_zero.mpr hne)) (sq_abs (Ri - Rj))).deriv

/-- **OZ.18 — `hslope` reduced to an elementary condition.** The cutoff slope is nonzero **iff**
`χ₂₂ ≠ χ₁/(4π)`. -/
theorem cHS_core_deriv_at_cutoff_ne_zero_iff (χ0 χ1 χ2 χ3 χ22 Ri Rj : ℝ) (hne : Ri ≠ Rj) :
    deriv (cHS_core χ0 χ1 χ2 χ3 χ22 Ri Rj) |Ri - Rj| ≠ 0 ↔ χ22 ≠ χ1 / (4 * Real.pi) := by
  rw [cHS_core_deriv_at_cutoff χ0 χ1 χ2 χ3 χ22 Ri Rj hne]
  constructor
  · intro h hc; exact h (by rw [hc]; ring)
  · intro h hc
    exact h (by linarith [hc])

/-- **OZ.18 (genuine kink, `hslope` discharged).** For an unlike pair with `χ₂₂ ≠ χ₁/(4π)`, the
clamped FMT DCF has a genuine C⁰ kink at the cutoff — no numerical slope hypothesis needed. -/
theorem cHS_FMT_not_differentiableAt_of_chi (χ0 χ1 χ2 χ3 χ22 Ri Rj : ℝ) (hne : Ri ≠ Rj)
    (hchi : χ22 ≠ χ1 / (4 * Real.pi)) :
    ¬ DifferentiableAt ℝ (cHS_FMT χ0 χ1 χ2 χ3 χ22 Ri Rj) |Ri - Rj| :=
  cHS_FMT_not_differentiableAt χ0 χ1 χ2 χ3 χ22 Ri Rj hne
    ((cHS_core_deriv_at_cutoff_ne_zero_iff χ0 χ1 χ2 χ3 χ22 Ri Rj hne).mpr hchi)

end FMSA.HSKink
