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

## Scope note (faithful to the numerics)

`F'(λ) ≠ 0` is a *state-point-dependent* fact: the White-Bear coefficients `χ₀…χ₃, χ₂₂` are
functions of the packing fraction `η` and partial densities, so the slope's sign is not
determined by `σ > 0` alone.  It is left as an explicit hypothesis here — numerically confirmed
in `verify_stepwise_breakpoints.py` — exactly as the strict-positivity half of the mediated
breakpoints (Group IB) is left numerical.  Everything else (continuity, both one-sided slopes,
the kink *given* the slope hypothesis) is proved unconditionally.

Status: ✓ DONE (conditional on the numerical `F'(λ) ≠ 0`).
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
cutoff (state-point-dependent; numerically confirmed, not derivable from `σ > 0`), the clamped FMT
DCF is **not differentiable** at `λ`: left slope `0` ≠ right slope `F'(λ)`. Together with
`cHS_FMT_continuousAt` this is the genuine C⁰ kink. -/
theorem cHS_FMT_not_differentiableAt (χ0 χ1 χ2 χ3 χ22 Ri Rj : ℝ) (hne : Ri ≠ Rj)
    (hslope : deriv (cHS_core χ0 χ1 χ2 χ3 χ22 Ri Rj) |Ri - Rj| ≠ 0) :
    ¬ DifferentiableAt ℝ (cHS_FMT χ0 χ1 χ2 χ3 χ22 Ri Rj) |Ri - Rj| := by
  have hlam : |Ri - Rj| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hne)
  have hdiff := cHS_core_differentiableAt χ0 χ1 χ2 χ3 χ22 Ri Rj hlam
  exact clampedBelow_not_differentiableAt _ hdiff.hasDerivAt hslope

end FMSA.HSKink
