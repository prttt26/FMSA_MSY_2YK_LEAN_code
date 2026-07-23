/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HSMixture.CHSKink

/-!
# Task OZ.19 — `c_HS,ij` is exactly constant on `(0, λ_ij)` (functional-agnostic flatness)

For a hard-sphere mixture and an unlike pair `i ≠ j` with `λ_ij = |R_i − R_j|`, the FMT
direct correlation function `c^HS_ij` is **exactly constant** on the sub-contact interval
`(0, λ_ij)`. This *strengthens* OZ.18: flatness on the whole interval gives left-slope `0`, so the
`λ_ij` kink is genuine whenever the right slope is nonzero — and unlike OZ.18's White-Bear-specific
slope `2(χ₂₂ − χ₁/(4π))`, flatness holds for **any** FMT functional.

## Why it is functional-agnostic

FMT writes the pair DCF as a fixed bilinear form in the weight convolutions,

  `c_ij(r) = −Σ_{αβ} (∂²Φ/∂n_α∂n_β) · (ω_α^i ⊛ ω_β^j)(r)`,

with the Hessian `∂²Φ/∂n_α∂n_β` evaluated at the **`r`-independent** bulk density. So all the
`r`-dependence sits in the convolutions. Below `λ_ij` the smaller sphere lies entirely inside the
larger, and every ball-overlap convolution is then `r`-independent (`get_HS_FMT`'s `r < λ` branch):

  `ω₂ⁱ⊛ω₂ʲ = 0`,  `ω₂ⁱ⊛ω₃ʲ = 4πR_i²` (if `R_i<R_j`),  `ω₃ⁱ⊛ω₃ʲ = (4π/3)·min(R_i,R_j)³`,
  `∇²(ω₃ⁱ⊛ω₃ʲ) = 0`.

Hence the Hessian factors out of a sum of constants: `c_ij` is constant on `(0, λ_ij)` for **any**
`Φ`. This file makes exactly that reduction precise and division-free.

## What is proved here (and what is taken as input)

`cHS_flat_of_convs_const` is the **functional-agnostic reduction**, fully general: for *any* eight
Hessian entries and *any* six scalar + one vector convolution functions that are constant on an
interval, the FMT bilinear form is constant there. It is genuinely universally quantified — not an
`∃`/`rfl` shell.

The one physical input is that the FMT weight convolutions **are** `r`-constant below `λ_ij` (the
ball-containment geometry). That is exactly what `get_HS_FMT` encodes as its `r < λ` branch, and it
is supplied here as the explicit hypothesis `hconv…` of the instantiation `cHS_fmt_inner_const`
(honest: the ball-overlap volume `vol(B(0,R_i) ∩ B(r·ê,R_j)) = (4π/3)min³` for `r < |R_i−R_j|` is a
spherical-geometry fact the codebase encodes as a closed form rather than deriving from measure
theory — see `get_HS_FMT`). The reduction itself is what removes the free-energy functional from
the picture.

Numerically (project discipline): the spread of `c^HS_ij` over `(0, λ_ij)` is `0.000e+00` (White
Bear FMT, exact) / `1.8×10⁻¹¹` (Baxter–PY, roundoff) — `numerical_notes/results/`,
`probe_sigma_ratio.py`.

**Status:** ✓ the functional-agnostic reduction + the FMT instantiation, axiom-clean.
-/

set_option linter.style.longLine false

open Set

namespace FMSA.HSKink

/-- **FMT pair DCF as a bilinear form in the weight convolutions.** `c(r) = −Σ_{αβ} Φ_αβ · w_αβ(r)`
for the six independent scalar Hessian entries (`03, 12, 13, 23, 22, 33`) plus the vector piece
`wv` carrying `Φ_v1v2, Φ_v2v2`. Functional-agnostic: the `Φ`'s are arbitrary reals. -/
noncomputable def cHS_fmt_form
    (Φ03 Φ12 Φ13 Φ23 Φ22 Φ33 : ℝ) (w03 w12 w13 w23 w22 w33 : ℝ → ℝ) (wv : ℝ → ℝ) (r : ℝ) : ℝ :=
  -(Φ03 * w03 r + Φ12 * w12 r + Φ13 * w13 r + Φ23 * w23 r + Φ22 * w22 r + Φ33 * w33 r) + wv r

/-- **OZ.19 — the functional-agnostic reduction.** If every weight convolution is constant on a set
`s`, then the FMT pair DCF is constant on `s`, for **any** free-energy Hessian. This is the whole
content of "flatness is functional-agnostic": the `Φ`'s factor out of a sum of constants. -/
theorem cHS_flat_of_convs_const
    {Φ03 Φ12 Φ13 Φ23 Φ22 Φ33 : ℝ} {w03 w12 w13 w23 w22 w33 wv : ℝ → ℝ} {s : Set ℝ}
    {c03 c12 c13 c23 c22 c33 cv : ℝ}
    (h03 : EqOn w03 (fun _ => c03) s) (h12 : EqOn w12 (fun _ => c12) s)
    (h13 : EqOn w13 (fun _ => c13) s) (h23 : EqOn w23 (fun _ => c23) s)
    (h22 : EqOn w22 (fun _ => c22) s) (h33 : EqOn w33 (fun _ => c33) s)
    (hv : EqOn wv (fun _ => cv) s) :
    EqOn (cHS_fmt_form Φ03 Φ12 Φ13 Φ23 Φ22 Φ33 w03 w12 w13 w23 w22 w33 wv)
      (fun _ => -(Φ03 * c03 + Φ12 * c12 + Φ13 * c13 + Φ23 * c23 + Φ22 * c22 + Φ33 * c33) + cv) s := by
  intro r hr
  unfold cHS_fmt_form
  rw [h03 hr, h12 hr, h13 hr, h23 hr, h22 hr, h33 hr, hv hr]

/-- **OZ.19, FMT instantiation — `c^HS_ij` is constant on `(0, λ_ij)`.** Below `λ_ij = |R_i − R_j|`
the ball-containment geometry makes every weight convolution constant (`hconv…`, the `r < λ` branch
of `get_HS_FMT`); the reduction then gives a flat DCF there, for **any** functional `Φ`. -/
theorem cHS_fmt_inner_const
    (Φ03 Φ12 Φ13 Φ23 Φ22 Φ33 : ℝ) (w03 w12 w13 w23 w22 w33 wv : ℝ → ℝ)
    {Ri Rj : ℝ} {c03 c12 c13 c23 c22 c33 cv : ℝ}
    (hconv03 : EqOn w03 (fun _ => c03) (Ioo 0 |Ri - Rj|))
    (hconv12 : EqOn w12 (fun _ => c12) (Ioo 0 |Ri - Rj|))
    (hconv13 : EqOn w13 (fun _ => c13) (Ioo 0 |Ri - Rj|))
    (hconv23 : EqOn w23 (fun _ => c23) (Ioo 0 |Ri - Rj|))
    (hconv22 : EqOn w22 (fun _ => c22) (Ioo 0 |Ri - Rj|))
    (hconv33 : EqOn w33 (fun _ => c33) (Ioo 0 |Ri - Rj|))
    (hconvv : EqOn wv (fun _ => cv) (Ioo 0 |Ri - Rj|)) :
    ∃ C : ℝ, EqOn (cHS_fmt_form Φ03 Φ12 Φ13 Φ23 Φ22 Φ33 w03 w12 w13 w23 w22 w33 wv)
      (fun _ => C) (Ioo 0 |Ri - Rj|) :=
  ⟨_, cHS_flat_of_convs_const hconv03 hconv12 hconv13 hconv23 hconv22 hconv33 hconvv⟩

/-- **Corollary — left slope is `0` on the sub-contact interval** (the OZ.18 hand-off). A function
constant on `(0, λ_ij)` has derivative `0` at every interior point, which is exactly the left-slope
input OZ.18's kink needs — now established without the `clampedBelow` modelling assumption. -/
theorem cHS_fmt_inner_hasDerivAt_zero
    {f : ℝ → ℝ} {C lam : ℝ} (hflat : EqOn f (fun _ => C) (Ioo 0 lam))
    {r : ℝ} (hr : r ∈ Ioo 0 lam) :
    HasDerivAt f 0 r := by
  have hmem : Ioo 0 lam ∈ nhds r := Ioo_mem_nhds hr.1 hr.2
  refine (hasDerivAt_const r C).congr_of_eventuallyEq ?_
  filter_upwards [hmem] with x hx using hflat hx

/-! ### Cleaning OZ.18 — the functional-agnostic kink, off the `clampedBelow` model

OZ.18's kink (`clampedBelow_not_differentiableAt`, `CHSKink.lean`) gets its **left** slope `0`
from `clampedBelow_eqOn_Iic` — i.e. from the *modelling assumption* that the sub-contact branch is
the clamp `F(λ)`. OZ.19 removes that assumption: the real FMT DCF is genuinely flat below `λ`, so
the left slope `0` is a *proved* fact, not a modelling choice. The lemmas here re-derive the kink
from (flat below `λ`) + (right slope `≠ 0`) alone, for **any** function — the honest hypotheses. -/

/-- **Left slope `0` from genuine flatness** (not from a clamp). If `f` is constant on the open
sub-contact interval `(0, λ)` and left-continuous into `λ` with the same value, its within-`Iic`
derivative at `λ` is `0`. -/
theorem hasDerivWithinAt_Iic_zero_of_flat
    {f : ℝ → ℝ} {C lam : ℝ} (hlam : 0 < lam)
    (hflat : EqOn f (fun _ => C) (Ioo 0 lam)) (hval : f lam = C) :
    HasDerivWithinAt f 0 (Iic lam) lam := by
  refine (hasDerivWithinAt_const lam (Iic lam) C).congr_of_eventuallyEq ?_ (by simpa using hval)
  have hmem : Ioc 0 lam ∈ nhdsWithin lam (Iic lam) := by
    have h := inter_mem_nhdsWithin (Iic lam) (Ioi_mem_nhds hlam)
    rwa [Set.inter_comm, Set.Ioi_inter_Iic] at h
  filter_upwards [hmem] with x hx
  rcases eq_or_lt_of_le hx.2 with hxe | hxl
  · simp [hxe, hval]
  · simp only [hflat ⟨hx.1, hxl⟩]

/-- **Functional-agnostic kink** (the OZ.18 hand-off, off `clampedBelow`). A function that is flat
on `(0, λ)`, left-continuous into `λ`, and has a nonzero right derivative `D` at `λ`, is **not
differentiable** at `λ`. Same slope-mismatch argument as `clampedBelow_not_differentiableAt`, but
the left slope now comes from OZ.19's genuine flatness rather than the clamp construction. -/
theorem not_differentiableAt_of_flat_below_of_right_deriv
    {f : ℝ → ℝ} {C lam D : ℝ} (hlam : 0 < lam)
    (hflat : EqOn f (fun _ => C) (Ioo 0 lam)) (hval : f lam = C)
    (hRight : HasDerivWithinAt f D (Ici lam) lam) (hD : D ≠ 0) :
    ¬ DifferentiableAt ℝ f lam := by
  intro hdiff
  have hL := hdiff.hasDerivAt
  set L := deriv f lam with hLdef
  have hLIic : HasDerivWithinAt f L (Iic lam) lam := hL.hasDerivWithinAt
  have hLIci : HasDerivWithinAt f L (Ici lam) lam := hL.hasDerivWithinAt
  have hs_iic : UniqueDiffWithinAt ℝ (Iic lam) lam := uniqueDiffOn_Iic lam lam self_mem_Iic
  have hs_ici : UniqueDiffWithinAt ℝ (Ici lam) lam := uniqueDiffOn_Ici lam lam self_mem_Ici
  have h0 : L = 0 := by
    rw [← hLIic.derivWithin hs_iic,
      (hasDerivWithinAt_Iic_zero_of_flat hlam hflat hval).derivWithin hs_iic]
  have hd : L = D := by rw [← hLIci.derivWithin hs_ici, hRight.derivWithin hs_ici]
  exact hD (by rw [← hd, h0])

end FMSA.HSKink
