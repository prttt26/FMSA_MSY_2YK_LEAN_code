/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Homotopy invariance of contour integrals through loops — axiom-free (MA.8 core)

Group MA (`MATH_AXIOMS.md`), retiring the mathematical core of the former axiom `MA.8`
(`contourIntegral_eq_of_homotopic_loops`, `Analysis/HomotopyInvariance.lean`). When that axiom was
written, Mathlib had **no** homotopy-invariance machinery for contour integrals; as of `v4.31.0` it
has gained the Poincaré lemma for `1`-forms, including
`ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt`
(`Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean`): the curve integrals of a **closed**
`1`-form along two paths joined by a `C²` homotopy agree (up to the endpoint-trace terms). This file
turns the homotopy form of Cauchy's theorem — for a `C²` free homotopy **through loops** — into a
genuine theorem, `#print axioms` = standard three only.

## The two reusable pieces

* `holoForm f z := (id ℂ).smulRight (f z)` — the complex `1`-form "`f(z)·dz`", with
  `holoForm f z w = w • f z`.  Its curve integral is the usual contour integral
  `∫₀¹ γ'(t) • f(γ(t)) dt` (`curveIntegral_holoForm`, immediate from Mathlib's `curveIntegral` def).
* `holoForm_fderiv_symm` — **Cauchy–Riemann closedness**: if `f` is `ℂ`-differentiable at `x`, the
  `ℝ`-Fréchet derivative of `holoForm f` is symmetric (`dω x u v = dω x v u`).  This is what makes
  `holoForm f` a *closed* `1`-form, the hypothesis Mathlib's Poincaré lemma needs.  (It is a pure
  algebra fact once `fderiv ℝ f = restrictScalars (fderiv ℂ f)`: the `ℂ`-linear derivative satisfies
  `v • (u • c) = u • (v • c)` by commutativity.)

## The theorem

`contourIntegral_holoForm_eq_of_homotopic_loops`: for `f` holomorphic on an open `U`, a `C²`
homotopy `φ` of loops with image in `U` (each intermediate curve closed, `hloop`), the contour
integrals of `f` along the two boundary loops agree.  The endpoint-trace terms of Mathlib's identity
cancel *because* the homotopy is through loops (`φ.evalAt 0 = φ.evalAt 1` as functions).

Using the **`range φ`** set (compact) rather than `U` sidesteps the `ContinuousOn ω (closure t)`
hypothesis — `closure U` could leave `U`, but `closure (range φ) = range φ ⊆ U`; and supplying `dω`
explicitly as `fderiv ℝ (holoForm f)` avoids any `fderivWithin`/tangent-cone reasoning, since
`holoForm_fderiv_symm` gives symmetry for *all* directions, hence on the tangent cone a fortiori.
-/

open MeasureTheory Set intervalIntegral Topology

noncomputable section

namespace FMSA.Analysis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ### The holomorphic 1-form `holoForm f z = w ↦ w • f z` -/

/-- The complex `1`-form `f(z)·dz`, as `ℂ → (ℂ →L[ℂ] V)`: `holoForm f z` is the map `w ↦ w • f z`. -/
def holoForm (f : ℂ → V) (z : ℂ) : ℂ →L[ℂ] V :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (f z)

@[simp] theorem holoForm_apply (f : ℂ → V) (z w : ℂ) : holoForm f z w = w • f z := by
  simp [holoForm]

/-- The fixed `ℂ`-linear map `y ↦ (w ↦ w • y)`; `holoForm f = smulRightCLM ∘ f`. -/
def smulRightCLM : V →L[ℂ] (ℂ →L[ℂ] V) :=
  ContinuousLinearMap.smulRightL ℂ ℂ V (ContinuousLinearMap.id ℂ ℂ)

@[simp] theorem smulRightCLM_apply (y : V) (w : ℂ) : smulRightCLM y w = w • y := by
  simp [smulRightCLM]

theorem holoForm_eq_comp (f : ℂ → V) : holoForm f = fun z => smulRightCLM (f z) := by
  funext z; exact ContinuousLinearMap.ext fun w => by simp

theorem holoForm_differentiableAt {f : ℂ → V} {x : ℂ} (hf : DifferentiableAt ℂ f x) :
    DifferentiableAt ℂ (holoForm f) x := by
  rw [holoForm_eq_comp]; exact (smulRightCLM.differentiableAt).comp x hf

theorem holoForm_continuousOn {f : ℂ → V} {U : Set ℂ} (hf : ContinuousOn f U) :
    ContinuousOn (holoForm f) U := by
  rw [holoForm_eq_comp]; exact smulRightCLM.continuous.comp_continuousOn hf

/-! ### Crux B — Cauchy–Riemann closedness -/

/-- **Cauchy–Riemann closedness.** If `f` is `ℂ`-differentiable at `x`, the `ℝ`-Fréchet derivative
of `holoForm f` is symmetric: `dω x u v = dω x v u`.  This makes `holoForm f` a *closed* `1`-form. -/
theorem holoForm_fderiv_symm {f : ℂ → V} {x : ℂ} (hf : DifferentiableAt ℂ f x) (u v : ℂ) :
    (fderiv ℝ (holoForm f) x) u v = (fderiv ℝ (holoForm f) x) v u := by
  have hLf : HasFDerivAt (holoForm f)
      ((smulRightCLM (V := V)).restrictScalars ℝ ∘L (fderiv ℝ f x)) x := by
    rw [holoForm_eq_comp]
    have hf_R : HasFDerivAt f (fderiv ℝ f x) x := (hf.restrictScalars ℝ).hasFDerivAt
    exact ((smulRightCLM (V := V)).restrictScalars ℝ).hasFDerivAt.comp x hf_R
  rw [hLf.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    smulRightCLM_apply]
  have hres : fderiv ℝ f x = (fderiv ℂ f x).restrictScalars ℝ := hf.fderiv_restrictScalars ℝ
  rw [hres]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  have hlin : ∀ w : ℂ, (fderiv ℂ f x) w = w • (fderiv ℂ f x) 1 := fun w => by
    rw [← ContinuousLinearMap.map_smul]; simp
  rw [hlin u, hlin v, smul_smul, smul_smul, mul_comm]

/-! ### Crux A — curve integral of `holoForm f` is the contour integral -/

/-- The `curveIntegral` of `holoForm f` along `γ` is the ordinary contour integral
`∫₀¹ γ'(t) • f(γ(t)) dt`. -/
theorem curveIntegral_holoForm {a b : ℂ} (f : ℂ → V) (γ : Path a b) :
    (∫ᶜ x in γ, holoForm f x) = ∫ t in (0:ℝ)..1, deriv γ.extend t • f (γ.extend t) := by
  rw [curveIntegral_eq_intervalIntegral_deriv]
  simp only [holoForm_apply]

/-! ### The homotopy-invariance theorem -/

/-- **Homotopy invariance of contour integrals through loops** (homotopy form of Cauchy's theorem),
axiom-free.  For `f` holomorphic on the open set `U` and a `C²` homotopy `φ` of the loops `γ₁, γ₂`
whose image lies in `U` and each of whose intermediate curves is closed (`hloop`), the contour
integrals of `f` along `γ₁` and `γ₂` agree.  Proved from Mathlib's Poincaré-lemma homotopy identity
via `holoForm_fderiv_symm` (closedness); the endpoint-trace terms cancel because `φ` is a homotopy
*through loops*. -/
theorem contourIntegral_holoForm_eq_of_homotopic_loops {f : ℂ → V} {U : Set ℂ}
    {a₁ b₁ a₂ b₂ : ℂ} {γ₁ : Path a₁ b₁} {γ₂ : Path a₂ b₂}
    (φ : (γ₁.toContinuousMap).Homotopy γ₂.toContinuousMap)
    (hf : ∀ x ∈ U, DifferentiableAt ℂ f x)
    (hφU : ∀ p, φ p ∈ U)
    (hloop : ∀ s : unitInterval, φ (s, 0) = φ (s, 1))
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    (∫ᶜ x in γ₁, holoForm f x) = ∫ᶜ x in γ₂, holoForm f x := by
  set t : Set ℂ := range φ with ht_def
  have htU : t ⊆ U := by rw [ht_def, range_subset_iff]; exact hφU
  -- differentiability of `holoForm f` on `t`, plus continuity on `closure t = t`
  have hdiff : ∀ x ∈ t, DifferentiableAt ℂ (holoForm f) x :=
    fun x hx => holoForm_differentiableAt (hf x (htU hx))
  have hcompact : IsCompact t := isCompact_range (map_continuous _)
  have hclosure : closure t = t := hcompact.isClosed.closure_eq
  have hfcont : ContinuousOn f U := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hφt : ∀ a ∈ Ioo (0 : unitInterval) 1, ∀ b ∈ Ioo (0 : unitInterval) 1, φ (a, b) ∈ t :=
    fun a _ b _ => ht_def ▸ mem_range_self (a, b)
  have hω : ∀ x ∈ t, HasFDerivWithinAt (holoForm f) (fderiv ℝ (holoForm f) x) t x :=
    fun x hx => ((hdiff x hx).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have hωc : ContinuousOn (holoForm f) (closure t) := by
    rw [hclosure]; exact (holoForm_continuousOn hfcont).mono htU
  have hsymm : ∀ x ∈ t, ∀ u ∈ tangentConeAt ℝ t x, ∀ v ∈ tangentConeAt ℝ t x,
      (fderiv ℝ (holoForm f) x) u v = (fderiv ℝ (holoForm f) x) v u :=
    fun x hx _ _ _ _ => holoForm_fderiv_symm (hf x (htU hx)) _ _
  -- Mathlib's homotopy identity for the closed 1-form `holoForm f`
  have key := φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt (t := t)
    (ω := holoForm f) (dω := fun x => fderiv ℝ (holoForm f) x)
    hφt hω hωc hsymm hcontdiff
  -- the endpoint-trace curves coincide (loop homotopy): `(φ.evalAt 1).extend = (φ.evalAt 0).extend`
  -- the two boundary paths are loops (special case of `hloop` at the homotopy endpoints)
  have hγ₁loop : γ₁.toContinuousMap (1 : unitInterval) = γ₁.toContinuousMap 0 := by
    have h := hloop 0; rw [φ.apply_zero, φ.apply_zero] at h; exact h.symm
  have hγ₂loop : γ₂.toContinuousMap (1 : unitInterval) = γ₂.toContinuousMap 0 := by
    have h := hloop 1; rw [φ.apply_one, φ.apply_one] at h; exact h.symm
  have hextfun : (⇑(φ.evalAt (1 : unitInterval)).extend : ℝ → ℂ)
      = ⇑(φ.evalAt (0 : unitInterval)).extend := by
    funext s
    rw [ContinuousMap.Homotopy.pathExtend_evalAt, ContinuousMap.Homotopy.pathExtend_evalAt]
    change φ.extend s (1 : unitInterval) = φ.extend s (0 : unitInterval)
    -- `φ.extend s 1 = φ.extend s 0` for all real `s`
    rcases le_total s 0 with hs | hs
    · rw [φ.extend_apply_of_le_zero hs, φ.extend_apply_of_le_zero hs]; exact hγ₁loop
    · rcases le_total 1 s with hs1 | hs1
      · rw [φ.extend_apply_of_one_le hs1, φ.extend_apply_of_one_le hs1]; exact hγ₂loop
      · rw [φ.extend_apply_of_mem_I ⟨hs, hs1⟩, φ.extend_apply_of_mem_I ⟨hs, hs1⟩]
        exact (hloop ⟨s, ⟨hs, hs1⟩⟩).symm
  have hcancel : (∫ᶜ x in φ.evalAt 1, holoForm f x) = ∫ᶜ x in φ.evalAt 0, holoForm f x := by
    rw [curveIntegral_holoForm, curveIntegral_holoForm, hextfun]
  -- conclude: cancel the (equal) endpoint-trace terms
  have hgoal : (∫ᶜ x in γ₁, holoForm f x) + (∫ᶜ x in φ.evalAt 0, holoForm f x)
      = (∫ᶜ x in γ₂, holoForm f x) + (∫ᶜ x in φ.evalAt 0, holoForm f x) := by
    nth_rewrite 1 [← hcancel]
    exact key
  exact add_right_cancel hgoal

/-- **Cauchy's theorem, null-homotopic form** — genuine corollary, axiom-free.  A loop `γ₁` that is
`C²`-homotopic (through loops in `U`) to the constant loop at `z₀` has vanishing contour integral of
a function holomorphic on `U`.  Specialize `contourIntegral_holoForm_eq_of_homotopic_loops` to
`γ₂ := Path.refl z₀`, whose curve integral is `0`. -/
theorem contourIntegral_holoForm_eq_zero_of_nullhomotopic {f : ℂ → V} {U : Set ℂ}
    {a₁ b₁ z₀ : ℂ} {γ₁ : Path a₁ b₁}
    (φ : (γ₁.toContinuousMap).Homotopy (Path.refl z₀).toContinuousMap)
    (hf : ∀ x ∈ U, DifferentiableAt ℂ f x)
    (hφU : ∀ p, φ p ∈ U)
    (hloop : ∀ s : unitInterval, φ (s, 0) = φ (s, 1))
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1)) :
    (∫ᶜ x in γ₁, holoForm f x) = 0 := by
  rw [contourIntegral_holoForm_eq_of_homotopic_loops φ hf hφU hloop hcontdiff,
    curveIntegral_refl]

end FMSA.Analysis
