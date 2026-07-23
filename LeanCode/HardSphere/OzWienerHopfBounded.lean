/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.Analysis.RadialWienerHopf
import LeanCode.HardSphere.OzSymbolCoercive
import LeanCode.HardSphere.OzCoreClosure
import LeanCode.HardSphere.OzFixedPtDilute

/-!
# Bounded Wiener–Hopf uniqueness of the OZ fixed point

This retires the physics axiom `oz_fixed_pt_unique` (PYOZ_GHS.lean).  **Existence** is the
constructed `ozBaxterFixedPt`; **uniqueness** reduces, by linearity, to injectivity of `I −
oz_linear_op` on bounded exterior-continuous functions vanishing on the core — a *coercive-symbol*
bounded Wiener–Hopf fact.  We state that injectivity as one `L∞` math axiom
(`oz_linear_op_bounded_injective`), the analog of the proved `L²` `MA.12`
`wienerHopf_positive_symbol_injective`; its coercivity hypothesis is *discharged* from
`pyhs_no_spinodal` via `one_sub_rho_radial_fourier_c_HS_coercive`, so **no new physics axiom**.

The retired-axiom theorem is produced under the fresh name `oz_fixed_pt_unique_thm` (the swap of the
`oz_h` definition onto it is done separately).
-/

open MeasureTheory Set Real Filter Topology

namespace FMSA.HardSphere

noncomputable section

/-- **Bounded/`L∞` Wiener–Hopf injectivity of the OZ operator — now a THEOREM.**  The half-line OZ
convolution operator `I − oz_linear_op` has coercive symbol `1 − ρ·Ĉ (≥ ε > 0)`, hence is injective
on bounded, exterior-continuous functions vanishing on the core: the only bounded `d`, continuous on
`[σ,∞)`, zero on the core, solving the homogeneous equation `d = oz_linear_op d` on `[σ,∞)`, is
`d ≡ 0`.

**Abstracted and migrated 2026-07-19:** this was a domain-referencing math axiom; it is now derived
by instantiating the project-independent `FMSA.radialShell_bounded_injective`
(`Analysis/RadialWienerHopf.lean`) at the kernel `C := c_HS eta sigma`.  The two side conditions are
purely mechanical: the kernel support is `c_HS_outer`, and `radial_fourier` / `oz_linear_op` unfold
definitionally into the abstract statement's explicit integrals (the `if r ≤ 0` branch of
`oz_linear_op` is discharged by `σ ≤ r`).  Symbol positivity still enters only through `hcoercive`
(supplied from `pyhs_no_spinodal`), so **no physics** is used here. -/
theorem oz_linear_op_bounded_injective {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (hcoercive : ∃ ε, 0 < ε ∧ ∀ k, ε ≤ 1 - rho * radial_fourier (c_HS eta sigma) k)
    {d : ℝ → ℝ} (hbdd : ∃ C, ∀ r, |d r| ≤ C) (hcont : ContinuousOn d (Set.Ici sigma))
    (hcore : ∀ r, r < sigma → d r = 0)
    (hhom : ∀ r, sigma ≤ r → d r = oz_linear_op eta sigma rho d r) :
    ∀ r, d r = 0 := by
  refine radialShell_bounded_injective (C := c_HS eta sigma) (rho := rho) hsigma
    (fun t ht => c_HS_outer ht) ?_ hbdd hcont hcore ?_
  · obtain ⟨ε, hε, h⟩ := hcoercive
    exact ⟨ε, hε, fun k => by simpa [radial_fourier] using h k⟩
  · intro r hr
    rw [hhom r hr]
    simp only [oz_linear_op, if_neg (not_le.mpr (lt_of_lt_of_le hsigma hr))]

/-- `oz_linear_op` depends on `h` only through its values on `[σ,∞)` (the shell it integrates over):
if `f = g` on `[σ,∞)` then `oz_linear_op f r = oz_linear_op g r` for `r ≥ σ`. -/
theorem oz_linear_op_congr {eta sigma rho : ℝ} (hsigma : 0 < sigma) {f g : ℝ → ℝ}
    (hfg : ∀ s, sigma ≤ s → f s = g s) {r : ℝ} (hr : sigma ≤ r) :
    oz_linear_op eta sigma rho f r = oz_linear_op eta sigma rho g r := by
  have hr0 : ¬ r ≤ 0 := not_le.mpr (lt_of_lt_of_le hsigma hr)
  simp only [oz_linear_op, if_neg hr0]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hsigma.le] at ht
  obtain ⟨ht0, ht1⟩ := ht
  have hmax : max (r - t) sigma ≤ r + t := max_le (by linarith) (by linarith)
  refine congrArg (fun z => t * c_HS eta sigma t * z) ?_
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hmax] at hs
  have hsσ : sigma ≤ s := le_trans (le_max_right (r - t) sigma) hs.1
  simp only [hfg s hsσ]

/-- **Linearity of `oz_linear_op` on the exterior, for exterior-continuous bounded functions.**
`oz_linear_op h₁ − oz_linear_op h₂ = oz_linear_op (h₁ − h₂)` for `r ≥ σ`.  Reduces to
`oz_linear_op_sub` on globally continuous clamped surrogates `hᵢ(max · σ)` (which agree with `hᵢ` on
the shell), via `oz_linear_op_congr`. -/
theorem oz_linear_op_sub_of_continuousOn {eta sigma rho : ℝ} (hsigma : 0 < sigma) {h₁ h₂ : ℝ → ℝ}
    (hc₁ : ContinuousOn h₁ (Set.Ici sigma)) (hb₁ : ∃ C, ∀ r, |h₁ r| ≤ C)
    (hc₂ : ContinuousOn h₂ (Set.Ici sigma)) (hb₂ : ∃ C, ∀ r, |h₂ r| ≤ C)
    {r : ℝ} (hr : sigma ≤ r) :
    oz_linear_op eta sigma rho h₁ r - oz_linear_op eta sigma rho h₂ r
      = oz_linear_op eta sigma rho (fun s => h₁ s - h₂ s) r := by
  obtain ⟨C₁, hC₁⟩ := hb₁
  obtain ⟨C₂, hC₂⟩ := hb₂
  have hk₁cont : Continuous (fun s => h₁ (max s sigma)) :=
    hc₁.comp_continuous (by fun_prop) (fun x => le_max_right x sigma)
  have hk₂cont : Continuous (fun s => h₂ (max s sigma)) :=
    hc₂.comp_continuous (by fun_prop) (fun x => le_max_right x sigma)
  have hk₁bd : ∀ x, |h₁ (max x sigma)| ≤ C₁ := fun x => hC₁ (max x sigma)
  have hk₂bd : ∀ x, |h₂ (max x sigma)| ≤ C₂ := fun x => hC₂ (max x sigma)
  have hC₁0 : 0 ≤ C₁ := le_trans (abs_nonneg _) (hC₁ 0)
  have hC₂0 : 0 ≤ C₂ := le_trans (abs_nonneg _) (hC₂ 0)
  have he₁ : oz_linear_op eta sigma rho h₁ r
      = oz_linear_op eta sigma rho (fun s => h₁ (max s sigma)) r :=
    oz_linear_op_congr hsigma (fun s hs => by rw [max_eq_left hs]) hr
  have he₂ : oz_linear_op eta sigma rho h₂ r
      = oz_linear_op eta sigma rho (fun s => h₂ (max s sigma)) r :=
    oz_linear_op_congr hsigma (fun s hs => by rw [max_eq_left hs]) hr
  have hediff : oz_linear_op eta sigma rho (fun s => h₁ s - h₂ s) r
      = oz_linear_op eta sigma rho (fun s => h₁ (max s sigma) - h₂ (max s sigma)) r :=
    oz_linear_op_congr hsigma (fun s hs => by rw [max_eq_left hs]) hr
  rw [he₁, he₂, hediff]
  exact oz_linear_op_sub hsigma hk₁cont hk₂cont hC₁0 hk₁bd hC₂0 hk₂bd hr

/-- **Uniqueness of the bounded exterior-continuous OZ fixed point.**  The difference of two such
fixed points is bounded, continuous on `[σ,∞)`, `0` on the core (both `= -1`), and homogeneous on
`[σ,∞)`; the coercive-symbol bounded Wiener–Hopf injectivity forces it to vanish. -/
theorem oz_bounded_fixedpt_unique {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    {h₁ h₂ : ℝ → ℝ}
    (hfp₁ : OzFixedPt eta sigma rho h₁) (hc₁ : ContinuousOn h₁ (Set.Ici sigma))
    (hb₁ : ∃ C, ∀ r, |h₁ r| ≤ C)
    (hfp₂ : OzFixedPt eta sigma rho h₂) (hc₂ : ContinuousOn h₂ (Set.Ici sigma))
    (hb₂ : ∃ C, ∀ r, |h₂ r| ≤ C) :
    h₁ = h₂ := by
  funext r
  suffices hd0 : ∀ x, h₁ x - h₂ x = 0 by linarith [hd0 r]
  refine oz_linear_op_bounded_injective (d := fun x => h₁ x - h₂ x) hsigma
    (one_sub_rho_radial_fourier_c_HS_coercive heta0 heta1 hsigma hrho heta_def) ?_ ?_ ?_ ?_
  · -- bounded
    obtain ⟨C₁, hC₁⟩ := hb₁
    obtain ⟨C₂, hC₂⟩ := hb₂
    refine ⟨C₁ + C₂, fun x => ?_⟩
    have htri : |h₁ x - h₂ x| ≤ |h₁ x| + |h₂ x| := by
      rw [sub_eq_add_neg, ← abs_neg (h₂ x)]; exact abs_add_le _ _
    linarith [hC₁ x, hC₂ x, htri]
  · exact hc₁.sub hc₂
  · intro x hx
    simp only [oz_fixed_pt_core hfp₁ hx, oz_fixed_pt_core hfp₂ hx, sub_self]
  · intro x hx
    have h1 := oz_fixed_pt_exterior hfp₁ hx
    have h2 := oz_fixed_pt_exterior hfp₂ hx
    have hlin := oz_linear_op_sub_of_continuousOn (eta := eta) (rho := rho)
      hsigma hc₁ hb₁ hc₂ hb₂ hx
    change h₁ x - h₂ x = oz_linear_op eta sigma rho (fun s => h₁ s - h₂ s) x
    calc h₁ x - h₂ x
        = oz_linear_op eta sigma rho h₁ x - oz_linear_op eta sigma rho h₂ x := by
          rw [h1, h2]; ring
      _ = oz_linear_op eta sigma rho (fun s => h₁ s - h₂ s) x := hlin

/-- **`oz_fixed_pt_unique` as a theorem** (physics axiom retired).  Existence is the constructed
`ozBaxterFixedPt`; uniqueness is `oz_bounded_fixedpt_unique`. -/
theorem oz_fixed_pt_unique_thm (eta sigma rho : ℝ) (hsigma : 0 < sigma) (hrho : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1) :
    ∃! h : ℝ → ℝ, OzFixedPt eta sigma rho h ∧ ContinuousOn h (Set.Ici sigma)
      ∧ ∃ C, ∀ r, |h r| ≤ C := by
  have heta0 : 0 < eta := by rw [heta_def]; positivity
  refine ⟨ozBaxterFixedPt eta sigma rho, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact ozBaxterFixedPt_isFixedPt hsigma hrho heta_def heta_lt
  · exact ozBaxterFixedPt_continuousOn hsigma heta_def heta_lt
  · exact ozBaxterFixedPt_bounded hsigma hrho heta_def heta_lt
  · rintro h ⟨hfp, hc, hb⟩
    exact oz_bounded_fixedpt_unique heta0 heta_lt hsigma hrho heta_def hfp hc hb
      (ozBaxterFixedPt_isFixedPt hsigma hrho heta_def heta_lt)
      (ozBaxterFixedPt_continuousOn hsigma heta_def heta_lt)
      (ozBaxterFixedPt_bounded hsigma hrho heta_def heta_lt)

end

end FMSA.HardSphere
