/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterOzStar
import LeanCode.HardSphere.OzExteriorDerivBundle
import LeanCode.HardSphere.OzExteriorIntegrability
import LeanCode.HardSphere.OzExteriorFromBaxter

/-!
# Exterior convolution/Fubini integrability clauses (6g / 6h / 6j)

The three integrability clauses of the exterior "derivative bundle" of `baxter_exterior_regularity`
that involve the OZ shell/convolution integrands against `ozBaxterFixedPt`.  These are *not* about
the exterior derivative `g'`; they are pure measure-theory integrability facts about the constructed
solution and its convolution with the compactly-supported `c_HS`.

All three are **theorems** — this file contains no axiom.

* `ozBaxterExterior_shell_integrable` — clause **6g** (for each fixed `r`, the double product over
  the finite shell box is integrable), proved from finite support + boundedness.
* `ozExterior_triple_shell_sin_integrable` — clause **6h**, the joint integrability over `(a,t,s)`,
  proved by the Tonelli estimate below (`ozShellMajorant`).  Retired from an axiom 2026-07-19.
* `ozExterior_conv_sin_integrable` — clause **6j**, derived from 6h by one Fubini swap.
-/

open MeasureTheory Set Real Filter Topology

namespace FMSA.HardSphere

noncomputable section

/-- A measurable function on `ℝ × ℝ` supported (relative to the `(Ioi 0)²`-restricted product
measure) on a finite box `Ioc 0 a × Ioc 0 b`, and bounded there, is integrable for that measure. -/
theorem integrable_prodIoi_of_box_support {f : ℝ × ℝ → ℝ} (hf : Measurable f) {a b C : ℝ}
    (hsupp : ∀ p : ℝ × ℝ, p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) →
      p ∉ Set.Ioc (0 : ℝ) a ×ˢ Set.Ioc (0 : ℝ) b → f p = 0)
    (hbdd : ∀ p ∈ Set.Ioc (0 : ℝ) a ×ˢ Set.Ioc (0 : ℝ) b, ‖f p‖ ≤ C) :
    Integrable f ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
  have hBmeas : MeasurableSet (Set.Ioc (0 : ℝ) a ×ˢ Set.Ioc (0 : ℝ) b) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have hae : f =ᵐ[(volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))]
      (Set.Ioc (0 : ℝ) a ×ˢ Set.Ioc (0 : ℝ) b).indicator f := by
    have hIoi : ∀ᵐ p ∂((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))),
        p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
    filter_upwards [hIoi] with p hp
    by_cases hb : p ∈ Set.Ioc (0 : ℝ) a ×ˢ Set.Ioc (0 : ℝ) b
    · rw [Set.indicator_of_mem hb]
    · rw [Set.indicator_of_notMem hb, hsupp p hp hb]
  rw [integrable_congr hae, integrable_indicator_iff hBmeas]
  have hμB : ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ))))
      (Set.Ioc (0 : ℝ) a ×ˢ Set.Ioc (0 : ℝ) b) ≠ ⊤ := by
    rw [Measure.prod_prod]
    refine ENNReal.mul_ne_top ?_ ?_ <;>
      · rw [Measure.restrict_apply measurableSet_Ioc]
        exact ne_top_of_le_ne_top measure_Ioc_lt_top.ne (measure_mono Set.inter_subset_left)
  refine Measure.integrableOn_of_bounded (M := C) hμB hf.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hBmeas] with p hp using hbdd p hp

/-- **Clause 6g.**  For each fixed `r > 0`, the shell double-product integrand
`p ↦ p.1·c_HS(p.1)·1_{[|r-p.1|,r+p.1]}(p.2)·(p.2·ozBaxterFixedPt(p.2))` is integrable for the
`(Ioi 0)²` product measure.  Its support is contained in the finite box `Ioc 0 σ × Ioc 0 (r+σ)`
(`c_HS` vanishes for `p.1 ≥ σ`; the indicator forces `p.2 ≤ r+p.1 ≤ r+σ`), where it is bounded. -/
theorem ozBaxterExterior_shell_integrable {eta sigma rho : ℝ} (hsigma : 0 < sigma) (hrho : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1) :
    ∀ k : ℝ, 0 < k → ∀ r ∈ Set.Ioi (0 : ℝ), Integrable
      (fun p : ℝ × ℝ => p.1 * c_HS eta sigma p.1 *
        (Set.Icc |r - p.1| (r + p.1)).indicator
          (fun s => s * ozBaxterFixedPt eta sigma rho s) p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
  intro _ _ r hr
  have hr0 : (0 : ℝ) < r := hr
  obtain ⟨Cc, hCc0, hCc⟩ := c_HS_bddOn (eta := eta) (sigma := sigma) hsigma
  obtain ⟨Cb, hCb⟩ := ozBaxterFixedPt_bounded hsigma hrho heta_def heta_lt
  have hCb0 : 0 ≤ Cb := le_trans (abs_nonneg _) (hCb 0)
  -- measurability of the integrand
  have hset : MeasurableSet {p : ℝ × ℝ | |r - p.1| ≤ p.2 ∧ p.2 ≤ r + p.1} :=
    (measurableSet_le ((measurable_const.sub measurable_fst).abs) measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_const.add measurable_fst))
  have hind_meas : Measurable (fun p : ℝ × ℝ => (Set.Icc |r - p.1| (r + p.1)).indicator
      (fun s => s * ozBaxterFixedPt eta sigma rho s) p.2) := by
    have heq : (fun p : ℝ × ℝ => (Set.Icc |r - p.1| (r + p.1)).indicator
          (fun s => s * ozBaxterFixedPt eta sigma rho s) p.2)
        = {p : ℝ × ℝ | |r - p.1| ≤ p.2 ∧ p.2 ≤ r + p.1}.indicator
          (fun p => p.2 * ozBaxterFixedPt eta sigma rho p.2) := by
      funext p; simp only [Set.indicator_apply, Set.mem_Icc, Set.mem_setOf_eq]
    rw [heq]
    exact (measurable_snd.mul (ozBaxterFixedPt_measurable.comp measurable_snd)).indicator hset
  have hf_meas : Measurable (fun p : ℝ × ℝ => p.1 * c_HS eta sigma p.1 *
      (Set.Icc |r - p.1| (r + p.1)).indicator
        (fun s => s * ozBaxterFixedPt eta sigma rho s) p.2) :=
    (measurable_fst.mul ((c_HS_measurable eta sigma).comp measurable_fst)).mul hind_meas
  refine integrable_prodIoi_of_box_support (a := sigma) (b := r + sigma)
    (C := sigma * Cc * ((r + sigma) * Cb)) hf_meas ?_ ?_
  · -- support inside the box
    intro p hp hnotb
    obtain ⟨hp1, hp2⟩ := hp
    rw [Set.mem_Ioi] at hp1 hp2
    by_cases hp1σ : p.1 ≤ sigma
    · -- `p.1 ≤ σ`; then not-in-box forces `p.2 > r+σ`, so the indicator vanishes
      have hp2b : r + sigma < p.2 := by
        by_contra h
        exact hnotb ⟨⟨hp1, hp1σ⟩, ⟨hp2, not_lt.mp h⟩⟩
      have hnotmem : p.2 ∉ Set.Icc |r - p.1| (r + p.1) := by
        rw [Set.mem_Icc]; rintro ⟨_, h2⟩; linarith
      change p.1 * c_HS eta sigma p.1 *
        (Set.Icc |r - p.1| (r + p.1)).indicator _ p.2 = 0
      rw [Set.indicator_of_notMem hnotmem, mul_zero]
    · -- `p.1 > σ`; then `c_HS p.1 = 0`
      have hσp1 : sigma ≤ p.1 := (not_le.mp hp1σ).le
      change p.1 * c_HS eta sigma p.1 * _ = 0
      rw [c_HS_outer hσp1, mul_zero, zero_mul]
  · -- boundedness on the box
    intro p hp
    obtain ⟨⟨hp10, hp1σ⟩, ⟨hp20, hp2b⟩⟩ := hp
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |p.1 * c_HS eta sigma p.1| ≤ sigma * Cc := by
      rw [abs_mul, abs_of_pos hp10]
      exact mul_le_mul hp1σ (hCc p.1 ⟨hp10.le, hp1σ⟩) (abs_nonneg _) hsigma.le
    have h2 : |(Set.Icc |r - p.1| (r + p.1)).indicator
        (fun s => s * ozBaxterFixedPt eta sigma rho s) p.2| ≤ (r + sigma) * Cb := by
      have hle : |(Set.Icc |r - p.1| (r + p.1)).indicator
          (fun s => s * ozBaxterFixedPt eta sigma rho s) p.2|
          ≤ |p.2 * ozBaxterFixedPt eta sigma rho p.2| := by
        rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
        exact norm_indicator_le_norm_self _ _
      refine le_trans hle ?_
      rw [abs_mul, abs_of_pos hp20]
      exact mul_le_mul hp2b (hCb p.2) (abs_nonneg _) (by linarith)
    exact mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hsigma.le hCc0)

/-!
### Clauses 6h and 6j — the exterior Fubini/Tonelli finiteness

Both remaining clauses reduce to the *same* absolutely-convergent Tonelli estimate over the
**unbounded** first axis: with `μ = ∫_t |t·c_HS(t)|·t dt < ∞` (finite by `c_HS`'s compact support,
`c_HS_abs_integral`) and `ν = ∫_s |s·ozBaxterFixedPt(s)| ds < ∞` (finite by the exterior `L¹` decay
`baxterPsiOuter_integrableOn` on `(σ,∞)` plus the elementary `-s` piece on `(0,σ)`), the shell
constraint `s ∈ [|a-t|, a+t]` confines the `a`-integral to a set of length `≤ 2·min(t,s) ≤ 2t`, so
`∬∫ |·| ≤ 2μν < ∞`.  Clause 6h is the joint integrability over `(a,t,s)`; clause 6j is the
integrability in `r` of the double-integral `r·(c_HS ⊛₃ ozBaxterFixedPt)(r)·sin(kr)` — the same
estimate read after one Fubini swap.

Clause 6h is proved below from exactly that estimate (`ozExterior_triple_shell_sin_integrable`, no
axiom); clause 6j follows from it by one Fubini swap.
-/

/-- The `(a,t,s)` **shell region** `|a−t| ≤ s ≤ a+t` — the triangle constraint carried by the 3-D
radial convolution, viewed as a subset of `ℝ × ℝ × ℝ` (coordinates `a = p.1`, `t = p.2.1`,
`s = p.2.2`).  For fixed `(t,s)` its `a`-slice is contained in `Icc |s−t| (s+t)`, of length
`2·min(s,t)`; that is the estimate driving the exterior Tonelli bound. -/
def ozShellRegion : Set (ℝ × ℝ × ℝ) := {p | |p.1 - p.2.1| ≤ p.2.2 ∧ p.2.2 ≤ p.1 + p.2.1}

/-- The Tonelli **majorant** of the clause-6h integrand: `sin(k·a)` dropped (`|sin| ≤ 1`) and the
shell indicator re-read as a constraint on the `a`-variable, so that the `a`-integral becomes a
plain measure of the shell slice. -/
noncomputable def ozShellMajorant (eta sigma rho : ℝ) : ℝ × ℝ × ℝ → ENNReal :=
  ozShellRegion.indicator fun q =>
    ‖q.2.1 * c_HS eta sigma q.2.1‖ₑ * ‖q.2.2 * ozBaxterFixedPt eta sigma rho q.2.2‖ₑ

theorem measurableSet_ozShellRegion : MeasurableSet ozShellRegion :=
  (measurableSet_le ((measurable_fst.sub (measurable_fst.comp measurable_snd)).abs)
      (measurable_snd.comp measurable_snd)).inter
    (measurableSet_le (measurable_snd.comp measurable_snd)
      (measurable_fst.add (measurable_fst.comp measurable_snd)))

theorem measurable_ozShellMajorant {eta sigma rho : ℝ} :
    Measurable (ozShellMajorant eta sigma rho) :=
  Measurable.indicator
    ((((measurable_fst.comp measurable_snd).mul
        ((c_HS_measurable eta sigma).comp (measurable_fst.comp measurable_snd))).enorm).mul
      (((measurable_snd.comp measurable_snd).mul
        (ozBaxterFixedPt_measurable.comp (measurable_snd.comp measurable_snd))).enorm))
    measurableSet_ozShellRegion

/-- **The shell-slice length estimate.**  For fixed `(t,s)`, the set of `a` obeying the triangle
constraint `|a−t| ≤ s ≤ a+t` lies in `Icc |s−t| (s+t)`, whose length `s+t−|s−t| = 2·min(s,t)` is
at most `2t` (since `s−t ≤ |s−t|`).  This is the `∫_a 1_{s∈[|a−t|,a+t]} da ≤ 2t` of the sketch. -/
theorem volume_ozShell_slice_le (t s : ℝ) :
    (volume.restrict (Set.Ioi (0:ℝ))) {a : ℝ | |a - t| ≤ s ∧ s ≤ a + t}
      ≤ ENNReal.ofReal (2 * t) := by
  have hsub : {a : ℝ | |a - t| ≤ s ∧ s ≤ a + t} ⊆ Set.Icc |s - t| (s + t) := by
    rintro a ⟨h1, h2⟩
    rw [abs_le] at h1
    exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, by linarith⟩
  calc (volume.restrict (Set.Ioi (0:ℝ))) {a : ℝ | |a - t| ≤ s ∧ s ≤ a + t}
      ≤ volume {a : ℝ | |a - t| ≤ s ∧ s ≤ a + t} := Measure.restrict_apply_le _ _
    _ ≤ volume (Set.Icc |s - t| (s + t)) := measure_mono hsub
    _ = ENNReal.ofReal (s + t - |s - t|) := Real.volume_Icc
    _ ≤ ENNReal.ofReal (2 * t) :=
        ENNReal.ofReal_le_ofReal (by have := le_abs_self (s - t); linarith)

/-- **The `s`-side `L¹` factor.**  `s ↦ s·ozBaxterFixedPt s` is integrable on *all* of `(0,∞)`:
on the core `(0,σ]` it is a bounded function on a finite-measure set (`|s·ozBFP s| ≤ σ·C`, from
`ozBaxterFixedPt_bounded`), and on the exterior `(σ,∞)` it is
`r_mul_ozBaxterFixedPt_integrableOn` — i.e. MA.13's strengthened `baxterPsiOuter` `L¹` decay. -/
theorem r_mul_ozBaxterFixedPt_integrableOn_Ioi_zero {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1) :
    IntegrableOn (fun s => s * ozBaxterFixedPt eta sigma rho s) (Set.Ioi 0) := by
  have heta0 : 0 < eta := by rw [heta_def]; positivity
  obtain ⟨Cb, hCb⟩ := ozBaxterFixedPt_bounded hsigma hrho heta_def heta_lt
  have hmeas : Measurable (fun s => s * ozBaxterFixedPt eta sigma rho s) :=
    measurable_id.mul ozBaxterFixedPt_measurable
  have hcore : IntegrableOn (fun s => s * ozBaxterFixedPt eta sigma rho s) (Set.Ioc 0 sigma) := by
    refine Measure.integrableOn_of_bounded (M := sigma * Cb) measure_Ioc_lt_top.ne
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hs.1]
    exact mul_le_mul hs.2 (hCb s) (abs_nonneg _) hsigma.le
  have hunion := hcore.union
    (r_mul_ozBaxterFixedPt_integrableOn heta0 heta_lt hsigma hrho heta_def)
  rwa [Set.Ioc_union_Ioi_eq_Ioi hsigma.le] at hunion

/-- **The `t`-side compact-support factor.**  `∫_t 2t·|t·c_HS t| dt < ∞`: the integrand vanishes
for `t ≥ σ` (`c_HS_outer`) and is bounded by `2σ·(σ·C)` on `(0,σ]` (`c_HS_bddOn`). -/
theorem lintegral_shell_weight_c_HS_lt_top {eta sigma : ℝ} (hsigma : 0 < sigma) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (2 * t) * ‖t * c_HS eta sigma t‖ₑ < ⊤ := by
  obtain ⟨Cc, hCc0, hCc⟩ := c_HS_bddOn (eta := eta) (sigma := sigma) hsigma
  have hmono : ∀ t ∈ Set.Ioi (0:ℝ), ENNReal.ofReal (2 * t) * ‖t * c_HS eta sigma t‖ₑ
      ≤ (Set.Ioc (0:ℝ) sigma).indicator
        (fun _ => ENNReal.ofReal (2 * sigma) * ENNReal.ofReal (sigma * Cc)) t := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    rcases le_or_gt t sigma with hts | hts
    · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨ht0, hts⟩)]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) ?_
      rw [Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [abs_mul, abs_of_pos ht0]
      exact mul_le_mul hts (hCc t ⟨ht0.le, hts⟩) (abs_nonneg _) hsigma.le
    · rw [c_HS_outer hts.le, mul_zero, enorm_zero, mul_zero]
      simp
  calc ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (2 * t) * ‖t * c_HS eta sigma t‖ₑ
      ≤ ∫⁻ t in Set.Ioi (0:ℝ), (Set.Ioc (0:ℝ) sigma).indicator
          (fun _ => ENNReal.ofReal (2 * sigma) * ENNReal.ofReal (sigma * Cc)) t := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hmono t ht
    _ ≤ ∫⁻ t, (Set.Ioc (0:ℝ) sigma).indicator
          (fun _ => ENNReal.ofReal (2 * sigma) * ENNReal.ofReal (sigma * Cc)) t :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ = (ENNReal.ofReal (2 * sigma) * ENNReal.ofReal (sigma * Cc)) * volume (Set.Ioc (0:ℝ) sigma) :=
        by rw [lintegral_indicator measurableSet_Ioc, setLIntegral_const]
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) measure_Ioc_lt_top

/-- **The Tonelli estimate.**  `∭ ozShellMajorant < ∞`: swap so the `a`-integral is innermost
(`lintegral_prod_symm`), evaluate it as `C(t,s)·volume(shell slice) ≤ C(t,s)·2t`
(`volume_ozShell_slice_le`), then split the remaining `(t,s)`-integral as a product
(`lintegral_prod_mul`) of the two finite factors. -/
theorem lintegral_ozShellMajorant_lt_top {eta sigma rho : ℝ} (hsigma : 0 < sigma) (hrho : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1) :
    ∫⁻ p, ozShellMajorant eta sigma rho p
      ∂((volume.restrict (Set.Ioi 0)).prod
        ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0)))) < ⊤ := by
  rw [lintegral_prod_symm _ measurable_ozShellMajorant.aemeasurable]
  -- the inner `a`-integral is the shell-slice measure, weighted by the `(t,s)` amplitude
  have hinner : ∀ y : ℝ × ℝ,
      ∫⁻ a : ℝ, ozShellMajorant eta sigma rho (a, y) ∂(volume.restrict (Set.Ioi 0))
      = (‖y.1 * c_HS eta sigma y.1‖ₑ * ‖y.2 * ozBaxterFixedPt eta sigma rho y.2‖ₑ)
        * (volume.restrict (Set.Ioi (0:ℝ))) {a : ℝ | |a - y.1| ≤ y.2 ∧ y.2 ≤ a + y.1} := by
    intro y
    have hslice : MeasurableSet {a : ℝ | |a - y.1| ≤ y.2 ∧ y.2 ≤ a + y.1} := by
      measurability
    have hfun : (fun a : ℝ => ozShellMajorant eta sigma rho (a, y))
        = {a : ℝ | |a - y.1| ≤ y.2 ∧ y.2 ≤ a + y.1}.indicator
          (fun _ => ‖y.1 * c_HS eta sigma y.1‖ₑ *
            ‖y.2 * ozBaxterFixedPt eta sigma rho y.2‖ₑ) := by
      funext a
      simp only [ozShellMajorant, ozShellRegion, Set.indicator_apply, Set.mem_setOf_eq]
    rw [hfun, lintegral_indicator hslice, setLIntegral_const]
  simp only [hinner]
  calc ∫⁻ y : ℝ × ℝ, (‖y.1 * c_HS eta sigma y.1‖ₑ * ‖y.2 * ozBaxterFixedPt eta sigma rho y.2‖ₑ)
          * (volume.restrict (Set.Ioi (0:ℝ))) {a : ℝ | |a - y.1| ≤ y.2 ∧ y.2 ≤ a + y.1}
        ∂((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0)))
      ≤ ∫⁻ y : ℝ × ℝ, (ENNReal.ofReal (2 * y.1) * ‖y.1 * c_HS eta sigma y.1‖ₑ)
          * ‖y.2 * ozBaxterFixedPt eta sigma rho y.2‖ₑ
        ∂((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
        refine lintegral_mono fun y => ?_
        calc (‖y.1 * c_HS eta sigma y.1‖ₑ * ‖y.2 * ozBaxterFixedPt eta sigma rho y.2‖ₑ)
              * (volume.restrict (Set.Ioi (0:ℝ))) {a : ℝ | |a - y.1| ≤ y.2 ∧ y.2 ≤ a + y.1}
            ≤ (‖y.1 * c_HS eta sigma y.1‖ₑ * ‖y.2 * ozBaxterFixedPt eta sigma rho y.2‖ₑ)
              * ENNReal.ofReal (2 * y.1) := mul_le_mul' le_rfl (volume_ozShell_slice_le _ _)
          _ = (ENNReal.ofReal (2 * y.1) * ‖y.1 * c_HS eta sigma y.1‖ₑ)
              * ‖y.2 * ozBaxterFixedPt eta sigma rho y.2‖ₑ := by ring
    _ = (∫⁻ t, ENNReal.ofReal (2 * t) * ‖t * c_HS eta sigma t‖ₑ ∂(volume.restrict (Set.Ioi 0)))
          * ∫⁻ s, ‖s * ozBaxterFixedPt eta sigma rho s‖ₑ ∂(volume.restrict (Set.Ioi 0)) :=
        lintegral_prod_mul
          (((measurable_const.mul measurable_id).ennreal_ofReal).mul
            (measurable_id.mul ((c_HS_measurable eta sigma))).enorm).aemeasurable
          (measurable_id.mul ozBaxterFixedPt_measurable).enorm.aemeasurable
    _ < ⊤ := ENNReal.mul_lt_top (lintegral_shell_weight_c_HS_lt_top hsigma)
        (hasFiniteIntegral_iff_enorm.mp
          (r_mul_ozBaxterFixedPt_integrableOn_Ioi_zero
            hsigma hrho heta_def heta_lt).hasFiniteIntegral)

/-- **Clause 6h (exterior triple-shell Fubini integrability) — a THEOREM, no axiom.**  The OZ shell
integrand against `ozBaxterFixedPt`, weighted by `sin(k·a)`, is jointly integrable over `(Ioi 0)³`.
A pure absolute-convergence (Tonelli) fact: `∫_a 1_{s∈[|a-t|,a+t]} da ≤ 2t`
(`volume_ozShell_slice_le`), `∫_t t|t·c_HS(t)| dt < ∞` by compact support
(`lintegral_shell_weight_c_HS_lt_top`), and `∫_s |s·ozBaxterFixedPt(s)| ds < ∞` by exterior `L¹`
(`r_mul_ozBaxterFixedPt_integrableOn_Ioi_zero`).  Dominated by `ozShellMajorant`, whose integral is
finite by `lintegral_ozShellMajorant_lt_top`. -/
theorem ozExterior_triple_shell_sin_integrable {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (hrho : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1) :
    ∀ k : ℝ, 0 < k →
    Integrable
      (fun p : ℝ × ℝ × ℝ =>
        (p.2.1 * c_HS eta sigma p.2.1) *
          (Set.Icc |p.1 - p.2.1| (p.1 + p.2.1)).indicator
            (fun s => s * ozBaxterFixedPt eta sigma rho s) p.2.2 *
          Real.sin (k * p.1))
      ((volume.restrict (Set.Ioi 0)).prod
        ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0)))) := by
  intro k _
  -- measurability of the integrand (same shape as clause 6g, one variable deeper)
  have hind_meas : Measurable (fun p : ℝ × ℝ × ℝ =>
      (Set.Icc |p.1 - p.2.1| (p.1 + p.2.1)).indicator
        (fun s => s * ozBaxterFixedPt eta sigma rho s) p.2.2) := by
    have heq : (fun p : ℝ × ℝ × ℝ => (Set.Icc |p.1 - p.2.1| (p.1 + p.2.1)).indicator
          (fun s => s * ozBaxterFixedPt eta sigma rho s) p.2.2)
        = ozShellRegion.indicator
          (fun p => p.2.2 * ozBaxterFixedPt eta sigma rho p.2.2) := by
      funext p
      simp only [ozShellRegion, Set.indicator_apply, Set.mem_Icc, Set.mem_setOf_eq]
    rw [heq]
    exact Measurable.indicator
      ((measurable_snd.comp measurable_snd).mul
        (ozBaxterFixedPt_measurable.comp (measurable_snd.comp measurable_snd)))
      measurableSet_ozShellRegion
  have hF_meas : Measurable (fun p : ℝ × ℝ × ℝ =>
      (p.2.1 * c_HS eta sigma p.2.1) *
        (Set.Icc |p.1 - p.2.1| (p.1 + p.2.1)).indicator
          (fun s => s * ozBaxterFixedPt eta sigma rho s) p.2.2 * Real.sin (k * p.1)) :=
    (((measurable_fst.comp measurable_snd).mul
      ((c_HS_measurable eta sigma).comp (measurable_fst.comp measurable_snd))).mul
        hind_meas).mul (measurable_const.mul measurable_fst).sin
  refine ⟨hF_meas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  -- domination by the majorant: `|sin| ≤ 1`, and the `Icc`-indicator *is* the shell region
  refine lt_of_le_of_lt (lintegral_mono fun p => ?_)
    (lintegral_ozShellMajorant_lt_top hsigma hrho heta_def heta_lt)
  obtain ⟨a, t, s⟩ := p
  have hsin : ‖Real.sin (k * a)‖ₑ ≤ 1 := by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.abs_sin_le_one _)
  simp only [ozShellMajorant, ozShellRegion]
  rw [enorm_mul, enorm_mul, enorm_indicator_eq_indicator_enorm]
  by_cases hmem : s ∈ Set.Icc |a - t| (a + t)
  · rw [Set.indicator_of_mem hmem,
      Set.indicator_of_mem (show ((a, t, s) : ℝ × ℝ × ℝ) ∈ {p : ℝ × ℝ × ℝ |
        |p.1 - p.2.1| ≤ p.2.2 ∧ p.2.2 ≤ p.1 + p.2.1} from Set.mem_Icc.mp hmem)]
    calc ‖t * c_HS eta sigma t‖ₑ * ‖s * ozBaxterFixedPt eta sigma rho s‖ₑ
          * ‖Real.sin (k * a)‖ₑ
        ≤ ‖t * c_HS eta sigma t‖ₑ * ‖s * ozBaxterFixedPt eta sigma rho s‖ₑ * 1 :=
          mul_le_mul' le_rfl hsin
      _ = _ := mul_one _
  · rw [Set.indicator_of_notMem hmem, mul_zero, zero_mul]
    simp

/-- **Clause 6j (exterior convolution/sine integrability) — derived from 6h.**  The radial
convolution `r·(c_HS ⊛₃ ozBaxterFixedPt)(r)·sin(k·r)` is integrable on `(0,∞)`.  It is `2π` times
the `(t,s)`-marginal of the 6h triple integrand: `r·(c_HS ⊛₃ ozBFP)(r) = 2π·∫_t t·c_HS(t)·∫_{[|r-t|,
r+t]} s·ozBFP(s)`, so `2π·∫_{(t,s)} F(r,t,s) = r·(c_HS ⊛₃ ozBFP)(r)·sin(kr)` a.e.; `Fubini`
(`Integrable.integral_prod_left`) makes the marginal integrable in `r`. -/
theorem ozExterior_conv_sin_integrable {eta sigma rho : ℝ} (hsigma : 0 < sigma) (hrho : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1) :
    ∀ k : ℝ, 0 < k →
    Integrable
      (fun r => r * radial3d_conv (c_HS eta sigma) (ozBaxterFixedPt eta sigma rho) r
        * Real.sin (k * r))
      (volume.restrict (Set.Ioi 0)) := by
  intro k hk
  have h6h := ozExterior_triple_shell_sin_integrable hsigma hrho heta_def heta_lt k hk
  refine (h6h.integral_prod_left.const_mul (2 * Real.pi)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi, h6h.prod_right_ae] with r hr hslice
  have hr0 : (0 : ℝ) < r := hr
  -- (c): the `s`-integral over `Ioi 0` with the `Icc`-indicator equals the `Icc` set-integral
  have hc : ∀ t : ℝ, (∫ s in Set.Ioi (0 : ℝ),
        (Set.Icc |r - t| (r + t)).indicator
          (fun s => s * ozBaxterFixedPt eta sigma rho s) s)
      = ∫ s in Set.Icc |r - t| (r + t), s * ozBaxterFixedPt eta sigma rho s := by
    intro t
    rw [MeasureTheory.integral_indicator measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc]
    refine setIntegral_congr_set ?_
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · rw [Set.sdiff_eq_empty.mpr Set.inter_subset_left]; exact measure_empty
    · refine measure_mono_null (fun s hs => ?_) (measure_singleton (0 : ℝ))
      have hs0 : ¬ (0 < s) := fun h => hs.2 ⟨hs.1, h⟩
      have hge : (0 : ℝ) ≤ s := le_trans (abs_nonneg _) hs.1.1
      exact Set.mem_singleton_iff.mpr (le_antisymm (not_lt.mp hs0) hge)
  -- compute the marginal, matching the `radial3d_conv` definition
  rw [integral_prod _ hslice, radial3d_conv, if_neg (not_le.mpr hr0)]
  have hinner : ∀ t : ℝ, (∫ s in Set.Ioi (0 : ℝ),
        t * c_HS eta sigma t *
          (Set.Icc |r - t| (r + t)).indicator
            (fun s => s * ozBaxterFixedPt eta sigma rho s) s * Real.sin (k * r))
      = (t * c_HS eta sigma t *
            ∫ s in Set.Icc |r - t| (r + t), s * ozBaxterFixedPt eta sigma rho s)
          * Real.sin (k * r) := by
    intro t
    rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul, hc t]
  simp only [hinner]
  rw [MeasureTheory.integral_mul_const]
  field_simp

end

end FMSA.HardSphere
