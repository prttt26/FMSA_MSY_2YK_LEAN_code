/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterExteriorRegularityGeneral
import LeanCode.HardSphere.OzBaxterFixedPt
import LeanCode.HardSphere.OzFixedPtDilute

/-!
# Elementary regularity/integrability clauses of `baxter_exterior_regularity` — Task M1.2

This file discharges, as **theorems** (no axiom), the routine clauses of the
`baxter_exterior_regularity` bundle about the constructed Baxter solution `ozBaxterFixedPt`:

* `ozBaxterFixedPt_continuousOn` / `ozBaxterFixedPt_bounded` — the C2/C3 clauses (exterior
  continuity of `baxterPsi/·` and global boundedness), rewired onto the general-`η` decay/bound
  theorems (`baxterPsiOuter_continuousOn_Ici`, `baxterPsi_bounded_Ici`).  Moved here from
  `OzCoreClosure.lean` so the `baxter_exterior_regularity` *assembly* there can consume the
  integrability clauses below without an import cycle.
* `baxterExterior_forcing_integrand_intervalIntegrable` — clauses C4/6e (`oz_forcing` integrand
  interval-integrable), a direct alias of the general-`η` `oz_forcing_integrand_intervalIntegrable`.
* `baxterExterior_linear_op_integrand_intervalIntegrable` — clauses C5/6f (`oz_linear_op`
  shell-integral integrand interval-integrable), via `oz_linear_op_integrand_intervalIntegrable`
  instantiated at the **globally continuous, bounded surrogate** `s ↦ ozBaxterFixedPt (max s σ)`
  (which agrees with `ozBaxterFixedPt` on `[σ,∞)`, the only place the shell integral reads it).
* `baxterExterior_cHS_sin_integrable` — clause 6i (`r·c_HS(r)·sin(kr)` integrable on `(0,∞)`), from
  `c_HS`'s compact support `[0,σ]` and interval integrability.

All are general-`η` (only the physical hypotheses `0<σ`, `0<ρ`, `η<1`, `η=πρσ³/6`), matching what
the `baxter_exterior_regularity` theorem form will carry after Task M1.7.
-/

open MeasureTheory Set Real Filter Topology

namespace FMSA.HardSphere

noncomputable section

/-! ### C2/C3 — exterior continuity and global boundedness (moved from `OzCoreClosure.lean`) -/

/-- `ozBaxterFixedPt` is continuous on the exterior `[σ,∞)` (it equals `baxterPsi/·` there). -/
theorem ozBaxterFixedPt_continuousOn {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (_heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (_heta_lt : eta < 1) :
    ContinuousOn (ozBaxterFixedPt eta sigma rho) (Set.Ici sigma) := by
  -- Structural: `baxterPsiOuter` is continuous on `[σ,∞)`; there `baxterPsi = baxterPsiOuter`, so
  -- `baxterPsi/·` is continuous (÷ nonzero `r`) and equals `ozBaxterFixedPt`. No axiom used.
  have hpsi : ContinuousOn (baxterPsi eta sigma rho) (Set.Ici sigma) :=
    baxterPsiOuter_continuousOn_Ici.congr (fun r hr => baxterPsi_outer hr)
  have hcont : ContinuousOn (fun r => baxterPsi eta sigma rho r / r) (Set.Ici sigma) :=
    hpsi.div continuousOn_id (fun r hr => (lt_of_lt_of_le hsigma hr).ne')
  exact hcont.congr (fun r hr =>
    ozBaxterFixedPt_eq_div hsigma (lt_of_lt_of_le hsigma hr))

/-- `ozBaxterFixedPt` is globally bounded (`1` on the core, `|baxterPsi r|/r ≤ C/σ` outside). -/
theorem ozBaxterFixedPt_bounded {eta sigma rho : ℝ} (hsigma : 0 < sigma) (hrho : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1) :
    ∃ C, ∀ r, |ozBaxterFixedPt eta sigma rho r| ≤ C := by
  have heta0 : 0 < eta := by rw [heta_def]; positivity
  obtain ⟨C0, hC0⟩ := baxterPsi_bounded_Ici heta0 heta_lt hsigma hrho heta_def
  have hC0nonneg : 0 ≤ C0 := le_trans (abs_nonneg _) (hC0 sigma le_rfl)
  have hquot : 0 ≤ C0 / sigma := div_nonneg hC0nonneg hsigma.le
  refine ⟨1 + C0 / sigma, fun r => ?_⟩
  unfold ozBaxterFixedPt
  rcases lt_or_ge r sigma with hr | hr
  · rw [if_pos hr, abs_neg, abs_one]; linarith
  · rw [if_neg (not_lt.mpr hr)]
    have hr0 : 0 < r := lt_of_lt_of_le hsigma hr
    rw [abs_div, abs_of_pos hr0]
    have h1 : |baxterPsi eta sigma rho r| ≤ C0 := hC0 r hr
    have hb2 : |baxterPsi eta sigma rho r| / r ≤ C0 / sigma := by
      have hrr : 1 / r ≤ 1 / sigma := one_div_le_one_div_of_le hsigma hr
      calc |baxterPsi eta sigma rho r| / r
          = |baxterPsi eta sigma rho r| * (1 / r) := by rw [mul_one_div]
        _ ≤ C0 * (1 / sigma) := mul_le_mul h1 hrr (one_div_nonneg.mpr hr0.le) hC0nonneg
        _ = C0 / sigma := by rw [mul_one_div]
    linarith

/-! ### C4/6e — the `oz_forcing` integrand is interval integrable -/

/-- **Clause C4/6e.**  The `oz_forcing` integrand is interval integrable on `[0,σ]` for every
`r ≥ σ` — a direct alias of the general-`η` `oz_forcing_integrand_intervalIntegrable` (it holds for
all `r`, so the `σ ≤ r` hypothesis is discarded). -/
theorem baxterExterior_forcing_integrand_intervalIntegrable {eta sigma : ℝ}
    (hsigma : 0 < sigma) :
    ∀ r, sigma ≤ r → IntervalIntegrable
      (fun t => t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
        (if r < sigma + t then (1 : ℝ) else 0)) volume 0 sigma :=
  fun _ _ => oz_forcing_integrand_intervalIntegrable hsigma

/-! ### C5/6f — the `oz_linear_op` shell-integral integrand is interval integrable -/

/-- **Clause C5/6f.**  The `oz_linear_op` shell-integral integrand
`t ↦ t·c_HS(t)·∫_{max(r-t,σ)}^{r+t} s·ozBaxterFixedPt(s) ds` is interval integrable on `[0,σ]` for
`r ≥ σ`.

`ozBaxterFixedPt` is *not* globally continuous (it jumps at `σ`), so we run the general lemma
`oz_linear_op_integrand_intervalIntegrable` on the globally continuous, bounded **surrogate**
`hc s := ozBaxterFixedPt (max s σ)` (continuous by `ozBaxterFixedPt_continuousOn` composed with the
continuous `s ↦ max s σ`, bounded by `ozBaxterFixedPt_bounded`), then transfer to `ozBaxterFixedPt`
by `intervalIntegral.integral_congr`: on the shell `[max(r-t,σ), r+t] ⊆ [σ,∞)` one has
`max s σ = s`, so the two integrands agree. -/
theorem baxterExterior_linear_op_integrand_intervalIntegrable {eta sigma rho : ℝ}
    (hsigma : 0 < sigma) (hrho : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_lt : eta < 1) :
    ∀ r, sigma ≤ r → IntervalIntegrable
      (fun t => t * c_HS eta sigma t *
        ∫ s in (max (r - t) sigma)..(r + t), s * ozBaxterFixedPt eta sigma rho s)
      volume 0 sigma := by
  intro r hr
  -- globally continuous bounded surrogate agreeing with `ozBaxterFixedPt` on `[σ,∞)`
  set hc : ℝ → ℝ := fun s => ozBaxterFixedPt eta sigma rho (max s sigma) with hc_def
  have hc_cont : Continuous hc := by
    have hmax : Continuous (fun s : ℝ => max s sigma) := by fun_prop
    exact (ozBaxterFixedPt_continuousOn hsigma heta_def heta_lt).comp_continuous hmax
      (fun x => le_max_right x sigma)
  obtain ⟨Cb, hCb⟩ := ozBaxterFixedPt_bounded hsigma hrho heta_def heta_lt
  have hCb0 : 0 ≤ Cb := le_trans (abs_nonneg _) (hCb 0)
  have hNbound : ∀ x, |hc x| ≤ Cb := fun x => hCb (max x sigma)
  have key := oz_linear_op_integrand_intervalIntegrable (eta := eta) hsigma hc_cont hCb0 hNbound hr
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hsigma.le] at key ⊢
  refine key.congr_fun ?_ measurableSet_Icc
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have hle : max (r - t) sigma ≤ r + t := by
    apply max_le
    · linarith
    · linarith [hr]
  change t * c_HS eta sigma t * (∫ s in (max (r - t) sigma)..(r + t), s * hc s)
      = t * c_HS eta sigma t *
        (∫ s in (max (r - t) sigma)..(r + t), s * ozBaxterFixedPt eta sigma rho s)
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hle] at hs
  have hsσ : sigma ≤ s := le_trans (le_max_right (r - t) sigma) hs.1
  simp only [hc_def, max_eq_left hsσ]

/-! ### 6i — `r·c_HS(r)·sin(kr)` is integrable on `(0,∞)` -/

/-- **Clause 6i.**  `r ↦ r·c_HS(r)·sin(kr)` is integrable on `(0,∞)`: `c_HS` vanishes on `[σ,∞)`
(`c_HS_outer`), so the function is supported on `(0,σ]`, where it is a bounded factor `r·sin(kr)`
times the integrable `c_HS` (`c_HS_integrableOn`). -/
theorem baxterExterior_cHS_sin_integrable {eta sigma : ℝ} (hsigma : 0 < sigma) :
    ∀ k, 0 < k → Integrable (fun r => r * c_HS eta sigma r * Real.sin (k * r))
      (volume.restrict (Set.Ioi 0)) := by
  intro k _
  -- integrable on the finite support `(0,σ]`
  have h1 : IntegrableOn (fun r => r * c_HS eta sigma r * Real.sin (k * r)) (Set.Ioc 0 sigma) := by
    have hmeas : AEStronglyMeasurable (fun r : ℝ => r * Real.sin (k * r))
        (volume.restrict (Set.Ioc (0 : ℝ) sigma)) :=
      (continuous_id.mul (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))).aestronglyMeasurable
    have hbdd : ∀ᵐ r ∂(volume.restrict (Set.Ioc (0 : ℝ) sigma)),
        ‖r * Real.sin (k * r)‖ ≤ sigma := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [Real.norm_eq_abs, abs_mul]
      have hrσ : |r| ≤ sigma := by rw [abs_of_pos hr.1]; exact hr.2
      have hsin : |Real.sin (k * r)| ≤ 1 :=
        abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
      calc |r| * |Real.sin (k * r)| ≤ sigma * 1 :=
            mul_le_mul hrσ hsin (abs_nonneg _) hsigma.le
        _ = sigma := mul_one _
    have hcInt : IntegrableOn (c_HS eta sigma) (Set.Ioc 0 sigma) :=
      (c_HS_integrableOn hsigma).mono_set Set.Ioc_subset_Icc_self
    have hmul := hcInt.mul_bdd hmeas hbdd
    exact hmul.congr (Filter.Eventually.of_forall fun r => by ring)
  -- zero (hence integrable) on `(σ,∞)`
  have h2 : IntegrableOn (fun r => r * c_HS eta sigma r * Real.sin (k * r)) (Set.Ioi sigma) := by
    refine (integrableOn_zero (μ := volume) (s := Set.Ioi sigma)).congr_fun ?_ measurableSet_Ioi
    intro r hr
    change (0 : ℝ) = r * c_HS eta sigma r * Real.sin (k * r)
    rw [c_HS_outer (le_of_lt (Set.mem_Ioi.mp hr))]
    ring
  have hunion := h1.union h2
  rw [Set.Ioc_union_Ioi_eq_Ioi hsigma.le] at hunion
  exact hunion

end

end FMSA.HardSphere
