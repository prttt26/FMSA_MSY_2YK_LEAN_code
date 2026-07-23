/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.PYOZ_GHS

/-!
# Task OZ.10-dilute — `oz_fixed_pt_unique` for small `eta` (Banach)

## Summary

`oz_fixed_pt_unique` was a physics axiom (`PYOZ_GHS.lean`); it has since been retired to the
theorem `oz_fixed_pt_unique_thm` (`OzWienerHopfBounded.lean`). This file proves a genuine
(non-axiomatic) restriction of it, `oz_fixed_pt_unique_dilute`, for the dilute regime (`eta < 1`,
`24·eta·bracket < 1`, i.e. `eta ≲ 0.088`), via Banach's contraction-mapping theorem applied to
`oz_operator` restricted to the exterior `[σ,∞)` — see the original axiom's doc comment for the
physical/mathematical background, and `proof_notes_hard_sphere.md` (Task OZ.10-dilute) for the
full writeup, including what's still needed for middle/high density (Fredholm alternative).

**Status: all six pieces DONE, no axiom, no `sorry`.** (1) exterior domain, (2) `T_ext`
continuity, (3) `T_ext` boundedness, (4) contraction estimate, (5) Banach assembly, (6)
translation to the axiom's `∃! h : ℝ → ℝ` shape (plus `heta1 : eta < 1`, a necessary addition
— see `oz_fixed_pt_unique_dilute`'s own doc comment).
-/

open MeasureTheory Set Real intervalIntegral
open scoped BoundedContinuousFunction

namespace FMSA.HardSphere

/-! ### Piece 1 — exterior domain + extension helpers -/

/-- The exterior domain `[σ,∞)`, as a subtype (so `BoundedContinuousFunction` machinery
applies directly). -/
abbrev ExtDom (sigma : ℝ) := {x : ℝ // sigma ≤ x}

/-- Extend `h : ExtDom sigma →ᵇ ℝ` to all of `ℝ` by **clamping** `r` to `σ` before evaluating.
This is a *globally continuous* extension (unlike the eventual `-1`-on-core extension used in
piece 6) — used only internally, for the continuity/contraction arguments, since `oz_linear_op`
never reads `h`'s values below `σ` anyway, so clamping vs. any other extension gives the same
integral values on the domain that matters. -/
noncomputable def extendClamp {sigma : ℝ} (h : ExtDom sigma →ᵇ ℝ) : ℝ → ℝ :=
  fun r => h ⟨max r sigma, le_max_right r sigma⟩

theorem extendClamp_continuous {sigma : ℝ} (h : ExtDom sigma →ᵇ ℝ) :
    Continuous (extendClamp h) :=
  h.continuous.comp ((continuous_id.max continuous_const).subtype_mk _)

theorem extendClamp_eq_of_ge {sigma : ℝ} (h : ExtDom sigma →ᵇ ℝ) {r : ℝ} (hr : sigma ≤ r) :
    extendClamp h r = h ⟨r, hr⟩ := by
  unfold extendClamp
  congr 1
  exact Subtype.ext (max_eq_left hr)

/-- The `-1`-on-core extension (matches `oz_operator`'s own core branch) — used only in piece 6
to build the final `h* : ℝ → ℝ` satisfying `OzFixedPt`. -/
noncomputable def extendCore {sigma : ℝ} (h : ExtDom sigma →ᵇ ℝ) : ℝ → ℝ :=
  fun r => if hr : sigma ≤ r then h ⟨r, hr⟩ else -1

theorem extendCore_eq_of_ge {sigma : ℝ} (h : ExtDom sigma →ᵇ ℝ) {r : ℝ} (hr : sigma ≤ r) :
    extendCore h r = h ⟨r, hr⟩ := dif_pos hr

theorem extendCore_eq_of_lt {sigma : ℝ} (h : ExtDom sigma →ᵇ ℝ) {r : ℝ} (hr : r < sigma) :
    extendCore h r = -1 := dif_neg (not_le.mpr hr)

/-- `extendClamp` and `extendCore` agree wherever `oz_linear_op` ever reads them (`r ≥ σ`), so
they're interchangeable inside `oz_linear_op`'s call. -/
theorem extendClamp_eq_extendCore {sigma : ℝ} (h : ExtDom sigma →ᵇ ℝ) {r : ℝ} (hr : sigma ≤ r) :
    extendClamp h r = extendCore h r := by
  rw [extendClamp_eq_of_ge h hr, extendCore_eq_of_ge h hr]

/-! ### Piece 2 — `T_ext` continuity -/

/-- The `oz_forcing` integrand (measurable, bounded on `[0,σ]` for fixed `r`) is interval
integrable on `[0,σ]` — via `c_HS_integrableOn` (integrable) times the remaining polynomial ×
indicator factor (bounded, measurable), combined via `Integrable.mul_bdd`. -/
theorem oz_forcing_integrand_intervalIntegrable {eta sigma r : ℝ} (hsigma : 0 < sigma) :
    IntervalIntegrable (fun t => t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
      (if r < sigma + t then (1 : ℝ) else 0)) volume 0 sigma := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hsigma.le]
  have hmeas : Measurable (fun t : ℝ => t * (sigma ^ 2 - (r - t) ^ 2) *
      (if r < sigma + t then (1 : ℝ) else 0)) := by
    apply Measurable.mul
    · fun_prop
    · exact measurable_const.ite
        (measurableSet_lt measurable_const (measurable_const.add measurable_id))
        measurable_const
  set C : ℝ := sigma * (sigma ^ 2 + (|r| + sigma) ^ 2) with hC
  have hbdd : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) sigma)),
      ‖t * (sigma ^ 2 - (r - t) ^ 2) * (if r < sigma + t then (1 : ℝ) else 0)‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ sigma := ht.2
    have hrt : |r - t| ≤ |r| + sigma := by
      calc |r - t| ≤ |r| + |t| := abs_sub _ _
        _ ≤ |r| + sigma := by
            have : |t| ≤ sigma := by rw [abs_of_nonneg ht0]; exact ht1
            linarith
    have hsq : (r - t) ^ 2 ≤ (|r| + sigma) ^ 2 := by
      rw [← sq_abs (r - t)]
      exact pow_le_pow_left₀ (abs_nonneg _) hrt 2
    have h1 : |sigma ^ 2 - (r - t) ^ 2| ≤ sigma ^ 2 + (|r| + sigma) ^ 2 := by
      rw [abs_sub_le_iff]
      constructor <;> nlinarith [sq_nonneg (r - t), sq_nonneg (|r| + sigma)]
    rcases le_or_gt sigma 0 with hs0 | hs0
    · linarith [hsigma]
    · split_ifs with hi
      · simp only [mul_one, norm_mul, Real.norm_eq_abs, abs_of_nonneg ht0]
        exact mul_le_mul ht1 h1 (abs_nonneg _) hsigma.le
      · simp only [mul_zero, norm_zero]
        positivity
  have hmul := (c_HS_integrableOn (eta := eta) hsigma).mul_bdd hmeas.aestronglyMeasurable hbdd
  exact hmul.congr (Filter.Eventually.of_forall fun t => by ring)

private theorem oz_forcing_integral_eq_movingBound {eta sigma r : ℝ} (hsigma : 0 < sigma)
    (hr : sigma ≤ r) :
    (∫ t in (0 : ℝ)..sigma, t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
        (if r < sigma + t then (1 : ℝ) else 0)) =
    ∫ t in (min sigma (r - sigma))..sigma,
      t * (-(py_a0 eta + py_a1 eta * (t / sigma) + py_a3 eta * (t / sigma) ^ 3)) *
        (sigma ^ 2 - (r - t) ^ 2) := by
  have hIntFull := oz_forcing_integrand_intervalIntegrable (eta := eta) (r := r) hsigma
  by_cases hcase : sigma ≤ r - sigma
  · -- r ≥ 2σ: indicator is always 0 (since t ≤ σ ⟹ σ+t ≤ 2σ ≤ r), and min = σ so RHS = 0 too.
    rw [min_eq_left hcase, intervalIntegral.integral_same]
    have heq : (∫ t in (0 : ℝ)..sigma, t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
          (if r < sigma + t then (1 : ℝ) else 0)) = ∫ t in (0 : ℝ)..sigma, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hsigma.le] at ht
      change t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
        (if r < sigma + t then (1 : ℝ) else 0) = 0
      rw [if_neg (not_lt.mpr (by linarith [ht.2] : sigma + t ≤ r))]
      ring
    rw [heq]
    simp
  · -- σ ≤ r < 2σ: min = r - σ ∈ [0,σ); split the integral at r-σ.
    push Not at hcase
    have hrs0 : 0 ≤ r - sigma := by linarith
    rw [min_eq_right hcase.le]
    have hmem0 : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) sigma := by
      rw [Set.uIcc_of_le hsigma.le]; exact Set.mem_Icc.mpr ⟨le_refl 0, hsigma.le⟩
    have hmemrs : (r - sigma) ∈ Set.uIcc (0 : ℝ) sigma := by
      rw [Set.uIcc_of_le hsigma.le]; exact Set.mem_Icc.mpr ⟨hrs0, hcase.le⟩
    have hmemsig : sigma ∈ Set.uIcc (0 : ℝ) sigma := by
      rw [Set.uIcc_of_le hsigma.le]; exact Set.mem_Icc.mpr ⟨hsigma.le, le_refl sigma⟩
    have hI1 : IntervalIntegrable (fun t => t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
        (if r < sigma + t then (1 : ℝ) else 0)) volume 0 (r - sigma) :=
      hIntFull.mono_set (Set.uIcc_subset_uIcc hmem0 hmemrs)
    have hI2 : IntervalIntegrable (fun t => t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
        (if r < sigma + t then (1 : ℝ) else 0)) volume (r - sigma) sigma :=
      hIntFull.mono_set (Set.uIcc_subset_uIcc hmemrs hmemsig)
    rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
    have hzeroEq : (∫ t in (0 : ℝ)..(r - sigma), t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
          (if r < sigma + t then (1 : ℝ) else 0)) = ∫ t in (0 : ℝ)..(r - sigma), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hrs0] at ht
      change t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
        (if r < sigma + t then (1 : ℝ) else 0) = 0
      rw [if_neg (not_lt.mpr (by linarith [ht.2] : sigma + t ≤ r))]
      ring
    rw [hzeroEq]
    simp only [intervalIntegral.integral_zero, zero_add]
    -- The indicator is `1` and `c_HS = ` the explicit polynomial on the *open* interval
    -- `(r-σ, σ)` — both facts fail exactly at the single boundary point `t = r-σ` (indicator,
    -- where `σ+t = r`) — `c_HS` itself is only guaranteed to match the polynomial for `t < σ`,
    -- vacuously fine on the open interval — so use `uIoo` congruence rather than
    -- `integral_congr` (which needs equality on the closed `uIcc`).
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [Set.uIoo_of_le hcase.le] at ht
    change t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
        (if r < sigma + t then (1 : ℝ) else 0) =
      t * (-(py_a0 eta + py_a1 eta * (t / sigma) + py_a3 eta * (t / sigma) ^ 3)) *
        (sigma ^ 2 - (r - t) ^ 2)
    rw [if_pos (by linarith [ht.1] : r < sigma + t), c_HS_inner ht.2]
    ring

/-- **`oz_forcing` is continuous on the exterior `[σ,∞)`.** Assembled from the moving-bound
reformulation (`oz_forcing_integral_eq_movingBound`, indicator- and `c_HS`-jump-free) via
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous` (one moving bound,
jointly continuous polynomial integrand) — orientation-reversed since that lemma expects a
moving *upper* bound, not the moving *lower* bound `min σ (r-σ)` appearing here. -/
theorem oz_forcing_continuousOn (eta sigma rho : ℝ) (hsigma : 0 < sigma) :
    ContinuousOn (oz_forcing eta sigma rho) (Set.Ici sigma) := by
  have hcont : Continuous (fun r : ℝ => ∫ t in sigma..(min sigma (r - sigma)),
      t * (-(py_a0 eta + py_a1 eta * (t / sigma) + py_a3 eta * (t / sigma) ^ 3)) *
        (sigma ^ 2 - (r - t) ^ 2)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    · fun_prop
    · fun_prop
  have heq : Set.EqOn (oz_forcing eta sigma rho)
      (fun r => -(Real.pi * rho / r) * -(∫ t in sigma..(min sigma (r - sigma)),
        t * (-(py_a0 eta + py_a1 eta * (t / sigma) + py_a3 eta * (t / sigma) ^ 3)) *
          (sigma ^ 2 - (r - t) ^ 2))) (Set.Ici sigma) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le hsigma hr
    unfold oz_forcing
    rw [if_neg (not_le.mpr hr0), oz_forcing_integral_eq_movingBound hsigma hr,
      intervalIntegral.integral_symm sigma (min sigma (r - sigma))]
  apply ContinuousOn.congr _ heq
  have hne : ∀ r ∈ Set.Ici sigma, r ≠ 0 := fun r hr => (lt_of_lt_of_le hsigma hr).ne'
  exact (((continuousOn_const (c := Real.pi * rho)).div continuousOn_id hne).neg).mul
    hcont.neg.continuousOn

/-- **The inner shell integral `∫ s in max(r-t,σ)..(r+t), s·h(s)` is jointly continuous in
`(r,t)`,** for any continuous `h`. Handles the moving-both-bounds integral via
`integral_interval_sub_left` (anchored at `σ`) plus two applications of the moving-bound
continuity lemma. Factored out of `oz_linear_op_continuousOn` since the boundedness/contraction
estimates (`oz_linear_op_diff_bound`) also need this fact, sliced at a fixed `r`. -/
private theorem oz_inner_shell_continuous {sigma : ℝ} (_hsigma : 0 < sigma) {h : ℝ → ℝ}
    (hh : Continuous h) :
    Continuous (fun p : ℝ × ℝ => ∫ s in (max (p.1 - p.2) sigma)..(p.1 + p.2), s * h s) := by
  have hInt : ∀ a b : ℝ, IntervalIntegrable (fun s => s * h s) volume a b :=
    fun a b => (continuous_id.mul hh).intervalIntegrable a b
  have hG : Continuous (fun p : ℝ × ℝ =>
      (∫ s in sigma..(p.1 + p.2), s * h s) - ∫ s in sigma..(max (p.1 - p.2) sigma), s * h s) := by
    apply Continuous.sub
    · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (_ : ℝ × ℝ) s => s * h s) (by fun_prop)
        (show Continuous (fun p : ℝ × ℝ => p.1 + p.2) by fun_prop)
    · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (_ : ℝ × ℝ) s => s * h s) (by fun_prop)
        (show Continuous (fun p : ℝ × ℝ => max (p.1 - p.2) sigma) by fun_prop)
  have hGeq : ∀ r t : ℝ,
      (∫ s in sigma..(r + t), s * h s) - ∫ s in sigma..(max (r - t) sigma), s * h s =
        ∫ s in (max (r - t) sigma)..(r + t), s * h s := fun r t =>
    intervalIntegral.integral_interval_sub_left
      (hInt sigma (r + t)) (hInt sigma (max (r - t) sigma))
  simpa only [hGeq] using hG

/-- **`oz_linear_op eta sigma rho h` is continuous on the exterior `[σ,∞)`, for any globally
continuous `h`.** The inner integral's joint continuity is `oz_inner_shell_continuous`; the
outer (fixed-bounds) `t`-integral still has `c_HS`'s jump at `t=σ` to remove, via the same
`c_HS_inner`-polynomial swap (`uIoo`/a.e. congruence, single point) used for `oz_forcing`. -/
theorem oz_linear_op_continuousOn {eta sigma rho : ℝ} (hsigma : 0 < sigma) {h : ℝ → ℝ}
    (hh : Continuous h) :
    ContinuousOn (oz_linear_op eta sigma rho h) (Set.Ici sigma) := by
  have hGcont := oz_inner_shell_continuous hsigma hh
  have hOuterEq : Set.EqOn
      (fun r => ∫ t in (0 : ℝ)..sigma, t * c_HS eta sigma t *
        ∫ s in (max (r - t) sigma)..(r + t), s * h s)
      (fun r => ∫ t in (0 : ℝ)..sigma,
        t * (-(py_a0 eta + py_a1 eta * (t / sigma) + py_a3 eta * (t / sigma) ^ 3)) *
          ∫ s in (max (r - t) sigma)..(r + t), s * h s)
      (Set.univ) := by
    intro r _
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [Set.uIoo_of_le hsigma.le] at ht
    change t * c_HS eta sigma t * (∫ s in (max (r - t) sigma)..(r + t), s * h s) =
      t * (-(py_a0 eta + py_a1 eta * (t / sigma) + py_a3 eta * (t / sigma) ^ 3)) *
        ∫ s in (max (r - t) sigma)..(r + t), s * h s
    rw [c_HS_inner ht.2]
  have hOuterCont : Continuous (fun r => ∫ t in (0 : ℝ)..sigma,
      t * (-(py_a0 eta + py_a1 eta * (t / sigma) + py_a3 eta * (t / sigma) ^ 3)) *
        ∫ s in (max (r - t) sigma)..(r + t), s * h s) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    fun_prop (disch := (exact hGcont))
  have heq : Set.EqOn (oz_linear_op eta sigma rho h)
      (fun r => (2 * Real.pi * rho / r) * ∫ t in (0 : ℝ)..sigma,
        t * (-(py_a0 eta + py_a1 eta * (t / sigma) + py_a3 eta * (t / sigma) ^ 3)) *
          ∫ s in (max (r - t) sigma)..(r + t), s * h s) (Set.Ici sigma) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le hsigma hr
    have hOuterEqR := hOuterEq (Set.mem_univ r)
    simp only at hOuterEqR
    unfold oz_linear_op
    rw [if_neg (not_le.mpr hr0), hOuterEqR]
  apply ContinuousOn.congr _ heq
  have hne : ∀ r ∈ Set.Ici sigma, r ≠ 0 := fun r hr => (lt_of_lt_of_le hsigma hr).ne'
  exact ((continuousOn_const (c := 2 * Real.pi * rho)).div continuousOn_id hne).mul
    hOuterCont.continuousOn

/-! ### Piece 3 — `T_ext` boundedness -/

/-- The contraction-bound bracket `py_a0/3+py_a1/4+py_a3/6` is nonnegative for physical
`eta ∈ (0,1)` — a direct corollary of `c_HS_abs_integral` (its LHS is a nonneg integral of an
absolute value). -/
private theorem bracket_nonneg {eta sigma : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) :
    0 ≤ py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6 := by
  have hInt_nonneg : 0 ≤ ∫ t in (0 : ℝ)..sigma, t ^ 2 * |c_HS eta sigma t| :=
    intervalIntegral.integral_nonneg hsigma.le (fun t _ => by positivity)
  rw [c_HS_abs_integral heta0 heta1 hsigma] at hInt_nonneg
  nlinarith [pow_pos hsigma 3]

/-- **`oz_forcing` is bounded, uniformly in `r ≥ σ`,** by `2π|rho|·σ³·bracket` — the
`h`-independent piece of `T_ext`'s bound. The key pointwise estimate is the *tight* bound
`σ²-(r-t)² ≤ 2σt` on the indicator's support (from `σ-(r-t) ≤ t`, itself from `r ≥ σ`),
matching `c_HS_abs_integral`'s `t²|c_HS(t)|` integrand exactly (no slack from a cruder
sup-bound). -/
theorem oz_forcing_bound {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) {r : ℝ} (hr : sigma ≤ r) :
    |oz_forcing eta sigma rho r| ≤
      2 * Real.pi * |rho| * sigma ^ 3 * (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6) := by
  have hr0 : 0 < r := lt_of_lt_of_le hsigma hr
  have hbracket := bracket_nonneg heta0 heta1 hsigma
  have hgbound := c_HS_abs_t2_integrableOn (eta := eta) hsigma
  unfold oz_forcing
  rw [if_neg (not_le.mpr hr0), abs_mul, abs_neg, abs_div, abs_mul, abs_of_pos Real.pi_pos,
    abs_of_pos hr0]
  have hIbound : |∫ t in (0 : ℝ)..sigma, t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
      (if r < sigma + t then (1 : ℝ) else 0)| ≤
      ∫ t in (0 : ℝ)..sigma, 2 * sigma * (t ^ 2 * |c_HS eta sigma t|) := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hsigma.le
      (Filter.Eventually.of_forall (fun t ht => ?_)) (hgbound.const_mul (2 * sigma))
    rw [Set.mem_Ioc] at ht
    obtain ⟨ht0, ht1⟩ := ht
    rw [Real.norm_eq_abs]
    split_ifs with hcase
    · have h1 : sigma - (r - t) ≤ t := by linarith
      have h2 : 0 ≤ r - t := by linarith
      have h3 : sigma + (r - t) ≤ 2 * sigma := by linarith
      have hnn : 0 ≤ sigma ^ 2 - (r - t) ^ 2 := by nlinarith
      have hle : sigma ^ 2 - (r - t) ^ 2 ≤ 2 * sigma * t := by nlinarith
      simp only [abs_mul, mul_one]
      rw [abs_of_nonneg hnn, abs_of_nonneg ht0.le]
      have hfinal := mul_le_mul_of_nonneg_left hle
        (mul_nonneg ht0.le (abs_nonneg (c_HS eta sigma t)))
      nlinarith [hfinal]
    · simp only [mul_zero, abs_zero]
      positivity
  have hXnonneg : 0 ≤ 2 * Real.pi * |rho| * sigma ^ 3 *
      (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6) :=
    mul_nonneg (by positivity) hbracket
  calc Real.pi * |rho| / r *
        |∫ t in (0 : ℝ)..sigma, t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
          (if r < sigma + t then (1 : ℝ) else 0)|
      ≤ Real.pi * |rho| / r * ∫ t in (0 : ℝ)..sigma, 2 * sigma * (t ^ 2 * |c_HS eta sigma t|) :=
        mul_le_mul_of_nonneg_left hIbound (by positivity)
    _ = Real.pi * |rho| / r * (2 * sigma * ∫ t in (0 : ℝ)..sigma, t ^ 2 * |c_HS eta sigma t|) := by
        rw [intervalIntegral.integral_const_mul]
    _ = Real.pi * |rho| / r *
        (2 * sigma * (sigma ^ 3 * (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6))) := by
        rw [c_HS_abs_integral heta0 heta1 hsigma]
    _ ≤ 2 * Real.pi * |rho| * sigma ^ 3 * (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hr0]
        nlinarith [mul_le_mul_of_nonneg_left hr hXnonneg]

/-- **Tight bound on a single inner shell integral,** `|∫ s in max(r-t,σ)..(r+t), s·h(s)| ≤
N·2rt` whenever `|h| ≤ N` pointwise, `t ∈ [0,σ]`, `r ≥ σ`. The exact antiderivative
`∫s ds=(b²-a²)/2` combined with `max(r-t,σ)² ≥ (r-t)²` (from `r-t ≥ 0`, itself from `t≤σ≤r`)
gives the *tight* `2rt` factor — this tightness is what makes the eventual contraction
constant `K` match `hsmall`'s `24η·bracket` exactly, not merely up to some slack. -/
private theorem oz_inner_shell_bound {sigma : ℝ} (hsigma : 0 < sigma) {h : ℝ → ℝ}
    {N : ℝ} (hN0 : 0 ≤ N) (hN : ∀ x, |h x| ≤ N) {r t : ℝ} (hr : sigma ≤ r)
    (ht0 : 0 ≤ t) (ht1 : t ≤ sigma) :
    |∫ s in max (r - t) sigma..(r + t), s * h s| ≤ N * (2 * r * t) := by
  have hAB : max (r - t) sigma ≤ r + t := by
    rcases le_total (r - t) sigma with hc | hc
    · rw [max_eq_right hc]; linarith
    · rw [max_eq_left hc]; linarith
  have hAnn : 0 ≤ max (r - t) sigma := le_trans hsigma.le (le_max_right _ _)
  have hAge : r - t ≤ max (r - t) sigma := le_max_left _ _
  have hrt0 : 0 ≤ r - t := by linarith
  have hstep1 : |∫ s in max (r - t) sigma..(r + t), s * h s| ≤
      ∫ s in max (r - t) sigma..(r + t), s * N := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hAB
      (Filter.Eventually.of_forall (fun s hs => ?_))
      ((continuous_id.mul_const N).intervalIntegrable _ _)
    rw [Set.mem_Ioc] at hs
    have hspos : 0 < s := lt_of_le_of_lt hAnn hs.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hspos]
    exact mul_le_mul_of_nonneg_left (hN s) hspos.le
  have hstep2 : (∫ s in max (r - t) sigma..(r + t), s * N) ≤ N * (2 * r * t) := by
    rw [intervalIntegral.integral_mul_const, integral_id]
    have hsq : (r - t) ^ 2 ≤ max (r - t) sigma ^ 2 := pow_le_pow_left₀ hrt0 hAge 2
    have hkey : (r + t) ^ 2 - max (r - t) sigma ^ 2 ≤ 4 * r * t := by nlinarith [hsq]
    calc ((r + t) ^ 2 - max (r - t) sigma ^ 2) / 2 * N
        ≤ (4 * r * t) / 2 * N := mul_le_mul_of_nonneg_right (by linarith) hN0
      _ = N * (2 * r * t) := by ring
  linarith [hstep1, hstep2]

/-- **`oz_linear_op`'s outer-integral integrand is interval integrable,** for continuous `h`
bounded by `N`. Combines `c_HS`'s known integrability (`c_HS_integrableOn`) with a crude but
sufficient constant bound on the (continuous, hence a.e.-bounded on the compact `[0,σ]`) inner
shell integral, via `Integrable.mul_bdd` — mirrors `oz_forcing_integrand_intervalIntegrable`'s
technique. Only integrability is needed here; the tight numeric bound is applied separately. -/
theorem oz_linear_op_integrand_intervalIntegrable {eta sigma : ℝ}
    (hsigma : 0 < sigma) {h : ℝ → ℝ} (hh : Continuous h) {N : ℝ} (hN0 : 0 ≤ N)
    (hN : ∀ x, |h x| ≤ N) {r : ℝ} (hr : sigma ≤ r) :
    IntervalIntegrable (fun t => t * c_HS eta sigma t *
      ∫ s in max (r - t) sigma..(r + t), s * h s) volume 0 sigma := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hsigma.le]
  have hGcont : Continuous (fun t : ℝ => ∫ s in max (r - t) sigma..(r + t), s * h s) :=
    (oz_inner_shell_continuous hsigma hh).comp (continuous_const.prodMk continuous_id)
  have hbdd : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) sigma)),
      ‖t * ∫ s in max (r - t) sigma..(r + t), s * h s‖ ≤ sigma * (N * (2 * r * sigma)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hbound_inner := oz_inner_shell_bound hsigma hN0 hN hr ht0 ht1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht0]
    have hr0 : 0 < r := lt_of_lt_of_le hsigma hr
    have h1 : t * |∫ s in max (r - t) sigma..(r + t), s * h s| ≤ t * (N * (2 * r * t)) :=
      mul_le_mul_of_nonneg_left hbound_inner ht0
    have hc : 0 ≤ 2 * r * N := mul_nonneg (mul_nonneg (by norm_num) hr0.le) hN0
    have htt : t * t ≤ sigma * sigma := mul_le_mul ht1 ht1 ht0 hsigma.le
    have h2 : t * (N * (2 * r * t)) ≤ sigma * (N * (2 * r * sigma)) := by
      nlinarith [mul_le_mul_of_nonneg_left htt hc]
    linarith
  have hmeas : AEStronglyMeasurable (fun t : ℝ => t * ∫ s in max (r - t) sigma..(r + t), s * h s)
      (volume.restrict (Set.Icc (0 : ℝ) sigma)) :=
    (continuous_id.mul hGcont).aestronglyMeasurable
  have hmul := (c_HS_integrableOn (eta := eta) hsigma).mul_bdd hmeas hbdd
  exact hmul.congr (Filter.Eventually.of_forall fun t => by ring)

/-- **`oz_linear_op` is bounded, uniformly in `r ≥ σ`,** by `4π|rho|·N·σ³·bracket`, for
continuous `h` bounded by `N`. Same `2rt`-tight-bound technique as `oz_forcing_bound`; the
`r` factor cancels *exactly* against `oz_linear_op`'s own `1/r` prefactor (no `r ≥ σ` slack
needed here, unlike `oz_forcing_bound`), which is what makes the contraction constant match
`hsmall` exactly. -/
theorem oz_linear_op_bound {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) {h : ℝ → ℝ} (_hh : Continuous h) {N : ℝ} (hN0 : 0 ≤ N)
    (hN : ∀ x, |h x| ≤ N) {r : ℝ} (hr : sigma ≤ r) :
    |oz_linear_op eta sigma rho h r| ≤
      4 * Real.pi * |rho| * N * sigma ^ 3 * (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6) := by
  have hr0 : 0 < r := lt_of_lt_of_le hsigma hr
  unfold oz_linear_op
  rw [if_neg (not_le.mpr hr0), abs_mul, abs_div, abs_mul, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos Real.pi_pos, abs_of_pos hr0]
  have hIbound : |∫ t in (0 : ℝ)..sigma, t * c_HS eta sigma t *
      ∫ s in max (r - t) sigma..(r + t), s * h s| ≤
      ∫ t in (0 : ℝ)..sigma, 2 * r * N * (t ^ 2 * |c_HS eta sigma t|) := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le hsigma.le
      (Filter.Eventually.of_forall (fun t ht => ?_))
      ((c_HS_abs_t2_integrableOn (eta := eta) hsigma).const_mul (2 * r * N))
    rw [Set.mem_Ioc] at ht
    obtain ⟨ht0, ht1⟩ := ht
    have hb := oz_inner_shell_bound hsigma hN0 hN hr ht0.le ht1
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg ht0.le]
    have h1 : t * (|c_HS eta sigma t| * |∫ s in max (r - t) sigma..(r + t), s * h s|) ≤
        t * (|c_HS eta sigma t| * (N * (2 * r * t))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (abs_nonneg _)) ht0.le
    nlinarith [h1]
  calc 2 * Real.pi * |rho| / r *
        |∫ t in (0 : ℝ)..sigma, t * c_HS eta sigma t *
          ∫ s in max (r - t) sigma..(r + t), s * h s|
      ≤ 2 * Real.pi * |rho| / r *
          ∫ t in (0 : ℝ)..sigma, 2 * r * N * (t ^ 2 * |c_HS eta sigma t|) :=
        mul_le_mul_of_nonneg_left hIbound (by positivity)
    _ = 2 * Real.pi * |rho| / r *
        (2 * r * N * ∫ t in (0 : ℝ)..sigma, t ^ 2 * |c_HS eta sigma t|) := by
        rw [intervalIntegral.integral_const_mul]
    _ = 2 * Real.pi * |rho| / r *
        (2 * r * N * (sigma ^ 3 * (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6))) := by
        rw [c_HS_abs_integral heta0 heta1 hsigma]
    _ = 4 * Real.pi * |rho| * N * sigma ^ 3 * (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6) := by
        field_simp
        ring

/-- **`oz_linear_op` is linear (additive) in `h`,** for continuous bounded `f,g`. Needed to
reduce the contraction estimate to `oz_linear_op_bound` applied to `f - g`. -/
theorem oz_linear_op_sub {eta sigma rho : ℝ} (hsigma : 0 < sigma) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) {Nf Ng : ℝ} (hNf0 : 0 ≤ Nf) (hNf : ∀ x, |f x| ≤ Nf)
    (hNg0 : 0 ≤ Ng) (hNg : ∀ x, |g x| ≤ Ng) {r : ℝ} (hr : sigma ≤ r) :
    oz_linear_op eta sigma rho f r - oz_linear_op eta sigma rho g r =
      oz_linear_op eta sigma rho (fun s => f s - g s) r := by
  have hr0 : 0 < r := lt_of_lt_of_le hsigma hr
  have hIntF := oz_linear_op_integrand_intervalIntegrable (eta := eta) hsigma hf hNf0 hNf hr
  have hIntG := oz_linear_op_integrand_intervalIntegrable (eta := eta) hsigma hg hNg0 hNg hr
  unfold oz_linear_op
  rw [if_neg (not_le.mpr hr0), if_neg (not_le.mpr hr0), if_neg (not_le.mpr hr0), ← mul_sub,
    ← intervalIntegral.integral_sub hIntF hIntG]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  change t * c_HS eta sigma t * (∫ s in max (r - t) sigma..(r + t), s * f s) -
      t * c_HS eta sigma t * (∫ s in max (r - t) sigma..(r + t), s * g s) =
    t * c_HS eta sigma t * ∫ s in max (r - t) sigma..(r + t), s * (f s - g s)
  rw [← mul_sub]
  congr 1
  simp only [mul_sub]
  exact (intervalIntegral.integral_sub ((continuous_id.mul hf).intervalIntegrable _ _)
    ((continuous_id.mul hg).intervalIntegrable _ _)).symm

/-! ### Piece 3c — assembling `T_ext` as a `BoundedContinuousFunction` self-map -/

/-- `extendClamp h` is bounded by `‖h‖`, matching `oz_linear_op_bound`'s hypothesis. -/
private theorem extendClamp_bound {sigma : ℝ} (h : ExtDom sigma →ᵇ ℝ) (x : ℝ) :
    |extendClamp h x| ≤ ‖h‖ := by
  unfold extendClamp
  rw [← Real.norm_eq_abs]
  exact h.norm_coe_le_norm _

/-- The exterior OZ operator's raw (unbundled) action on `ℝ`, before packaging as a
`BoundedContinuousFunction`. -/
noncomputable def T_ext_raw (eta sigma rho : ℝ) (h_ext : ExtDom sigma →ᵇ ℝ) (r : ℝ) : ℝ :=
  oz_forcing eta sigma rho r + oz_linear_op eta sigma rho (extendClamp h_ext) r

private theorem T_ext_raw_continuous {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (h_ext : ExtDom sigma →ᵇ ℝ) :
    Continuous (fun x : ExtDom sigma => T_ext_raw eta sigma rho h_ext x.1) := by
  have hcont : ContinuousOn (fun r => oz_forcing eta sigma rho r +
      oz_linear_op eta sigma rho (extendClamp h_ext) r) (Set.Ici sigma) :=
    (oz_forcing_continuousOn eta sigma rho hsigma).add
      (oz_linear_op_continuousOn hsigma (extendClamp_continuous h_ext))
  exact hcont.comp_continuous continuous_subtype_val (fun x => x.2)

private theorem T_ext_raw_bound {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (h_ext : ExtDom sigma →ᵇ ℝ) (x : ExtDom sigma) :
    ‖T_ext_raw eta sigma rho h_ext x.1‖ ≤
      2 * Real.pi * |rho| * sigma ^ 3 * (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6) +
      4 * Real.pi * |rho| * ‖h_ext‖ * sigma ^ 3 *
        (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6) := by
  rw [Real.norm_eq_abs]
  unfold T_ext_raw
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact oz_forcing_bound heta0 heta1 hsigma x.2
  · exact oz_linear_op_bound heta0 heta1 hsigma (extendClamp_continuous h_ext)
      (norm_nonneg h_ext) (extendClamp_bound h_ext) x.2

/-- **The exterior OZ operator, bundled as a self-map of `ExtDom sigma →ᵇ ℝ`.** Well-defined
(continuous + bounded) via `T_ext_raw_continuous`/`T_ext_raw_bound`, assembled from Piece 2
(continuity) and Piece 3 (boundedness). -/
noncomputable def T_ext (eta sigma rho : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (h_ext : ExtDom sigma →ᵇ ℝ) : ExtDom sigma →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : ExtDom sigma => T_ext_raw eta sigma rho h_ext x.1)
    (T_ext_raw_continuous hsigma h_ext)
    (2 * Real.pi * |rho| * sigma ^ 3 * (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6) +
      4 * Real.pi * |rho| * ‖h_ext‖ * sigma ^ 3 * (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6))
    (T_ext_raw_bound heta0 heta1 hsigma h_ext)

theorem T_ext_apply {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1) (hsigma : 0 < sigma)
    (h_ext : ExtDom sigma →ᵇ ℝ) (x : ExtDom sigma) :
    T_ext eta sigma rho heta0 heta1 hsigma h_ext x = T_ext_raw eta sigma rho h_ext x.1 := rfl

/-! ### Piece 4 — contraction estimate -/

/-- `extendClamp h1 - extendClamp h2` is bounded by `dist h1 h2` — both clamp to the *same*
point, so the difference is exactly a coordinate-difference of `h1,h2`, bounded by
`BoundedContinuousFunction.dist_coe_le_dist`. -/
private theorem extendClamp_sub_bound {sigma : ℝ} (h1 h2 : ExtDom sigma →ᵇ ℝ) (y : ℝ) :
    |extendClamp h1 y - extendClamp h2 y| ≤ dist h1 h2 := by
  unfold extendClamp
  rw [← Real.dist_eq]
  exact BoundedContinuousFunction.dist_coe_le_dist _

/-- **`T_ext` is a contraction with constant `K := 4π|rho|·σ³·bracket`.** `oz_forcing` cancels
in the difference (it doesn't depend on `h`); the remainder is exactly `oz_linear_op_bound`
applied to `extendClamp h1 - extendClamp h2` (via `oz_linear_op_sub`), bounded pointwise by
`dist h1 h2` (`extendClamp_sub_bound`). -/
theorem T_ext_contracting {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (h1 h2 : ExtDom sigma →ᵇ ℝ) :
    dist (T_ext eta sigma rho heta0 heta1 hsigma h1) (T_ext eta sigma rho heta0 heta1 hsigma h2) ≤
      4 * Real.pi * |rho| * sigma ^ 3 * (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6) *
        dist h1 h2 := by
  set K := 4 * Real.pi * |rho| * sigma ^ 3 * (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6)
    with hK_def
  have hbracket := bracket_nonneg heta0 heta1 hsigma
  have hK0 : 0 ≤ K := mul_nonneg (by positivity) hbracket
  have hC0 : 0 ≤ K * dist h1 h2 := mul_nonneg hK0 dist_nonneg
  apply (BoundedContinuousFunction.dist_le hC0).mpr
  intro x
  rw [T_ext_apply, T_ext_apply, Real.dist_eq]
  unfold T_ext_raw
  have hcancel : oz_forcing eta sigma rho x.1 + oz_linear_op eta sigma rho (extendClamp h1) x.1 -
      (oz_forcing eta sigma rho x.1 + oz_linear_op eta sigma rho (extendClamp h2) x.1) =
      oz_linear_op eta sigma rho (extendClamp h1) x.1 -
        oz_linear_op eta sigma rho (extendClamp h2) x.1 := by ring
  rw [hcancel, oz_linear_op_sub hsigma (extendClamp_continuous h1) (extendClamp_continuous h2)
    (norm_nonneg h1) (extendClamp_bound h1) (norm_nonneg h2) (extendClamp_bound h2) x.2]
  calc |oz_linear_op eta sigma rho (fun s => extendClamp h1 s - extendClamp h2 s) x.1|
      ≤ 4 * Real.pi * |rho| * dist h1 h2 * sigma ^ 3 *
          (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6) :=
        oz_linear_op_bound heta0 heta1 hsigma
          ((extendClamp_continuous h1).sub (extendClamp_continuous h2)) dist_nonneg
          (fun y => extendClamp_sub_bound h1 h2 y) x.2
    _ = K * dist h1 h2 := by rw [hK_def]; ring

/-! ### Piece 5 — Banach fixed-point assembly -/

/-- The contraction constant `K := 4π|rho|·σ³·bracket`, as a plain real number. -/
noncomputable def T_ext_K (eta sigma rho : ℝ) : ℝ :=
  4 * Real.pi * |rho| * sigma ^ 3 * (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6)

theorem T_ext_K_nonneg {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) : 0 ≤ T_ext_K eta sigma rho :=
  mul_nonneg (by positivity) (bracket_nonneg heta0 heta1 hsigma)

theorem T_ext_lipschitzWith {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) :
    LipschitzWith (Real.toNNReal (T_ext_K eta sigma rho))
      (T_ext eta sigma rho heta0 heta1 hsigma) := by
  apply LipschitzWith.of_dist_le_mul
  intro h1 h2
  rw [Real.coe_toNNReal _ (T_ext_K_nonneg heta0 heta1 hsigma)]
  exact T_ext_contracting heta0 heta1 hsigma h1 h2

/-- **`T_ext` is a contraction (Banach's theorem hypothesis), given `K < 1`.** The `K < 1`
hypothesis is discharged from `hsmall` at the call site (`oz_fixed_pt_unique_dilute`), via the
`eta = π·ρ·σ³/6` identity. -/
theorem T_ext_contractingWith {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hK1 : T_ext_K eta sigma rho < 1) :
    ContractingWith (Real.toNNReal (T_ext_K eta sigma rho))
      (T_ext eta sigma rho heta0 heta1 hsigma) :=
  ⟨(Real.toNNReal_lt_iff_lt_coe (T_ext_K_nonneg heta0 heta1 hsigma)).mpr (by simpa using hK1),
    T_ext_lipschitzWith heta0 heta1 hsigma⟩

/-- **The (unique, within `ExtDom sigma →ᵇ ℝ`) exterior OZ fixed point,** via Banach's
fixed-point theorem (`ContractingWith.fixedPoint`). -/
noncomputable def h_ext_star (eta sigma rho : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hK1 : T_ext_K eta sigma rho < 1) : ExtDom sigma →ᵇ ℝ :=
  (T_ext_contractingWith heta0 heta1 hsigma hK1).fixedPoint

theorem h_ext_star_isFixedPt {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hK1 : T_ext_K eta sigma rho < 1) :
    T_ext eta sigma rho heta0 heta1 hsigma (h_ext_star eta sigma rho heta0 heta1 hsigma hK1) =
      h_ext_star eta sigma rho heta0 heta1 hsigma hK1 :=
  (T_ext_contractingWith heta0 heta1 hsigma hK1).fixedPoint_isFixedPt

theorem h_ext_star_unique {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hK1 : T_ext_K eta sigma rho < 1) {h_ext : ExtDom sigma →ᵇ ℝ}
    (hfp : T_ext eta sigma rho heta0 heta1 hsigma h_ext = h_ext) :
    h_ext = h_ext_star eta sigma rho heta0 heta1 hsigma hK1 :=
  (T_ext_contractingWith heta0 heta1 hsigma hK1).fixedPoint_unique hfp

/-! ### Piece 6 — translation to the `∃! h : ℝ → ℝ` shape -/

/-- **`oz_linear_op` only ever reads its function argument on `[σ,∞)`,** so it agrees for any
two functions that agree there — regardless of what they do below `σ`. The integration domain
`[max(r-t,σ), r+t] ⊆ [σ,∞)` always (given `r ≥ σ`, `t ∈ [0,σ]`), which is exactly the fact
flagged in Piece 1 as sidestepping the core/exterior gluing issue that caused the earlier
`oz_fixed_pt_unique` contradiction. -/
private theorem oz_linear_op_congr_on_ext {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    {f g : ℝ → ℝ} {r : ℝ} (hr : sigma ≤ r) (hfg : ∀ s, sigma ≤ s → f s = g s) :
    oz_linear_op eta sigma rho f r = oz_linear_op eta sigma rho g r := by
  have hr0 : 0 < r := lt_of_lt_of_le hsigma hr
  unfold oz_linear_op
  rw [if_neg (not_le.mpr hr0), if_neg (not_le.mpr hr0)]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  simp only
  rw [Set.uIcc_of_le hsigma.le] at ht
  obtain ⟨ht0, ht1⟩ := ht
  congr 1
  have hAB : max (r - t) sigma ≤ r + t := by
    rcases le_total (r - t) sigma with hc | hc
    · rw [max_eq_right hc]; linarith
    · rw [max_eq_left hc]; linarith
  apply intervalIntegral.integral_congr
  intro s hs
  simp only
  rw [Set.uIcc_of_le hAB] at hs
  have hsge : sigma ≤ s := le_trans (le_max_right (r - t) sigma) hs.1
  rw [hfg s hsge]

theorem h_star_isFixedPt {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hK1 : T_ext_K eta sigma rho < 1) :
    OzFixedPt eta sigma rho (extendCore (h_ext_star eta sigma rho heta0 heta1 hsigma hK1)) := by
  intro r
  rcases lt_or_ge r sigma with hr | hr
  · rw [oz_operator_core _ hr, extendCore_eq_of_lt _ hr]
  · unfold oz_operator
    rw [if_neg (not_lt.mpr hr), extendCore_eq_of_ge _ hr,
      oz_linear_op_congr_on_ext hsigma hr
        (fun s hs => (extendClamp_eq_extendCore
          (h_ext_star eta sigma rho heta0 heta1 hsigma hK1) hs).symm)]
    have hpt := DFunLike.congr_fun (h_ext_star_isFixedPt heta0 heta1 hsigma hK1)
      (⟨r, hr⟩ : ExtDom sigma)
    rwa [T_ext_apply] at hpt

theorem h_star_continuousOn {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hK1 : T_ext_K eta sigma rho < 1) :
    ContinuousOn (extendCore (h_ext_star eta sigma rho heta0 heta1 hsigma hK1))
      (Set.Ici sigma) := by
  apply ContinuousOn.congr (extendClamp_continuous
    (h_ext_star eta sigma rho heta0 heta1 hsigma hK1)).continuousOn
  intro r hr
  exact (extendClamp_eq_extendCore _ hr).symm

theorem h_star_bounded {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hK1 : T_ext_K eta sigma rho < 1) :
    ∃ C, ∀ r, |extendCore (h_ext_star eta sigma rho heta0 heta1 hsigma hK1) r| ≤ C := by
  refine ⟨max 1 ‖h_ext_star eta sigma rho heta0 heta1 hsigma hK1‖, fun r => ?_⟩
  rcases lt_or_ge r sigma with hr | hr
  · rw [extendCore_eq_of_lt _ hr, abs_neg, abs_one]
    exact le_max_left _ _
  · rw [extendCore_eq_of_ge _ hr, ← Real.norm_eq_abs]
    exact le_trans ((h_ext_star eta sigma rho heta0 heta1 hsigma hK1).norm_coe_le_norm _)
      (le_max_right _ _)

/-- **The dilute-regime uniqueness theorem — a genuine (non-axiomatic) restriction of
`oz_fixed_pt_unique_thm` to `eta < eta* ≈ 0.088`.** Compared to that theorem's stated signature, this
adds `heta1 : eta < 1`: `hsmall` alone does *not* force `eta < 1` (e.g. `eta = 5` satisfies
`24·eta·bracket < 1` too, since the bracket goes negative there) but `eta < 1` is needed for
`c_HS`'s sign lemma (`c_HS_neg`) and closed form (`c_HS_abs_integral`), both used throughout —
physically `eta` is a packing fraction, so `eta < 1` is not a real restriction.

Proof: `heta_def` + `heta_pos` + `hsigma` force `rho > 0`, so `4π|rho|σ³ = 4·(π·rho·σ³) = 24η`
exactly (via `heta_def`), making `T_ext_K eta sigma rho = 24·eta·bracket`, i.e. *exactly*
`hsmall`'s LHS — so `hsmall` gives `T_ext_K < 1` directly, no slack. Banach's theorem
(`T_ext_contractingWith`/`h_ext_star`) then gives existence+uniqueness on the exterior
`ExtDom sigma →ᵇ ℝ`; `extendCore` glues in the forced core value `-1`, and
`oz_linear_op_congr_on_ext` (using that `oz_linear_op` never reads below `σ`) transports the
exterior fixed-point property back to a genuine `OzFixedPt` on all of `ℝ`. -/
theorem oz_fixed_pt_unique_dilute (eta sigma rho : ℝ) (hsigma : 0 < sigma)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (heta_pos : 0 < eta) (heta1 : eta < 1)
    (hsmall : 24 * eta * (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6) < 1) :
    ∃! h : ℝ → ℝ, OzFixedPt eta sigma rho h ∧ ContinuousOn h (Set.Ici sigma) ∧
      ∃ C, ∀ r, |h r| ≤ C := by
  have hrho_eq : rho = 6 * eta / (Real.pi * sigma ^ 3) := by rw [heta_def]; field_simp
  have hrho_pos : 0 < rho := by rw [hrho_eq]; positivity
  have h6eta : Real.pi * rho * sigma ^ 3 = 6 * eta := by rw [heta_def]; ring
  have hTextK_eq : T_ext_K eta sigma rho =
      24 * eta * (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6) := by
    unfold T_ext_K
    rw [abs_of_pos hrho_pos]
    have h24eta : (4 : ℝ) * Real.pi * rho * sigma ^ 3 = 24 * eta := by linear_combination 4 * h6eta
    rw [h24eta]
  have hK1 : T_ext_K eta sigma rho < 1 := hTextK_eq ▸ hsmall
  refine ⟨extendCore (h_ext_star eta sigma rho heta_pos heta1 hsigma hK1),
    ⟨h_star_isFixedPt heta_pos heta1 hsigma hK1, h_star_continuousOn heta_pos heta1 hsigma hK1,
      h_star_bounded heta_pos heta1 hsigma hK1⟩, ?_⟩
  rintro h' ⟨hfp', hcont', C, hbound'⟩
  have hcont'' : Continuous (fun x : ExtDom sigma => h' x.1) :=
    hcont'.comp_continuous continuous_subtype_val (fun x => x.2)
  set h'_ext : ExtDom sigma →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun x : ExtDom sigma => h' x.1) hcont'' C
      (fun x => by rw [Real.norm_eq_abs]; exact hbound' x.1) with h'_ext_def
  have hextclamp_eq : ∀ s, sigma ≤ s → extendClamp h'_ext s = h' s := by
    intro s hs
    rw [extendClamp_eq_of_ge h'_ext hs]
    rfl
  have hfixed : T_ext eta sigma rho heta_pos heta1 hsigma h'_ext = h'_ext := by
    apply DFunLike.ext
    intro x
    rw [T_ext_apply]
    unfold T_ext_raw
    have hshow : h'_ext x = h' x.1 := rfl
    rw [hshow, oz_linear_op_congr_on_ext hsigma x.2 hextclamp_eq]
    exact (oz_fixed_pt_exterior hfp' x.2).symm
  have heq_ext : h'_ext = h_ext_star eta sigma rho heta_pos heta1 hsigma hK1 :=
    h_ext_star_unique heta_pos heta1 hsigma hK1 hfixed
  funext r
  rcases lt_or_ge r sigma with hr | hr
  · rw [extendCore_eq_of_lt _ hr]
    exact oz_fixed_pt_core hfp' hr
  · rw [extendCore_eq_of_ge _ hr]
    have hshow2 : h'_ext ⟨r, hr⟩ = h' r := rfl
    rw [← hshow2, heq_ext]

end FMSA.HardSphere
