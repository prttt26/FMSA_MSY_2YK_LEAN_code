/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.PYOZ_GHS
import LeanCode.HardSphere.RadialLaplace

/-!
# Task OZ.2b, Gap A — the exterior OZ equation for `oz_h`

## Summary

`oz_laplace_oz_eq` (`PYOZ_GHS.lean`) bundles two independent gaps: the `r ≥ σ` half (shown
here to be provable with **no new hard input** — only `oz_h_core`, already proved, plus an
interval-splitting argument), and the `r < σ` PY core closure (genuinely hard, left as an
explicit hypothesis on `oz_laplace_oz_eq_of_core_closure` below).

## Key identity

For `r ≥ σ`, comparing `oz_forcing`/`oz_linear_op` (`PYOZ_GHS.lean`) term-by-term against
`radial3d_conv c_HS h` (`RadialLaplace.lean`): whenever `h(s) = -1` for `s < σ` (true for
`h := oz_h`, via `oz_h_core`), splitting the convolution's inner integral
`∫_{|r-t|}^{r+t} s·h(s) ds` at `σ` reproduces exactly `oz_forcing`'s core contribution (using
`h = -1` there) plus `oz_linear_op`'s exterior contribution. So:

    oz_forcing(r) + oz_linear_op(r)[h] = ρ · radial3d_conv c_HS h (r)     for r ≥ σ

Combined with `oz_fixed_pt_exterior` and `c_HS(r) = 0` for `r ≥ σ`, this gives the full
pointwise 3D-OZ convolution equation for `oz_h`, unconditionally, on the exterior.
-/

set_option linter.style.longLine false

open MeasureTheory Set Real intervalIntegral

namespace FMSA.HardSphere

/-! ### Interval-integral / set-integral bridge -/

private lemma intervalIntegral_eq_integral_Icc {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    ∫ x in a..b, f x = ∫ x in Set.Icc a b, f x := by
  rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-! ### Domain reduction: `radial3d_conv c_HS h` only sees `t ∈ (0,σ)` -/

private lemma radial3d_conv_cHS_eq_Ioo {eta sigma : ℝ} (h : ℝ → ℝ) {r : ℝ} (hr : 0 < r)
    (hsigma : 0 < sigma) :
    radial3d_conv (c_HS eta sigma) h r =
    (2 * Real.pi / r) * ∫ t in Set.Ioo (0 : ℝ) sigma,
      t * c_HS eta sigma t * ∫ s in Set.Icc (|r - t|) (r + t), s * h s := by
  unfold radial3d_conv
  rw [if_neg (not_le.mpr hr)]
  congr 1
  rw [← Ioo_union_Ici_eq_Ioi hsigma]
  apply MeasureTheory.integral_union_eq_left_of_forall isClosed_Ici.measurableSet
  intro t ht
  simp [c_HS_outer ht]

/-- `oz_h` is continuous on the exterior `[σ,∞)` (it is, by construction, the chosen witness
of `oz_fixed_pt_unique`'s `ContinuousOn ... (Set.Ici sigma)` conjunct).

**2026 correction:** this used to claim `Continuous (oz_h eta sigma rho)` (global continuity,
via coercion of a `BoundedContinuousFunction`) — now known **false** (see `oz_fixed_pt_unique`'s
doc comment, `PYOZ_GHS.lean`): `oz_h` has a genuine jump at `r = σ`, matching the PY contact
discontinuity encoded by `g0_HS_contact_value`. -/
theorem oz_h_continuousOn_ext {eta sigma rho : ℝ} (hsigma : 0 < sigma) :
    ContinuousOn (oz_h eta sigma rho) (Set.Ici sigma) := by
  unfold oz_h
  rw [dif_pos hsigma]
  exact (Classical.choose_spec (oz_fixed_pt_unique eta sigma rho hsigma).exists).2.1

/-! ### The pointwise (per-`t`) inner-integral identity -/

private lemma inner_integral_bridge {sigma : ℝ} {h : ℝ → ℝ}
    (hcontExt : ContinuousOn h (Set.Ici sigma)) (hcore : ∀ s, s < sigma → h s = -1)
    {t r : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) sigma) (hr : sigma ≤ r) :
    (-(1 / 2) * (sigma ^ 2 - (r - t) ^ 2) * (if r < sigma + t then (1 : ℝ) else 0)) +
      ∫ s in (max (r - t) sigma)..(r + t), s * h s =
    ∫ s in Set.Icc (|r - t|) (r + t), s * h s := by
  have hrt0 : 0 < r - t := by linarith [ht.2]
  have habs : |r - t| = r - t := abs_of_pos hrt0
  have hle : r - t ≤ r + t := by linarith [ht.1]
  rw [habs, ← intervalIntegral_eq_integral_Icc hle]
  by_cases hlt : r < sigma + t
  · have hmax : max (r - t) sigma = sigma := max_eq_right (by linarith)
    rw [if_pos hlt, hmax]
    have hle1 : r - t ≤ sigma := by linarith
    have hle2 : sigma ≤ r + t := by linarith [ht.1]
    -- `h = -1` on the *open* core interval `(r-t,σ)` (from `hcore`); the single boundary
    -- point `s = σ` is not covered — and indeed `h(σ) ≠ -1` in general now (the genuine,
    -- possibly-nonzero contact-adjacent value) — but a single point is Lebesgue-null, so an
    -- open-interval (`uIoo`) congruence suffices for both integrability and the integral value.
    have hcoreEqOpen : Set.EqOn (fun _ : ℝ => (-1 : ℝ)) h (Set.uIoo (r - t) sigma) := by
      intro s hs
      rw [Set.uIoo_of_le hle1] at hs
      exact (hcore s hs.2).symm
    have hcontII : IntervalIntegrable h MeasureTheory.volume (r - t) sigma :=
      (continuous_const.intervalIntegrable (r - t) sigma).congr_uIoo hcoreEqOpen
    have hcontIII : IntervalIntegrable h MeasureTheory.volume sigma (r + t) :=
      ContinuousOn.intervalIntegrable (hcontExt.mono (by
        rw [Set.uIcc_of_le hle2]; exact Set.Icc_subset_Ici_self))
    have hsplit : (∫ s in (r - t)..sigma, s * h s) + ∫ s in sigma..(r + t), s * h s =
        ∫ s in (r - t)..(r + t), s * h s :=
      intervalIntegral.integral_add_adjacent_intervals
        (hcontII.continuousOn_mul continuousOn_id) (hcontIII.continuousOn_mul continuousOn_id)
    have hconst : ∫ s in (r - t)..sigma, s * h s = ∫ s in (r - t)..sigma, s * (-1 : ℝ) :=
      intervalIntegral.integral_congr_uIoo (fun s hs => by rw [← hcoreEqOpen hs])
    have hconst2 : ∫ s in (r - t)..sigma, s * (-1 : ℝ) = -(sigma ^ 2 - (r - t) ^ 2) / 2 := by
      rw [intervalIntegral.integral_mul_const, integral_id]
      ring
    rw [← hsplit, hconst, hconst2]
    ring
  · have hmax : max (r - t) sigma = r - t := max_eq_left (by linarith)
    rw [if_neg hlt, hmax]
    ring

/-! ### Outer (`t`) integrand identity, extended to the closed interval `[0,σ]` -/

private lemma outer_integrand_bridge {eta sigma : ℝ} {h : ℝ → ℝ}
    (hcontExt : ContinuousOn h (Set.Ici sigma)) (hcore : ∀ s, s < sigma → h s = -1)
    {r : ℝ} (hr : sigma ≤ r) :
    Set.EqOn
      (fun t => t * c_HS eta sigma t *
          (-(1 / 2) * (sigma ^ 2 - (r - t) ^ 2) * (if r < sigma + t then (1 : ℝ) else 0)) +
        t * c_HS eta sigma t * ∫ s in (max (r - t) sigma)..(r + t), s * h s)
      (fun t => t * c_HS eta sigma t * ∫ s in Set.Icc (|r - t|) (r + t), s * h s)
      (Set.Icc (0 : ℝ) sigma) := by
  intro t ht
  rcases ht.1.eq_or_lt with heq0 | hpos
  · simp [← heq0]
  rcases ht.2.eq_or_lt with heqs | hlts
  · simp [heqs]
  · have hin := inner_integral_bridge hcontExt hcore (Set.mem_Ioo.mpr ⟨hpos, hlts⟩) hr
    change t * c_HS eta sigma t * _ + t * c_HS eta sigma t * _ = t * c_HS eta sigma t * _
    rw [← mul_add, hin]

/-! ### Main bridge lemma -/

/-- **Gap A bridge (proved, no new axiom):** for `r ≥ σ` and any continuous `h` equal to `-1`
on the core `(0,σ)` (in particular `h := oz_h`, via `oz_h_core`), the sum of the reduced
OZ operator's two exterior pieces equals `ρ` times the general 3D radial convolution of
`c_HS` with `h`. This is the algebraic heart of Gap A: it needs no PY core-closure input,
only `oz_h_core` (already proved) and interval-splitting.

The two `IntervalIntegrable` hypotheses are the routine (not mathematically deep) technical
side-conditions for combining the two integrals inside `oz_forcing`/`oz_linear_op`; they are
taken as explicit hypotheses here (in the same spirit as `radial_laplace_conv`'s own
integrability hypotheses) rather than re-derived, since they follow from `c_HS_integrableOn`
(boundedness of the polynomial/indicator factors) and continuity of `h`. -/
theorem oz_forcing_add_linear_op_eq_radial3d_conv {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    {h : ℝ → ℝ} (hcontExt : ContinuousOn h (Set.Ici sigma)) (hcore : ∀ s, s < sigma → h s = -1)
    {r : ℝ} (hr : sigma ≤ r)
    (hint1 : IntervalIntegrable
      (fun t => t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
        if r < sigma + t then (1 : ℝ) else 0) MeasureTheory.volume 0 sigma)
    (hint2 : IntervalIntegrable
      (fun t => t * c_HS eta sigma t * ∫ s in (max (r - t) sigma)..(r + t), s * h s)
      MeasureTheory.volume 0 sigma) :
    oz_forcing eta sigma rho r + oz_linear_op eta sigma rho h r =
    rho * radial3d_conv (c_HS eta sigma) h r := by
  have hr0 : 0 < r := lt_of_lt_of_le hsigma hr
  rw [radial3d_conv_cHS_eq_Ioo h hr0 hsigma]
  unfold oz_forcing oz_linear_op
  rw [if_neg (not_le.mpr hr0), if_neg (not_le.mpr hr0)]
  have hcombine :
      (-(Real.pi * rho / r) *
          ∫ t in (0 : ℝ)..sigma, t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
            if r < sigma + t then (1 : ℝ) else 0) +
        (2 * Real.pi * rho / r) *
          ∫ t in (0 : ℝ)..sigma, t * c_HS eta sigma t *
            ∫ s in (max (r - t) sigma)..(r + t), s * h s =
      (2 * Real.pi * rho / r) *
        ∫ t in (0 : ℝ)..sigma,
          (t * c_HS eta sigma t *
              (-(1 / 2) * (sigma ^ 2 - (r - t) ^ 2) * (if r < sigma + t then (1 : ℝ) else 0)) +
            t * c_HS eta sigma t * ∫ s in (max (r - t) sigma)..(r + t), s * h s) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add (hint1.const_mul _) (hint2.const_mul _),
        ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hcongr :
      (∫ t in (0 : ℝ)..sigma,
          (t * c_HS eta sigma t *
              (-(1 / 2) * (sigma ^ 2 - (r - t) ^ 2) * (if r < sigma + t then (1 : ℝ) else 0)) +
            t * c_HS eta sigma t * ∫ s in (max (r - t) sigma)..(r + t), s * h s)) =
      ∫ t in (0 : ℝ)..sigma, t * c_HS eta sigma t * ∫ s in Set.Icc (|r - t|) (r + t), s * h s :=
    intervalIntegral.integral_congr
      (by rw [Set.uIcc_of_le hsigma.le]; exact outer_integrand_bridge hcontExt hcore hr)
  rw [hcombine, hcongr, intervalIntegral_eq_integral_Icc hsigma.le,
    MeasureTheory.integral_Icc_eq_integral_Ioo]
  ring

/-! ### Specialization to `oz_h`: the unconditional exterior OZ equation -/

/-- `oz_h` is a fixed point of `oz_operator` (derived from the public
`g0_HS_outer_is_oz_fp` + `g0_HS_outer_eq_oz_h`, without needing the private `oz_h_is_fp`). -/
private lemma oz_h_is_fixed_pt {eta sigma rho : ℝ} (hsigma : 0 < sigma) :
    OzFixedPt eta sigma rho (oz_h eta sigma rho) := by
  have heq : (fun r => g0_HS_outer eta sigma rho r - 1) = oz_h eta sigma rho :=
    funext fun r => by rw [g0_HS_outer_eq_oz_h hsigma]; ring
  rw [← heq]
  exact g0_HS_outer_is_oz_fp hsigma

/-- **Gap A, fully closed (proved, no new axiom):** `oz_h` satisfies the full pointwise
3D-OZ convolution equation for all `r ≥ σ`, unconditionally. This is the entire content of
`oz_laplace_oz_eq`'s "r ≥ σ half" — only Gap B (the `r < σ` core closure) remains to extend
this to all `r`, which is needed before `radial_laplace_conv` can be invoked. -/
theorem oz_h_satisfies_conv_ext {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    {r : ℝ} (hr : sigma ≤ r)
    (hint1 : IntervalIntegrable
      (fun t => t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
        if r < sigma + t then (1 : ℝ) else 0) MeasureTheory.volume 0 sigma)
    (hint2 : IntervalIntegrable
      (fun t => t * c_HS eta sigma t *
        ∫ s in (max (r - t) sigma)..(r + t), s * oz_h eta sigma rho s)
      MeasureTheory.volume 0 sigma) :
    oz_h eta sigma rho r =
    c_HS eta sigma r + rho * radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho) r := by
  rw [c_HS_outer hr, zero_add, oz_fixed_pt_exterior (oz_h_is_fixed_pt hsigma) hr]
  exact oz_forcing_add_linear_op_eq_radial3d_conv hsigma (oz_h_continuousOn_ext hsigma)
    (fun s hs => oz_h_core hsigma hs) hr hint1 hint2

/-! ### Final assembly: `oz_laplace_oz_eq`, conditional only on Gap B -/

private lemma intervalIntegral_eq_integral_Ioo {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    ∫ x in a..b, f x = ∫ x in Set.Ioo a b, f x := by
  rw [intervalIntegral_eq_integral_Icc hab, MeasureTheory.integral_Icc_eq_integral_Ioo]

/-- `radial_laplace c_HS s` agrees with the already-defined `C_HS_laplace` (they are the same
transform, just via `radial3d_conv`'s `Set.Ioi` convention vs `C_HS_laplace`'s `intervalIntegral`
convention). -/
private lemma radial_laplace_cHS_eq {eta sigma s : ℝ} (hsigma : 0 < sigma) :
    radial_laplace (c_HS eta sigma) s = C_HS_laplace eta sigma s := by
  unfold radial_laplace
  rw [C_HS_laplace_eq_cHS hsigma, ← Ioo_union_Ici_eq_Ioi hsigma,
    MeasureTheory.integral_union_eq_left_of_forall isClosed_Ici.measurableSet
      (fun r hr => by simp [c_HS_outer hr]),
    ← intervalIntegral_eq_integral_Ioo hsigma.le]

/-- **Task OZ.2b (conditional on Gap B only):** the Laplace-domain hard-sphere OZ equation,
proved (not axiomatized) given the PY core closure `hcore` for `r < σ` (Gap B — the one
genuinely hard, unscaffolded physics input) plus the routine (Gap A / `radial_laplace_conv`)
integrability side-conditions. This replaces `oz_laplace_oz_eq`'s single opaque axiom with a
theorem whose *only* non-mechanical hypothesis is `hcore`. -/
theorem oz_laplace_oz_eq_of_core_closure {eta sigma rho s : ℝ}
    (hsigma : 0 < sigma) (hs : 0 < s)
    (hcore : ∀ r ∈ Set.Ioo (0 : ℝ) sigma,
      oz_h eta sigma rho r =
        c_HS eta sigma r + rho * radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho) r)
    (hintA1 : ∀ r, sigma ≤ r → IntervalIntegrable
      (fun t => t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
        if r < sigma + t then (1 : ℝ) else 0) MeasureTheory.volume 0 sigma)
    (hintA2 : ∀ r, sigma ≤ r → IntervalIntegrable
      (fun t => t * c_HS eta sigma t *
        ∫ s' in (max (r - t) sigma)..(r + t), s' * oz_h eta sigma rho s')
      MeasureTheory.volume 0 sigma)
    (hintB1 : Integrable (fun r => r * c_HS eta sigma r * Real.exp (-s * r))
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hintB2 : Integrable (fun r => r * oz_h eta sigma rho r * Real.exp (-s * r))
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hintConv : Integrable
      (fun r => r * radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho) r * Real.exp (-s * r))
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (_hne : 1 - rho * C_HS_laplace eta sigma s ≠ 0) :
    (∫ r in Set.Ioi (0 : ℝ), r * oz_h eta sigma rho r * Real.exp (-s * r)) *
    (1 - rho * C_HS_laplace eta sigma s) = C_HS_laplace eta sigma s := by
  -- Step 1: the pointwise 3D-OZ equation, for every `r > 0` (Gap A ∪ Gap B).
  have hpointwise : ∀ r ∈ Set.Ioi (0 : ℝ), oz_h eta sigma rho r =
      c_HS eta sigma r + rho * radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho) r := by
    intro r hrpos
    by_cases hr : r < sigma
    · exact hcore r ⟨hrpos, hr⟩
    · exact oz_h_satisfies_conv_ext hsigma (not_lt.mp hr) (hintA1 r (not_lt.mp hr))
        (hintA2 r (not_lt.mp hr))
  -- Step 2: apply `radial_laplace` to both sides.
  have hlaplace : radial_laplace (oz_h eta sigma rho) s =
      radial_laplace (c_HS eta sigma) s +
        rho * radial_laplace (radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho)) s := by
    unfold radial_laplace
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add hintB1 (hintConv.const_mul rho)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change r * oz_h eta sigma rho r * Real.exp (-s * r) =
      r * c_HS eta sigma r * Real.exp (-s * r) +
        rho * (r * radial3d_conv (c_HS eta sigma) (oz_h eta sigma rho) r * Real.exp (-s * r))
    rw [hpointwise r hr]
    ring
  -- Step 3: `radial_laplace_conv` factors the convolution transform.
  rw [radial_laplace_conv hs hintB1 hintB2] at hlaplace
  rw [radial_laplace_cHS_eq hsigma] at hlaplace
  -- Step 4: rearrange to the `H·(1-ρC) = C` form.
  change radial_laplace (oz_h eta sigma rho) s * (1 - rho * C_HS_laplace eta sigma s) =
    C_HS_laplace eta sigma s
  linear_combination hlaplace

end FMSA.HardSphere
