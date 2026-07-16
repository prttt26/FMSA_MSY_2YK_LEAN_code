/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterResidue

/-!
# Task OZFIX.7 — regularity of `h_explicit`: `ContinuousOn` + boundedness

`oz_fixed_pt_unique`'s regularity clause needs `ContinuousOn h (Set.Ici σ)` and a global bound
`∃ C, ∀ r, |h r| ≤ C`. This file supplies both for `h_explicit` itself, reusing the uniform-bound
infrastructure already built for `OZFIX.3`/`OZFIX.5`
(`h_explicit_term_uniform_summable_bound_of_pole_family`) — as anticipated, this part is close to
free reuse.

## Results

* `h_explicit_continuousOn_Ioi` — `ContinuousOn h_explicit (Set.Ioi σ)` (open ray), unconditional.
  Built by localizing at each point `x∈(σ,∞)` to the threshold `r0:=(σ+x)/2` and lifting the
  existing `ContinuousOn ... (Set.Ici r0)` fact (from `s_mul_h_explicit_integral`'s own proof) to
  a `ContinuousAt` fact at `x` via `ContinuousOn.continuousAt` + `Ici_mem_nhds`.
* `h_explicit_bounded_on_Ici` — `∃ C, ∀ r ∈ Set.Ici r0, |h_explicit r| ≤ C` for any `r0 > σ`,
  via the uniform bound `u` (`Summable`) on `h_explicit_term`, `Summable.tsum_mono`, and the
  `1/(2πr) ≤ 1/(2πr0)` monotonicity of the prefactor for `r ≥ r0 > 0`.

**Status:** ✓ DONE **on `(σ,∞)`/`[r0,∞)` for `r0>σ`**, no `sorry`/new axiom. **What's left:** the
single closed endpoint `r=σ` itself — `oz_fixed_pt_unique`'s literal hypothesis needs
`ContinuousOn h (Set.Ici σ)` (closed at `σ`), but `h_explicit`'s own series is only known
summable/continuous for `r>σ` strictly (the same genuine `σ`-boundary gap flagged in `OZFIX.4`'s
`hint` and `OZFIX.6`'s scoping finding — not attempted here, not a quick corollary of the above).
-/

open MeasureTheory Set Real intervalIntegral Filter Topology

namespace FMSA.HardSphere

noncomputable section

/-- **`h_explicit` is continuous on the open ray `(σ,∞)`.** For each `x>σ`, localize at the
threshold `r0:=(σ+x)/2∈(σ,x)`: `h_explicit_term_uniform_summable_bound_of_pole_family` gives a
`Summable`, `y`-independent bound valid on `Set.Ici r0`, so `continuousOn_tsum` gives
`ContinuousOn (∑'h_explicit_term) (Ici r0)`; since `Ici r0` is a neighborhood of `x` (`r0<x`),
this upgrades to `ContinuousAt (∑'h_explicit_term) x` via `ContinuousOn.continuousAt`, and
`h_explicit`'s own `(1/(2πr))·Re[…]` shape is continuous at `x` (`x≠0` since `x>σ>0`). -/
theorem h_explicit_continuousOn_Ioi {eta sigma rho : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖) :
    ContinuousOn (fun r => h_explicit eta sigma rho r kfam) (Set.Ioi sigma) := by
  intro x hx
  have hr0 : sigma < (sigma + x) / 2 := by
    have : sigma < x := hx
    linarith
  have hlox : (sigma + x) / 2 < x := by
    have : sigma < x := hx
    linarith
  set r0 := (sigma + x) / 2 with hr0def
  obtain ⟨u, hu, hub⟩ := h_explicit_term_uniform_summable_bound_of_pole_family heta0 heta1
    hsigma hrho hr0 hc hd hkfam_zero hkfam_im hkfam_re
  have hcont_term : ∀ n : ℕ,
      Continuous (fun s : ℝ => h_explicit_term eta sigma rho s kfam n) := by
    intro n
    unfold h_explicit_term residue_term
    fun_prop
  have hcontOn : ContinuousOn (fun s => ∑' n, h_explicit_term eta sigma rho s kfam n)
      (Set.Ici r0) := continuousOn_tsum (fun n => (hcont_term n).continuousOn) hu
    (fun n y hy => by unfold h_explicit_term; exact (norm_add_le _ _).trans (hub n hy))
  have hcontAt : ContinuousAt (fun s => ∑' n, h_explicit_term eta sigma rho s kfam n) x :=
    hcontOn.continuousAt (Ici_mem_nhds hlox)
  have hrpos : (0:ℝ) < x := lt_trans hsigma hx
  have heq : (fun r => h_explicit eta sigma rho r kfam) =ᶠ[nhds x]
      (fun r => (1 / (2 * Real.pi * r)) * (∑' n, h_explicit_term eta sigma rho r kfam n).re) := by
    filter_upwards with r
    rfl
  refine ContinuousWithinAt.congr_of_eventuallyEq ?_ (heq.filter_mono nhdsWithin_le_nhds) (by rfl)
  refine ContinuousAt.continuousWithinAt ?_
  have h1 : ContinuousAt (fun r : ℝ => (1:ℝ) / (2 * Real.pi * r)) x :=
    ContinuousAt.div continuousAt_const (by fun_prop) (by positivity)
  exact h1.mul (Complex.continuous_re.continuousAt.comp hcontAt)

/-- **`h_explicit` is bounded on `[r0,∞)`** for any `r0 > σ`, via the same uniform bound `u`
(`h_explicit_term_uniform_summable_bound_of_pole_family`) and the `1/(2πr)≤1/(2πr0)` monotonicity
of `h_explicit`'s own prefactor for `r≥r0>0`. -/
theorem h_explicit_bounded_on_Ici {eta sigma rho r0 : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho) (hr0 : sigma < r0)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖) :
    ∃ C, ∀ r ∈ Set.Ici r0, |h_explicit eta sigma rho r kfam| ≤ C := by
  obtain ⟨u, hu, hub⟩ := h_explicit_term_uniform_summable_bound_of_pole_family heta0 heta1
    hsigma hrho hr0 hc hd hkfam_zero hkfam_im hkfam_re
  have hr0pos : (0:ℝ) < r0 := lt_trans hsigma hr0
  refine ⟨(1 / (2 * Real.pi * r0)) * (∑' n, u n), fun r hr => ?_⟩
  rw [Set.mem_Ici] at hr
  have hrpos : (0:ℝ) < r := lt_of_lt_of_le hr0pos hr
  have hub' : ∀ n, ‖h_explicit_term eta sigma rho r kfam n‖ ≤ u n := by
    intro n
    unfold h_explicit_term
    exact (norm_add_le _ _).trans (hub n hr)
  have hsummable_terms : Summable (fun n => h_explicit_term eta sigma rho r kfam n) :=
    Summable.of_norm_bounded hu hub'
  have hbound_sum : ‖∑' n, h_explicit_term eta sigma rho r kfam n‖ ≤ ∑' n, u n :=
    (norm_tsum_le_tsum_norm hsummable_terms.norm).trans
      (Summable.tsum_mono hsummable_terms.norm hu hub')
  unfold h_explicit
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * Real.pi * r))]
  have hre_le : |(∑' n, h_explicit_term eta sigma rho r kfam n).re| ≤ ∑' n, u n :=
    (Complex.abs_re_le_norm _).trans hbound_sum
  have hcoef_le : (1:ℝ) / (2 * Real.pi * r) ≤ 1 / (2 * Real.pi * r0) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [Real.pi_pos, hr]
  calc 1 / (2 * Real.pi * r) * |(∑' n, h_explicit_term eta sigma rho r kfam n).re|
      ≤ 1 / (2 * Real.pi * r0) * |(∑' n, h_explicit_term eta sigma rho r kfam n).re| :=
        mul_le_mul_of_nonneg_right hcoef_le (abs_nonneg _)
    _ ≤ 1 / (2 * Real.pi * r0) * (∑' n, u n) :=
        mul_le_mul_of_nonneg_left hre_le (by positivity)

end

end FMSA.HardSphere
