/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterResidue
import LeanCode.HardSphere.PYOZ_GHS

/-!
# Task OZFIX.5 — outer `t`-integral assembly for `h_explicit`

Wraps `OZFIX.3`'s `s_mul_h_explicit_integral` and `OZFIX.4`'s
`s_mul_h_explicit_integral_from_sigma` in `oz_linear_op`'s outer `t`-integral, combined with
`oz_forcing`, to express `oz_forcing(r) + oz_linear_op[h_explicit](r)` (`r ≥ σ`) purely as an
outer `∫ t in 0..σ` integral whose integrand is a closed form in `Hterm` — the raw inner
`∫ s in max(r-t,σ)..(r+t)` integral is eliminated entirely. This is the direct analogue of
`OZExteriorBridge.lean`'s `oz_forcing_add_linear_op_eq_radial3d_conv` (same `hcombine`/`hcongr`
assembly technique, same case-split on `r-t ≷ σ` via `max_eq_left`/`max_eq_right`), but targets
the `h_explicit`-specific closed form instead of the generic `radial3d_conv` — matching Group
OZFIX's chosen termwise strategy (not routed through `radial3d_conv`).

**Key correction versus the naive first guess:** `oz_forcing`'s indicator term does *not* cancel
against `h_explicit`'s inner-integral closed form the way it does in the general
`inner_integral_bridge`/`outer_integrand_bridge` lemmas (which fold the core's `h≡-1` value into
a *shell* integral over `[|r-t|,r+t]`, matching `radial3d_conv`). `h_explicit` is only ever
sampled on `s ≥ σ` (`oz_linear_op`'s own domain restriction `max(r-t,σ)..(r+t)`), so the forcing
term stays as a genuinely separate additive piece throughout — only the *raw inner integral* gets
replaced by its `Hterm` closed form; nothing merges with the forcing indicator.

## Results

* `inner_h_explicit_integral_bridge` — pointwise-in-`t` (`t ∈ (0,σ)`, `r ≥ σ`) closed form for
  `∫ s in max(r-t,σ)..(r+t), s·h_explicit(s)`, case-split on `σ ≷ r-t` (`s_mul_h_explicit_integral`
  vs. its `_from_sigma` counterpart), stated uniformly as `Hterm` evaluated at the two endpoints.
* `outer_h_explicit_integrand_bridge` — the `Set.EqOn (Icc 0 σ)` wrapper (peels the two
  measure-zero boundary points `t=0,σ` via `simp`/`c_HS_contact`, matching
  `outer_integrand_bridge`'s pattern) needed for `intervalIntegral.integral_congr`.
* `oz_forcing_add_linear_op_h_explicit_eq_outer_integral` — the main assembly theorem.

**Status:** ✓ DONE, no `sorry`/new axiom. The `hint`-family hypothesis (integrability of
`h_explicit_term`'s sum on `[σ,r+t]`, needed only when `r ≤ σ+t`) is inherited from `OZFIX.4`'s
own `hint`, carried explicitly (not derived) per that task's established finding that it is a
genuine, currently-open analytic gap. `OZFIX.6` (algebraic collapse) continues from here.
-/

open MeasureTheory Set Real intervalIntegral Filter Topology

namespace FMSA.HardSphere

noncomputable section

/-- **Inner-integral case-split bridge for `h_explicit`** (`OZFIX.5`): for `t ∈ (0,σ)` and
`r ≥ σ`, `oz_linear_op`'s inner integral `∫ s in max(r-t,σ)..(r+t), s·h_explicit(s)` has the
uniform closed form `(1/2π)·Re[∑'Hterm(r+t) − ∑'Hterm(max(r-t,σ))]` — proved by case-splitting on
whether `max(r-t,σ)` equals `r-t` (strictly past `σ`, use `s_mul_h_explicit_integral`) or `σ`
itself (the boundary case, use `s_mul_h_explicit_integral_from_sigma`, needing `hint`). -/
theorem inner_h_explicit_integral_bridge {eta sigma rho : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖)
    (hkfam_ne : ∀ n, kfam n ≠ 0)
    {t r : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) sigma) (hr : sigma ≤ r)
    (hint : r ≤ sigma + t → IntervalIntegrable
      (fun s => ∑' n, h_explicit_term eta sigma rho s kfam n) MeasureTheory.volume sigma (r + t)) :
    ∫ s in (max (r - t) sigma)..(r + t), s * h_explicit eta sigma rho s kfam =
      (1 / (2 * Real.pi)) *
        ((∑' n, Hterm eta sigma rho kfam n (r + t)) -
          (∑' n, Hterm eta sigma rho kfam n (max (r - t) sigma))).re := by
  have hhi : sigma < r + t := by linarith [ht.1]
  by_cases hlt : sigma < r - t
  · have hmax : max (r - t) sigma = r - t := max_eq_left hlt.le
    rw [hmax]
    have hr0lt : sigma < (sigma + (r - t)) / 2 := by linarith
    have hlolt : (sigma + (r - t)) / 2 < r - t := by linarith
    have hhile : r - t ≤ r + t := by linarith [ht.1]
    exact s_mul_h_explicit_integral heta0 heta1 hsigma hrho hr0lt hlolt hhile hc hd
      hkfam_zero hkfam_im hkfam_re hkfam_ne
  · have hmax : max (r - t) sigma = sigma := max_eq_right (by linarith)
    rw [hmax]
    exact s_mul_h_explicit_integral_from_sigma heta0 heta1 hsigma hrho hhi hc hd
      hkfam_zero hkfam_im hkfam_re hkfam_ne (hint (by linarith))

/-- **Outer pointwise wrapper** (`OZFIX.5`): the `Set.EqOn (Icc 0 σ)` congruence needed for
`intervalIntegral.integral_congr` to push `inner_h_explicit_integral_bridge` inside the outer
`t`-integral. Mirrors `outer_integrand_bridge`'s boundary-peeling structure (`t=0`: both sides
vanish since the whole integrand is `t·(…)`; `t=σ`: both sides vanish via `c_HS_contact`), but
keeps the `oz_forcing` indicator term as a separate, unmodified additive piece on both sides —
only the raw inner integral gets replaced. -/
theorem outer_h_explicit_integrand_bridge {eta sigma rho : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖)
    (hkfam_ne : ∀ n, kfam n ≠ 0)
    {r : ℝ} (hr : sigma ≤ r)
    (hint : ∀ t ∈ Set.Ioo (0 : ℝ) sigma, r ≤ sigma + t → IntervalIntegrable
      (fun s => ∑' n, h_explicit_term eta sigma rho s kfam n) MeasureTheory.volume sigma (r + t)) :
    Set.EqOn
      (fun t => t * c_HS eta sigma t *
          (-(1 / 2) * (sigma ^ 2 - (r - t) ^ 2) * (if r < sigma + t then (1 : ℝ) else 0)) +
        t * c_HS eta sigma t *
          ∫ s in (max (r - t) sigma)..(r + t), s * h_explicit eta sigma rho s kfam)
      (fun t => t * c_HS eta sigma t *
          (-(1 / 2) * (sigma ^ 2 - (r - t) ^ 2) * (if r < sigma + t then (1 : ℝ) else 0)) +
        t * c_HS eta sigma t *
          ((1 / (2 * Real.pi)) *
            ((∑' n, Hterm eta sigma rho kfam n (r + t)) -
              (∑' n, Hterm eta sigma rho kfam n (max (r - t) sigma))).re))
      (Set.Icc (0 : ℝ) sigma) := by
  intro t ht
  rcases ht.1.eq_or_lt with heq0 | hpos
  · simp [← heq0]
  rcases ht.2.eq_or_lt with heqs | hlts
  · simp [heqs]
  · have hin := inner_h_explicit_integral_bridge heta0 heta1 hsigma hrho hc hd hkfam_zero
      hkfam_im hkfam_re hkfam_ne (Set.mem_Ioo.mpr ⟨hpos, hlts⟩) hr
      (hint t (Set.mem_Ioo.mpr ⟨hpos, hlts⟩))
    dsimp only
    rw [hin]

/-- **`OZFIX.5` main assembly theorem**: `oz_forcing(r) + oz_linear_op[h_explicit](r)`, for
`r ≥ σ`, expressed purely as an outer `∫ t in 0..σ` integral with the raw inner integral
eliminated in favor of its `Hterm` closed form. Two routine `IntervalIntegrable` side-conditions
(`hint1`, `hint2`, for combining the two definitional integrals) are carried explicitly, in the
same spirit as `oz_forcing_add_linear_op_eq_radial3d_conv`'s own `hint1`/`hint2`. `OZFIX.6`
(algebraic collapse) picks up from this outer-integral form to show it equals `h_explicit(r)`
itself, using `G_baxter(k_n)=0` and the complex Wiener–Hopf bridge. -/
theorem oz_forcing_add_linear_op_h_explicit_eq_outer_integral {eta sigma rho : ℝ}
    (hsigma : 0 < sigma) (heta0 : 0 < eta) (heta1 : eta < 1) (hrho : 0 < rho)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖)
    (hkfam_ne : ∀ n, kfam n ≠ 0)
    {r : ℝ} (hr : sigma ≤ r)
    (hint1 : IntervalIntegrable
      (fun t => t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
        if r < sigma + t then (1 : ℝ) else 0) MeasureTheory.volume 0 sigma)
    (hint2 : IntervalIntegrable
      (fun t => t * c_HS eta sigma t *
        ∫ s in (max (r - t) sigma)..(r + t), s * h_explicit eta sigma rho s kfam)
      MeasureTheory.volume 0 sigma)
    (hint : ∀ t ∈ Set.Ioo (0 : ℝ) sigma, r ≤ sigma + t → IntervalIntegrable
      (fun s => ∑' n, h_explicit_term eta sigma rho s kfam n) MeasureTheory.volume sigma (r + t)) :
    oz_forcing eta sigma rho r +
      oz_linear_op eta sigma rho (fun s => h_explicit eta sigma rho s kfam) r =
    (2 * Real.pi * rho / r) *
      ∫ t in (0 : ℝ)..sigma,
        (t * c_HS eta sigma t *
            (-(1 / 2) * (sigma ^ 2 - (r - t) ^ 2) * (if r < sigma + t then (1 : ℝ) else 0)) +
          t * c_HS eta sigma t *
            ((1 / (2 * Real.pi)) *
              ((∑' n, Hterm eta sigma rho kfam n (r + t)) -
                (∑' n, Hterm eta sigma rho kfam n (max (r - t) sigma))).re)) := by
  have hr0 : 0 < r := lt_of_lt_of_le hsigma hr
  unfold oz_forcing oz_linear_op
  rw [if_neg (not_le.mpr hr0), if_neg (not_le.mpr hr0)]
  have hcombine :
      (-(Real.pi * rho / r) *
          ∫ t in (0 : ℝ)..sigma, t * c_HS eta sigma t * (sigma ^ 2 - (r - t) ^ 2) *
            if r < sigma + t then (1 : ℝ) else 0) +
        (2 * Real.pi * rho / r) *
          ∫ t in (0 : ℝ)..sigma, t * c_HS eta sigma t *
            ∫ s in (max (r - t) sigma)..(r + t), s * h_explicit eta sigma rho s kfam =
      (2 * Real.pi * rho / r) *
        ∫ t in (0 : ℝ)..sigma,
          (t * c_HS eta sigma t *
              (-(1 / 2) * (sigma ^ 2 - (r - t) ^ 2) * (if r < sigma + t then (1 : ℝ) else 0)) +
            t * c_HS eta sigma t *
              ∫ s in (max (r - t) sigma)..(r + t), s * h_explicit eta sigma rho s kfam) := by
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
            t * c_HS eta sigma t *
              ∫ s in (max (r - t) sigma)..(r + t), s * h_explicit eta sigma rho s kfam)) =
      ∫ t in (0 : ℝ)..sigma,
        (t * c_HS eta sigma t *
            (-(1 / 2) * (sigma ^ 2 - (r - t) ^ 2) * (if r < sigma + t then (1 : ℝ) else 0)) +
          t * c_HS eta sigma t *
            ((1 / (2 * Real.pi)) *
              ((∑' n, Hterm eta sigma rho kfam n (r + t)) -
                (∑' n, Hterm eta sigma rho kfam n (max (r - t) sigma))).re)) :=
    intervalIntegral.integral_congr
      (by rw [Set.uIcc_of_le hsigma.le]
          exact outer_h_explicit_integrand_bridge heta0 heta1 hsigma hrho hc hd hkfam_zero
            hkfam_im hkfam_re hkfam_ne hr hint)
  rw [hcombine, hcongr]

end

end FMSA.HardSphere
