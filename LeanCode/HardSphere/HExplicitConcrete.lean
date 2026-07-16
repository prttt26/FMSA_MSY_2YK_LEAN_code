/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterResidue

/-!
# Task POLE.6 — concrete pole family wired into `h_explicit`'s summability

`POLE.5`'s `h_explicit_summable_of_pole_family` (`BaxterResidue.lean`) is stated over an
*abstract* pole family `kfam : ℕ → ℂ` with three properties (`hkfam_zero`, `hkfam_im`,
`hkfam_re`). The only constructor of a concrete indexed family with the zero + linear-growth
data is `G_baxter_pole_family_exists_growth` (`BaxterPoles.lean`, conditional on `POLE.3`'s
open `hstep`). This file supplies the missing glue, in two pieces:

## Results

* `pole_family_im_nonneg` — **the `hkfam_im` gap fix.** `G_baxter_pole_family_exists_growth`'s
  conclusion supplies `Injective`, ball-membership, `G_baxter (g n) = 0`, and `c·n+d ≤ ‖g n‖`,
  but **not** the upper-half-plane fact `0 ≤ (g n).im` that every `h_explicit` lemma consumes.
  It is recovered here from the centres: if `r ≤ (k1 n).im` (numerically comfortable — the
  fitted centres have `Im(k1 n) = 2·ln(2πn/σ) − 2.12`, already `≈1.44` at the first pole and
  growing, vs. `r < π/σ`), then every member of `closedBall (k1 (n+N)) r` has `Im ≥ 0`
  (`Complex.abs_im_le_norm`, mirroring `_growth`'s own `Complex.abs_re_le_norm` argument).
* `h_explicit_summable_concrete` — the wiring: the growth-theorem's conclusion tuple + the new
  centre hypothesis `hk1im` ⇒ a family `g` that is injective, a `G_baxter` zero set, upper-half-
  plane, and with `h_explicit_term eta sigma rho y g` `Summable` for every `y > σ`.

## Design note (why the family enters existentially)

`G_baxter_pole_family_exists_growth`'s own *hypotheses* (`hkN`/`hkD`/`hDball`/`hC`) are stated
in terms of `baxterP0`/`baxterP1`/`baxterP2`, which are `private` to `BaxterPoles.lean` — a new
file cannot restate them (the same cross-file privacy constraint `POLE.5` hit, there worked
around by existential wrappers). So `h_explicit_summable_concrete` consumes the growth theorem's
*conclusion* (`hfam`, exactly its output shape) rather than re-listing its hypotheses. The
conditional chain is unchanged: the moment `POLE.3`'s `hstep` is discharged,
`G_baxter_pole_family_exists_growth` fires, its conclusion discharges `hfam`, and the concrete
summability here becomes unconditional.

**Status:** ✓ DONE, no `sorry`/new axiom; conditional only through `hfam` (= `hstep` upstream).
-/

open MeasureTheory Set Real Filter Topology

namespace FMSA.HardSphere

noncomputable section

/-- **The `hkfam_im` gap fix (`POLE.6`).** Members of radius-`r` disks around centres with
`Im ≥ r` lie in the closed upper half-plane: `|Im(g n − k1 (n+N))| ≤ ‖g n − k1 (n+N)‖ ≤ r`, so
`Im(g n) ≥ Im(k1 (n+N)) − r ≥ 0`. This is the one family property
`G_baxter_pole_family_exists_growth`'s conclusion does *not* carry, though every `h_explicit`
lemma consumes it (`hkfam_im`). -/
theorem pole_family_im_nonneg {r : ℝ} {N : ℕ} {k1 g : ℕ → ℂ}
    (hk1im : ∀ n, N ≤ n → r ≤ (k1 n).im)
    (hgmem : ∀ n, g n ∈ Metric.closedBall (k1 (n + N)) r) :
    ∀ n, 0 ≤ (g n).im := by
  intro n
  have hmem := hgmem n
  rw [Metric.mem_closedBall, dist_eq_norm] at hmem
  have him : |(g n - k1 (n + N)).im| ≤ ‖g n - k1 (n + N)‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im] at him
  have hk1 := hk1im (n + N) (Nat.le_add_left N n)
  have hge : -|(g n).im - (k1 (n + N)).im| ≤ (g n).im - (k1 (n + N)).im := neg_abs_le _
  linarith [him, hmem, hk1, hge]

/-- **`POLE.6` — concrete-family instantiation of `POLE.5`'s summability.** Consumes exactly
`G_baxter_pole_family_exists_growth`'s conclusion (`hfam`; see the file docstring for why it
enters existentially rather than via that theorem's `private`-referencing hypotheses) plus the
centre imaginary-part hypothesis `hk1im`, and produces a pole family that is simultaneously
injective, a `G_baxter` zero set, upper-half-plane (`pole_family_im_nonneg`), and summable for
`h_explicit` at every radial distance `y > σ`
(`h_explicit_summable_of_pole_family`). Conditional only through `hfam` — unconditional as soon
as `POLE.3`'s `hstep` lands. -/
theorem h_explicit_summable_concrete {eta sigma rho y r : ℝ} {N : ℕ} {k1 : ℕ → ℂ}
    (heta0 : 0 < eta) (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 < rho)
    (hy : sigma < y)
    (hk1im : ∀ n, N ≤ n → r ≤ (k1 n).im)
    (hfam : ∃ g : ℕ → ℂ, Function.Injective g ∧
      (∀ n, g n ∈ Metric.closedBall (k1 (n + N)) r) ∧
      (∀ n, G_baxter eta sigma rho (g n) = 0) ∧
      ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖g n‖) :
    ∃ g : ℕ → ℂ, Function.Injective g ∧
      (∀ n, G_baxter eta sigma rho (g n) = 0) ∧ (∀ n, 0 ≤ (g n).im) ∧
      Summable (h_explicit_term eta sigma rho y g) := by
  obtain ⟨g, hginj, hgmem, hgzero, c, d, hc, hd, hgrow⟩ := hfam
  have him : ∀ n, 0 ≤ (g n).im := pole_family_im_nonneg hk1im hgmem
  exact ⟨g, hginj, hgzero, him,
    h_explicit_summable_of_pole_family heta0 heta1 hsigma hrho hy hc hd hgzero him hgrow⟩

end

end FMSA.HardSphere
