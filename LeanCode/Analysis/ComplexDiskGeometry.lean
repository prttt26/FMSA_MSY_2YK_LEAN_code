/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Closed-disk geometry helpers for `ℂ`

Three elementary bounds on a point of a closed disk `Metric.closedBall c r ⊆ ℂ`, used by the
single-component (`BaxterPoleFamilyConcrete`) and mixture (`MixtureChordFamily`) pole-family
constructions.  Hoisted to `Analysis/` in the 2026-08 restructure — they had been copy-pasted
(unprimed in `HardSphere/`, primed in `HSMixture/`); this is the single shared home both cite.
-/

/-- Every point of a closed disk has real part at least `Re(centre) − radius`. -/
theorem mem_closedBall_re_ge {c k : ℂ} {r : ℝ} (hk : k ∈ Metric.closedBall c r) :
    c.re - r ≤ k.re := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hk
  have h1 : |(k - c).re| ≤ ‖k - c‖ := Complex.abs_re_le_norm _
  rw [Complex.sub_re] at h1
  have h2 := abs_le.mp (le_trans h1 hk)
  linarith [h2.1]

/-- Every point of a closed disk has `|Im|` at most `|Im(centre)| + radius`. -/
theorem mem_closedBall_abs_im_le {c k : ℂ} {r : ℝ} (hk : k ∈ Metric.closedBall c r) :
    |k.im| ≤ |c.im| + r := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hk
  have h1 : |(k - c).im| ≤ ‖k - c‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im] at h1
  have h2 : |k.im| ≤ |c.im| + |k.im - c.im| := by
    calc |k.im| = |c.im + (k.im - c.im)| := by congr 1; ring
      _ ≤ |c.im| + |k.im - c.im| := abs_add_le _ _
  linarith

/-- Every point of a closed disk has norm at most `‖centre‖ + radius`. -/
theorem mem_closedBall_norm_le {c k : ℂ} {r : ℝ} (hk : k ∈ Metric.closedBall c r) :
    ‖k‖ ≤ ‖c‖ + r := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hk
  calc ‖k‖ = ‖c + (k - c)‖ := by congr 1; ring
    _ ≤ ‖c‖ + ‖k - c‖ := norm_add_le _ _
    _ ≤ ‖c‖ + r := by linarith
