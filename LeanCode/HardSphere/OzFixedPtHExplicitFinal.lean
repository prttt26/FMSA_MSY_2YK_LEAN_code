/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.OzFixedPtHExplicit
import LeanCode.HardSphere.HExplicitRegularity
import LeanCode.HardSphere.OzWienerHopfBounded

/-!
# Task OZFIX.8 — final assembly: `oz_h = ` the spliced `h_explicit`/`-1` function (conditional)

Packages `OZFIX.5`–`7` into the `OzFixedPt ∧ ContinuousOn ∧ bounded` shape and invokes the
theorem `oz_fixed_pt_unique_thm` (formerly the physics axiom `oz_fixed_pt_unique`) to conclude
`oz_h eta sigma rho` equals the spliced
`h_explicit`/`(-1)` function — **conditional** on two explicit hypotheses corresponding to the two
genuine gaps found by `OZFIX.6`/`OZFIX.7`:

- `hcollapse` — the `OZFIX.6` algebraic-collapse identity itself
  (`oz_forcing(r) + oz_linear_op[h_explicit](r) = h_explicit(r)` for all `r ≥ σ`). `OZFIX.6`'s
  scoping pass found the originally-planned per-pole/termwise proof route does **not** work (a
  concrete counter-check: a single pole's isolated contribution has ratio `-2.72`, not `1`,
  against its naive per-pole target), so this identity is taken as a hypothesis rather than
  derived — matching this project's established fallback pattern (`hstep`, `hint`,
  `oz_h_exterior_regularity`) for hard, currently-open analytic/algebraic gaps.
- `hcont_sigma` — continuity of `h_explicit` *at* `σ` from the right
  (`ContinuousWithinAt h_explicit (Set.Ici σ) σ`). `OZFIX.7` proved continuity on the *open* ray
  `(σ,∞)` unconditionally, but `h_explicit`'s own series is only known summable there strictly —
  the closed endpoint needs this genuine, currently-open `σ`-boundary fact (the same root
  difficulty as `OZFIX.4`'s `hint`) as an explicit hypothesis.

Everything else in the proof — the fixed-point equation on the core (`r<σ`, trivial `-1=-1`), the
observation that `oz_linear_op` never samples the spliced function outside `h_explicit`'s own
valid domain `s≥σ` (so splicing doesn't change `oz_linear_op`'s value), global boundedness
(gluing `OZFIX.7`'s `[r0,∞)` bound with a compactness argument on `[σ,r0]`, itself powered by
`hcont_sigma`+`OZFIX.7`'s open-ray continuity), and the final `oz_fixed_pt_unique_thm` invocation
— is unconditional, no `sorry`/new axiom beyond the two explicit hypotheses above.

**Status:** ✓ DONE, conditional on `hcollapse` and `hcont_sigma` (plus the standard pole-family
data `hkfam_zero`/`hkfam_im`/`hkfam_re`, `c`,`d`>0 — `POLE.3`'s `hstep` gap is not
threaded through explicitly since this theorem is stated over an abstract `kfam`, matching
`OZFIX.3`–`7`'s own convention).
-/

open MeasureTheory Set Real intervalIntegral Filter Topology

namespace FMSA.HardSphere

noncomputable section

/-- **`OZFIX.8`: `oz_h` equals the spliced `h_explicit`/`(-1)` function, conditionally on the
`OZFIX.6` algebraic-collapse identity (`hcollapse`) and `OZFIX.7`'s missing `σ`-endpoint
continuity (`hcont_sigma`).** -/
theorem oz_h_eq_spliced_h_explicit {eta sigma rho : ℝ} (hsigma : 0 < sigma)
    (heta0 : 0 < eta) (heta1 : eta < 1) (hrho : 0 < rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    {kfam : ℕ → ℂ} {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hkfam_zero : ∀ n, G_baxter eta sigma rho (kfam n) = 0)
    (hkfam_im : ∀ n, 0 ≤ (kfam n).im)
    (hkfam_re : ∀ n : ℕ, c * (n : ℝ) + d ≤ ‖kfam n‖)
    (hcollapse : ∀ r, sigma ≤ r →
      oz_forcing eta sigma rho r +
        oz_linear_op eta sigma rho (fun s => h_explicit eta sigma rho s kfam) r =
      h_explicit eta sigma rho r kfam)
    (hcont_sigma : ContinuousWithinAt (fun r => h_explicit eta sigma rho r kfam)
      (Set.Ici sigma) sigma) :
    oz_h eta sigma rho =
      (fun r => if r < sigma then (-1 : ℝ) else h_explicit eta sigma rho r kfam) := by
  set hspliced : ℝ → ℝ := fun r => if r < sigma then (-1 : ℝ) else h_explicit eta sigma rho r kfam
    with hsplicedDef
  have hsplice_eq_hexplicit : ∀ s, sigma ≤ s → hspliced s = h_explicit eta sigma rho s kfam := by
    intro s hs
    rw [hsplicedDef]
    simp only
    rw [if_neg (not_lt.mpr hs)]
  have hfp : OzFixedPt eta sigma rho hspliced := by
    intro r
    unfold oz_operator
    by_cases hr : r < sigma
    · rw [if_pos hr, hsplicedDef]
      simp only
      rw [if_pos hr]
    · rw [if_neg hr]
      push Not at hr
      have hlinop_eq : oz_linear_op eta sigma rho hspliced r =
          oz_linear_op eta sigma rho (fun s => h_explicit eta sigma rho s kfam) r := by
        unfold oz_linear_op
        by_cases hrpos : r ≤ 0
        · rw [if_pos hrpos, if_pos hrpos]
        · rw [if_neg hrpos, if_neg hrpos]
          have houter : ∀ t ∈ Set.uIcc (0:ℝ) sigma,
              t * c_HS eta sigma t * ∫ s in (max (r - t) sigma)..(r + t), s * hspliced s =
              t * c_HS eta sigma t *
                ∫ s in (max (r - t) sigma)..(r + t), s * h_explicit eta sigma rho s kfam := by
            intro t ht
            rw [Set.uIcc_of_le hsigma.le] at ht
            have hmaxle : max (r - t) sigma ≤ r + t := by
              apply max_le
              · linarith [ht.1]
              · linarith [ht.1]
            have hinner : ∀ s ∈ Set.uIcc (max (r - t) sigma) (r + t),
                s * hspliced s = s * h_explicit eta sigma rho s kfam := by
              intro s hs
              rw [Set.uIcc_of_le hmaxle] at hs
              rw [hsplice_eq_hexplicit s (le_trans (le_max_right (r - t) sigma) hs.1)]
            rw [intervalIntegral.integral_congr hinner]
          rw [intervalIntegral.integral_congr houter]
      rw [hlinop_eq, hcollapse r hr]
      rw [hsplicedDef]
      simp only
      rw [if_neg (not_lt.mpr hr)]
  have hcontOn : ContinuousOn hspliced (Set.Ici sigma) := by
    intro x hx
    rw [Set.mem_Ici] at hx
    rcases hx.eq_or_lt with heq | hlt
    · rw [hsplicedDef]
      refine ContinuousWithinAt.congr (f := fun r => h_explicit eta sigma rho r kfam) ?_ ?_ ?_
      · rw [← heq]; exact hcont_sigma
      · intro y hy
        show (if y < sigma then (-1:ℝ) else h_explicit eta sigma rho y kfam) =
          h_explicit eta sigma rho y kfam
        rw [if_neg (not_lt.mpr hy)]
      · show (if x < sigma then (-1:ℝ) else h_explicit eta sigma rho x kfam) =
          h_explicit eta sigma rho x kfam
        rw [if_neg (not_lt.mpr hx)]
    · have hioi : Set.Ioi sigma ∈ nhds x := Ioi_mem_nhds hlt
      have hcAt : ContinuousAt (fun r => h_explicit eta sigma rho r kfam) x :=
        (h_explicit_continuousOn_Ioi heta0 heta1 hsigma hrho hc hd hkfam_zero hkfam_im
          hkfam_re).continuousAt hioi
      have heqAt : hspliced =ᶠ[nhds x] (fun r => h_explicit eta sigma rho r kfam) := by
        filter_upwards [hioi] with y hy
        rw [hsplicedDef]
        simp only
        rw [if_neg (not_lt.mpr hy.le)]
      exact (hcAt.congr heqAt.symm).continuousWithinAt
  have hbdd : ∃ C, ∀ r, |hspliced r| ≤ C := by
    set r0 := sigma + 1 with hr0def
    have hr0 : sigma < r0 := by linarith
    obtain ⟨C1, hC1⟩ := h_explicit_bounded_on_Ici heta0 heta1 hsigma hrho hr0 hc hd
      hkfam_zero hkfam_im hkfam_re
    have hcompact : IsCompact (Set.Icc sigma r0) := isCompact_Icc
    have hcontIcc : ContinuousOn hspliced (Set.Icc sigma r0) :=
      hcontOn.mono (by intro x hx; exact hx.1)
    obtain ⟨C2, hC2⟩ := hcompact.bddAbove_image hcontIcc
    obtain ⟨C3, hC3⟩ := hcompact.bddBelow_image hcontIcc
    refine ⟨max (max C2 (-C3)) (max 1 C1), fun r => ?_⟩
    have hle1 : max C2 (-C3) ≤ max (max C2 (-C3)) (max 1 C1) := le_max_left _ _
    have hle2 : max 1 C1 ≤ max (max C2 (-C3)) (max 1 C1) := le_max_right _ _
    have hle3 : C2 ≤ max C2 (-C3) := le_max_left _ _
    have hle4 : -C3 ≤ max C2 (-C3) := le_max_right _ _
    have hle5 : (1:ℝ) ≤ max 1 C1 := le_max_left _ _
    have hle6 : C1 ≤ max 1 C1 := le_max_right _ _
    by_cases hr1 : r < sigma
    · change |if r < sigma then (-1:ℝ) else h_explicit eta sigma rho r kfam| ≤ _
      rw [if_pos hr1]
      rw [abs_neg, abs_one]
      linarith
    · push Not at hr1
      by_cases hr2 : r ≤ r0
      · have hmem : hspliced r ∈ hspliced '' (Set.Icc sigma r0) := ⟨r, ⟨hr1, hr2⟩, rfl⟩
        have hupper : hspliced r ≤ C2 := hC2 hmem
        have hlower : C3 ≤ hspliced r := hC3 hmem
        rw [abs_le]
        constructor <;> linarith
      · push Not at hr2
        have heq : hspliced r = h_explicit eta sigma rho r kfam := hsplice_eq_hexplicit r hr1
        rw [heq]
        have := hC1 r hr2.le
        linarith
  have huniq := oz_fixed_pt_unique_thm eta sigma rho hsigma hrho heta_def heta1
  have hex := huniq.exists
  have hspliced_fp : OzFixedPt eta sigma rho hspliced ∧ ContinuousOn hspliced (Set.Ici sigma) ∧
      ∃ C, ∀ r, |hspliced r| ≤ C := ⟨hfp, hcontOn, hbdd⟩
  have hoz_h_eq : oz_h eta sigma rho = Classical.choose hex := by simp only [oz_h, dif_pos hex]
  have hoz_h_fp := Classical.choose_spec hex
  rw [hoz_h_eq]
  exact huniq.unique hoz_h_fp hspliced_fp

end

end FMSA.HardSphere
