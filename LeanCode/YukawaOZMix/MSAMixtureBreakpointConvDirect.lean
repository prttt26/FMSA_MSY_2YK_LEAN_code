/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.YukawaOZMix.MSAMixtureBaxterConv

/-!
# BRK.16 — `baxterConvCore` breakpoints DIRECTLY from the convolution (axiom-reduction)

Goal (`proof_notes_breakpoints_MSA.md`, BRK.16): prove the physical-core breakpoint structure from
the convolution `baxterConvCore = (−Q'_ij + Σ_l ρ_l ∫ Q'_il(t+r) Q_jl(t) dt)/(2π r)` DIRECTLY, so
`baxterConvCore_smooth_off_unique_breakpoint` drops the sympy axiom `baxterConvCore_eq_matCoreUneq`
and becomes std-3.  This is legitimate because the breakpoint is *structural* (interior knot
`= |λ_ij|`, a support-edge geometric fact), independent of the coefficient VALUES — no closed-form
(hence no symbolic computation, hence no axiom) is needed.

## This file so far — BRK.16a (the factor smoothness, the buildable foundation)

`baxterQ`/`baxterQ'` are `ContDiffOn ℝ ⊤` on each of their open smooth pieces — the core
`(λ_ab, σ_ab)` and the tail `(σ_ab, ∞)` — each an entire polynomial/exponential formula.  (Below
`λ_ab` both are `0`.)  These feed the interval-split for the convolution smoothness (BRK.16b, the
load-bearing analytic core, still to come).
-/

open MSAMixture MSAMixtureCoreUneq

namespace FMSA.ExactMSA.Breakpoint

variable {N : ℕ}

/-- **BRK.16a — `baxterQ` on the core piece** `(λ_ab, σ_ab)` equals its polynomial+exponential core
formula, hence `ContDiffOn ℝ ⊤`. -/
theorem baxterQ_contDiffOn_core (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (a b : Fin N) :
    ContDiffOn ℝ ⊤ (baxterQ z σ A qp Wt Ct a b) (Set.Ioo (edgeLo σ a b) (edgeHi σ a b)) := by
  have hg : ContDiffOn ℝ ⊤ (fun x => qp a b * (x - edgeLo σ a b - σ a)
      + A b / 2 * (x - edgeLo σ a b - σ a) ^ 2
      + Wt a b * Real.exp (-z * (x - edgeLo σ a b)) + Ct a b)
      (Set.Ioo (edgeLo σ a b) (edgeHi σ a b)) := by fun_prop
  refine hg.congr (fun x hx => ?_)
  unfold baxterQ
  rw [if_neg (not_lt.mpr (le_of_lt hx.1)), if_pos (le_of_lt hx.2)]

/-- **BRK.16a — `baxterQ` on the tail piece** `(σ_ab, ∞)` equals its two-exponential tail formula,
hence `ContDiffOn ℝ ⊤`. -/
theorem baxterQ_contDiffOn_tail (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (a b : Fin N) (hσ : ∀ i, 0 ≤ σ i) :
    ContDiffOn ℝ ⊤ (baxterQ z σ A qp Wt Ct a b) (Set.Ioi (edgeHi σ a b)) := by
  have hg : ContDiffOn ℝ ⊤ (fun x => Wt a b * Real.exp (-z * (x - edgeLo σ a b))
      + Ct a b * Real.exp (-z * (x - edgeHi σ a b))) (Set.Ioi (edgeHi σ a b)) := by fun_prop
  have hle : edgeLo σ a b ≤ edgeHi σ a b := by
    simp only [edgeLo, edgeHi]; linarith [hσ a, hσ b]
  refine hg.congr (fun x hx => ?_)
  have hxi : edgeHi σ a b < x := Set.mem_Ioi.mp hx
  unfold baxterQ
  rw [if_neg (by linarith : ¬ x < edgeLo σ a b), if_neg (not_le.mpr hxi)]

/-- **BRK.16a — `baxterQ'` on the core piece** `(λ_ab, σ_ab)`, `ContDiffOn ℝ ⊤`. -/
theorem baxterQ'_contDiffOn_core (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (a b : Fin N) :
    ContDiffOn ℝ ⊤ (baxterQ' z σ A qp Wt Ct a b) (Set.Ioo (edgeLo σ a b) (edgeHi σ a b)) := by
  have hg : ContDiffOn ℝ ⊤ (fun x => qp a b + A b * (x - edgeLo σ a b - σ a)
      - z * Wt a b * Real.exp (-z * (x - edgeLo σ a b)))
      (Set.Ioo (edgeLo σ a b) (edgeHi σ a b)) := by fun_prop
  refine hg.congr (fun x hx => ?_)
  unfold baxterQ'
  rw [if_neg (not_lt.mpr (le_of_lt hx.1)), if_pos (le_of_lt hx.2)]

/-- **BRK.16a — `baxterQ'` on the tail piece** `(σ_ab, ∞)`, `ContDiffOn ℝ ⊤`. -/
theorem baxterQ'_contDiffOn_tail (z : ℝ) (σ A : Fin N → ℝ) (qp Wt Ct : Fin N → Fin N → ℝ)
    (a b : Fin N) (hσ : ∀ i, 0 ≤ σ i) :
    ContDiffOn ℝ ⊤ (baxterQ' z σ A qp Wt Ct a b) (Set.Ioi (edgeHi σ a b)) := by
  have hg : ContDiffOn ℝ ⊤ (fun x => -z * Wt a b * Real.exp (-z * (x - edgeLo σ a b))
      - z * Ct a b * Real.exp (-z * (x - edgeHi σ a b))) (Set.Ioi (edgeHi σ a b)) := by fun_prop
  have hle : edgeLo σ a b ≤ edgeHi σ a b := by
    simp only [edgeLo, edgeHi]; linarith [hσ a, hσ b]
  refine hg.congr (fun x hx => ?_)
  have hxi : edgeHi σ a b < x := Set.mem_Ioi.mp hx
  unfold baxterQ'
  rw [if_neg (by linarith : ¬ x < edgeLo σ a b), if_neg (not_le.mpr hxi)]

end FMSA.ExactMSA.Breakpoint
