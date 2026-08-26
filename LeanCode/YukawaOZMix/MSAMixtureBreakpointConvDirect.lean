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

open MSAMixture MSAMixtureCoreUneq MeasureTheory Set

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

/-! ### BRK.16b (item 1) — integrability of the convolution integrand -/

/-- **`baxterQ` is `Integrable`** (`z > 0`): `0` below `λ_ab`, continuous on the compact core
`[λ_ab, σ_ab]`, exponentially decaying on the tail `(σ_ab, ∞)` — the tail via
`integrableOn_exp_mul_Ioi`.  Exp-tailed analog of the compact-support PY-factor integrability. -/
theorem baxterQ_integrable (z : ℝ) (hz : 0 < z) (σ A : Fin N → ℝ)
    (qp Wt Ct : Fin N → Fin N → ℝ) (a b : Fin N) (hσ : ∀ i, 0 ≤ σ i) :
    Integrable (baxterQ z σ A qp Wt Ct a b) := by
  have hle : edgeLo σ a b ≤ edgeHi σ a b := by simp only [edgeLo, edgeHi]; linarith [hσ a, hσ b]
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := edgeHi σ a b), integrableOn_union]
  refine ⟨?_, ?_⟩
  · have hset : Set.Iic (edgeHi σ a b)
        = Set.Iio (edgeLo σ a b) ∪ Set.Icc (edgeLo σ a b) (edgeHi σ a b) := by
      ext x; simp only [mem_Iic, mem_union, mem_Iio, mem_Icc]
      constructor
      · intro h
        by_cases h' : x < edgeLo σ a b
        · exact Or.inl h'
        · exact Or.inr ⟨not_lt.mp h', h⟩
      · rintro (h | ⟨_, h⟩)
        · exact le_trans h.le hle
        · exact h
    rw [hset, integrableOn_union]
    refine ⟨?_, ?_⟩
    · refine (integrableOn_zero).congr_fun ?_ measurableSet_Iio
      intro x hx; rw [Set.mem_Iio] at hx; simp [baxterQ, hx]
    · have hg : ContinuousOn (fun x => qp a b * (x - edgeLo σ a b - σ a)
          + A b / 2 * (x - edgeLo σ a b - σ a) ^ 2
          + Wt a b * Real.exp (-z * (x - edgeLo σ a b)) + Ct a b)
          (Icc (edgeLo σ a b) (edgeHi σ a b)) := by fun_prop
      refine (hg.congr (fun x hx => ?_)).integrableOn_compact isCompact_Icc
      unfold baxterQ; rw [if_neg (not_lt.mpr hx.1), if_pos hx.2]
  · have hexp : ∀ c : ℝ, IntegrableOn (fun x => Real.exp (-z * (x - c))) (Ioi (edgeHi σ a b)) := by
      intro c
      have heq : (fun x => Real.exp (-z * (x - c)))
          = (fun x => Real.exp (z * c) * Real.exp (-z * x)) := by
        funext x; rw [← Real.exp_add]; congr 1; ring
      rw [heq]; exact (integrableOn_exp_mul_Ioi (by linarith : -z < 0) _).const_mul _
    have htail : IntegrableOn (fun x => Wt a b * Real.exp (-z * (x - edgeLo σ a b))
        + Ct a b * Real.exp (-z * (x - edgeHi σ a b))) (Ioi (edgeHi σ a b)) :=
      ((hexp (edgeLo σ a b)).const_mul (Wt a b)).add ((hexp (edgeHi σ a b)).const_mul (Ct a b))
    refine htail.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hxi : edgeHi σ a b < x := hx
    unfold baxterQ; rw [if_neg (by linarith : ¬ x < edgeLo σ a b), if_neg (not_le.mpr hxi)]

end FMSA.ExactMSA.Breakpoint
