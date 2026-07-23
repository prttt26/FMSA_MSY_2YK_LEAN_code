/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.Analysis.JensenCounting

/-!
# Boundary growth of `circleAverage (log ‖f‖)` versus an infinite zero set

Abstract complex analysis for an arbitrary `f : ℂ → ℂ` — no hard-sphere object appears, which is
why this lives in `Analysis/` (split out of `HSMixture/MixtureHSCounting.lean` on 2026-07-19).

`DetBoundaryGrowth f` says the circle average of `log ‖f‖` outgrows **every** `M · log R + C`.
By Jensen's formula a function with finitely many zeros cannot do that, so super-logarithmic
growth forces infinitely many zeros (`infinite_zeros_of_growth`), and the physically natural
`≥ c·R` bound is one instance (`detBoundaryGrowth_of_linear`).
-/

set_option linter.style.longLine false

open Filter MeasureTheory Metric Real Set Topology

namespace FMSA.BoundaryGrowth

/-- **MZERO.10 — boundary growth of `log‖f‖`.**  The circle-average `circleAverage (Real.log ‖f·‖) 0 R`
eventually exceeds *every* log-linear bound `M·log R + C`.  This is implied by the physical estimate
`circleAverage (log‖det‖) 0 R ≥ c·R − C` (`c > 0`, from the `e^{−sσ}` growth on the `Re s < 0` arc) —
the single analytic input Route B needs, numerically confirmed by MZERO.2 (the quasi-periodic zero family
with `Re(s_n) ~ log Im(s_n)`). -/
def DetBoundaryGrowth (f : ℂ → ℂ) : Prop :=
  ∀ M C R₀ : ℝ, ∃ R : ℝ, R₀ ≤ R ∧ M * Real.log R + C < circleAverage (fun s => Real.log ‖f s‖) 0 R

/-- The physical `≥ c·R` growth (`c > 0`) implies `DetBoundaryGrowth`: an `R`-linear term eventually
dominates any `M·log R + C` (since `Real.log =o[atTop] id`).  Records that `DetBoundaryGrowth` is the
*weaker*, log-comparison form actually consumed by the capstone. -/
theorem detBoundaryGrowth_of_linear {f : ℂ → ℂ} {c : ℝ} (hc : 0 < c) (C₀ : ℝ)
    (hlin : ∀ R : ℝ, c * R - C₀ ≤ circleAverage (fun s => Real.log ‖f s‖) 0 R) :
    DetBoundaryGrowth f := by
  intro M C R₀
  have hlittle : (fun R : ℝ => M * Real.log R) =o[atTop] fun R : ℝ => R :=
    Real.isLittleO_log_id_atTop.const_mul_left M
  have h1 : ∀ᶠ R : ℝ in atTop, ‖M * Real.log R‖ ≤ (c / 2) * ‖R‖ := hlittle.def (by positivity)
  have h2 : ∀ᶠ R : ℝ in atTop, C + C₀ < (c / 2) * R :=
    (Tendsto.const_mul_atTop (by positivity : (0:ℝ) < c / 2) tendsto_id).eventually_gt_atTop (C + C₀)
  obtain ⟨R, ⟨⟨hR1, hR2⟩, hR0⟩, hRge⟩ :=
    (((h1.and h2).and (eventually_ge_atTop (0 : ℝ))).and (eventually_ge_atTop R₀)).exists
  refine ⟨R, hRge, lt_of_lt_of_le ?_ (hlin R)⟩
  have hlog_le : M * Real.log R ≤ (c / 2) * R :=
    le_trans (le_abs_self _) (le_trans hR1 (by rw [Real.norm_eq_abs, abs_of_nonneg hR0]))
  linarith

/-! ### MZERO.11 — structural capstone (Jensen-bound + growth ⟹ infinitely many zeros) -/

/-- **MZERO.11 — structural capstone.**  If (for the finite-zero case) the boundary log-average is bounded
by some `M·log R + C`, but `DetBoundaryGrowth` makes it exceed every such bound, then the zero set is
infinite.  Pure contradiction — the analytic content lives entirely in the two hypotheses. -/
theorem infinite_zeros_of_growth {f : ℂ → ℂ}
    (hJensen : Set.Finite {s : ℂ | f s = 0} →
        ∃ M C R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
          circleAverage (fun s => Real.log ‖f s‖) 0 R ≤ M * Real.log R + C)
    (hgrow : DetBoundaryGrowth f) :
    Set.Infinite {s : ℂ | f s = 0} := by
  intro hfin
  obtain ⟨M, C, R₀, hle⟩ := hJensen hfin
  obtain ⟨R, hR0, hlt⟩ := hgrow M C R₀
  exact absurd (hle R hR0) (not_le.mpr hlt)

/-- Partial `Finset` sum ≤ `finsum`, for a nonnegative, finitely-supported function. -/
theorem finset_sum_le_finsum_of_nonneg (h : ℂ → ℝ) (hh : ∀ u, 0 ≤ h u)
    (hfin : (Function.support h).Finite) (S : Finset ℂ) :
    ∑ z ∈ S, h z ≤ ∑ᶠ u, h u := by
  have hsub : Function.support h ⊆ ↑(S ∪ hfin.toFinset) := by
    intro x hx; rw [Finset.coe_union, Set.mem_union]; right
    rw [Set.Finite.coe_toFinset]; exact hx
  rw [finsum_eq_sum_of_support_subset h hsub]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun i _ _ => hh i)

end FMSA.BoundaryGrowth
