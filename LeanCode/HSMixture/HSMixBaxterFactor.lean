/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/
import Mathlib
import LeanCode.HSMixture.HSMix

/-!
# `HSMix` Baxter-factor analytic lemmas — measurability, integrability, bound (Yukawa-free)

The measurability / interval-integrability / global-bound side-conditions on the pure hard-sphere
mixture Baxter entry `q0MixEntry` (`HSMixture/HSMix.lean`).  These are the `hQ0`/`hQ1`
side-conditions of the Wertheim–Thiele moment seed and the boundedness inputs of the row-sum
machinery — proved here at the **pure-HS layer** (Mathlib-only, no Yukawa tail), so the seed route
can be re-based onto `HSMix`.  The Yukawa `Mix N M` reaches them through `Mix.toHSMix`
(`WHSupports.lean`): the underlying functions are `rfl`-equal, so these transfer for any `M`
(`M=0` = pure hard sphere).

Ported (2026-08-11) from the `Mix`-based versions in `YukawaOZMix/MixtureRowSum.lean`
(`q0MixEntry_measurable`, `_intervalIntegrable`, `_mul_id_intervalIntegrable`, `_abs_le`,
`_mul_exp_integrable`); the proofs use only the compact core support `[λᵢₖ, Rᵢₖ]` and the continuity
of the Baxter quadratic, both of which live on `HSMix`.
-/

open MeasureTheory Set

namespace FMSA.HSMix

variable {N : ℕ}

/-- Global measurability of the mixture Baxter entry (indicator of a continuous quadratic). -/
theorem q0MixEntry_measurable (X : FMSA.HSMix N) (i k : Fin N) :
    Measurable (X.q0MixEntry i k) := by
  unfold q0MixEntry
  exact Measurable.indicator (by fun_prop) measurableSet_Icc

/-- **`q0MixEntry X i k` is interval-integrable on any `[a,b]`.**  It is the measurable indicator
of a continuous quadratic on the compact core `[λᵢₖ, Rᵢₖ]`, hence bounded and measurable, so
integrable on any finite interval. -/
theorem q0MixEntry_intervalIntegrable (X : FMSA.HSMix N) (i k : Fin N) (a b : ℝ) :
    IntervalIntegrable (X.q0MixEntry i k) volume a b := by
  have hmeas : Measurable (X.q0MixEntry i k) := q0MixEntry_measurable X i k
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := X.lam i k) (b := X.R i k)).exists_bound_of_continuousOn
    (f := fun r => X.Q0 i k * (r - X.R i k) + X.Qpp k * (r - X.R i k) ^ 2 / 2)
    (Continuous.continuousOn (by fun_prop))
  rw [intervalIntegrable_iff]
  have hfin : volume (Set.uIoc a b) ≠ ⊤ :=
    ne_top_of_le_ne_top isCompact_uIcc.measure_ne_top (measure_mono Set.uIoc_subset_uIcc)
  refine Measure.integrableOn_of_bounded (M := max C 0) hfin hmeas.aestronglyMeasurable ?_
  filter_upwards with u
  rw [Real.norm_eq_abs]
  unfold q0MixEntry
  by_cases h : u ∈ Set.Icc (X.lam i k) (X.R i k)
  · rw [Set.indicator_of_mem h]
    have hb := hC u h
    rw [Real.norm_eq_abs] at hb
    exact le_trans hb (le_max_left _ _)
  · rw [Set.indicator_of_notMem h, abs_zero]; exact le_max_right _ _

/-- **`t ↦ t · q0MixEntry X i k t` is interval-integrable on any `[a,b]`** (product of the bounded
measurable factor and the continuous `t`). -/
theorem q0MixEntry_mul_id_intervalIntegrable (X : FMSA.HSMix N) (i k : Fin N) (a b : ℝ) :
    IntervalIntegrable (fun t => t * X.q0MixEntry i k t) volume a b :=
  (q0MixEntry_intervalIntegrable X i k a b).continuousOn_mul (g := fun t => t)
    continuous_id.continuousOn

/-- Global bound on `|q0MixEntry|` (bounded on the compact core, zero elsewhere). -/
theorem q0MixEntry_abs_le (X : FMSA.HSMix N) (i k : Fin N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |X.q0MixEntry i k t| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := X.lam i k) (b := X.R i k)).exists_bound_of_continuousOn
    (f := fun r => X.Q0 i k * (r - X.R i k) + X.Qpp k * (r - X.R i k) ^ 2 / 2)
    (Continuous.continuousOn (by fun_prop))
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  unfold q0MixEntry
  by_cases h : t ∈ Set.Icc (X.lam i k) (X.R i k)
  · rw [Set.indicator_of_mem h]
    have hb := hC t h; rw [Real.norm_eq_abs] at hb
    exact le_trans hb (le_max_left _ _)
  · rw [Set.indicator_of_notMem h, abs_zero]; exact le_max_right _ _

/-- **Full-line integrability of `(q0MixEntry)·exp(w·t)` for any `w : ℂ`.**  Compactly supported on
`[λᵢₖ,Rᵢₖ]` where it agrees with the continuous `(quadratic)·e^{w·t}`, hence bounded there. -/
theorem q0MixEntry_mul_exp_integrable (X : FMSA.HSMix N) (i k : Fin N) (w : ℂ) :
    Integrable (fun t => (X.q0MixEntry i k t : ℂ) * Complex.exp (w * t)) := by
  have hmeas : Measurable (fun t => (X.q0MixEntry i k t : ℂ) * Complex.exp (w * t)) :=
    (Complex.measurable_ofReal.comp (q0MixEntry_measurable X i k)).mul (by fun_prop)
  have hsupp : Function.support (fun t => (X.q0MixEntry i k t : ℂ) * Complex.exp (w * t))
      ⊆ Set.Icc (X.lam i k) (X.R i k) := by
    intro t ht
    rw [Function.mem_support] at ht
    by_contra hns
    have h0 : X.q0MixEntry i k t = 0 := by
      by_contra hq
      exact hns (q0MixEntry_support_subset X i k (Function.mem_support.mpr hq))
    exact ht (by rw [h0]; simp)
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := X.lam i k) (b := X.R i k)).exists_bound_of_continuousOn
    (f := fun t => ((X.Q0 i k * (t - X.R i k) + X.Qpp k * (t - X.R i k) ^ 2 / 2 : ℝ) : ℂ)
      * Complex.exp (w * t))
    (Continuous.continuousOn (by fun_prop))
  refine Measure.integrableOn_of_bounded (M := C) measure_Icc_lt_top.ne
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  have hval : (X.q0MixEntry i k u : ℂ) * Complex.exp (w * u)
      = ((X.Q0 i k * (u - X.R i k) + X.Qpp k * (u - X.R i k) ^ 2 / 2 : ℝ) : ℂ)
        * Complex.exp (w * u) := by
    unfold q0MixEntry; rw [Set.indicator_of_mem hu]
  rw [hval]; exact hC u hu

end FMSA.HSMix
