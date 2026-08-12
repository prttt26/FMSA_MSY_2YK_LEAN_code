/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/
import Mathlib
import LeanCode.HSMixture.HSMix

/-!
# `HSMix` windowing-loss structural lemmas — sub-zero tail / full-line split (Yukawa-free)

The real-space **windowing-loss** structure of the pure hard-sphere mixture Baxter entry
`q0MixEntry`: how the full-line first Baxter convolution `∫_ℝ` splits into the windowed `∫₀^σ` piece
plus a sub-zero tail `∫_{≤0}`, and how that tail vanishes (smallest species, `λᵢₖ ≥ 0`) or collapses
to the explicit Lebowitz polynomial moment on `[λᵢₖ, 0]` (larger species, `λᵢₖ ≤ 0`).

All of it uses only the compact support `[λᵢₖ, Rᵢₖ]` (`q0MixEntry_support_subset`) and the geometry
`R`/`lam` — pure hard sphere, no Yukawa tail.  Proved here at the **pure-HS layer**; the Yukawa
`Mix N M` reaches them through `Mix.toHSMix` (`WHSupports.lean`) for any `M` (`M=0` = pure HS).

Ported (2026-08-11) from the `Mix`-based versions in `YukawaOZMix/MixtureHSDCFFin1.lean`.  The
seed-coupled windowing *bridges* (`matBaxterUExt_eq_matBaxterU_…`) stay at the Yukawa layer, since
they weave these structural facts together with the generic Matrix seed machinery.
-/

open MeasureTheory Set

namespace FMSA.HSMix

variable {N : ℕ}

/-- **Windowing loss vanishes for `λᵢₖ ≥ 0`.**  `q0MixEntry X i k` is supported in `[λᵢₖ, Rᵢₖ]`, so
for `λᵢₖ ≥ 0` it vanishes at `t < 0`; the sub-zero tail `∫_{≤0} q0MixEntry·f = 0` (`{0}` null). -/
theorem q0MixEntry_subZeroTail_zero (X : FMSA.HSMix N) (i k : Fin N) (f : ℝ → ℝ)
    (hlam : 0 ≤ X.lam i k) :
    (∫ t in Set.Iic (0:ℝ), X.q0MixEntry i k t * f t) = 0 := by
  rw [show (∫ t in Set.Iic (0:ℝ), X.q0MixEntry i k t * f t)
      = ∫ _t in Set.Iic (0:ℝ), (0:ℝ) from ?_, MeasureTheory.integral_zero]
  refine MeasureTheory.setIntegral_congr_ae measurableSet_Iic ?_
  have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by
    simp only [MeasureTheory.ae_iff, not_not]; simpa using MeasureTheory.measure_singleton (0:ℝ)
  filter_upwards [h0] with t htne htmem
  have hq : X.q0MixEntry i k t = 0 :=
    Function.notMem_support.mp (fun hs => absurd (q0MixEntry_support_subset X i k hs).1
      (not_le.mpr (lt_of_lt_of_le (lt_of_le_of_ne htmem htne) hlam)))
  rw [hq, zero_mul]

/-- **Full-line ⇄ windowed split for the compactly-supported `q0MixEntry`.**  `∫_ℝ q0MixEntry·g =
∫₀^σ + ∫_{≤0}` — the `(σ,∞)` piece vanishes (`q0MixEntry = 0` past `Rᵢₖ ≤ σ`). -/
theorem q0MixEntry_intSplit (X : FMSA.HSMix N) (i k : Fin N) (g : ℝ → ℝ) (sigma : ℝ)
    (hsig0 : 0 ≤ sigma) (hRσ : X.R i k ≤ sigma)
    (hint : Integrable (fun t => X.q0MixEntry i k t * g t)) :
    (∫ t, X.q0MixEntry i k t * g t)
      = (∫ t in (0:ℝ)..sigma, X.q0MixEntry i k t * g t)
        + ∫ t in Set.Iic (0:ℝ), X.q0MixEntry i k t * g t := by
  have hcompl := MeasureTheory.integral_add_compl (measurableSet_Iic (a := (0:ℝ))) hint
  rw [Set.compl_Iic] at hcompl
  have hzero : (∫ t in Set.Ioi sigma, X.q0MixEntry i k t * g t) = 0 :=
    MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun t ht => by
      rw [Function.notMem_support.mp (fun hs => absurd (q0MixEntry_support_subset X i k hs).2
        (not_le.mpr (lt_of_le_of_lt hRσ (Set.mem_Ioi.mp ht)))), zero_mul])
  have hIoi : (∫ t in Set.Ioi (0:ℝ), X.q0MixEntry i k t * g t)
      = ∫ t in (0:ℝ)..sigma, X.q0MixEntry i k t * g t := by
    rw [(Set.Ioc_union_Ioi_eq_Ioi hsig0).symm, MeasureTheory.setIntegral_union
      Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hint.integrableOn hint.integrableOn, hzero,
      add_zero, intervalIntegral.integral_of_le hsig0]
  rw [← hcompl, hIoi, add_comm]

/-- `q0MixEntry X i k` integrates to `0` over `(-∞, λᵢₖ]` (below its support; `{λᵢₖ}` is null). -/
theorem q0MixEntry_intIic_lam_eq_zero (X : FMSA.HSMix N) (i k : Fin N) (g : ℝ → ℝ) :
    (∫ t in Set.Iic (X.lam i k), X.q0MixEntry i k t * g t) = 0 := by
  rw [show (∫ t in Set.Iic (X.lam i k), X.q0MixEntry i k t * g t)
      = ∫ _t in Set.Iic (X.lam i k), (0:ℝ) from ?_, MeasureTheory.integral_zero]
  refine MeasureTheory.setIntegral_congr_ae measurableSet_Iic ?_
  have h0 : ∀ᵐ t : ℝ, t ≠ X.lam i k := by
    simp only [MeasureTheory.ae_iff, not_not]
    simpa using MeasureTheory.measure_singleton (X.lam i k)
  filter_upwards [h0] with t htne htmem
  have hq : X.q0MixEntry i k t = 0 :=
    Function.notMem_support.mp (fun hs => absurd (q0MixEntry_support_subset X i k hs).1
      (not_le.mpr (lt_of_le_of_ne htmem htne)))
  rw [hq, zero_mul]

/-- **Larger-species sub-zero tail, compact form.**  For `λᵢₖ ≤ 0` (species `i` bigger than `k`,
`σᵢ > σₖ`) the windowing-loss tail collapses to the COMPACT interval integral over `[λᵢₖ, 0]` — the
`(-∞,λᵢₖ]` piece is below the support and vanishes (`q0MixEntry_intIic_lam_eq_zero`). -/
theorem q0MixEntry_subZeroTail_compact (X : FMSA.HSMix N) (i k : Fin N) (g : ℝ → ℝ)
    (hlam : X.lam i k ≤ 0) (hint : Integrable (fun t => X.q0MixEntry i k t * g t)) :
    (∫ t in Set.Iic (0:ℝ), X.q0MixEntry i k t * g t)
      = ∫ t in (X.lam i k)..(0:ℝ), X.q0MixEntry i k t * g t := by
  rw [← Set.Iic_union_Ioc_eq_Iic hlam, MeasureTheory.setIntegral_union
      (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hint.integrableOn hint.integrableOn,
    q0MixEntry_intIic_lam_eq_zero X i k g, zero_add, intervalIntegral.integral_of_le hlam]

/-- `q0MixEntry` on its support `[λᵢₖ, Rᵢₖ]` is the explicit Lebowitz quadratic. -/
theorem q0MixEntry_inner_expand (X : FMSA.HSMix N) (i k : Fin N) {t : ℝ}
    (ht : t ∈ Set.Icc (X.lam i k) (X.R i k)) :
    X.q0MixEntry i k t
      = X.Q0 i k * (t - X.R i k) + X.Qpp k * (t - X.R i k) ^ 2 / 2 := by
  rw [q0MixEntry, Set.indicator_of_mem ht]

/-- **Larger-species windowing loss made EXPLICIT.**  For `λᵢₖ ≤ 0`, the sub-zero tail equals the
concrete polynomial moment `∫_{λᵢₖ}^0 (Q0ᵢₖ·(t−Rᵢₖ) + Qppₖ·(t−Rᵢₖ)²/2)·g(t) dt` — the Lebowitz
Baxter quadratic against `g` over `[λᵢₖ, 0]` (there the kernel is the bare polynomial). -/
theorem q0MixEntry_subZeroTail_poly (X : FMSA.HSMix N) (i k : Fin N) (g : ℝ → ℝ)
    (hlam : X.lam i k ≤ 0) (hint : Integrable (fun t => X.q0MixEntry i k t * g t)) :
    (∫ t in Set.Iic (0:ℝ), X.q0MixEntry i k t * g t)
      = ∫ t in (X.lam i k)..(0:ℝ),
          (X.Q0 i k * (t - X.R i k) + X.Qpp k * (t - X.R i k) ^ 2 / 2) * g t := by
  rw [q0MixEntry_subZeroTail_compact X i k g hlam hint]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le hlam, Set.mem_Icc] at ht
  have hR : (0:ℝ) ≤ X.R i k := by
    simp only [FMSA.HSMix.R]; linarith [X.hσ i, X.hσ k]
  rw [q0MixEntry_inner_expand X i k (Set.mem_Icc.mpr ⟨ht.1, le_trans ht.2 hR⟩)]

end FMSA.HSMix
