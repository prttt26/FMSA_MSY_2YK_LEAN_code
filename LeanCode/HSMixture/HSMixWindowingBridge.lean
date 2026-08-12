/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/
import Mathlib
import LeanCode.HSMixture.MixtureSeedExtended
import LeanCode.HSMixture.HSMixWindowing

/-!
# `HSMix` windowing-loss bridges — extended (`∫_ℝ`) vs windowed (`∫₀^σ`) seed arms (Yukawa-free)

The seed-coupled windowing-loss bridges for the pure hard-sphere mixture, stated on `HSMix`: how the
extended (full-line) first Baxter convolution `matBaxterUExt` relates to the windowed `matBaxterU`
for the concrete Baxter kernel `q0MixEntry`, on each seed arm, and how the two arms' losses SUM to
the symmetrized-kernel sub-zero tail (the un-reflected part of the DCF fold kernel `Ĉ₀`).

These weave the generic Matrix seed machinery (`matBaxterU*`,
`matBaxterUExt_eq_matBaxterU_sub_tail`, `HSMixture/MixtureSeedExtended.lean`) with the migrated HS
structural facts (`q0MixEntry_intSplit`, `_subZeroTail_zero`, `_subZeroTail_poly`,
`HSMixture/HSMixWindowing.lean`) — all Yukawa-free.  The Yukawa `Mix N M` reaches them through
`Mix.toHSMix` (`WHSupports.lean`) for any `M` (`M=0` = pure HS).

Ported (2026-08-11) from the `Mix`-based versions in `YukawaOZMix/MixtureHSDCFFin1.lean`.
-/

open MeasureTheory Set FMSA.MixtureOzStar

namespace FMSA.HSMix

variable {N : ℕ}

/-- **Windowing-loss bridge — extended = windowed for the smallest species.**  On a row `i` whose
species is smallest (`λᵢₖ ≥ 0` ∀k, i.e. `σᵢ ≤ σₖ`), every sub-zero tail vanishes, so the extended
(`∫_ℝ`) and windowed (`∫₀^σ`) first Baxter convolutions COINCIDE — NO windowing loss. -/
theorem matBaxterUExt_eq_matBaxterU_of_row_lam_nonneg (X : FMSA.HSMix N)
    (Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma) (i j : Fin N) (r : ℝ)
    (hlam : ∀ k, 0 ≤ X.lam i k) (hRσ : ∀ k, X.R i k ≤ sigma)
    (hint : ∀ k, Integrable (fun t => X.q0MixEntry i k t * Psi k j (r - t))) :
    matBaxterUExt Psi (fun a b => X.q0MixEntry a b) i j r
      = matBaxterU Psi (fun a b => X.q0MixEntry a b) sigma i j r := by
  rw [matBaxterUExt_eq_matBaxterU_sub_tail Psi (fun a b => X.q0MixEntry a b) sigma i j r
      (fun k => q0MixEntry_intSplit X i k (fun t => Psi k j (r - t)) sigma hsig0 (hRσ k) (hint k)),
    Finset.sum_eq_zero (fun k _ => q0MixEntry_subZeroTail_zero X i k _ (hlam k)), sub_zero]

/-- **Windowing loss for the LARGEST species, made EXPLICIT.**  On a row `i` whose species is
largest (`λᵢₖ ≤ 0` ∀k, i.e. `σᵢ ≥ σₖ`), the extended and windowed convolutions differ by the
concrete sum of Lebowitz polynomial moments `∑ₖ ∫_{λᵢₖ}^0 (Q0ᵢₖ(t−Rᵢₖ)+Qppₖ(t−Rᵢₖ)²/2)·Ψₖⱼ(r−t)` —
the exact windowing loss, NOT fabricated away. -/
theorem matBaxterUExt_eq_matBaxterU_sub_polyTail (X : FMSA.HSMix N)
    (Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma) (i j : Fin N) (r : ℝ)
    (hlam : ∀ k, X.lam i k ≤ 0) (hRσ : ∀ k, X.R i k ≤ sigma)
    (hint : ∀ k, Integrable (fun t => X.q0MixEntry i k t * Psi k j (r - t))) :
    matBaxterUExt Psi (fun a b => X.q0MixEntry a b) i j r
      = matBaxterU Psi (fun a b => X.q0MixEntry a b) sigma i j r
        - ∑ k, ∫ t in (X.lam i k)..(0:ℝ),
            (X.Q0 i k * (t - X.R i k) + X.Qpp k * (t - X.R i k) ^ 2 / 2) * Psi k j (r - t) := by
  rw [matBaxterUExt_eq_matBaxterU_sub_tail Psi (fun a b => X.q0MixEntry a b) sigma i j r
    (fun k => q0MixEntry_intSplit X i k (fun t => Psi k j (r - t)) sigma hsig0 (hRσ k) (hint k))]
  congr 1
  exact Finset.sum_congr rfl (fun k _ =>
    q0MixEntry_subZeroTail_poly X i k (fun t => Psi k j (r - t)) (hlam k) (hint k))

/-- **Transposed-arm windowing loss vanishes — `matBaxterUtExt = matBaxterUt` when `λₖᵢ ≥ 0`.**  The
transposed seed arm convolves the kernel `Qₖᵢ`, so its sub-zero tail is governed by `λₖᵢ`.  DUAL to
the un-transposed arm: it VANISHES on the LARGEST-species row (`σᵢ ≥ σₖ ∀k ⟺ λₖᵢ ≥ 0`), via the
transpose `rfl`s at kernel `Qᵀ`. -/
theorem matBaxterUtExt_eq_matBaxterUt_of_row (X : FMSA.HSMix N)
    (Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma) (i j : Fin N) (r : ℝ)
    (hlam : ∀ k, 0 ≤ X.lam k i) (hRσ : ∀ k, X.R k i ≤ sigma)
    (hint : ∀ k, Integrable (fun t => X.q0MixEntry k i t * Psi k j (r - t))) :
    matBaxterUtExt Psi (fun a b => X.q0MixEntry a b) i j r
      = matBaxterUt Psi (fun a b => X.q0MixEntry a b) sigma i j r := by
  rw [matBaxterUtExt_eq_transpose, matBaxterUt_eq_transpose,
    matBaxterUExt_eq_matBaxterU_sub_tail Psi (fun a b => X.q0MixEntry b a) sigma i j r
      (fun k => q0MixEntry_intSplit X k i (fun t => Psi k j (r - t)) sigma hsig0 (hRσ k) (hint k)),
    Finset.sum_eq_zero (fun k _ => q0MixEntry_subZeroTail_zero X k i _ (hlam k)), sub_zero]

/-- **Transposed-arm windowing loss, EXPLICIT — smallest species (`λₖᵢ ≤ 0`).**  On the
SMALLEST-species row (`σᵢ ≤ σₖ ∀k`), the transposed extended arm differs from the windowed by the
explicit sum of Lebowitz polynomial moments `∑ₖ ∫_{λₖᵢ}^0 (Q0ₖᵢ(t−Rₖᵢ)+Qppᵢ(t−Rₖᵢ)²/2)·Ψₖⱼ(r−t)` —
the DUAL of the un-transposed largest-species loss. -/
theorem matBaxterUtExt_eq_matBaxterUt_sub_polyTail (X : FMSA.HSMix N)
    (Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma) (i j : Fin N) (r : ℝ)
    (hlam : ∀ k, X.lam k i ≤ 0) (hRσ : ∀ k, X.R k i ≤ sigma)
    (hint : ∀ k, Integrable (fun t => X.q0MixEntry k i t * Psi k j (r - t))) :
    matBaxterUtExt Psi (fun a b => X.q0MixEntry a b) i j r
      = matBaxterUt Psi (fun a b => X.q0MixEntry a b) sigma i j r
        - ∑ k, ∫ t in (X.lam k i)..(0:ℝ),
            (X.Q0 k i * (t - X.R k i) + X.Qpp i * (t - X.R k i) ^ 2 / 2) * Psi k j (r - t) := by
  rw [matBaxterUtExt_eq_transpose, matBaxterUt_eq_transpose,
    matBaxterUExt_eq_matBaxterU_sub_tail Psi (fun a b => X.q0MixEntry b a) sigma i j r
      (fun k => q0MixEntry_intSplit X k i (fun t => Psi k j (r - t)) sigma hsig0 (hRσ k) (hint k))]
  congr 1
  exact Finset.sum_congr rfl (fun k _ =>
    q0MixEntry_subZeroTail_poly X k i (fun t => Psi k j (r - t)) (hlam k) (hint k))

/-- **Sum of the two seed arms' windowing losses = the SYMMETRIZED-kernel sub-zero tail.**  The
un-transposed loss `matBaxterU − matBaxterUExt = ∑ₖ ∫_{≤0} q0MixEntry i k·Ψ` and the transposed loss
`matBaxterUt − matBaxterUtExt = ∑ₖ ∫_{≤0} q0MixEntry k i·Ψ` ADD, by linearity, to the sub-zero tail
of the SYMMETRIZED Baxter kernel `q0MixEntry i k + q0MixEntry k i` — the un-reflected part of the
DCF fold kernel `Ĉ₀`.  Holds on ANY row (no species condition). -/
theorem windowing_loss_sum_eq_symTail (X : FMSA.HSMix N)
    (Psi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma) (i j : Fin N) (r : ℝ)
    (hRun : ∀ k, X.R i k ≤ sigma) (hRt : ∀ k, X.R k i ≤ sigma)
    (hint_un : ∀ k, Integrable (fun t => X.q0MixEntry i k t * Psi k j (r - t)))
    (hint_t : ∀ k, Integrable (fun t => X.q0MixEntry k i t * Psi k j (r - t))) :
    (matBaxterU Psi (fun a b => X.q0MixEntry a b) sigma i j r
       - matBaxterUExt Psi (fun a b => X.q0MixEntry a b) i j r)
    + (matBaxterUt Psi (fun a b => X.q0MixEntry a b) sigma i j r
       - matBaxterUtExt Psi (fun a b => X.q0MixEntry a b) i j r)
    = ∑ k, ∫ t in Set.Iic (0:ℝ),
        (X.q0MixEntry i k t + X.q0MixEntry k i t) * Psi k j (r - t) := by
  have hun : matBaxterUExt Psi (fun a b => X.q0MixEntry a b) i j r
      = matBaxterU Psi (fun a b => X.q0MixEntry a b) sigma i j r
        - ∑ k, ∫ t in Set.Iic (0:ℝ), X.q0MixEntry i k t * Psi k j (r - t) :=
    matBaxterUExt_eq_matBaxterU_sub_tail Psi (fun a b => X.q0MixEntry a b) sigma i j r
      (fun k => q0MixEntry_intSplit X i k (fun t => Psi k j (r - t)) sigma hsig0 (hRun k)
        (hint_un k))
  have ht : matBaxterUtExt Psi (fun a b => X.q0MixEntry a b) i j r
      = matBaxterUt Psi (fun a b => X.q0MixEntry a b) sigma i j r
        - ∑ k, ∫ t in Set.Iic (0:ℝ), X.q0MixEntry k i t * Psi k j (r - t) := by
    rw [matBaxterUtExt_eq_transpose, matBaxterUt_eq_transpose]
    exact matBaxterUExt_eq_matBaxterU_sub_tail Psi (fun a b => X.q0MixEntry b a) sigma i j r
      (fun k => q0MixEntry_intSplit X k i (fun t => Psi k j (r - t)) sigma hsig0 (hRt k) (hint_t k))
  have e1 : matBaxterU Psi (fun a b => X.q0MixEntry a b) sigma i j r
      - matBaxterUExt Psi (fun a b => X.q0MixEntry a b) i j r
      = ∑ k, ∫ t in Set.Iic (0:ℝ), X.q0MixEntry i k t * Psi k j (r - t) := by rw [hun]; ring
  have e2 : matBaxterUt Psi (fun a b => X.q0MixEntry a b) sigma i j r
      - matBaxterUtExt Psi (fun a b => X.q0MixEntry a b) i j r
      = ∑ k, ∫ t in Set.Iic (0:ℝ), X.q0MixEntry k i t * Psi k j (r - t) := by rw [ht]; ring
  rw [e1, e2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← MeasureTheory.integral_add (hint_un k).integrableOn (hint_t k).integrableOn]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Iic (fun t _ => ?_)
  ring

end FMSA.HSMix
