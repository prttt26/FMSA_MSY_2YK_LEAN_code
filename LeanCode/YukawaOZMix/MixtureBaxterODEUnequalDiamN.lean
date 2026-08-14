/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MixtureDCFAEInjective
import LeanCode.YukawaOZMix.MixtureBaxterODEUnequalDiam
import LeanCode.YukawaOZMix.MixtureCorrelationDeriv

/-!
# The mixture Baxter ODE at UNEQUAL diameters — GENERAL `N` (MIXCHS.7-N)

`MixtureBaxterODEUnequalDiam.lean` closed the unequal-σ value route for a **binary** mixture
(`Fin 2`).  Its proofs collapsed the species sum `∑ₗ` by `fin_cases i <;> fin_cases k` and
hard-coded the pre-summed DCF coefficients.  This file lifts the whole route to a **general
`N`-component** mixture (`Fin N`), where the correlation `∑ₗ` genuinely ranges over all species.

The key structural change: keep the species sum **symbolic**.  The `√`-collapse
`√(ρᵢρₗ)·√(ρₖρₗ) = ρₗ·√(ρᵢρₖ)` (`rhoGeoPhys_mul_eq`, general `N`) fires for **every** `l` without
`fin_cases`, so the per-species contribution to the DCF is a single ring identity under the sum.

This foundations layer generalizes the `Fin 2` objects to `Fin N`:
* `physMixN` — the physical (Lebowitz/PY) `Mix N 0` (`Q0phys`/`Qppphys`, `Qpp` row-independent);
* `qWeightedN`, `matDCFreCoreN` — the `√ρ`-weighted Baxter factor and the real DCF core
  `matDCFreCoreN i k v = qWeightedN i k v + qWeightedN k i(−v) − matCorrFull(qWeightedN) i k v`
  (the structural form of `Re(matDCFfull)`; all `q0MixEntry` real);
* `matCorrFull_eq_qpConvN` — the correlation as the species sum of `qpConv/(2π)²`;
* `matDCFreCoreN_upper_eq` / `_lower_eq` — the two-piece decomposition.
-/

open MeasureTheory Set

namespace FMSA.MixtureOzStar

open FMSA.HardSphere FMSA.MatrixQ0 FMSA.WHSupports FMSA.InnerDecomp
open FMSA.MixtureHSDCF FMSA.MixtureConvolution

/-- **The `√ρ`-weighted Baxter factor** `qWeightedNᵢₖ(v) = rgᵢₖ·q0MixEntry(physMixN)ᵢₖ(v)`.
(`physMixN` = the general-`N` physical `Mix N 0`, `MixtureDCFAEInjective.lean`.) -/
noncomputable def qWeightedN {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) :
    Matrix (Fin N) (Fin N) (ℝ → ℝ) :=
  fun i k => fun v => rhoGeoPhys rho i k * q0MixEntry (physMixN rho sigma hsig) i k v

/-- **The DCF core at general `N`** — `matDCFreCoreN i k v = qWeightedN i k v + qWeightedN k i(−v)
− matCorrFull(qWeightedN) i k v`.  This is the structural form of `Re(matDCFfull)` (the two `√ρ`
linear Baxter terms minus the correlation); all `q0MixEntry` values are real, so no `Re`-bookkeeping
is needed.  At `N = 2` it agrees with `matDCFreCore`. -/
noncomputable def matDCFreCoreN {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) (v : ℝ) : ℝ :=
  qWeightedN rho sigma hsig i k v + qWeightedN rho sigma hsig k i (-v)
    - matCorrFull (qWeightedN rho sigma hsig) i k v

/-- `qWeightedN i k` vanishes off the support `[λᵢₖ, Rᵢₖ] = [(σₖ−σᵢ)/2, (σᵢ+σₖ)/2]`
(`q0MixEntry_support_subset`). -/
theorem qWeightedN_eq_zero_of_notMem {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) {v : ℝ} (hv : v ∉ Set.Icc ((sigma k - sigma i) / 2)
      ((sigma i + sigma k) / 2)) :
    qWeightedN rho sigma hsig i k v = 0 := by
  simp only [qWeightedN]
  have hsupp : v ∉ Function.support (q0MixEntry (physMixN rho sigma hsig) i k) := by
    intro hs
    have hmem := q0MixEntry_support_subset (physMixN rho sigma hsig) i k hs
    simp only [physMixN, Mix.lam, Mix.R] at hmem
    exact hv hmem
  rw [Function.notMem_support.mp hsupp, mul_zero]

/-- The forward Baxter term `qWeightedN i k` vanishes on `(−∞, λᵢₖ)`. -/
theorem qWeightedN_forward_eq_zero_of_lt_lam {N : ℕ} (rho sigma : Fin N → ℝ)
    (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) {v : ℝ} (hv : v < (sigma k - sigma i) / 2) :
    qWeightedN rho sigma hsig i k v = 0 :=
  qWeightedN_eq_zero_of_notMem rho sigma hsig i k
    (fun hmem => by rw [Set.mem_Icc] at hmem; linarith [hmem.1])

/-- The reflected Baxter term `qWeightedN k i(−v)` vanishes on `(λᵢₖ, ∞)` (for `v > λᵢₖ`,
`−v < λₖᵢ`, below the support of `qWeightedN k i`). -/
theorem qWeightedN_reflected_eq_zero_of_gt_lam {N : ℕ} (rho sigma : Fin N → ℝ)
    (hsig : ∀ k, 0 < sigma k) (i k : Fin N) {v : ℝ} (hv : (sigma k - sigma i) / 2 < v) :
    qWeightedN rho sigma hsig k i (-v) = 0 :=
  qWeightedN_eq_zero_of_notMem rho sigma hsig k i
    (fun hmem => by rw [Set.mem_Icc] at hmem; linarith [hmem.1])

open FMSA.MixtureHSDCF in
/-- **Correlation as the species sum of `qpConv/(2π)²`** (general `N`) —
`matCorrFull(qWeightedN)ᵢₖ = ∑ₗ qpConv(physMixN)ᵢₗₖ/(2π)²`.  Structural: `qFwd = 2π·qWeightedN` and
`pMixEntry = 2π·qWeightedN(−·)` per `l`, then `field_simp`.  (The `N = 2` proof verbatim.) -/
theorem matCorrFull_eq_qpConvN {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) (v : ℝ) :
    matCorrFull (qWeightedN rho sigma hsig) i k v
      = ∑ l, qpConv (physMixN rho sigma hsig) i l k v / (2 * Real.pi) ^ 2 := by
  simp only [matCorrFull]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hqFwd : ∀ t, qFwd (physMixN rho sigma hsig) i l t
      = 2 * Real.pi * qWeightedN rho sigma hsig i l t := by
    intro t; simp only [qFwd, qWeightedN, rhoGeoPhys, physMixN]; ring
  have hpMix : ∀ u, pMixEntry (physMixN rho sigma hsig) k l u
      = 2 * Real.pi * qWeightedN rho sigma hsig k l (-u) := by
    intro u; simp only [pMixEntry, qWeightedN, rhoGeoPhys, physMixN]; ring
  rw [show qpConv (physMixN rho sigma hsig) i l k v
      = ∫ t, qFwd (physMixN rho sigma hsig) i l t
          * pMixEntry (physMixN rho sigma hsig) k l (v - t) from rfl,
    ← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  rw [hqFwd, hpMix, show -(v - t) = t - v from by ring]
  have h2π : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  field_simp

/-- **Two-piece decomposition — UPPER piece `(λᵢₖ, Rᵢₖ)`** (general `N`).  For `v > λᵢₖ` the
reflected term vanishes: `matDCFreCoreN i k v = qWeightedN i k v − matCorrFull i k v`. -/
theorem matDCFreCoreN_upper_eq {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) {v : ℝ} (hv : (sigma k - sigma i) / 2 < v) :
    matDCFreCoreN rho sigma hsig i k v
      = qWeightedN rho sigma hsig i k v - matCorrFull (qWeightedN rho sigma hsig) i k v := by
  simp only [matDCFreCoreN]
  rw [qWeightedN_reflected_eq_zero_of_gt_lam rho sigma hsig i k hv]; ring

/-- **Two-piece decomposition — LOWER piece `(0, λᵢₖ)`** (general `N`).  For `v < λᵢₖ` the forward
term vanishes: `matDCFreCoreN i k v = qWeightedN k i(−v) − matCorrFull i k v`. -/
theorem matDCFreCoreN_lower_eq {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) {v : ℝ} (hv : v < (sigma k - sigma i) / 2) :
    matDCFreCoreN rho sigma hsig i k v
      = qWeightedN rho sigma hsig k i (-v) - matCorrFull (qWeightedN rho sigma hsig) i k v := by
  simp only [matDCFreCoreN]
  rw [qWeightedN_forward_eq_zero_of_lt_lam rho sigma hsig i k hv]; ring

end FMSA.MixtureOzStar
