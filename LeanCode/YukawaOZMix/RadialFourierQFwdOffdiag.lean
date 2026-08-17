/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.YukawaOZMix.RadialFourierQFwd
import LeanCode.YukawaOZMix.MixtureRowSum

/-!
# Radial Fourier transform of the OFF-DIAGONAL forward Baxter factor `qFwd_im` (MRS.8 sub-fact 1)

Extends `RadialFourierQFwd.lean` (diagonal) to the general pair `(i,m)`.  The forward factor
`qFwd_im = 2π√(ρᵢρₘ)·q0MixEntry` is a quadratic windowed on `[λ_im, R_im]` with
`λ_im = (σₘ − σᵢ)/2` of either sign.

* `qFwd_outer` / `qFwd_lower` — the factor vanishes at/beyond `R_im` and below `λ_im`.
* `radial_fourier_qFwd_eq_intervalIntegral` — **general interval reduction** (all pairs): only the
  UPPER support bound is used, so `radial_fourier(qFwd_im) = (4π/k)·∫₀^{R_im} r·qFwd·sin`.  Subsumes
  the diagonal `radial_fourier_qFwd_diag_eq_intervalIntegral`.
* `cubic_moment` — `∫₀ˣ (A·r + B·r² + C·r³)·sin(kr)` via `psi1/2/3` (reusable moment).
* `radial_fourier_qFwd_offdiag` — the CLOSED FORM for the upper triangle `λ_im ≥ 0` (`σᵢ ≤ σₘ`): the
  window sits in `(0,∞)`, so the cubic-moment combo `A·ψ1 + B·ψ2 + C·ψ3` becomes the DIFFERENCE
  between `R_im` and the lower edge `λ_im` (`∫_{λ}^{R} = ∫₀^R − ∫₀^λ`).  Recovers the diagonal at
  `λ = 0` (all `ψ(0) = 0`).

⚠ These transforms do NOT assemble into `Cmix0` via `radial_fourier_conv` — `qpConv` is Mathlib 1D
convolution (not the 3D `radial3d_conv`), and the DCF relates to `cHSmixRaw` by the odd-part factor
`cHSodd = 2π√ρ·r·c^HS`, so `radial_fourier(cHSmixRaw) ≠ Cmix0`.  See the CORRECTION in
`RadialFourierQFwd.lean`; the correct bridge is `matRadialSymbol_eq_shellKernel_cos`.
-/

open MeasureTheory Set
namespace FMSA.MixtureHSDCF
open FMSA.HardSphere FMSA.InnerDecomp FMSA.WHSupports
variable {N M : ℕ}

/-- The forward factor vanishes at/beyond contact `R_im` (any pair). -/
theorem qFwd_outer (X : Mix N M) (i m : Fin N) {r : ℝ} (hr : X.R i m ≤ r) :
    qFwd X i m r = 0 := by
  unfold qFwd q0MixEntry
  by_cases hmem : r ∈ Set.Icc (X.lam i m) (X.R i m)
  · rw [Set.indicator_of_mem hmem]
    have hrR : r = X.R i m := le_antisymm hmem.2 hr
    rw [hrR]; ring
  · rw [Set.indicator_of_notMem hmem]; ring

/-- The forward factor vanishes below the lower window edge `λ_im`. -/
theorem qFwd_lower (X : Mix N M) (i m : Fin N) {r : ℝ} (hr : r < X.lam i m) :
    qFwd X i m r = 0 := by
  unfold qFwd q0MixEntry
  rw [Set.indicator_of_notMem (fun h => absurd h.1 (not_le.mpr hr))]; ring

/-- **General interval reduction** — `radial_fourier(qFwd_im)` over the core `[0, R_im]` (only the
UPPER support bound is used, so this holds for every pair `(i,m)`, `λ` of either sign). -/
theorem radial_fourier_qFwd_eq_intervalIntegral (X : Mix N M) (i m : Fin N) (k : ℝ) :
    radial_fourier (qFwd X i m) k
      = (4 * Real.pi / k) * ∫ r in (0 : ℝ)..(X.R i m), r * qFwd X i m r * Real.sin (k * r) := by
  unfold radial_fourier
  congr 1
  have hpt : Set.EqOn (fun r => r * qFwd X i m r * Real.sin (k * r))
      ((Set.Ioc 0 (X.R i m)).indicator (fun r => r * qFwd X i m r * Real.sin (k * r)))
      (Set.Ioi (0 : ℝ)) := by
    intro r hr0
    by_cases hr : r ∈ Set.Ioc (0 : ℝ) (X.R i m)
    · rw [Set.indicator_of_mem hr]
    · rw [Set.indicator_of_notMem hr]
      have hrge : X.R i m ≤ r := by
        simp only [Set.mem_Ioc, not_and, not_le] at hr
        exact (hr hr0).le
      simp [qFwd_outer X i m hrge]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt,
    MeasureTheory.setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_self_of_subset_right Set.Ioc_subset_Ioi_self,
    ← intervalIntegral.integral_of_le (X.R_pos i m).le]

/-- Moment of a cubic `A·r + B·r² + C·r³` against `sin(kr)` over `[0,x]`, via `psi1/2/3`. -/
theorem cubic_moment {k : ℝ} (hk : k ≠ 0) (A B C x : ℝ) :
    (∫ r in (0 : ℝ)..x, (A * (r * Real.sin (k * r)) + B * (r ^ 2 * Real.sin (k * r))
        + C * (r ^ 3 * Real.sin (k * r))))
      = A * ((Real.sin (k * x) - k * x * Real.cos (k * x)) / k ^ 2)
        + B * ((2 / k ^ 3 - x ^ 2 / k) * Real.cos (k * x)
            + (2 * x / k ^ 2) * Real.sin (k * x) - 2 / k ^ 3)
        + C * ((-x ^ 3 / k + 6 * x / k ^ 3) * Real.cos (k * x)
            + (3 * x ^ 2 / k ^ 2 - 6 / k ^ 4) * Real.sin (k * x)) := by
  have hi1 : IntervalIntegrable (fun r => r * Real.sin (k * r)) volume 0 x :=
    (continuous_id.mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun r => r ^ 2 * Real.sin (k * r)) volume 0 x :=
    ((continuous_id.pow 2).mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun r => r ^ 3 * Real.sin (k * r)) volume 0 x :=
    ((continuous_id.pow 3).mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add ((hi1.const_mul _).add (hi2.const_mul _)) (hi3.const_mul _),
      intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      psi1_formula hk, psi2_formula hk, psi3_formula hk]

/-- **Off-diagonal `radial_fourier(qFwd_im)` closed form (upper triangle `λ_im ≥ 0`, `σᵢ ≤ σₘ`).**
The window `[λ_im, R_im]` sits in `(0,∞)`, so the transform is the diagonal cubic-moment combination
`A·ψ1 + B·ψ2 + C·ψ3` evaluated as the DIFFERENCE between `R_im` and `λ_im` (the lower window edge no
longer at `0`).  Recovers `radial_fourier_qFwd_diag` at `λ = 0` (where every `ψ(0) = 0`). -/
theorem radial_fourier_qFwd_offdiag (X : Mix N M) (i m : Fin N)
    (hlam : 0 ≤ X.lam i m) {k : ℝ} (hk : k ≠ 0) :
    radial_fourier (qFwd X i m) k
      = (4 * Real.pi / k) * (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m)) *
        (((-(X.Q0 i m) * X.R i m + X.Qpp m * (X.R i m) ^ 2 / 2)
              * ((Real.sin (k * X.R i m) - k * X.R i m * Real.cos (k * X.R i m)) / k ^ 2)
            + (X.Q0 i m - X.Qpp m * X.R i m)
              * ((2 / k ^ 3 - (X.R i m) ^ 2 / k) * Real.cos (k * X.R i m)
                + (2 * X.R i m / k ^ 2) * Real.sin (k * X.R i m) - 2 / k ^ 3)
            + (X.Qpp m / 2)
              * ((-(X.R i m) ^ 3 / k + 6 * X.R i m / k ^ 3) * Real.cos (k * X.R i m)
                + (3 * (X.R i m) ^ 2 / k ^ 2 - 6 / k ^ 4) * Real.sin (k * X.R i m)))
          - ((-(X.Q0 i m) * X.R i m + X.Qpp m * (X.R i m) ^ 2 / 2)
              * ((Real.sin (k * X.lam i m) - k * X.lam i m * Real.cos (k * X.lam i m)) / k ^ 2)
            + (X.Q0 i m - X.Qpp m * X.R i m)
              * ((2 / k ^ 3 - (X.lam i m) ^ 2 / k) * Real.cos (k * X.lam i m)
                + (2 * X.lam i m / k ^ 2) * Real.sin (k * X.lam i m) - 2 / k ^ 3)
            + (X.Qpp m / 2)
              * ((-(X.lam i m) ^ 3 / k + 6 * X.lam i m / k ^ 3) * Real.cos (k * X.lam i m)
                + (3 * (X.lam i m) ^ 2 / k ^ 2 - 6 / k ^ 4) * Real.sin (k * X.lam i m)))) := by
  have hLR : X.lam i m ≤ X.R i m := by simp only [Mix.lam, Mix.R]; linarith [X.hσ i]
  have hqII : ∀ a b, IntervalIntegrable
      (fun r => r * qFwd X i m r * Real.sin (k * r)) volume a b := by
    intro a b
    have hq : IntervalIntegrable (qFwd X i m) volume a b :=
      (FMSA.MixtureBaxter.q0MixEntry_intervalIntegrable X i m a b).const_mul
        (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m))
    exact (hq.mul_continuousOn (g := fun r => r * Real.sin (k * r))
      ((continuous_id.mul (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))).continuousOn)).congr (fun r _ => by ring)
  have hcII : ∀ a b, IntervalIntegrable
      (fun r => (-(X.Q0 i m) * X.R i m + X.Qpp m * (X.R i m) ^ 2 / 2) * (r * Real.sin (k * r))
        + (X.Q0 i m - X.Qpp m * X.R i m) * (r ^ 2 * Real.sin (k * r))
        + (X.Qpp m / 2) * (r ^ 3 * Real.sin (k * r))) volume a b := fun a b => by
    apply Continuous.intervalIntegrable; fun_prop
  rw [radial_fourier_qFwd_eq_intervalIntegral, mul_assoc]
  congr 1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hqII 0 (X.lam i m)) (hqII (X.lam i m) (X.R i m))]
  have hz : (∫ r in (0 : ℝ)..(X.lam i m), r * qFwd X i m r * Real.sin (k * r)) = 0 := by
    rw [intervalIntegral.integral_congr_uIoo (g := fun _ => (0 : ℝ)) (fun r hr => ?_),
      intervalIntegral.integral_zero]
    rw [Set.uIoo_of_le hlam] at hr
    rw [qFwd_lower X i m hr.2]; ring
  rw [hz, zero_add]
  have hpoly : Set.EqOn (fun r => r * qFwd X i m r * Real.sin (k * r))
      (fun r => (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m)) *
          ((-(X.Q0 i m) * X.R i m + X.Qpp m * (X.R i m) ^ 2 / 2) * (r * Real.sin (k * r))
          + (X.Q0 i m - X.Qpp m * X.R i m) * (r ^ 2 * Real.sin (k * r))
          + (X.Qpp m / 2) * (r ^ 3 * Real.sin (k * r))))
      (Set.uIoo (X.lam i m) (X.R i m)) := by
    intro r hr
    rw [Set.uIoo_of_le hLR] at hr
    have hmem : r ∈ Set.Icc (X.lam i m) (X.R i m) := Set.mem_Icc.mpr ⟨hr.1.le, hr.2.le⟩
    have hq : qFwd X i m r = 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m)
        * (X.Q0 i m * (r - X.R i m) + X.Qpp m * (r - X.R i m) ^ 2 / 2) := by
      unfold qFwd q0MixEntry; rw [Set.indicator_of_mem hmem]
    dsimp only; rw [hq]; ring
  rw [intervalIntegral.integral_congr_uIoo hpoly, intervalIntegral.integral_const_mul]
  congr 1
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (hcII 0 (X.lam i m)) (hcII (X.lam i m) (X.R i m))
  rw [cubic_moment hk _ _ _ (X.R i m), cubic_moment hk _ _ _ (X.lam i m)] at hadj
  linarith [hadj]

end FMSA.MixtureHSDCF
