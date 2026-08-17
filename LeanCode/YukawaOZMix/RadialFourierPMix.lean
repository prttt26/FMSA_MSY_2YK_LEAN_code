/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.YukawaOZMix.RadialFourierQFwdOffdiag

/-!
# Radial Fourier transform of the REFLECTED Baxter factor `pMixEntry` (MRS.8 sub-fact 1)

`pMixEntry_im(u) = 2π√(ρᵢρₘ)·q0MixEntry_im(−u)` is the reflection of `qFwd_im`, supported on the
reflected core `[−R_im, −λ_im]`.  Its radial transform (integrating over `r > 0`) therefore depends
on the sign of `λ_im`:

* `pMixEntry_upper` — the reflected factor vanishes strictly above `−λ_im` on the positive axis.
* `radial_fourier_pMixEntry_upper` — upper triangle `λ_im ≥ 0` (`σᵢ ≤ σₘ`): the support
  `[−R_im, −λ_im] ⊆ (−∞, 0]`, so the transform is `0`.
* `radial_fourier_pMixEntry_lower` — lower triangle `λ_im < 0` (`σₘ < σᵢ`): support meets `(0,∞)`
  on `(0, −λ_im]`, where `pMixEntry(r) = 2π√(ρᵢρₘ)·q0MixEntry(−r)`; `r·q0MixEntry(−r)` is the cubic
  `A·r − B·r² + C·r³` (the reflected coefficients — only the `r²` sign flips), so the transform is
  `(4π/k)·2π√(ρᵢρₘ)·(A·ψ1 − B·ψ2 + C·ψ3)` at `−λ_im > 0`, via `cubic_moment`.

Note the complementarity with `qFwd`: for each pair exactly one of `qFwd`/`pMixEntry` is nonzero on
`(0,∞)` — `qFwd` for `λ ≥ 0`, `pMixEntry` for `λ < 0`.  ⚠ These do NOT assemble into `Cmix0` via
`radial_fourier_conv` (`qpConv` is 1D, not `radial3d_conv`; and `radial_fourier(cHSmixRaw) ≠ Cmix0`
since `cHSodd = 2π√ρ·r·c^HS`) — see the CORRECTION in `RadialFourierQFwd.lean`.
-/

open MeasureTheory Set
namespace FMSA.MixtureHSDCF
open FMSA.HardSphere FMSA.InnerDecomp FMSA.WHSupports FMSA.MixtureConvolution
variable {N M : ℕ}

/-- The reflected factor vanishes strictly above its upper edge `−λ_im` (on the positive axis). -/
theorem pMixEntry_upper (X : Mix N M) (i m : Fin N) {r : ℝ} (hr : -(X.lam i m) < r) :
    pMixEntry X i m r = 0 := by
  unfold pMixEntry q0MixEntry
  rw [Set.indicator_of_notMem (fun hmem => absurd hmem.1 (by
    simp only [not_le]; linarith))]
  ring

/-- **Upper triangle `λ_im ≥ 0` (`σᵢ ≤ σₘ`): the reflected factor's radial transform is `0`.**  Its
support `[−R_im, −λ_im]` lies in `(−∞, 0]`, so `pMixEntry_im = 0` on `(0,∞)`. -/
theorem radial_fourier_pMixEntry_upper (X : Mix N M) (i m : Fin N)
    (hlam : 0 ≤ X.lam i m) (k : ℝ) :
    radial_fourier (pMixEntry X i m) k = 0 := by
  unfold radial_fourier
  have hz : (∫ r in Set.Ioi (0 : ℝ), r * pMixEntry X i m r * Real.sin (k * r)) = 0 := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (g := fun _ => (0 : ℝ)) (fun r hr => ?_)]
    · simp
    · rw [Set.mem_Ioi] at hr
      rw [pMixEntry_upper X i m (by linarith)]; ring
  rw [hz, mul_zero]

/-- **Lower triangle `λ_im < 0` (`σₘ < σᵢ`): the reflected factor's radial transform.**  Its support
meets `(0,∞)` on `(0, −λ_im]`, where `pMixEntry(r) = 2π√(ρᵢρₘ)·q0MixEntry(−r)`; `r·q0MixEntry(−r)`
is the cubic `A·r − B·r² + C·r³`, giving `(4π/k)·2π√(ρᵢρₘ)·(A·ψ1 − B·ψ2 + C·ψ3)` at `−λ_im > 0`. -/
theorem radial_fourier_pMixEntry_lower (X : Mix N M) (i m : Fin N)
    (hlam : X.lam i m < 0) {k : ℝ} (hk : k ≠ 0) :
    radial_fourier (pMixEntry X i m) k
      = (4 * Real.pi / k) * (2 * Real.pi * Real.sqrt (X.rho i * X.rho m)) *
        ((-(X.Q0 i m) * X.R i m + X.Qpp m * (X.R i m) ^ 2 / 2)
            * ((Real.sin (k * (-(X.lam i m))) - k * (-(X.lam i m)) * Real.cos (k * (-(X.lam i m))))
                / k ^ 2)
          + (-(X.Q0 i m - X.Qpp m * X.R i m))
            * ((2 / k ^ 3 - (-(X.lam i m)) ^ 2 / k) * Real.cos (k * (-(X.lam i m)))
              + (2 * (-(X.lam i m)) / k ^ 2) * Real.sin (k * (-(X.lam i m))) - 2 / k ^ 3)
          + (X.Qpp m / 2)
            * ((-(-(X.lam i m)) ^ 3 / k + 6 * (-(X.lam i m)) / k ^ 3)
                  * Real.cos (k * (-(X.lam i m)))
              + (3 * (-(X.lam i m)) ^ 2 / k ^ 2 - 6 / k ^ 4)
                  * Real.sin (k * (-(X.lam i m))))) := by
  have hlpos : (0 : ℝ) < -(X.lam i m) := by linarith
  unfold radial_fourier
  have hpt : Set.EqOn (fun r => r * pMixEntry X i m r * Real.sin (k * r))
      ((Set.Ioc 0 (-(X.lam i m))).indicator (fun r => r * pMixEntry X i m r * Real.sin (k * r)))
      (Set.Ioi (0 : ℝ)) := by
    intro r hr0
    by_cases hr : r ∈ Set.Ioc (0 : ℝ) (-(X.lam i m))
    · rw [Set.indicator_of_mem hr]
    · rw [Set.indicator_of_notMem hr]
      have hrge : -(X.lam i m) < r := by
        simp only [Set.mem_Ioc, not_and, not_le] at hr
        exact hr hr0
      simp [pMixEntry_upper X i m hrge]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt,
    MeasureTheory.setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_self_of_subset_right Set.Ioc_subset_Ioi_self,
    ← intervalIntegral.integral_of_le hlpos.le, mul_assoc]
  congr 1
  have hexpand : Set.EqOn (fun r => r * pMixEntry X i m r * Real.sin (k * r))
      (fun r => (2 * Real.pi * Real.sqrt (X.rho i * X.rho m)) *
          ((-(X.Q0 i m) * X.R i m + X.Qpp m * (X.R i m) ^ 2 / 2) * (r * Real.sin (k * r))
          + (-(X.Q0 i m - X.Qpp m * X.R i m)) * (r ^ 2 * Real.sin (k * r))
          + (X.Qpp m / 2) * (r ^ 3 * Real.sin (k * r))))
      (Set.uIoo (0 : ℝ) (-(X.lam i m))) := by
    intro r hr
    rw [Set.uIoo_of_le hlpos.le] at hr
    have hmem : -r ∈ Set.Icc (X.lam i m) (X.R i m) := by
      rw [Set.mem_Icc]; exact ⟨by linarith [hr.2], by linarith [hr.1, X.R_pos i m]⟩
    have hq : pMixEntry X i m r = 2 * Real.pi * Real.sqrt (X.rho i * X.rho m)
        * (X.Q0 i m * (-r - X.R i m) + X.Qpp m * (-r - X.R i m) ^ 2 / 2) := by
      unfold pMixEntry q0MixEntry; rw [Set.indicator_of_mem hmem]
    dsimp only; rw [hq]; ring
  rw [intervalIntegral.integral_congr_uIoo hexpand, intervalIntegral.integral_const_mul]
  congr 1
  exact cubic_moment hk _ _ _ (-(X.lam i m))

end FMSA.MixtureHSDCF
