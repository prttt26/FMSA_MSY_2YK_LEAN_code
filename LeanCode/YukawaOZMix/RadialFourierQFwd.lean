/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HardSphere.RadialFourierCHS
import LeanCode.YukawaOZMix.MixtureHSDCF

/-!
# Radial Fourier transform of the forward Baxter factor `qFwd` (MRS.8 sub-fact 1, first atom)

This file computes the 3D radial Fourier transform of the DIAGONAL forward Baxter factor `qFwd_ii`,
supported on the core `[0, R_ii]` (`λ_ii = 0`) — a genuine, reusable closed form.

**⚠ CORRECTION (2026-08-09).**  These `radial_fourier(qFwd)`/`radial_fourier(pMixEntry)` do NOT
assemble into `Cmix0` via `radial_fourier_conv`, contrary to an earlier plan.  Two reasons: (1)
`qpConv = qFwd ⋆ pMixEntry` is Mathlib's **1D** convolution, but `radial_fourier_conv` is for the
**3D radial** convolution `radial3d_conv` (a `(2π/r)∫∫` triangle integral); (2) the DCF relates to
`cHSmixRaw` by the ODD-part/`r`-factor `cHSodd = cHSmixRaw(r) − cHSmixRaw(−r) = 2π√(ρᵢρⱼ)·r·c^HS`,
so `radial_fourier(cHSmixRaw) ≠ Cmix0`.  The correct MRS.8 bridge is the
cosine-transform/shell-kernel route `matRadialSymbol_eq_shellKernel_cos`
(`radial_fourier(Φ) = 2∫shellKernel(Φ)·cos`); its gap is shell-kernel ⟷ Baxter WH factorization.
The transforms here remain correct 3D-radial-FT facts about the Baxter factors, just off that path.

* `psi3_formula` — the missing sine moment `∫₀^σ r³·sin(kr) dr` (the `psi`-family had `1,2,4`; the
  `r·(quadratic)` integrand of `radial_fourier(qFwd)` needs `r³`).
* `qFwd_diag_outer` — the diagonal forward factor vanishes at/beyond contact `R_ii`.
* `radial_fourier_qFwd_diag_eq_intervalIntegral` — reduces the `Set.Ioi 0` transform to the interval
  integral over `[0, R_ii]` (mirror of `radial_fourier_c_HS_eq_intervalIntegral`).
* `radial_fourier_qFwd_diag` — the CLOSED FORM: `qFwd_ii = 2π√(ρᵢρᵢ)·(quadratic)`, so `r·qFwd_ii` a
  cubic and the transform is `(4π/k)·2π√(ρᵢρᵢ)·(A·ψ1 + B·ψ2 + C·ψ3)` at `σᵢ = R_ii`.

Companion transforms: the off-diagonal `qFwd_im` (`RadialFourierQFwdOffdiag.lean`) and the reflected
`pMixEntry` (`RadialFourierPMix.lean`).
-/

open MeasureTheory Set
namespace FMSA.MixtureHSDCF

private lemma hasDerivAt_sin_mul_q {k r : ℝ} :
    HasDerivAt (fun x => Real.sin (k * x)) (Real.cos (k * r) * k) r := by
  have h : HasDerivAt (fun x => k * x) k r := by simpa using (hasDerivAt_id r).const_mul k
  exact h.sin

private lemma hasDerivAt_cos_mul_q {k r : ℝ} :
    HasDerivAt (fun x => Real.cos (k * x)) (-Real.sin (k * r) * k) r := by
  have h : HasDerivAt (fun x => k * x) k r := by simpa using (hasDerivAt_id r).const_mul k
  exact h.cos

private lemma psi3_hasDerivAt {k : ℝ} (hk : k ≠ 0) (r : ℝ) :
    HasDerivAt (fun r => (-r ^ 3 / k + 6 * r / k ^ 3) * Real.cos (k * r)
        + (3 * r ^ 2 / k ^ 2 - 6 / k ^ 4) * Real.sin (k * r))
      (r ^ 3 * Real.sin (k * r)) r := by
  have hx3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * r ^ 2) r := by
    have h := hasDerivAt_pow (𝕜 := ℝ) 3 r; simpa using h
  have hx2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    have h := hasDerivAt_pow (𝕜 := ℝ) 2 r; simpa [Nat.cast_ofNat, pow_one] using h
  have hA : HasDerivAt (fun x => -x ^ 3 / k + 6 * x / k ^ 3) (-3 * r ^ 2 / k + 6 / k ^ 3) r := by
    have h := ((hx3.neg.div_const k).add (((hasDerivAt_id r).const_mul 6).div_const (k ^ 3)))
    exact h.congr_deriv (by ring)
  have hB : HasDerivAt (fun x => 3 * x ^ 2 / k ^ 2 - 6 / k ^ 4) (6 * r / k ^ 2) r := by
    have h := ((hx2.const_mul 3).div_const (k ^ 2)).sub (hasDerivAt_const r (6 / k ^ 4))
    exact h.congr_deriv (by ring)
  have hT1 : HasDerivAt (fun x => (-x ^ 3 / k + 6 * x / k ^ 3) * Real.cos (k * x))
      ((-3 * r ^ 2 / k + 6 / k ^ 3) * Real.cos (k * r)
        + (-r ^ 3 / k + 6 * r / k ^ 3) * (-Real.sin (k * r) * k)) r :=
    hA.mul hasDerivAt_cos_mul_q
  have hT2 : HasDerivAt (fun x => (3 * x ^ 2 / k ^ 2 - 6 / k ^ 4) * Real.sin (k * x))
      ((6 * r / k ^ 2) * Real.sin (k * r)
        + (3 * r ^ 2 / k ^ 2 - 6 / k ^ 4) * (Real.cos (k * r) * k)) r :=
    hB.mul hasDerivAt_sin_mul_q
  exact (hT1.add hT2).congr_deriv (by field_simp; ring)

/-- **ψ3 formula:** `∫0^sigma r³·sin(k·r) dr = (-σ³/k + 6σ/k³)cos(kσ) + (3σ²/k² − 6/k⁴)sin(kσ)`.
Completes the `psi`-family (`psi1`/`psi2`/`psi4` are in `RadialFourierCHS.lean`). -/
theorem psi3_formula {k : ℝ} (hk : k ≠ 0) (sigma : ℝ) :
    ∫ r in (0 : ℝ)..sigma, r ^ 3 * Real.sin (k * r) =
    (-sigma ^ 3 / k + 6 * sigma / k ^ 3) * Real.cos (k * sigma)
      + (3 * sigma ^ 2 / k ^ 2 - 6 / k ^ 4) * Real.sin (k * sigma) := by
  have hint : IntervalIntegrable (fun r => r ^ 3 * Real.sin (k * r)) volume 0 sigma :=
    ((continuous_id.pow 3).mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).intervalIntegrable 0 sigma
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => psi3_hasDerivAt hk r) hint]
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, zero_div, mul_one, zero_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, add_zero]
  ring

end FMSA.MixtureHSDCF

namespace FMSA.MixtureHSDCF
open FMSA.HardSphere FMSA.InnerDecomp FMSA.WHSupports
variable {N M : ℕ}

/-- The diagonal forward factor vanishes at and beyond contact `R_ii`. -/
theorem qFwd_diag_outer (X : Mix N M) (i : Fin N) {r : ℝ} (hr : X.R i i ≤ r) :
    qFwd X i i r = 0 := by
  unfold qFwd q0MixEntry
  by_cases hmem : r ∈ Set.Icc (X.lam i i) (X.R i i)
  · rw [Set.indicator_of_mem hmem]
    have hrR : r = X.R i i := le_antisymm hmem.2 hr
    rw [hrR]; ring
  · rw [Set.indicator_of_notMem hmem]; ring

/-- `radial_fourier(qFwd_ii)` reduces to the interval integral over the core `[0, R_ii]` (forward
factor vanishes beyond `R_ii`; mirror of `radial_fourier_c_HS_eq_intervalIntegral`). -/
theorem radial_fourier_qFwd_diag_eq_intervalIntegral (X : Mix N M) (i : Fin N) (k : ℝ) :
    radial_fourier (qFwd X i i) k
      = (4 * Real.pi / k) * ∫ r in (0 : ℝ)..(X.R i i), r * qFwd X i i r * Real.sin (k * r) := by
  unfold radial_fourier
  congr 1
  have hpt : Set.EqOn (fun r => r * qFwd X i i r * Real.sin (k * r))
      ((Set.Ioc 0 (X.R i i)).indicator (fun r => r * qFwd X i i r * Real.sin (k * r)))
      (Set.Ioi (0 : ℝ)) := by
    intro r hr0
    by_cases hr : r ∈ Set.Ioc (0 : ℝ) (X.R i i)
    · rw [Set.indicator_of_mem hr]
    · rw [Set.indicator_of_notMem hr]
      have hrge : X.R i i ≤ r := by
        simp only [Set.mem_Ioc, not_and, not_le] at hr
        exact (hr hr0).le
      simp [qFwd_diag_outer X i hrge]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt,
    MeasureTheory.setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_self_of_subset_right Set.Ioc_subset_Ioi_self,
    ← intervalIntegral.integral_of_le (X.R_pos i i).le]

/-- **`radial_fourier(qFwd_ii)` closed form** — the diagonal forward Baxter factor's radial Fourier
transform.  `qFwd_ii = 2π√(ρᵢρᵢ)·(quadratic in r)`, so `r·qFwd_ii` is a cubic and the transform is
`(4π/k)·2π√(ρᵢρᵢ)·(A·ψ1 + B·ψ2 + C·ψ3)` — the `r·(quadratic)` coefficients `A,B,C` against the sine
moments `ψ1,ψ2,ψ3` at `σᵢ = R_ii`. -/
theorem radial_fourier_qFwd_diag (X : Mix N M) (i : Fin N) {k : ℝ} (hk : k ≠ 0) :
    radial_fourier (qFwd X i i) k
      = (4 * Real.pi / k) * (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ i)) *
        ((-(X.Q0 i i) * X.R i i + X.Qpp i * (X.R i i) ^ 2 / 2)
            * ((Real.sin (k * X.R i i) - k * X.R i i * Real.cos (k * X.R i i)) / k ^ 2)
          + (X.Q0 i i - X.Qpp i * X.R i i)
            * ((2 / k ^ 3 - (X.R i i) ^ 2 / k) * Real.cos (k * X.R i i)
              + (2 * X.R i i / k ^ 2) * Real.sin (k * X.R i i) - 2 / k ^ 3)
          + (X.Qpp i / 2)
            * ((-(X.R i i) ^ 3 / k + 6 * X.R i i / k ^ 3) * Real.cos (k * X.R i i)
              + (3 * (X.R i i) ^ 2 / k ^ 2 - 6 / k ^ 4) * Real.sin (k * X.R i i))) := by
  have hlam : X.lam i i = 0 := by simp [Mix.lam]
  have hexpand : Set.EqOn (fun r => r * qFwd X i i r * Real.sin (k * r))
      (fun r => (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ i)) *
          ((-(X.Q0 i i) * X.R i i + X.Qpp i * (X.R i i) ^ 2 / 2) * (r * Real.sin (k * r))
          + (X.Q0 i i - X.Qpp i * X.R i i) * (r ^ 2 * Real.sin (k * r))
          + (X.Qpp i / 2) * (r ^ 3 * Real.sin (k * r))))
      (Set.uIoo (0 : ℝ) (X.R i i)) := by
    intro r hr
    rw [Set.uIoo_of_le (X.R_pos i i).le] at hr
    have hmem : r ∈ Set.Icc (X.lam i i) (X.R i i) := by
      rw [hlam, Set.mem_Icc]; exact ⟨hr.1.le, hr.2.le⟩
    have hq : qFwd X i i r = 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ i)
        * (X.Q0 i i * (r - X.R i i) + X.Qpp i * (r - X.R i i) ^ 2 / 2) := by
      unfold qFwd q0MixEntry; rw [Set.indicator_of_mem hmem]
    dsimp only
    rw [hq]; ring
  have hi1 : IntervalIntegrable (fun r => r * Real.sin (k * r)) volume 0 (X.R i i) :=
    (continuous_id.mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun r => r ^ 2 * Real.sin (k * r)) volume 0 (X.R i i) :=
    ((continuous_id.pow 2).mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun r => r ^ 3 * Real.sin (k * r)) volume 0 (X.R i i) :=
    ((continuous_id.pow 3).mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _
  rw [radial_fourier_qFwd_diag_eq_intervalIntegral,
      intervalIntegral.integral_congr_uIoo hexpand,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add
        ((hi1.const_mul _).add (hi2.const_mul _)) (hi3.const_mul _),
      intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      psi1_formula hk, psi2_formula hk, psi3_formula hk]
  ring

end FMSA.MixtureHSDCF
