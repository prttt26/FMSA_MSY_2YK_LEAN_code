/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.YukawaOZMix.MixtureRDFUnequalDiam

/-!
# MRS.8 companion — the reconstruction core is the SHELL-INTEGRAL of the DCF (not the DCF)

The Baxter reconstruction core `matDCFreCoreN` (`= Re matDCFfullN`, whose Laplace transform is
`Cmix0 = I − Q̂₀Q̂₀ᵀ`) is **not** the physical Lebowitz DCF `cMixDCFN`.  The two are related by a
derivative, not an equality: `cMixDCFN = −matDCFreCoreN'/(2π·rg·v)` (the MRS.8 ODE), so the core is
the *shell-integral* of the DCF.  (The earlier "`matDCFfullN = cMixDCFN`" reading was a
mis-statement — `matDCFfullN = (matDCFreCoreN : ℂ)` by `matDCFfullN_eq_ofReal`.)

This file states the corrected identity.  For `σᵢ < σₖ` and `w ∈ (0, Rᵢₖ)`:

    matDCFreCoreN(w) = 2π·rgᵢₖ · ∫_w^{Rᵢₖ} s·cMixDCFN(s) ds,   matDCFfullN(w) = ↑(that).

It is a direct corollary of MML.8's `hShellDCF_uneq` (`shellKernel(Φ) = matDCFreCoreCont/ρ`, with
`shellKernel c σ v = 2π∫_{|v|}^σ s·c`) at `ρ = 1`, `σₛ = Rᵢₖ`, plus the a.e. rewrite
`Φ = rg·cMixDCFN` on the core.  Off-critical-path completeness for MRS.8 (MML.8's uniqueness route
never needed it); std-3.
-/

open MeasureTheory Set

namespace FMSA.MixtureBaxter

open FMSA.MatrixQ0 FMSA.MixtureHSDCF FMSA.HardSphere MeasureTheory intervalIntegral

variable {N : ℕ}

/-- **The reconstruction core is the shell-integral of the DCF** (continuous representative).  For
`σᵢ < σₖ` and `w ∈ (0, Rᵢₖ)`, `matDCFreCoreCont(w) = 2π·rgᵢₖ · ∫_w^{Rᵢₖ} s·cMixDCFN(s) ds`.
Corollary of `hShellDCF_uneq` at `ρ = 1`, `σₛ = Rᵢₖ`. -/
theorem matDCFreCoreCont_eq_shellIntegral (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hrho : ∀ n, 0 ≤ rho n) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) (hlt : sigma i < sigma k)
    {w : ℝ} (hw0 : 0 < w) (hwR : w < (sigma i + sigma k) / 2) :
    matDCFreCoreCont rho sigma hsig i k w
      = 2 * Real.pi * rhoGeoPhys rho i k
          * ∫ s in w..((sigma i + sigma k) / 2), s * cMixDCFN rho sigma i k s := by
  have hkey := hShellDCF_uneq rho sigma hsig hrho hvac i k hlt 1 (le_refl _) hw0 hwR
  rw [div_one] at hkey
  rw [← hkey, shellKernel, abs_of_pos hw0]
  have hcong : (∫ s in w..((sigma i + sigma k) / 2), s * PhiUneq rho sigma 1 i k s)
      = ∫ s in w..((sigma i + sigma k) / 2),
          rhoGeoPhys rho i k * (s * cMixDCFN rho sigma i k s) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton ((sigma i + sigma k) / 2))]
      with x hxb hmem
    rw [Set.uIoc_of_le hwR.le] at hmem
    have hxR : x < (sigma i + sigma k) / 2 :=
      lt_of_le_of_ne hmem.2 (Set.mem_compl_singleton_iff.mp hxb)
    rw [PhiUneq, if_pos hxR]
    ring
  rw [hcong, intervalIntegral.integral_const_mul]
  ring

/-- **Off the knot: the DCF core is the shell-integral of the DCF.**  `matDCFreCoreN(w) =
2π·rgᵢₖ · ∫_w^{Rᵢₖ} s·cMixDCFN(s) ds`, from the continuous-representative version + off-knot
equality. -/
theorem matDCFreCoreN_eq_shellIntegral (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hrho : ∀ n, 0 ≤ rho n) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) (hlt : sigma i < sigma k)
    {w : ℝ} (hw0 : 0 < w) (hwR : w < (sigma i + sigma k) / 2)
    (hwne : w ≠ (sigma k - sigma i) / 2) :
    matDCFreCoreN rho sigma hsig i k w
      = 2 * Real.pi * rhoGeoPhys rho i k
          * ∫ s in w..((sigma i + sigma k) / 2), s * cMixDCFN rho sigma i k s := by
  rw [← matDCFreCoreCont_eq_of_ne rho sigma hsig i k hwne]
  exact matDCFreCoreCont_eq_shellIntegral rho sigma hsig hrho hvac i k hlt hw0 hwR

/-- **The corrected `matDCFfullN ↔ cMixDCFN` bridge.**  `matDCFfullN` is NOT the DCF; it is the
`ℂ`-cast of the reconstruction core, i.e. the shell-integral of the DCF:
`matDCFfullN(w) = ↑(2π·rgᵢₖ · ∫_w^{Rᵢₖ} s·cMixDCFN)`.  This is the true statement replacing the
mis-stated `matDCFfullN = cMixDCFN`. -/
theorem matDCFfullN_eq_shellIntegral (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hrho : ∀ n, 0 ≤ rho n) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) (hlt : sigma i < sigma k)
    {w : ℝ} (hw0 : 0 < w) (hwR : w < (sigma i + sigma k) / 2)
    (hwne : w ≠ (sigma k - sigma i) / 2) :
    matDCFfullN rho sigma hsig i k w
      = ((2 * Real.pi * rhoGeoPhys rho i k
          * ∫ s in w..((sigma i + sigma k) / 2), s * cMixDCFN rho sigma i k s : ℝ) : ℂ) := by
  rw [matDCFfullN_eq_ofReal,
    matDCFreCoreN_eq_shellIntegral rho sigma hsig hrho hvac i k hlt hw0 hwR hwne]

end FMSA.MixtureBaxter
