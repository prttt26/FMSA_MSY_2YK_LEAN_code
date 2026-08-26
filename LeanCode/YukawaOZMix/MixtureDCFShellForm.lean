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

open FMSA.MatrixQ0 FMSA.MixtureHSDCF FMSA.HardSphere FMSA.MixtureBaxterCore FMSA.MixtureOzStar
open MeasureTheory intervalIntegral

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

/-! ### The k-space transform companion: `Cmix0 = ρ·radial_fourier(DCF)` (quadratic-form level) -/

/-- ⭐ **MRS.8 transform companion.**  The Baxter zeroth-order DCF matrix `Cmix0 = I − Q̂₀Q̂₀ᵀ`
equals `ρ` times the radial Fourier transform of the (symmetrised, ρ-weighted, truncated) physical
DCF `PhiSymN`, at the quadratic-form level:
`∑ᵢⱼ Cmix0(ik)ᵢⱼ vᵢvⱼ = ↑(ρ·∑ᵢⱼ radial_fourier(PhiSymN)ᵢⱼ(k) vᵢvⱼ)`.  Both sides reduce to
`2·∑ᵢⱼ Tᵢⱼ vᵢvⱼ` with `Tᵢⱼ = ∫₀^∞ matDCFreCoreN·cos`: the RHS via `radial_fourier_PhiSymN`
(`𝓕(PhiSymN) = (2/ρ)·T`), the LHS via `Cmix0_quadForm_cosN` + `matDCFfullN_eq_ofReal`.  This is the
k-space form of `matDCFfullN_eq_shellIntegral` — the "Baxter reconstruction = radial-FT of the ODE
Lebowitz DCF" identity, completing MRS.8's transform statement. -/
theorem Cmix0_quadForm_eq_rho_radial_fourier (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hrho : ∀ n, 0 ≤ rho n) (hvac : vacMix rho sigma ≠ 0) {rho_s : ℝ} (hrho_s : rho_s ≠ 0)
    {k : ℝ} (hk : k ≠ 0) (v : Fin N → ℝ) :
    (∑ i, ∑ j, Cmix0 (QphysN rho sigma) (Complex.I * (k : ℂ)) i j * (v i : ℂ) * (v j : ℂ))
      = ((rho_s * ∑ i, ∑ j,
          radial_fourier (PhiSymN rho sigma rho_s i j) k * v i * v j : ℝ) : ℂ) := by
  set T : Fin N → Fin N → ℝ :=
    fun i j => ∫ w in Set.Ioi (0:ℝ), matDCFreCoreN rho sigma hsig i j w * Real.cos (k * w) with hT
  have hRHS : (rho_s * ∑ i, ∑ j, radial_fourier (PhiSymN rho sigma rho_s i j) k * v i * v j)
      = 2 * ∑ i, ∑ j, T i j * v i * v j := by
    have hper : ∀ i j, rho_s * radial_fourier (PhiSymN rho sigma rho_s i j) k = 2 * T i j := by
      intro i j
      simp only [hT]
      rw [radial_fourier_PhiSymN rho sigma hsig hrho hvac i j hrho_s hk]
      field_simp
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    linear_combination (v i * v j) * hper i j
  rw [Cmix0_quadForm_cosN rho sigma hsig k hk v]
  have hcast : (∫ w in Set.Ioi (0:ℝ),
        (∑ i, ∑ j, matDCFfullN rho sigma hsig i j w * (v i : ℂ) * (v j : ℂ))
          * (2 * Complex.cos ((k : ℂ) * w)))
      = ((∫ w in Set.Ioi (0:ℝ),
        (∑ i, ∑ j, matDCFreCoreN rho sigma hsig i j w * v i * v j) * (2 * Real.cos (k * w))
          : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi (fun w _ => ?_)
    simp only [matDCFfullN_eq_ofReal]
    push_cast [Complex.ofReal_cos]
    ring
  have hreal : (∫ w in Set.Ioi (0:ℝ),
        (∑ i, ∑ j, matDCFreCoreN rho sigma hsig i j w * v i * v j) * (2 * Real.cos (k * w)))
      = 2 * ∑ i, ∑ j, T i j * v i * v j := by
    have hstep : (∫ w in Set.Ioi (0:ℝ),
          (∑ i, ∑ j, matDCFreCoreN rho sigma hsig i j w * v i * v j) * (2 * Real.cos (k * w)))
        = ∫ w in Set.Ioi (0:ℝ),
          ∑ i, ∑ j, (matDCFreCoreN rho sigma hsig i j w * Real.cos (k * w)) * (2 * v i * v j) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun w _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hstep]
    have hout : (∫ w in Set.Ioi (0:ℝ),
          ∑ i, ∑ j, (matDCFreCoreN rho sigma hsig i j w * Real.cos (k * w)) * (2 * v i * v j))
        = ∑ i, ∫ w in Set.Ioi (0:ℝ),
          ∑ j, (matDCFreCoreN rho sigma hsig i j w * Real.cos (k * w)) * (2 * v i * v j) :=
      integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
        ((matDCFreCoreN_cos_integrable rho sigma hsig i j k).mul_const
          (2 * v i * v j)).integrableOn))
    rw [hout]
    simp only [hT]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hin : (∫ w in Set.Ioi (0:ℝ),
          ∑ j, (matDCFreCoreN rho sigma hsig i j w * Real.cos (k * w)) * (2 * v i * v j))
        = ∑ j, ∫ w in Set.Ioi (0:ℝ),
          (matDCFreCoreN rho sigma hsig i j w * Real.cos (k * w)) * (2 * v i * v j) :=
      integral_finset_sum _ (fun j _ =>
        ((matDCFreCoreN_cos_integrable rho sigma hsig i j k).mul_const
          (2 * v i * v j)).integrableOn)
    rw [hin, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [MeasureTheory.integral_mul_const]
    ring
  rw [hcast, hreal, hRHS]

end FMSA.MixtureBaxter
