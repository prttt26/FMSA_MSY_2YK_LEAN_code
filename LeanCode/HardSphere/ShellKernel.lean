/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterRenewal
import LeanCode.Analysis.IntervalIntegralSwap

/-!
# The Baxter shell identity for a general kernel `c`

`radial3d_conv_eq_baxterK_shell` (`OZFIX.19`, `BaxterRenewal.lean`) is the bridge

    r·radial3d_conv(c_HS, g)(r) = ∫₀^σ baxterK(u)·(oddExt g(r−u) + oddExt g(r+u)) du,

converting the 3D radial convolution into a 1D convolution with the Baxter shell kernel. Its proof
uses `c_HS` only through **(a)** its support (`c_HS = 0` off `[0,σ]`, in the `Ioi 0 → [0,σ]`
reduction) and **(b)** the definition of `baxterK` as its shell integral `2π ∫_v^σ s·c_HS(s) ds`.
Everything else — `radial3d_conv_eq_oddExt`, `intervalIntegral_triangle_swap`, the inner
`∫₀^s H = ∫_{r−s}^{r+s} g̃` — is generic in the kernel.

This file abstracts both: for an **arbitrary** `c` supported in `[0,σ]`, with the general shell kernel
`shellKernel c σ v = 2π ∫_|v|^σ s·c(s) ds`, the same identity holds
(`radial3d_conv_eq_shellKernel`). This is what discharges the per-entry `hentry` of the mixture
shell bridge (`matRadialConv_eq_matShellConv`, `HSMixture/MixtureOzStar.lean`) for the mixture DCF
entries `C₀ᵢₖ` — each a different `c`-shape at its own `σ_ik`, not the single `c_HS`.

The proof is a transcription of `radial3d_conv_eq_baxterK_shell` with `c_HS → c`,
`baxterK → shellKernel c`, `c_HS_outer → hc_outer`.

Status: ✓ axiom-clean.
-/

set_option linter.style.longLine false

open MeasureTheory Set Real Filter Topology

namespace FMSA.HardSphere

noncomputable section

/-- **General Baxter shell kernel** for an arbitrary `c`: `shellKernel c σ v = 2π ∫_|v|^σ s·c(s) ds`.
Reduces to `baxterK` at `c = c_HS`. -/
def shellKernel (c : ℝ → ℝ) (sigma v : ℝ) : ℝ := 2 * Real.pi * ∫ s in |v|..sigma, s * c s

/-- **The Baxter shell identity, general kernel** (`OZFIX.19` off `c_HS`).  For any `c` supported in
`[0,σ]` (`hc_outer`), `r·radial3d_conv(c, g)(r) = ∫₀^σ shellKernel(c)(u)·(oddExt g(r−u) +
oddExt g(r+u)) du`.  Transcription of `radial3d_conv_eq_baxterK_shell` with `c_HS → c`,
`baxterK → shellKernel c`, `c_HS_outer → hc_outer`. -/
theorem radial3d_conv_eq_shellKernel {c : ℝ → ℝ} {sigma : ℝ} (hsigma : 0 < sigma)
    (hc_outer : ∀ s, sigma ≤ s → c s = 0) {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hshell : ∀ t ∈ Set.Ioi (0 : ℝ),
      IntervalIntegrable (oddExt g) MeasureTheory.volume (r - t) (r + t))
    (hjoint : MeasureTheory.Integrable
      (Function.uncurry fun u s => (Set.Ioi u).indicator (fun s => s * c s) s
        * (oddExt g (r - u) + oddExt g (r + u)))
      ((MeasureTheory.volume.restrict (Set.Ioc 0 sigma)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 sigma)))) :
    r * radial3d_conv c g r
      = ∫ u in (0 : ℝ)..sigma, shellKernel c sigma u * (oddExt g (r - u) + oddExt g (r + u)) := by
  set H : ℝ → ℝ := fun u => oddExt g (r - u) + oddExt g (r + u) with hH
  rw [radial3d_conv_eq_oddExt hr hshell]
  have hr0 : r ≠ 0 := ne_of_gt hr
  rw [show r * (2 * Real.pi / r *
      ∫ t in Set.Ioi (0 : ℝ), t * c t * ∫ s in (r - t)..(r + t), oddExt g s)
      = 2 * Real.pi *
      ∫ t in Set.Ioi (0 : ℝ), t * c t * ∫ s in (r - t)..(r + t), oddExt g s by field_simp]
  have hLred : (∫ t in Set.Ioi (0 : ℝ), t * c t * ∫ s in (r - t)..(r + t), oddExt g s)
      = ∫ t in (0 : ℝ)..sigma, t * c t * ∫ s in (r - t)..(r + t), oddExt g s := by
    rw [intervalIntegral.integral_of_le hsigma.le]
    have hEq : Set.EqOn
        (fun t => t * c t * ∫ s in (r - t)..(r + t), oddExt g s)
        ((Set.Ioc 0 sigma).indicator
          (fun t => t * c t * ∫ s in (r - t)..(r + t), oddExt g s))
        (Set.Ioi 0) := by
      intro t ht
      by_cases htσ : t ∈ Set.Ioc 0 sigma
      · rw [Set.indicator_of_mem htσ]
      · rw [Set.indicator_of_notMem htσ]
        have htge : sigma ≤ t := by
          rcases not_and_or.mp htσ with h | h
          · exact absurd ht h
          · exact (not_le.mp h).le
        show t * c t * (∫ s in (r - t)..(r + t), oddExt g s) = 0
        rw [hc_outer t htge, mul_zero, zero_mul]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEq,
      MeasureTheory.setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_self_of_subset_right Set.Ioc_subset_Ioi_self]
  rw [hLred]
  have hKrw : (∫ u in (0 : ℝ)..sigma, shellKernel c sigma u * H u)
      = 2 * Real.pi * ∫ u in (0 : ℝ)..sigma, (∫ s in u..sigma, s * c s) * H u := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro u hu
    rw [Set.uIcc_of_le hsigma.le] at hu
    show shellKernel c sigma u * H u = 2 * Real.pi * ((∫ s in u..sigma, s * c s) * H u)
    rw [shellKernel, abs_of_nonneg hu.1]; ring
  rw [hKrw, intervalIntegral_triangle_swap hsigma.le (fun s => s * c s) H hjoint]
  congr 1
  refine intervalIntegral.integral_congr ?_
  intro s hs
  rw [Set.uIcc_of_le hsigma.le] at hs
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · show s * c s * (∫ w in (r - s)..(r + s), oddExt g w) = s * c s * ∫ u in (0 : ℝ)..s, H u
    rw [← h0]; simp
  have hsIoi : s ∈ Set.Ioi (0 : ℝ) := h0
  have hIL : IntervalIntegrable (oddExt g) MeasureTheory.volume (r - s) r :=
    (hshell s hsIoi).mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.mem_uIcc]; left; exact ⟨le_refl _, by linarith [hs.1]⟩)
      (by rw [Set.mem_uIcc]; left; exact ⟨by linarith [hs.1], by linarith [hs.1]⟩))
  have hIR : IntervalIntegrable (oddExt g) MeasureTheory.volume r (r + s) :=
    (hshell s hsIoi).mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.mem_uIcc]; left; exact ⟨by linarith [hs.1], by linarith [hs.1]⟩)
      (by rw [Set.mem_uIcc]; left; exact ⟨by linarith [hs.1], le_refl _⟩))
  have hinner : (∫ u in (0 : ℝ)..s, H u) = ∫ w in (r - s)..(r + s), oddExt g w := by
    have h1 : (∫ u in (0 : ℝ)..s, oddExt g (r - u)) = ∫ w in (r - s)..r, oddExt g w := by
      have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := s) (f := oddExt g) r
      simpa using this
    have h2 : (∫ u in (0 : ℝ)..s, oddExt g (r + u)) = ∫ w in r..(r + s), oddExt g w := by
      have := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := s) (f := oddExt g) r
      simpa using this
    have hcs : IntervalIntegrable (fun u => oddExt g (r - u)) MeasureTheory.volume 0 s := by
      have := (hIL.symm).comp_sub_left (f := oddExt g) r
      simpa using this
    have hca : IntervalIntegrable (fun u => oddExt g (r + u)) MeasureTheory.volume 0 s := by
      have := hIR.comp_add_left (f := oddExt g) r
      simpa using this
    rw [hH, intervalIntegral.integral_add hcs hca, h1, h2,
      intervalIntegral.integral_add_adjacent_intervals hIL hIR]
  show s * c s * (∫ w in (r - s)..(r + s), oddExt g w) = s * c s * ∫ u in (0 : ℝ)..s, H u
  rw [hinner]

/-- At `c = c_HS` the general shell kernel is `baxterK` (definitional up to the shell integral). -/
theorem shellKernel_c_HS (eta sigma v : ℝ) :
    shellKernel (c_HS eta sigma) sigma v = baxterK eta sigma v := by
  rw [shellKernel, baxterK]

end

end FMSA.HardSphere
