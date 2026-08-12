/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.Analysis.FourierAEInjective
import LeanCode.Analysis.RadialFourierInversion
import LeanCode.HardSphere.RadialFourier

/-!
# Radial Fourier transform is a.e.-injective (the `radial_fourier ↔ 𝓕` bridge)

The MML.15 mixture-DCF symmetry transfer needs: equal radial (3-D sine) transforms of two DCFs force
the DCFs equal a.e. on the physical half-line `r > 0`.  This bridges the project's `radial_fourier`
(`HardSphere/RadialFourier.lean`) to Mathlib's 1-D `𝓕` and then to the a.e.-injectivity
`Analysis/FourierAEInjective.ae_eq_of_fourier_eq`.

The reduction: `radial_fourier f k = (4π/k)·∫₀^∞ r·f(r)·sin(kr) dr` is the sine transform of
`r ↦ r·f(r)`, and Mathlib's `𝓕` of the **odd extension** `ψ_f : v ↦ v·f|v|` is `−2i` times that
sine integral (`RadialFourierInversion.fourier_of_odd`).  So `radial_fourier f = radial_fourier g`
⇒ `𝓕 ψ_f = 𝓕 ψ_g` ⇒ (by `ae_eq_of_fourier_eq`, whose `𝓕 d = 0` route needs no `Integrable (𝓕 ·)`,
the point that makes it apply to non-`L¹`-transform DCFs) ⇒ `ψ_f = ψ_g` a.e. ⇒ dividing the `v`
factor, `f = g` a.e. on `(0,∞)`.

* **`ae_eq_oddExt_of_radial_fourier_eq`** — the odd extensions agree a.e. on `ℝ`;
* **`ae_eq_of_radial_fourier_eq`** — `f = g` a.e. on `Ioi 0` (the form the DCF symmetry consumes).

Hypotheses on `f`/`g`: the odd extension `v ↦ v·f|v|` integrable + a.e.-continuous — both routine
for a compactly-supported DCF with finitely many jumps.  All axiom-clean (`propext`,
`Classical.choice`, `Quot.sound`).
-/

open MeasureTheory Real Set FourierTransform Complex

namespace FMSA.HardSphere

/-- The `fourier_of_odd` integral of the odd extension `v ↦ v·f|v|` equals the (cast) real radial
integral `∫₀^∞ v·f(v)·sin(2πvw) dv` (same argument order as `fourier_of_odd`). -/
theorem oddExt_fourier_integral_eq (f : ℝ → ℝ) (w : ℝ) :
    (∫ v in Ioi (0:ℝ), (Real.sin (2 * π * v * w) : ℂ) * ((v * f |v| : ℝ) : ℂ))
      = ((∫ v in Ioi (0:ℝ), v * f v * Real.sin (2 * π * v * w) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [abs_of_pos (mem_Ioi.mp hv)]
  push_cast
  ring

theorem ae_eq_oddExt_of_radial_fourier_eq (f g : ℝ → ℝ)
    (hint_f : Integrable (fun v => ((v * f |v| : ℝ) : ℂ)))
    (hint_g : Integrable (fun v => ((v * g |v| : ℝ) : ℂ)))
    (hcont_f : ∀ᵐ v, ContinuousAt (fun v => ((v * f |v| : ℝ) : ℂ)) v)
    (hcont_g : ∀ᵐ v, ContinuousAt (fun v => ((v * g |v| : ℝ) : ℂ)) v)
    (hFeq : ∀ k, radial_fourier f k = radial_fourier g k) :
    (fun v => ((v * f |v| : ℝ) : ℂ)) =ᵐ[volume] (fun v => ((v * g |v| : ℝ) : ℂ)) := by
  set ψf : ℝ → ℂ := fun v => ((v * f |v| : ℝ) : ℂ) with hψf
  set ψg : ℝ → ℂ := fun v => ((v * g |v| : ℝ) : ℂ) with hψg
  have hoddf : ∀ v, ψf (-v) = -ψf v := fun v => by simp only [hψf, abs_neg]; push_cast; ring
  have hoddg : ∀ v, ψg (-v) = -ψg v := fun v => by simp only [hψg, abs_neg]; push_cast; ring
  -- radial integrals (with the fourier argument order) agree for w ≠ 0
  have hReq : ∀ w : ℝ, w ≠ 0 →
      (∫ v in Ioi (0:ℝ), v * f v * Real.sin (2 * π * v * w))
        = ∫ v in Ioi (0:ℝ), v * g v * Real.sin (2 * π * v * w) := by
    intro w hw
    have hw' : (2 : ℝ) * π * w ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hw
    have h := hFeq (2 * π * w)
    simp only [radial_fourier] at h
    have hc : (4 * π / (2 * π * w)) ≠ 0 := div_ne_zero (by positivity) hw'
    have hcancel := mul_left_cancel₀ hc h
    have reorder : ∀ h : ℝ → ℝ,
        (∫ v in Ioi (0:ℝ), v * h v * Real.sin (2 * π * v * w))
          = ∫ v in Ioi (0:ℝ), v * h v * Real.sin (2 * π * w * v) := fun h =>
      setIntegral_congr_fun measurableSet_Ioi (fun v _ => by
        rw [show (2:ℝ) * π * v * w = 2 * π * w * v from by ring])
    rw [reorder f, reorder g]; exact hcancel
  -- the Fourier transforms agree
  have hFourier : 𝓕 ψf = 𝓕 ψg := by
    funext w
    rw [fourier_of_odd ψf hoddf hint_f w, fourier_of_odd ψg hoddg hint_g w]
    congr 1
    rw [oddExt_fourier_integral_eq f w, oddExt_fourier_integral_eq g w]
    rcases eq_or_ne w 0 with rfl | hw
    · norm_num
    · exact congrArg _ (hReq w hw)
  exact ae_eq_of_fourier_eq hint_f hint_g hFourier hcont_f hcont_g

/-- **Radial-Fourier a.e.-injectivity on `(0,∞)`.**  Equal radial (sine) transforms ⇒ the functions
agree a.e. on the physical half-line — the form the mixture-DCF symmetry needs (`matDCF i k = matDCF
k i` a.e. on `r > 0` from `Cmix0` symmetry).  Divides out the `v > 0` factor of the extension. -/
theorem ae_eq_of_radial_fourier_eq (f g : ℝ → ℝ)
    (hint_f : Integrable (fun v => ((v * f |v| : ℝ) : ℂ)))
    (hint_g : Integrable (fun v => ((v * g |v| : ℝ) : ℂ)))
    (hcont_f : ∀ᵐ v, ContinuousAt (fun v => ((v * f |v| : ℝ) : ℂ)) v)
    (hcont_g : ∀ᵐ v, ContinuousAt (fun v => ((v * g |v| : ℝ) : ℂ)) v)
    (hFeq : ∀ k, radial_fourier f k = radial_fourier g k) :
    f =ᵐ[volume.restrict (Ioi 0)] g := by
  have h := ae_eq_oddExt_of_radial_fourier_eq f g hint_f hint_g hcont_f hcont_g hFeq
  have hmem : ∀ᵐ v ∂(volume.restrict (Ioi (0:ℝ))), v ∈ Ioi (0:ℝ) :=
    ae_restrict_mem measurableSet_Ioi
  filter_upwards [ae_restrict_of_ae h, hmem] with v hv hvmem
  have hvpos : (0:ℝ) < v := hvmem
  rw [abs_of_pos hvpos] at hv
  have hvfg : v * f v = v * g v := by exact_mod_cast hv
  exact mul_left_cancel₀ (ne_of_gt hvpos) hvfg

end FMSA.HardSphere
