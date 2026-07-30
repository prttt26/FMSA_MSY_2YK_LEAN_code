/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterRenewal
import LeanCode.HardSphere.RadialFourier
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

/-! ### `F[shellKernel] = radial_fourier c` — the general-`c` `F[K]=Ĉ` (`OZFIX.18` F-part)

The scalar `baxterK_cos_eq_radial_fourier` (`OZFIX.18`) is `2∫₀^σ K·cos(kv) = radial_fourier(c_HS)`.
Its matrix analog is this identity per entry, so the genuine content is the **general-`c` version**:
for any `c` supported in `[0,σ]`, continuous on the open core, with `s·c(s)` interval-integrable,
`2∫₀^σ shellKernel(c)·cos(kv) = radial_fourier(c)(k)`.  Proof = one integration by parts, using the
general-`c` shell-kernel calculus below.  Transcription of the scalar with `baxterK → shellKernel c`,
`hasDerivAt_baxterK → shellKernel_hasDerivAt`, `c_HS_outer → hc_outer`. -/

/-- `shellKernel c σ σ = 0` — the boundary value that kills the IBP boundary term. -/
theorem shellKernel_apply_sigma (c : ℝ → ℝ) (sigma : ℝ) (hsigma : 0 < sigma) :
    shellKernel c sigma sigma = 0 := by
  rw [shellKernel, abs_of_pos hsigma, intervalIntegral.integral_same, mul_zero]

/-- **`shellKernel(c)' = −2π·(v·c(v))` on `(0,σ)`** — the general-`c` analog of `hasDerivAt_baxterK`.
FTC-1 (left endpoint) on `2π ∫_v^σ s·c(s) ds`, needing `s·c(s)` continuous at `v`. -/
theorem shellKernel_hasDerivAt {c : ℝ → ℝ} {sigma v : ℝ} (hv0 : 0 < v) (hvs : v < sigma)
    (hcv : ContinuousAt (fun s : ℝ => s * c s) v)
    (hmeas : StronglyMeasurableAtFilter (fun s : ℝ => s * c s) (nhds v))
    (hint : IntervalIntegrable (fun s : ℝ => s * c s) MeasureTheory.volume 0 sigma) :
    HasDerivAt (shellKernel c sigma) (-(2 * Real.pi) * (v * c v)) v := by
  have hintvs : IntervalIntegrable (fun s : ℝ => s * c s) MeasureTheory.volume v sigma :=
    hint.mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.mem_uIcc]; left; exact ⟨hv0.le, hvs.le⟩)
      (by rw [Set.mem_uIcc]; left; exact ⟨by linarith, le_refl _⟩))
  have hg : HasDerivAt (fun u : ℝ => 2 * Real.pi * ∫ s in u..sigma, s * c s)
      (2 * Real.pi * (-(v * c v))) v :=
    ((intervalIntegral.integral_hasStrictDerivAt_left hintvs hmeas hcv).hasDerivAt).const_mul
      (2 * Real.pi)
  have heq : shellKernel c sigma =ᶠ[nhds v] fun u => 2 * Real.pi * ∫ s in u..sigma, s * c s := by
    filter_upwards [eventually_gt_nhds hv0] with x hx
    rw [shellKernel, abs_of_pos hx]
  refine (hg.congr_of_eventuallyEq heq).congr_deriv ?_
  ring

/-- `shellKernel c σ` is continuous on `[0,σ]` (a primitive of the integrable `s·c(s)`). -/
theorem shellKernel_continuousOn {c : ℝ → ℝ} {sigma : ℝ}
    (hint : ∀ a b, IntervalIntegrable (fun s : ℝ => s * c s) MeasureTheory.volume a b) :
    ContinuousOn (shellKernel c sigma) (Set.Icc 0 sigma) := by
  have heqOn : Set.EqOn (shellKernel c sigma)
      (fun v => 2 * Real.pi * (-(∫ s in sigma..v, s * c s))) (Set.Icc 0 sigma) := by
    intro v hv
    rw [shellKernel, abs_of_nonneg hv.1, intervalIntegral.integral_symm sigma v]
  refine (Continuous.continuousOn ?_).congr heqOn
  exact ((intervalIntegral.continuous_primitive hint sigma).neg).const_mul (2 * Real.pi)

/-- **Support reduction of `radial_fourier` for a compactly-supported `c`.**  `radial_fourier(c)(k) =
(4π/k)∫₀^σ r·c(r)·sin(kr) dr` when `c = 0` off `[0,σ]`.  General-`c` form of
`radial_fourier_c_HS_eq_intervalIntegral`. -/
theorem radial_fourier_eq_intervalIntegral_of_support {c : ℝ → ℝ} {sigma : ℝ} (hsigma : 0 < sigma)
    (hc_outer : ∀ s, sigma ≤ s → c s = 0) (k : ℝ) :
    radial_fourier c k
      = (4 * Real.pi / k) * ∫ r in (0 : ℝ)..sigma, r * c r * Real.sin (k * r) := by
  unfold radial_fourier
  congr 1
  have hpt : Set.EqOn (fun r => r * c r * Real.sin (k * r))
      ((Set.Ioc 0 sigma).indicator (fun r => r * c r * Real.sin (k * r)))
      (Set.Ioi (0 : ℝ)) := by
    intro r hr0
    by_cases hr : r ∈ Set.Ioc (0 : ℝ) sigma
    · rw [Set.indicator_of_mem hr]
    · rw [Set.indicator_of_notMem hr]
      have hrge : sigma ≤ r := by
        simp only [Set.mem_Ioc, not_and, not_le] at hr
        exact (hr hr0).le
      simp [hc_outer r hrge]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt,
    MeasureTheory.setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_self_of_subset_right Set.Ioc_subset_Ioi_self,
    ← intervalIntegral.integral_of_le hsigma.le]

/-- **The general-`c` `F[K]=Ĉ`** (`OZFIX.18` F-part off `c_HS`).  `2∫₀^σ shellKernel(c)·cos(kv) dv =
radial_fourier(c)(k)`, `k ≠ 0`, for `c` supported in `[0,σ]`, continuous on the open core, with
`s·c(s)` interval-integrable.  One integration by parts (`shellKernel_hasDerivAt`, boundary killed by
`shellKernel_apply_sigma`), then the support reduction. -/
theorem shellKernel_cos_eq_radial_fourier {c : ℝ → ℝ} {sigma : ℝ} (hsigma : 0 < sigma)
    (hc_outer : ∀ s, sigma ≤ s → c s = 0)
    (hint : ∀ a b, IntervalIntegrable (fun s : ℝ => s * c s) MeasureTheory.volume a b)
    (hccore : ∀ v ∈ Set.Ioo (0 : ℝ) sigma, ContinuousAt (fun s : ℝ => s * c s) v)
    (hmeas : ∀ v ∈ Set.Ioo (0 : ℝ) sigma,
      StronglyMeasurableAtFilter (fun s : ℝ => s * c s) (nhds v))
    {k : ℝ} (hk : k ≠ 0) :
    2 * ∫ v in (0 : ℝ)..sigma, shellKernel c sigma v * Real.cos (k * v)
      = radial_fourier c k := by
  set Kp : ℝ → ℝ := fun v => -(2 * Real.pi) * (v * c v) with hKp
  set w : ℝ → ℝ := fun x => Real.sin (k * x) / k with hw
  set w' : ℝ → ℝ := fun x => Real.cos (k * x) with hw'
  have hwderiv : ∀ x, HasDerivAt w (w' x) x := by
    intro x
    have hlin : HasDerivAt (fun x => k * x) k x := by simpa using (hasDerivAt_id x).const_mul k
    have h1 : HasDerivAt (fun x => Real.sin (k * x)) (Real.cos (k * x) * k) x := hlin.sin
    have h2 : HasDerivAt w (Real.cos (k * x) * k / k) x := h1.div_const k
    rw [hw']; exact h2.congr_deriv (by field_simp)
  have hwcont : Continuous w := by rw [hw]; fun_prop
  have hw'cont : Continuous w' := by rw [hw']; fun_prop
  have hKcont : ContinuousOn (shellKernel c sigma) (Set.uIcc (0 : ℝ) sigma) := by
    rw [Set.uIcc_of_le hsigma.le]; exact shellKernel_continuousOn hint
  have hKp_II : IntervalIntegrable Kp MeasureTheory.volume 0 sigma := by
    have hbase : IntervalIntegrable (fun s : ℝ => -(2 * Real.pi) * (s * c s))
        MeasureTheory.volume 0 sigma := (hint 0 sigma).const_mul _
    exact hbase
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (u := shellKernel c sigma) (v := w) (u' := Kp) (v' := w')
    hKcont hwcont.continuousOn
    (fun x hx => by
      rw [min_eq_left hsigma.le, max_eq_right hsigma.le] at hx
      exact shellKernel_hasDerivAt hx.1 hx.2 (hccore x hx) (hmeas x hx) (hint 0 sigma))
    (fun x _ => hwderiv x)
    hKp_II (hw'cont.intervalIntegrable _ _)
  have hKsigma : shellKernel c sigma sigma = 0 := shellKernel_apply_sigma c sigma hsigma
  have hw0 : w 0 = 0 := by rw [hw]; simp
  rw [hKsigma, hw0] at hibp
  simp only [zero_mul, mul_zero, sub_zero] at hibp
  have hI1 : IntervalIntegrable (fun x => Kp x * w x) MeasureTheory.volume 0 sigma :=
    hKp_II.mul_continuousOn hwcont.continuousOn
  have hI2 : IntervalIntegrable (fun x => shellKernel c sigma x * w' x)
      MeasureTheory.volume 0 sigma :=
    (hw'cont.intervalIntegrable 0 sigma).continuousOn_mul hKcont
  rw [intervalIntegral.integral_add hI1 hI2] at hibp
  have hmain : (∫ x in (0 : ℝ)..sigma, shellKernel c sigma x * w' x)
      = -(∫ x in (0 : ℝ)..sigma, Kp x * w x) := by linarith [hibp]
  have hrhs : -(∫ x in (0 : ℝ)..sigma, Kp x * w x)
      = (2 * Real.pi / k) * ∫ x in (0 : ℝ)..sigma, x * c x * Real.sin (k * x) := by
    rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr ?_
    intro x _
    simp only [hKp, hw]
    field_simp
  rw [hrhs] at hmain
  rw [radial_fourier_eq_intervalIntegral_of_support hsigma hc_outer k]
  rw [show (fun x => shellKernel c sigma x * w' x)
    = fun x => shellKernel c sigma x * Real.cos (k * x) from rfl] at hmain
  rw [hmain]
  ring

end

end FMSA.HardSphere
