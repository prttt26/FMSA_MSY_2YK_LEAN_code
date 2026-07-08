/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.RadialLaplace

/-!
# Radial Fourier (sine) convolution theorem — correct replacement for `radial_laplace_conv`

## Summary

`radial_laplace_conv` (`RadialLaplace.lean`) was found mathematically **false**: the
one-sided real Laplace transform of `r·f(r)` does not turn the 3D radial convolution
`radial3d_conv` into a clean product — see that file's doc comment for the disproof.

This file proves the mathematically correct replacement: the **radial sine transform**
```
𝓕_r[f](k) = (4π/k) ∫_0^∞ r·f(r)·sin(kr) dr
```
(the radial reduction of the genuine 3D Fourier transform) *does* turn `radial3d_conv` into
a clean product:
```
𝓕_r[f ⊛₃D g](k) = 𝓕_r[f](k) · 𝓕_r[g](k)
```

**Why this succeeds where the Laplace version failed:** doing the same triangle-region
integration-order swap, the inner step reduces via
```
∫_{|t-s|}^{t+s} sin(kr) dr = (2/k)·sin(kt)·sin(ks)
```
(antiderivative `-cos(kr)/k` plus the identity `cos(a-b) - cos(a+b) = 2 sin a sin b`) — an
EXACT factorization into a product of `sin(kt)` and `sin(ks)`, with no leftover cross term.
The analogous step for `e^{-sr}` has no such identity (the discrepancy term
`e^{-s|t-s'|}` in the Laplace case does not factor), which is the root cause of
`radial_laplace_conv`'s failure.

## References

- Baxter, R.J. (1970) J. Chem. Phys. 52, 4559
- Hansen, J.P. & McDonald, I.R., *Theory of Simple Liquids* — the radial Fourier transform
  of the 3D OZ convolution is the standard textbook route this file formalizes.
-/

open MeasureTheory Set Real

namespace FMSA.HardSphere

/-! ### Radial Fourier (sine) transform -/

/-- **Radial (sine) Fourier transform** — the radial reduction of the genuine 3D Fourier
transform for a radially symmetric function:

    `𝓕_r[f](k) = (4π/k) ∫_0^∞ r·f(r)·sin(kr) dr` -/
noncomputable def radial_fourier (f : ℝ → ℝ) (k : ℝ) : ℝ :=
  (4 * Real.pi / k) * ∫ r in Set.Ioi (0 : ℝ), r * f r * Real.sin (k * r)

/-! ### Key trig lemma: the triangle-region integral separates exactly -/

/-- **Key algebraic fact.** `∫_{|t-s|}^{t+s} sin(kr) dr = (2/k)·sin(kt)·sin(ks)`.

This is the reason the Fourier/sine transform succeeds where the Laplace transform failed:
the antiderivative gives `(cos(k|t-s|) - cos(k(t+s)))/k`, then `cos(k|t-s|) = cos(k(t-s))`
(cos even) and the product-to-sum identity `cos(a-b) - cos(a+b) = 2 sin a sin b` (with
`a=kt, b=ks`) factors this exactly. -/
theorem sin_triangle_integral (t s k : ℝ) (hk : k ≠ 0) :
    ∫ r in |t - s|..(t + s), Real.sin (k * r) =
    (2 / k) * Real.sin (k * t) * Real.sin (k * s) := by
  rw [intervalIntegral.integral_comp_mul_left (f := Real.sin) hk, integral_sin]
  have habs : Real.cos (k * |t - s|) = Real.cos (k * (t - s)) := by
    rcases abs_cases (t - s) with ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq]
    · rw [heq, mul_neg, Real.cos_neg]
  have hsub : Real.cos (k * (t - s)) - Real.cos (k * (t + s)) =
      2 * Real.sin (k * t) * Real.sin (k * s) := by
    rw [show k * (t - s) = k * t - k * s from by ring,
        show k * (t + s) = k * t + k * s from by ring,
        Real.cos_sub, Real.cos_add]
    ring
  rw [smul_eq_mul, habs, hsub]
  ring

/-! ### Symmetry of the triangle-inequality region -/

/-- The triangle-inequality region is symmetric under solving for any one of its three
variables: `s ∈ [|r-t|, r+t] ↔ r ∈ [|t-s|, t+s]`. Both sides unfold (via `abs_le`) to the
same three linear inequalities on `r,t,s`, just reordered. -/
private lemma triangle_mem_iff (r t s : ℝ) :
    s ∈ Set.Icc |r - t| (r + t) ↔ r ∈ Set.Icc |t - s| (t + s) := by
  simp only [Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith⟩

/-- For `a ≥ 0`, `Icc a b` meets `Ioi 0` in exactly `Icc a b` minus the single point `0`
(an exact set identity: membership in `Icc a b` already forces `x ≥ a ≥ 0`, so `x ≠ 0` and
`x ≥ 0` together give `x > 0`), and removing a single point doesn't change a real integral. -/
private lemma setIntegral_Icc_eq_setIntegral_Ioi_indicator {a b : ℝ} (ha : 0 ≤ a) (h : ℝ → ℝ) :
    ∫ x in Set.Icc a b, h x = ∫ x in Set.Ioi (0 : ℝ), (Set.Icc a b).indicator h x := by
  rw [MeasureTheory.setIntegral_indicator measurableSet_Icc, Set.inter_comm]
  apply MeasureTheory.setIntegral_congr_set
  have hset : Set.Icc a b ∩ Set.Ioi (0 : ℝ) = Set.Icc a b \ {0} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioi, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, h3.ne'⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, lt_of_le_of_ne (le_trans ha h1) (Ne.symm h3)⟩
  rw [hset]
  apply MeasureTheory.ae_eq_set.mpr
  constructor
  · have hsub : Set.Icc a b \ (Set.Icc a b \ {(0 : ℝ)}) ⊆ {(0 : ℝ)} := by
      intro x hx
      simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hx
      by_contra hne
      exact hx.2 ⟨hx.1, hne⟩
    exact measure_mono_null hsub Real.volume_singleton
  · have hempty : (Set.Icc a b \ {(0 : ℝ)}) \ Set.Icc a b = ∅ := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨hx1, _⟩, hx2⟩
      exact hx2 hx1
    rw [hempty, measure_empty]

/-! ### Main theorem: the radial Fourier transform factors the 3D convolution -/

/-- **`radial_fourier_conv`** — the correct replacement for the disproven
`radial_laplace_conv`: the radial sine transform turns the 3D radial convolution into a
clean product, with **no extra term** (contrast `radial_laplace_conv`'s false claim).

**Hypotheses:** `htsInt` and `hjoint` are the joint (product-measure) integrability facts
needed to justify the two Fubini/Tonelli swaps of integration order over the
triangle-inequality region `{(r,t,s) : |r-t|≤s≤r+t}` — stated as explicit hypotheses in the
same spirit as `OZExteriorBridge.lean`'s own integrability side-conditions (deriving them
purely from marginal L¹ facts about `f,g` is a further, orthogonal piece of work: it needs the
genuine structure of `radial3d_conv`'s support, not just abstract Fubini, since the crude
bound `|sin|≤1` alone is too lossy to give integrability in `r` over all of `(0,∞)` without
extra decay/support information on `f,g`). No separate marginal-integrability hypothesis on
`f` or `g` alone is needed: the conclusion is a genuine equality of real numbers regardless
(Lean's `integral` returns `0` by convention for non-integrable functions), and `htsInt`/
`hjoint` are what the proof actually uses. -/
theorem radial_fourier_conv {f g : ℝ → ℝ} {k : ℝ} (hk : 0 < k)
    (htsInt : ∀ r ∈ Set.Ioi (0 : ℝ), Integrable
      (fun p : ℝ × ℝ =>
        p.1 * f p.1 * (Set.Icc |r - p.1| (r + p.1)).indicator (fun s => s * g s) p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))))
    (hjoint : Integrable
      (fun p : ℝ × ℝ × ℝ =>
        (p.2.1 * f p.2.1) *
          (Set.Icc |p.1 - p.2.1| (p.1 + p.2.1)).indicator (fun s => s * g s) p.2.2 *
          Real.sin (k * p.1))
      ((volume.restrict (Set.Ioi 0)).prod
        ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))))) :
    radial_fourier (radial3d_conv f g) k = radial_fourier f k * radial_fourier g k := by
  unfold radial_fourier
  -- Step 1: for r > 0, `r * radial3d_conv f g r = 2π * (inner double integral)`.
  have hpt : Set.EqOn
      (fun r => r * radial3d_conv f g r * Real.sin (k * r))
      (fun r => 2 * Real.pi *
        (∫ t in Set.Ioi (0 : ℝ), t * f t * ∫ s in Set.Icc (|r - t|) (r + t), s * g s) *
        Real.sin (k * r))
      (Set.Ioi (0 : ℝ)) := by
    intro r hr
    simp only
    unfold radial3d_conv
    rw [if_neg (not_le.mpr hr)]
    have hcancel : ∀ X : ℝ, r * (2 * Real.pi / r * X) = 2 * Real.pi * X := by
      intro X; field_simp [(Set.mem_Ioi.mp hr).ne']
    rw [hcancel]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt]
  -- Step 2: for each r, convert the (t,s) nested double integral into a single integral
  -- over the product measure (first rewriting the moving-bound `s`-integral as an indicator).
  have hstep2 : Set.EqOn
      (fun r => 2 * Real.pi *
        (∫ t in Set.Ioi (0 : ℝ), t * f t * ∫ s in Set.Icc (|r - t|) (r + t), s * g s) *
        Real.sin (k * r))
      (fun r => 2 * Real.pi *
        (∫ p : ℝ × ℝ, p.1 * f p.1 *
          (Set.Icc |r - p.1| (r + p.1)).indicator (fun s => s * g s) p.2
          ∂((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0)))) *
        Real.sin (k * r))
      (Set.Ioi (0 : ℝ)) := by
    intro r hr
    simp only
    have hind : ∀ t : ℝ, t * f t * (∫ s in Set.Icc (|r - t|) (r + t), s * g s) =
        ∫ s in Set.Ioi (0 : ℝ),
          t * f t * (Set.Icc |r - t| (r + t)).indicator (fun s => s * g s) s := by
      intro t
      rw [setIntegral_Icc_eq_setIntegral_Ioi_indicator (abs_nonneg _) (fun s => s * g s),
          ← MeasureTheory.integral_const_mul]
    simp_rw [hind]
    have hconv := MeasureTheory.integral_integral
      (μ := volume.restrict (Set.Ioi (0 : ℝ))) (ν := volume.restrict (Set.Ioi (0 : ℝ)))
      (f := fun t s => t * f t * (Set.Icc |r - t| (r + t)).indicator (fun s => s * g s) s)
      (htsInt r hr)
    congr 2
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hstep2]
  -- Step 3: pull `2π` out of the r-integral, push `sin(kr)` into the (t,s)-integral,
  -- then swap `r` against the `(t,s)` pair via Fubini (using `hjoint`).
  simp_rw [mul_assoc (2 * Real.pi)]
  rw [MeasureTheory.integral_const_mul]
  have hpush : ∀ r : ℝ,
      (∫ p : ℝ × ℝ, p.1 * f p.1 *
          (Set.Icc |r - p.1| (r + p.1)).indicator (fun s => s * g s) p.2
          ∂((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0)))) *
        Real.sin (k * r) =
      ∫ p : ℝ × ℝ, p.1 * f p.1 *
          (Set.Icc |r - p.1| (r + p.1)).indicator (fun s => s * g s) p.2 * Real.sin (k * r)
        ∂((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) :=
    fun r => (MeasureTheory.integral_mul_const _ _).symm
  simp_rw [hpush]
  have hswap := MeasureTheory.integral_integral_swap
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (ν := (volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ))))
    (f := fun r p => p.1 * f p.1 *
      (Set.Icc |r - p.1| (r + p.1)).indicator (fun s => s * g s) p.2 * Real.sin (k * r))
    hjoint
  rw [hswap]
  -- Step 4: evaluate the inner `r`-integral for each fixed `(t,s) ∈ Ioi 0 ×ˢ Ioi 0` via
  -- `triangle_mem_iff` + `sin_triangle_integral`, then factor via `integral_prod_mul`.
  have hinner : Set.EqOn
      (fun p : ℝ × ℝ => ∫ r in Set.Ioi (0 : ℝ), p.1 * f p.1 *
        (Set.Icc |r - p.1| (r + p.1)).indicator (fun s => s * g s) p.2 * Real.sin (k * r))
      (fun p : ℝ × ℝ =>
        (p.1 * f p.1 * Real.sin (k * p.1)) * ((2 / k) * (p.2 * g p.2 * Real.sin (k * p.2))))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    simp only [Set.mem_Ioi] at ht hs
    simp only
    have hcombined : ∀ r : ℝ,
        t * f t * (Set.Icc |r - t| (r + t)).indicator (fun s => s * g s) s * Real.sin (k * r) =
        (Set.Icc |t - s| (t + s)).indicator
          (fun r => t * f t * (s * g s) * Real.sin (k * r)) r := by
      intro r
      by_cases hmem : s ∈ Set.Icc |r - t| (r + t)
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ((triangle_mem_iff r t s).mp hmem)]
      · rw [Set.indicator_of_notMem hmem,
            Set.indicator_of_notMem (fun hc => hmem ((triangle_mem_iff r t s).mpr hc)),
            mul_zero, zero_mul]
    simp_rw [hcombined]
    rw [← setIntegral_Icc_eq_setIntegral_Ioi_indicator (abs_nonneg _),
        MeasureTheory.integral_const_mul]
    have habs : |t - s| ≤ t + s := abs_le.mpr ⟨by linarith, by linarith⟩
    have hIccIntv : (∫ a in Set.Icc |t - s| (t + s), Real.sin (k * a)) =
        ∫ a in |t - s|..(t + s), Real.sin (k * a) := by
      rw [intervalIntegral.integral_of_le habs, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [hIccIntv, sin_triangle_integral t s k hk.ne']
    ring
  have hpstep : (∫ p : ℝ × ℝ, (∫ r in Set.Ioi (0 : ℝ), p.1 * f p.1 *
      (Set.Icc |r - p.1| (r + p.1)).indicator (fun s => s * g s) p.2 * Real.sin (k * r))
      ∂((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0)))) =
    ∫ p : ℝ × ℝ,
      (p.1 * f p.1 * Real.sin (k * p.1)) * ((2 / k) * (p.2 * g p.2 * Real.sin (k * p.2)))
      ∂((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioi) hinner
  rw [hpstep]
  have hprodfac : (∫ p : ℝ × ℝ,
      (p.1 * f p.1 * Real.sin (k * p.1)) * ((2 / k) * (p.2 * g p.2 * Real.sin (k * p.2)))
      ∂((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0)))) =
    (∫ t in Set.Ioi (0 : ℝ), t * f t * Real.sin (k * t)) *
    ((2 / k) * ∫ s in Set.Ioi (0 : ℝ), s * g s * Real.sin (k * s)) := by
    have := MeasureTheory.integral_prod_mul
      (μ := volume.restrict (Set.Ioi (0 : ℝ))) (ν := volume.restrict (Set.Ioi (0 : ℝ)))
      (f := fun t => t * f t * Real.sin (k * t))
      (g := fun s => (2 / k) * (s * g s * Real.sin (k * s)))
    rw [this, MeasureTheory.integral_const_mul]
  rw [hprodfac]
  ring

end FMSA.HardSphere
