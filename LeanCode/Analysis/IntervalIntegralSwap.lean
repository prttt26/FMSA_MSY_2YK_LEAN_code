/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Triangle Fubini for interval integrals

Two swap lemmas for integrals over the triangle `{0 ≤ u ≤ s ≤ a}`:

  `∫₀^a (∫_u^a p) q(u) du = ∫₀^a p(s) (∫₀^s q) ds`      (`intervalIntegral_triangle_swap`)
  `∫₀^a ∫_u^a f u s ds du = ∫₀^a ∫₀^s f u s du ds`      (`intervalIntegral_triangle_swap_gen`)

Both take joint integrability of the `Ioi u`-indicator on `(0,a]²` as the only hypothesis, so they
are **jump-proof**: they need integrability, not continuity or differentiability, which is exactly
what makes them usable on the Baxter kernels that jump at the contact point.

Pure real analysis, project-independent — moved here from `HardSphere/BaxterRenewal.lean` (where
they were introduced for `OZFIX.19`/`OZFIX.20`) so that the `Analysis/` layer can use them too
(the causal-resolvent derivation of `MA.13` in `WienerRenewal.lean` needs the general form).
-/

open MeasureTheory

namespace FMSA

/-- **Triangle Fubini on `[0,a]`**: `∫₀^a (∫_u^a p) q(u) du = ∫₀^a p(s) (∫₀^s q) ds`.

The joint integrability of `(u,s) ↦ 1_{u<s}·p(s)·q(u)` on `(0,a]²` is the only hypothesis — for the
`OZFIX.19` use `p = s·c(s)` and `q` are bounded on the compact, so boundedness discharges it. -/
theorem intervalIntegral_triangle_swap {a : ℝ} (ha : 0 ≤ a) (p q : ℝ → ℝ)
    (hint : MeasureTheory.Integrable
      (Function.uncurry fun u s => (Set.Ioi u).indicator p s * q u)
      ((MeasureTheory.volume.restrict (Set.Ioc 0 a)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 a)))) :
    (∫ u in (0:ℝ)..a, (∫ s in u..a, p s) * q u)
      = ∫ s in (0:ℝ)..a, p s * ∫ u in (0:ℝ)..s, q u := by
  have hmeasp : ∀ u : ℝ, MeasurableSet (Set.Ioi u) := fun u => measurableSet_Ioi
  -- LHS as an iterated integral over `Ioc 0 a`, inner slice via the `Ioi u` indicator
  have hLHS : (∫ u in (0:ℝ)..a, (∫ s in u..a, p s) * q u)
      = ∫ u in Set.Ioc 0 a, (∫ s in Set.Ioc 0 a, (Set.Ioi u).indicator p s) * q u := by
    rw [intervalIntegral.integral_of_le ha]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
    intro u hu
    have hua : u ≤ a := hu.2
    have hInter : Set.Ioc 0 a ∩ Set.Ioi u = Set.Ioc u a := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨hu.1.trans h1, h2⟩, h1⟩
    have hslice : (∫ s in u..a, p s) = ∫ s in Set.Ioc 0 a, (Set.Ioi u).indicator p s := by
      rw [intervalIntegral.integral_of_le hua,
        MeasureTheory.setIntegral_indicator (hmeasp u), hInter]
    show (∫ s in u..a, p s) * q u = (∫ s in Set.Ioc 0 a, (Set.Ioi u).indicator p s) * q u
    rw [hslice]
  -- pull `q u` inside, swap, then read off the `s`-slice
  rw [hLHS]
  have hpull : ∀ u : ℝ,
      (∫ s in Set.Ioc 0 a, (Set.Ioi u).indicator p s) * q u
        = ∫ s in Set.Ioc 0 a, (Set.Ioi u).indicator p s * q u := by
    intro u; rw [MeasureTheory.integral_mul_const]
  simp_rw [hpull]
  rw [MeasureTheory.integral_integral_swap hint]
  -- RHS: for each `s`, the `u`-integral collapses to `p s · ∫₀^s q`
  rw [intervalIntegral.integral_of_le ha]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
  intro s hs
  have hInter2 : Set.Ioc 0 a ∩ Set.Iio s = Set.Ioo 0 s := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_of_lt (lt_of_lt_of_le h2 hs.2)⟩, h2⟩
  have hslice2 : (∫ u in Set.Ioc 0 a, (Set.Ioi u).indicator p s * q u)
      = p s * ∫ u in (0:ℝ)..s, q u := by
    have hrw : ∀ u : ℝ, (Set.Ioi u).indicator p s * q u
        = (Set.Iio s).indicator (fun u => p s * q u) u := by
      intro u
      by_cases huv : u < s
      · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr huv : s ∈ Set.Ioi u),
          Set.indicator_of_mem (Set.mem_Iio.mpr huv : u ∈ Set.Iio s)]
      · rw [Set.indicator_of_notMem (by simpa using huv : s ∉ Set.Ioi u),
          Set.indicator_of_notMem (by simpa using huv : u ∉ Set.Iio s), zero_mul]
    simp_rw [hrw]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Iio, hInter2,
      MeasureTheory.integral_const_mul, intervalIntegral.integral_of_le hs.1.le,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
  show (∫ u in Set.Ioc 0 a, (Set.Ioi u).indicator p s * q u) = p s * ∫ u in (0:ℝ)..s, q u
  rw [hslice2]

/-- **General triangle Fubini** (2-variable integrand):
`∫₀^a ∫_u^a f(u,s) ds du = ∫₀^a ∫₀^s f(u,s) du ds`.  Same `integral_integral_swap` + indicator
argument as `intervalIntegral_triangle_swap`, but the
integrand `f u s` need not factor as `p(s)·q(u)`.  Used by `OZFIX.20` where the integrand
`H(u)·q0(t)·q0(t−u)` couples both variables through `q0(t−u)`. -/
theorem intervalIntegral_triangle_swap_gen {a : ℝ} (ha : 0 ≤ a) (f : ℝ → ℝ → ℝ)
    (hint : MeasureTheory.Integrable
      (Function.uncurry fun u s => (Set.Ioi u).indicator (f u) s)
      ((MeasureTheory.volume.restrict (Set.Ioc 0 a)).prod
        (MeasureTheory.volume.restrict (Set.Ioc 0 a)))) :
    (∫ u in (0:ℝ)..a, ∫ s in u..a, f u s) = ∫ s in (0:ℝ)..a, ∫ u in (0:ℝ)..s, f u s := by
  have hmeasp : ∀ u : ℝ, MeasurableSet (Set.Ioi u) := fun u => measurableSet_Ioi
  have hLHS : (∫ u in (0:ℝ)..a, ∫ s in u..a, f u s)
      = ∫ u in Set.Ioc 0 a, ∫ s in Set.Ioc 0 a, (Set.Ioi u).indicator (f u) s := by
    rw [intervalIntegral.integral_of_le ha]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
    intro u hu
    have hua : u ≤ a := hu.2
    have hInter : Set.Ioc 0 a ∩ Set.Ioi u = Set.Ioc u a := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨hu.1.trans h1, h2⟩, h1⟩
    show (∫ s in u..a, f u s) = ∫ s in Set.Ioc 0 a, (Set.Ioi u).indicator (f u) s
    rw [intervalIntegral.integral_of_le hua, MeasureTheory.setIntegral_indicator (hmeasp u), hInter]
  rw [hLHS, MeasureTheory.integral_integral_swap hint,
    intervalIntegral.integral_of_le ha]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
  intro s hs
  have hInter2 : Set.Ioc 0 a ∩ Set.Iio s = Set.Ioo 0 s := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_of_lt (lt_of_lt_of_le h2 hs.2)⟩, h2⟩
  show (∫ u in Set.Ioc 0 a, (Set.Ioi u).indicator (f u) s) = ∫ u in (0:ℝ)..s, f u s
  have hrw : ∀ u : ℝ, (Set.Ioi u).indicator (f u) s
      = (Set.Iio s).indicator (fun u => f u s) u := by
    intro u
    by_cases huv : u < s
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr huv : s ∈ Set.Ioi u),
        Set.indicator_of_mem (Set.mem_Iio.mpr huv : u ∈ Set.Iio s)]
    · rw [Set.indicator_of_notMem (by simpa using huv : s ∉ Set.Ioi u),
        Set.indicator_of_notMem (by simpa using huv : u ∉ Set.Iio s)]
  simp_rw [hrw]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Iio, hInter2,
    intervalIntegral.integral_of_le hs.1.le, ← MeasureTheory.integral_Ioc_eq_integral_Ioo]

end FMSA
