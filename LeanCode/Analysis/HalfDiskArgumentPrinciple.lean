/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.Analysis.ArgumentPrinciple

/-!
# The argument principle over a half-disk

The upper-half-disk analogue of `Analysis/ArgumentPrinciple.lean`'s circle version. Group MA
(`MATH_AXIOMS.md`): reusable general-purpose complex analysis, built on the MA.2 contour-deformation
axiom `halfDiskBoundary_eq_sum_of_small_circles` and the axiom-free per-circle bridge
`circleIntegral_logDeriv_zpow_smul_eq`.

## Results

* `halfDiskArgumentPrinciple_sum` — the boundary integral of a log-derivative over the half-disk
  boundary (diameter `[−R,R]` ∪ upper arc) equals `∑ i, 2πi·nᵢ` for explicitly-factored holes.
  A line-for-line mirror of `argumentPrinciple_sum` with the half-disk deformation.

`#print axioms` = `halfDiskBoundary_eq_sum_of_small_circles` + the standard three.

## Motivation

Consumers that need to count zeros/poles in a *half*-plane region (Baxter pole location in the open
upper half-plane, mixture MZERO exact counting) close a `[−R,R]`-diameter-plus-arc contour rather
than a full circle. This file provides the argument principle for that shape.
-/

open Set Metric Complex circleIntegral

noncomputable section

/-- **Half-disk argument principle (finite factored holes).** The upper-half-disk analogue of
`argumentPrinciple_sum`: the half-disk boundary integral of `F` (diameter `[−R,R]` plus the upper
arc) equals `∑ i, 2πi·nᵢ` when `F` equals `logDeriv((·−c'ᵢ)^{nᵢ}·gᵢ)` on each small hole sphere,
with `gᵢ` analytic and nonzero. Mirrors `argumentPrinciple_sum` with MA.2's half-disk deformation
axiom in place of MA.1's circle deformation. -/
theorem halfDiskArgumentPrinciple_sum {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    {ι : Type*} [Fintype ι] {c' : ι → ℂ} {r' : ι → ℝ} (hr'pos : ∀ i, 0 < r' i)
    (hinside : ∀ i, closedBall (c' i) (r' i) ⊆ {z : ℂ | ‖z‖ < R ∧ 0 < z.im})
    (hdisj : ∀ i j, i ≠ j → Disjoint (closedBall (c' i) (r' i)) (closedBall (c' j) (r' j)))
    {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn F (({z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) \ ⋃ i, ball (c' i) (r' i)))
    (hd : ∀ z ∈ (({z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) \ ⋃ i, closedBall (c' i) (r' i)) \ s,
      DifferentiableAt ℂ F z)
    {n : ι → ℤ} {g : ι → ℂ → ℂ}
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) (closedBall (c' i) (r' i)))
    (hgne : ∀ i, ∀ z ∈ closedBall (c' i) (r' i), g i z ≠ 0)
    (hFlog : ∀ i, EqOn F (logDeriv (fun w => (w - c' i) ^ n i * g i w)) (sphere (c' i) (r' i))) :
    ((∫ x in (-R)..R, F (x : ℂ)) +
        ∫ θ in (0:ℝ)..Real.pi,
          (Complex.I * (R : ℂ) * Complex.exp (θ * Complex.I)) •
            F ((R : ℂ) * Complex.exp (θ * Complex.I)))
      = ∑ i, 2 * (Real.pi : ℂ) * I * (n i : ℂ) := by
  rw [halfDiskBoundary_eq_sum_of_small_circles hR hr'pos hinside hdisj hs hc hd]
  apply Finset.sum_congr rfl
  intro i _
  rw [circleIntegral.integral_congr (hr'pos i).le (hFlog i)]
  exact circleIntegral_logDeriv_zpow_smul_eq (hr'pos i) (hg i) (hgne i) (n i)

end
