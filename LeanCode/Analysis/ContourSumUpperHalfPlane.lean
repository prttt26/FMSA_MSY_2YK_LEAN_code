/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.Analysis.ContourDeformation
import LeanCode.Analysis.JordanLemma

/-!
# Contour-sum step: improper integral = 2πi · Σ residues (Tang & Lu eq (19))

The residue extraction of `LeanCode/YukawaDCF/MixtureYukawaResidue.lean` computed the *value*
of each per-pole residue.  This file supplies the other half of Tang & Lu eq (19): the
**contour-sum step** turning the inversion integral `∫dy/(y−k)` into the finite **sum** of
those residues.

`improper_integral_eq_sum_residues_upperHalfPlane` is the general engine: for any `f` with finitely
many simple poles strictly inside the *open* upper half-plane, holomorphic on the rest of the closed
UHP (off a countable set), and with a vanishing upper-arc integral (`harc`, a Jordan-type decay),
`∫_{−R}^{R} f → Σ_i 2πi · gᵢ(cᵢ)` as `R → ∞`, where `gᵢ` is the residue-generating factor
(`f = gᵢ/(·−cᵢ)` near the pole `cᵢ`).  It generalizes `fourier_kernel_one_pole` /
`fourier_kernel_finite_poles` from the specific Fourier kernel `e^{ixr}/(x−k)` to an arbitrary
integrand, and rests only on the accepted contour-deformation axiom
`halfDiskBoundary_eq_sum_of_small_circles` (via
`halfDiskBoundary_eq_sum_two_pi_I_mul_of_simple_poles`).

Why the enclosed poles are *only* the Yukawa poles of `U₁`: in Tang & Lu's integrand
`E(−y)[Q̂₀(−y)]⁻¹U₁(y)[Q̂₀ᵀ(−y)]⁻¹E(−y)/(y−k)` the factor `[Q̂₀(−y)]⁻¹` is **pole-free in the UHP**
(`mixtureDet_pole_free_N`, proved for all `N`), so closing the contour upward encloses exactly the
simple Yukawa poles `y = i zᵢⱼ` of `U₁` — which is precisely why eq (19)'s residue is taken "with
respect to each element of `U₁(y)`".

`improper_integral_eq_sum_yukawa_residues` specializes the engine to those Yukawa poles
`cᵢ = i·zᵢ` and rewrites the conclusion into the residue **values**
`−ĝᵢ(i zᵢ)/(i k + zᵢ)` that `residue_yukawa_pole_general` produces — closing the loop between
the two halves of task (3).

The integrand-specific inputs `hc`/`hd` (holomorphy off the poles, from `mixtureDet_pole_free_N`)
and `harc` (the Jordan arc bound for the concrete matrix integrand) remain hypotheses here; the
on-contour `y = k` real-axis pole (the `½`-Plemelj boundary term of eq (14)) needs
Sokhotski–Plemelj, which is outside the current half-disk infrastructure (it requires poles in
the *open* UHP).
-/

open Filter Topology Metric MeasureTheory Complex

namespace FMSA.MixtureRDF

/-- **Contour-sum step (general engine).**  Finitely many simple poles `c' i` strictly inside the
open upper half-plane, residue factor `g i` (`f = g i /(·−c' i)` near `c' i`), `f` holomorphic on
the rest of the closed UHP off a countable set `s`, and a vanishing upper-arc integral `harc` ⟹
`∫_{−R}^{R} f → Σᵢ 2πi · g i (c' i)`.  Generalizes `fourier_kernel_one_pole`; the only axiom is the
contour-deformation one (via `halfDiskBoundary_eq_sum_two_pi_I_mul_of_simple_poles`). -/
theorem improper_integral_eq_sum_residues_upperHalfPlane
    {f : ℂ → ℂ} {ι : Type*} [Fintype ι] {c' : ι → ℂ} {r' : ι → ℝ} {g : ι → ℂ → ℂ}
    {s : Set ℂ} (hs : s.Countable)
    (hr'pos : ∀ i, 0 < r' i)
    (hUHP : ∀ i, r' i < (c' i).im)
    (hdisj : ∀ i j, i ≠ j → Disjoint (closedBall (c' i) (r' i)) (closedBall (c' j) (r' j)))
    (hc : ContinuousOn f ({z : ℂ | 0 ≤ z.im} \ ⋃ i, ball (c' i) (r' i)))
    (hd : ∀ z ∈ ({z : ℂ | 0 ≤ z.im} \ ⋃ i, closedBall (c' i) (r' i)) \ s,
      DifferentiableAt ℂ f z)
    (hgeq : ∀ i, ∀ z ∈ closedBall (c' i) (r' i), f z = g i z / (z - c' i))
    (hgc : ∀ i, ContinuousOn (g i) (closedBall (c' i) (r' i)))
    (hgd : ∀ i, ∀ z ∈ ball (c' i) (r' i) \ s, DifferentiableAt ℂ (g i) z)
    (harc : Tendsto (fun R : ℝ => ∫ θ in (0:ℝ)..Real.pi,
        (Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)) •
          f ((R:ℂ) * Complex.exp (θ * Complex.I))) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ => ∫ x in (-R)..R, f (x : ℂ)) atTop
      (𝓝 (∑ i, (2 * (Real.pi : ℂ) * Complex.I) * g i (c' i))) := by
  set S : ℂ := ∑ i, (2 * (Real.pi : ℂ) * Complex.I) * g i (c' i) with hSdef
  set arc : ℝ → ℂ := fun R => ∫ θ in (0:ℝ)..Real.pi,
    (Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)) •
      f ((R:ℂ) * Complex.exp (θ * Complex.I)) with harcdef
  have hev : ∀ᶠ R : ℝ in atTop, 0 < R ∧ ∀ i, ‖c' i‖ + r' i < R :=
    (eventually_gt_atTop 0).and
      (Filter.eventually_all.mpr (fun i => eventually_gt_atTop (‖c' i‖ + r' i)))
  have heq : (fun R : ℝ => ∫ x in (-R)..R, f (x : ℂ)) =ᶠ[atTop] fun R => S - arc R := by
    filter_upwards [hev] with R hR
    obtain ⟨hRpos, hRlt⟩ := hR
    have hinside : ∀ i, closedBall (c' i) (r' i) ⊆ {z : ℂ | ‖z‖ < R ∧ 0 < z.im} := by
      intro i z hz
      rw [mem_closedBall_iff_norm] at hz
      refine ⟨?_, ?_⟩
      · have h1 : ‖z‖ - ‖c' i‖ ≤ ‖z - c' i‖ := norm_sub_norm_le z (c' i)
        linarith [hRlt i]
      · have him : |z.im - (c' i).im| ≤ ‖z - c' i‖ := by
          have h : (z - c' i).im = z.im - (c' i).im := by simp
          rw [← h]; exact Complex.abs_im_le_norm _
        have h2 := abs_le.mp him
        linarith [h2.1, hUHP i]
    have hcR : ContinuousOn f (({z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) \ ⋃ i, ball (c' i) (r' i)) :=
      hc.mono (Set.sdiff_subset_sdiff_left (fun z hz => hz.2))
    have hdR : ∀ z ∈ (({z : ℂ | ‖z‖ ≤ R ∧ 0 ≤ z.im}) \ ⋃ i, closedBall (c' i) (r' i)) \ s,
        DifferentiableAt ℂ f z := fun z hz => hd z ⟨⟨hz.1.1.2, hz.1.2⟩, hz.2⟩
    have hform := halfDiskBoundary_eq_sum_two_pi_I_mul_of_simple_poles hRpos hr'pos hinside hdisj hs
      hcR hdR hgeq hgc hgd
    exact eq_sub_of_add_eq hform
  have hlim : Tendsto (fun R : ℝ => S - arc R) atTop (𝓝 (S - 0)) :=
    tendsto_const_nhds.sub harc
  rw [sub_zero] at hlim
  exact Filter.Tendsto.congr' heq.symm hlim

/-- **Contour-sum step at the Yukawa poles (Tang & Lu eq (19)→(21)).**  Specializes the engine to
poles `cᵢ = i·zᵢ` whose residue factor has the Yukawa shape `g i w = ĝ i w /((w−k)·i)` (so that
`f = ĝ i /((·−k)(i·+zᵢ))` near the pole, matching eq (20)).  The contour sum then equals
`Σᵢ 2πi · (−ĝᵢ(i zᵢ)/(i k + zᵢ))` — exactly `2πi` times the per-pole residue **value**
`residue_yukawa_pole_general` computes, via `(i zᵢ − k)·i = −(i k + zᵢ)`. -/
theorem improper_integral_eq_sum_yukawa_residues
    {f : ℂ → ℂ} {ι : Type*} [Fintype ι] {z : ι → ℂ} {r' : ι → ℝ} {ĝ : ι → ℂ → ℂ} {k : ℂ}
    {s : Set ℂ} (hs : s.Countable)
    (hr'pos : ∀ i, 0 < r' i)
    (hUHP : ∀ i, r' i < (Complex.I * z i).im)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (closedBall (Complex.I * z i) (r' i)) (closedBall (Complex.I * z j) (r' j)))
    (hc : ContinuousOn f ({w : ℂ | 0 ≤ w.im} \ ⋃ i, ball (Complex.I * z i) (r' i)))
    (hd : ∀ w ∈ ({w : ℂ | 0 ≤ w.im} \ ⋃ i, closedBall (Complex.I * z i) (r' i)) \ s,
      DifferentiableAt ℂ f w)
    (hgeq : ∀ i, ∀ w ∈ closedBall (Complex.I * z i) (r' i),
      f w = (ĝ i w / ((w - k) * Complex.I)) / (w - Complex.I * z i))
    (hgc : ∀ i, ContinuousOn (fun w => ĝ i w / ((w - k) * Complex.I))
      (closedBall (Complex.I * z i) (r' i)))
    (hgd : ∀ i, ∀ w ∈ ball (Complex.I * z i) (r' i) \ s,
      DifferentiableAt ℂ (fun w => ĝ i w / ((w - k) * Complex.I)) w)
    (harc : Tendsto (fun R : ℝ => ∫ θ in (0:ℝ)..Real.pi,
        (Complex.I * (R:ℂ) * Complex.exp (θ * Complex.I)) •
          f ((R:ℂ) * Complex.exp (θ * Complex.I))) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ => ∫ x in (-R)..R, f (x : ℂ)) atTop
      (𝓝 (∑ i, (2 * (Real.pi : ℂ) * Complex.I) *
        (- ĝ i (Complex.I * z i) / (Complex.I * k + z i)))) := by
  have key := improper_integral_eq_sum_residues_upperHalfPlane
    (c' := fun i => Complex.I * z i) (g := fun i w => ĝ i w / ((w - k) * Complex.I))
    hs hr'pos hUHP hdisj hc hd hgeq hgc hgd harc
  convert key using 2
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  show - ĝ i (Complex.I * z i) / (Complex.I * k + z i)
      = ĝ i (Complex.I * z i) / ((Complex.I * z i - k) * Complex.I)
  rw [show (Complex.I * z i - k) * Complex.I = -(Complex.I * k + z i) from by
    linear_combination (z i) * Complex.I_sq, div_neg, neg_div]

end FMSA.MixtureRDF
