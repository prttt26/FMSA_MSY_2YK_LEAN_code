/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Leibniz rule for a convolution integral with a variable upper limit

The rule

  `d/dr ∫_a^r K(r−t)·φ(t) dt = K 0 · φ r + ∫_a^r K'(r−t)·φ(t) dt`                    (**MA.16**)

in which the differentiation variable occurs **both** in the upper limit **and** inside the
integrand.  Mathlib has each half separately but not their combination on the diagonal.

## Why the Lipschitz (dominated) form is mandatory

The intended kernel (`q0_poly`, the Baxter renewal kernel) has a genuine **kink**, so it is
differentiable only off a single point.  A naive "differentiate under the integral" is therefore
unavailable: the parametric half must go through `hasDerivAt_integral_of_dominated_loc_of_lip`,
whose Lipschitz hypothesis a kink does not destroy.  Accordingly `K` is assumed differentiable only
**almost everywhere** (`hK'`), the regularity across the exceptional points being supplied by
`hKlip`.

## The two halves, and the window they share

Splitting `∫_a^r = ∫_a^{r₀} + ∫_{r₀}^r` at the base point separates the two difficulties:

* `hasDerivAt_intervalIntegral_param` — **fixed** limits, parameter in the integrand.  Stated with
  an arbitrary upper limit `b` (not just `b = r₀`) because the same lemma is what differentiates a
  fixed-window forcing term such as `∫_0^σ K(r−s)·(−s) ds`.
* `hasDerivAt_intervalIntegral_moving_endpoint` — **moving** limit; here the parameter in the
  integrand contributes nothing, since subtracting `K 0` leaves a term bounded by `C·M·|x−r₀|²`,
  which is `o(|x−r₀|)`.  This is where the boundary value `K 0 · φ r₀` comes from.

Both are controlled by a single Lipschitz window `Icc (r₀−δ−b) (r₀+δ−a)`, which contains every
argument `x − t` arising for `x` within `δ` of `r₀` and `t` in the integration range.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped Interval

namespace FMSA.Analysis

/-- **Parametric half — fixed limits, differentiation parameter inside the integrand.**

`d/dx ∫_a^b K(x−t)·φ(t) dt = ∫_a^b K'(x−t)·φ(t) dt` at `x = r₀`, for a kernel `K` that is only
**almost everywhere** differentiable but Lipschitz on the window `Icc (r₀−δ−b) (r₀+δ−a)` of
arguments that can occur.

The upper limit `b` is arbitrary (independent of `r₀`), so this also covers a fixed-window forcing
term such as `∫_0^σ K(r−s)·(−s) ds`. -/
theorem hasDerivAt_intervalIntegral_param {K K' φ : ℝ → ℝ} {a b r₀ δ : ℝ} {C : NNReal}
    (hδ : 0 < δ) (hab : a ≤ b)
    (hK : Continuous K) (hφ : Continuous φ)
    (hK' : ∀ᵐ u, HasDerivAt K (K' u) u) (hK'meas : Measurable K')
    (hKlip : LipschitzOnWith C K (Icc (r₀ - δ - b) (r₀ + δ - a))) :
    HasDerivAt (fun x => ∫ t in a..b, K (x - t) * φ t)
      (∫ t in a..b, K' (r₀ - t) * φ t) r₀ := by
  set μ : Measure ℝ := volume.restrict (Ioc a b) with hμ
  set s : Set ℝ := Icc (r₀ - δ) (r₀ + δ) with hs_def
  -- every argument `x - t` occurring below lies in the Lipschitz window
  have hwin : ∀ x ∈ s, ∀ t ∈ Ioc a b, x - t ∈ Icc (r₀ - δ - b) (r₀ + δ - a) := by
    intro x hx t ht
    exact ⟨by linarith [hx.1, ht.2], by linarith [hx.2, ht.1]⟩
  have hs : s ∈ 𝓝 r₀ := Icc_mem_nhds (by linarith) (by linarith)
  -- measurability / integrability data
  have hcont : ∀ x : ℝ, Continuous fun t => K (x - t) * φ t := by intro x; fun_prop
  have hF_meas : ∀ᶠ x in 𝓝 r₀, AEStronglyMeasurable (fun t => K (x - t) * φ t) μ :=
    Eventually.of_forall fun x => (hcont x).aestronglyMeasurable
  have hF_int : Integrable (fun t => K (r₀ - t) * φ t) μ := by
    rw [hμ]
    exact (hcont r₀).integrableOn_Ioc
  have hF'_meas : AEStronglyMeasurable (fun t => K' (r₀ - t) * φ t) μ :=
    ((hK'meas.comp (measurable_const.sub measurable_id)).mul hφ.measurable).aestronglyMeasurable
  -- the Lipschitz bound, uniform in `t`
  set bound : ℝ → ℝ := fun t => (C : ℝ) * |φ t| with hbound_def
  have hbound_nonneg : ∀ t, 0 ≤ bound t := fun t =>
    mul_nonneg C.coe_nonneg (abs_nonneg _)
  have h_lipsch : ∀ᵐ t ∂μ, LipschitzOnWith (Real.nnabs (bound t))
      (fun x => K (x - t) * φ t) s := by
    rw [hμ, ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun t ht => ?_
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have hK_le : dist (K (x - t)) (K (y - t)) ≤ (C : ℝ) * dist (x - t) (y - t) :=
      hKlip.dist_le_mul _ (hwin x hx t ht) _ (hwin y hy t ht)
    have hxy : dist (x - t) (y - t) = dist x y := by
      simp [Real.dist_eq]
    rw [hxy] at hK_le
    have hprod : dist (K (x - t) * φ t) (K (y - t) * φ t)
        = dist (K (x - t)) (K (y - t)) * |φ t| := by
      simp [Real.dist_eq, ← sub_mul, abs_mul]
    have hcoe : ((Real.nnabs (bound t) : NNReal) : ℝ) = bound t := by
      rw [Real.coe_nnabs, abs_of_nonneg (hbound_nonneg t)]
    rw [hprod, hcoe, hbound_def]
    calc dist (K (x - t)) (K (y - t)) * |φ t|
        ≤ ((C : ℝ) * dist x y) * |φ t| := mul_le_mul_of_nonneg_right hK_le (abs_nonneg _)
      _ = (C : ℝ) * |φ t| * dist x y := by ring
  have hbound_int : Integrable bound μ := by
    have hbc : Continuous bound := by rw [hbound_def]; fun_prop
    rw [hμ]
    exact hbc.integrableOn_Ioc
  -- the a.e. pointwise derivative, transported through the measure-preserving `t ↦ r₀ - t`
  have h_diff : ∀ᵐ t ∂μ, HasDerivAt (fun x => K (x - t) * φ t) (K' (r₀ - t) * φ t) r₀ := by
    have hshift : ∀ᵐ t, HasDerivAt K (K' (r₀ - t)) (r₀ - t) :=
      (Measure.measurePreserving_sub_left volume r₀).quasiMeasurePreserving.ae hK'
    have hshift' : ∀ᵐ t ∂μ, HasDerivAt K (K' (r₀ - t)) (r₀ - t) := by
      rw [hμ]; exact ae_restrict_of_ae hshift
    filter_upwards [hshift'] with t ht
    exact (ht.comp_sub_const r₀ t).mul_const (φ t)
  have key := (hasDerivAt_integral_of_dominated_loc_of_lip (μ := μ) (bound := bound) (s := s)
    (x₀ := r₀) (F := fun x t => K (x - t) * φ t) (F' := fun t => K' (r₀ - t) * φ t)
    hs hF_meas hF_int hF'_meas h_lipsch hbound_int h_diff).2
  simp only [intervalIntegral.integral_of_le hab]
  exact key

/-- **Moving-endpoint half — the boundary term.**

`d/dx ∫_{r₀}^x K(x−t)·φ(t) dt = K 0 · φ r₀` at `x = r₀`.  The parameter inside the integrand
contributes nothing: after subtracting the constant `K 0`, the remainder is bounded by
`C·M·|x−r₀|²` (the Lipschitz estimate over a range of length `|x−r₀|`, integrated over an interval
of the same length), hence is `o(|x−r₀|)`. -/
theorem hasDerivAt_intervalIntegral_moving_endpoint {K φ : ℝ → ℝ} {r₀ δ : ℝ} {C : NNReal}
    (hδ : 0 < δ) (hK : Continuous K) (hφ : Continuous φ)
    (hKlip : LipschitzOnWith C K (Icc (-δ) δ)) :
    HasDerivAt (fun x => ∫ t in r₀..x, K (x - t) * φ t) (K 0 * φ r₀) r₀ := by
  -- split off the constant part of the kernel
  set R : ℝ → ℝ := fun x => ∫ t in r₀..x, (K (x - t) - K 0) * φ t with hR_def
  have hsplit : ∀ x : ℝ, (∫ t in r₀..x, K (x - t) * φ t)
      = K 0 * (∫ t in r₀..x, φ t) + R x := by
    intro x
    have h1 : IntervalIntegrable (fun t => K 0 * φ t) volume r₀ x := by
      apply Continuous.intervalIntegrable; fun_prop
    have h2 : IntervalIntegrable (fun t => (K (x - t) - K 0) * φ t) volume r₀ x := by
      apply Continuous.intervalIntegrable; fun_prop
    rw [hR_def, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add h1 h2]
    exact intervalIntegral.integral_congr fun t _ => by ring
  -- the constant part: plain FTC
  have hconst : HasDerivAt (fun x => K 0 * ∫ t in r₀..x, φ t) (K 0 * φ r₀) r₀ :=
    (intervalIntegral.integral_hasDerivAt_right (hφ.intervalIntegrable _ _)
      (hφ.stronglyMeasurableAtFilter _ _) hφ.continuousAt).const_mul (K 0)
  -- a uniform bound for `φ` on the unit window around `r₀`
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := r₀ - 1) (b := r₀ + 1)).exists_bound_of_continuousOn
    hφ.continuousOn
  -- the remainder is `O(|x-r₀|²)`
  have hRbound : ∀ x, |x - r₀| ≤ min δ 1 → ‖R x‖ ≤ ((C : ℝ) * M * |x - r₀|) * |x - r₀| := by
    intro x hx
    have hxδ : |x - r₀| ≤ δ := le_trans hx (min_le_left _ _)
    have hx1 : |x - r₀| ≤ 1 := le_trans hx (min_le_right _ _)
    have hle : ∀ t ∈ Ι r₀ x, ‖(K (x - t) - K 0) * φ t‖ ≤ (C : ℝ) * M * |x - r₀| := by
      intro t ht
      have htmem : t ∈ uIcc r₀ x := uIoc_subset_uIcc ht
      -- `t` lies between `r₀` and `x`, so `|x - t| ≤ |x - r₀|`
      have hxt : |x - t| ≤ |x - r₀| := by
        rcases le_total r₀ x with h | h
        · rw [uIcc_of_le h] at htmem
          rw [abs_of_nonneg (by linarith [htmem.2] : (0:ℝ) ≤ x - t),
            abs_of_nonneg (by linarith : (0:ℝ) ≤ x - r₀)]
          linarith [htmem.1]
        · rw [uIcc_of_ge h] at htmem
          rw [abs_of_nonpos (by linarith [htmem.1] : x - t ≤ 0),
            abs_of_nonpos (by linarith : x - r₀ ≤ 0)]
          linarith [htmem.2]
      have hmemwin : x - t ∈ Icc (-δ) δ := abs_le.mp (le_trans hxt hxδ)
      have h0win : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, le_of_lt hδ⟩
      have hKle : ‖K (x - t) - K 0‖ ≤ (C : ℝ) * |x - r₀| := by
        have hd := hKlip.dist_le_mul _ hmemwin _ h0win
        rw [Real.dist_eq, Real.dist_eq, sub_zero] at hd
        calc ‖K (x - t) - K 0‖ = |K (x - t) - K 0| := Real.norm_eq_abs _
          _ ≤ (C : ℝ) * |x - t| := hd
          _ ≤ (C : ℝ) * |x - r₀| := mul_le_mul_of_nonneg_left hxt C.coe_nonneg
      have htIcc : t ∈ Icc (r₀ - 1) (r₀ + 1) := by
        have h1 := abs_le.mp hx1
        rcases le_total r₀ x with h | h
        · rw [uIcc_of_le h] at htmem
          exact ⟨by linarith [htmem.1], by linarith [htmem.2, h1.2]⟩
        · rw [uIcc_of_ge h] at htmem
          exact ⟨by linarith [htmem.1, h1.1], by linarith [htmem.2]⟩
      calc ‖(K (x - t) - K 0) * φ t‖ = ‖K (x - t) - K 0‖ * ‖φ t‖ := norm_mul _ _
        _ ≤ ((C : ℝ) * |x - r₀|) * M :=
            mul_le_mul hKle (hM t htIcc) (norm_nonneg _)
              (mul_nonneg C.coe_nonneg (abs_nonneg _))
        _ = (C : ℝ) * M * |x - r₀| := by ring
    exact intervalIntegral.norm_integral_le_of_norm_le_const hle
  -- ... hence `o(|x-r₀|)`
  have habs_tendsto : Tendsto (fun x : ℝ => |x - r₀|) (𝓝 r₀) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => x - r₀) (𝓝 r₀) (𝓝 0) :=
      (continuous_id.sub continuous_const).tendsto' r₀ 0 (by simp)
    simpa using h.abs
  have hRlittle : R =o[𝓝 r₀] fun x => x - r₀ := by
    rw [isLittleO_iff]
    intro c hc
    have h1 : ∀ᶠ x in 𝓝 r₀, (C : ℝ) * M * |x - r₀| ≤ c := by
      have htend : Tendsto (fun x : ℝ => (C : ℝ) * M * |x - r₀|) (𝓝 r₀) (𝓝 0) := by
        simpa using habs_tendsto.const_mul ((C : ℝ) * M)
      exact htend.eventually (eventually_le_nhds hc)
    have h2 : ∀ᶠ x in 𝓝 r₀, |x - r₀| ≤ min δ 1 :=
      habs_tendsto.eventually (eventually_le_nhds (lt_min hδ one_pos))
    filter_upwards [h1, h2] with x hx1 hx2
    calc ‖R x‖ ≤ ((C : ℝ) * M * |x - r₀|) * |x - r₀| := hRbound x hx2
      _ ≤ c * |x - r₀| := mul_le_mul_of_nonneg_right hx1 (abs_nonneg _)
      _ = c * ‖x - r₀‖ := by rw [Real.norm_eq_abs]
  have hRderiv : HasDerivAt R 0 r₀ := by
    rw [hasDerivAt_iff_isLittleO]
    have hR0 : R r₀ = 0 := by simp [hR_def]
    simpa [hR0] using hRlittle
  have hsum := hconst.add hRderiv
  rw [add_zero] at hsum
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards with x
  exact hsplit x

/-- **MA.16 — Leibniz rule with a variable upper limit AND an `r`-dependent integrand.**

  `d/dr ∫_a^r K(r−t)·φ(t) dt = K 0 · φ r + ∫_a^r K'(r−t)·φ(t) dt`

`K` need only be differentiable **almost everywhere** (with derivative `K'`); the regularity across
the exceptional points is carried by the Lipschitz hypothesis `hKlip` on the window of arguments
`x − t` that occur for `x` within `δ` of `r₀`.  This is what lets a kinked kernel through.

Proof: split `∫_a^r = ∫_a^{r₀} + ∫_{r₀}^r` at the base point and add the two halves above. -/
theorem hasDerivAt_intervalIntegral_convolution {K K' φ : ℝ → ℝ} {a r₀ δ : ℝ} {C : NNReal}
    (hδ : 0 < δ) (har : a ≤ r₀)
    (hK : Continuous K) (hφ : Continuous φ)
    (hK' : ∀ᵐ u, HasDerivAt K (K' u) u) (hK'meas : Measurable K')
    (hKlip : LipschitzOnWith C K (Icc (-δ) (r₀ + δ - a))) :
    HasDerivAt (fun x => ∫ t in a..x, K (x - t) * φ t)
      (K 0 * φ r₀ + ∫ t in a..r₀, K' (r₀ - t) * φ t) r₀ := by
  have hwindow : Icc (r₀ - δ - r₀) (r₀ + δ - a) = Icc (-δ) (r₀ + δ - a) := by
    congr 1; ring
  have hparam : HasDerivAt (fun x => ∫ t in a..r₀, K (x - t) * φ t)
      (∫ t in a..r₀, K' (r₀ - t) * φ t) r₀ :=
    hasDerivAt_intervalIntegral_param hδ har hK hφ hK' hK'meas (by rw [hwindow]; exact hKlip)
  have hmove : HasDerivAt (fun x => ∫ t in r₀..x, K (x - t) * φ t) (K 0 * φ r₀) r₀ :=
    hasDerivAt_intervalIntegral_moving_endpoint hδ hK hφ
      (hKlip.mono (Icc_subset_Icc (le_refl _) (by linarith)))
  have hsum := hparam.add hmove
  rw [add_comm (∫ t in a..r₀, K' (r₀ - t) * φ t) (K 0 * φ r₀)] at hsum
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards with x
  have hi : ∀ p q : ℝ, IntervalIntegrable (fun t => K (x - t) * φ t) volume p q := by
    intro p q; apply Continuous.intervalIntegrable; fun_prop
  exact (intervalIntegral.integral_add_adjacent_intervals (hi a r₀) (hi r₀ x)).symm

end FMSA.Analysis
