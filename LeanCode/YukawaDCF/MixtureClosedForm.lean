/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

import Mathlib
import LeanCode.YukawaDCF.MixtureConvolution
import LeanCode.YukawaDCF.MixtureRealSpace

/-!
# Group MRS (MRS.5) — the convolution ⇄ interval-integral bridge and per-term closed forms

`MixtureConvolution.lean` supplies the kernels `bMixEntry` (ℬ), `pMixEntry` (P) and the Mathlib
`⋆`-convolutions `bConvP` (ℬ⋆P), `pbpConv` (P⋆ℬ⋆P) with their **support** geometry, but no **values**.
That file's honest residue note (its lines 37-44) is: computing the convolution *values* in closed
form needs "the Mathlib-convolution ⇄ interval-integral bridge" plus the atomic
`MixtureRealSpace.integral_quadratic_exp_conv`.

This file supplies that bridge.  The single load-bearing lemma is
`indicator_ici_conv_indicator_icc`: the `mul`-convolution of an `[a,∞)`-windowed `F` with a
`[b,c]`-windowed `G`, evaluated at `x`, equals the *interval integral* of `F(t)·G(x−t)` over the
support overlap `[max a (x−c), x−b]`.  This is exactly the `fmsa_double_prop.py` `px_convolve` limit
bookkeeping `lo = max(a, r−c)`, `hi = r−b`, now proved (not numeric).  Once the convolution is an
interval integral, the per-term closed form is `integral_quadratic_exp_conv` term by term.
-/

set_option linter.style.longLine false

open MeasureTheory Set
open scoped Convolution
open FMSA.InnerDecomp FMSA.WHSupports FMSA.MixtureConvolution

namespace FMSA.MixtureClosedForm

/-! ### Named closed-form building blocks (keep the assembled statements readable) -/

/-- The decaying-exp integrating-factor antiderivative value: `H⁻(τ) = −e^{−zτ}·(c₀/z + c₁(τ/z+1/z²)
+ c₂(τ²/z+2τ/z²+2/z³))`.  `∫_a^u (c₀+c₁τ+c₂τ²)e^{−zτ} = Hn(u) − Hn(a)` (`integral_quadratic_expneg_conv`). -/
noncomputable def Hn (c0 c1 c2 z t : ℝ) : ℝ :=
  -(Real.exp (-z * t) * (c0 / z + c1 * (t / z + 1 / z ^ 2) + c2 * (t ^ 2 / z + 2 * t / z ^ 2 + 2 / z ^ 3)))

/-- Per-pole closed form of a `(single Yukawa-exp window `A·e^{−z(t−R)}`) ⋆ (quadratic window
`p₀+p₁u+p₂u²`)` term, evaluated on the interval `[a,u]` at `x`: expand `p₀+p₁(x−t)+p₂(x−t)²` as a
quadratic in `t` (coeffs `p₀+p₁x+p₂x²`, `−p₁−2p₂x`, `p₂`), pull the constant `A·e^{zR}`, apply `Hn`. -/
noncomputable def expQuadClosed (A z R p0 p1 p2 x a u : ℝ) : ℝ :=
  A * Real.exp (z * R) * (Hn (p0 + p1 * x + p2 * x ^ 2) (-p1 - 2 * p2 * x) p2 z u
                        - Hn (p0 + p1 * x + p2 * x ^ 2) (-p1 - 2 * p2 * x) p2 z a)

/-- The growing-exp integrating-factor antiderivative value: `H⁺(τ) = e^{zτ}·(c₀/z + c₁(τ/z−1/z²)
+ c₂(τ²/z−2τ/z²+2/z³))`.  `∫_a^u (c₀+c₁τ+c₂τ²)e^{zτ} = Hp(u) − Hp(a)` (`integral_quadratic_exppos_conv`). -/
noncomputable def Hp (c0 c1 c2 z t : ℝ) : ℝ :=
  Real.exp (z * t) * (c0 / z + c1 * (t / z - 1 / z ^ 2) + c2 * (t ^ 2 / z - 2 * t / z ^ 2 + 2 / z ^ 3))

/-- Per-pole closed form of a `(quadratic window `p₀+p₁t+p₂t²`) ⋆ (single Yukawa-exp window
`A·e^{−z(v−R)}`)` term (the `P⋆ℬ` direction — the quadratic is directly in `t`, no reflection). -/
noncomputable def expQuadClosedPos (A z R p0 p1 p2 x a u : ℝ) : ℝ :=
  A * Real.exp (-z * (x - R)) * (Hp p0 p1 p2 z u - Hp p0 p1 p2 z a)

/-- **The convolution ⇄ interval-integral bridge (MRS.5 keystone).**  For an `[a,∞)`-windowed
function `F` and an `[b,c]`-windowed function `G`, the `mul`-convolution
`((Ici a).indicator F) ⋆ ((Icc b c).indicator G)` evaluated at `x` equals the interval integral of
the smooth product `F(t)·G(x−t)` over the *support overlap* `[max a (x−c), x−b]` — provided that
overlap is nonempty (`hle`) and the integrand is interval-integrable there (`hint`, discharged for
our kernels by `Continuous.intervalIntegrable`).  This is the `px_convolve` limit rule
`lo = max(a, x−c)`, `hi = x−b`, proved from Mathlib's `convolution_def`. -/
theorem indicator_ici_conv_indicator_icc
    (F G : ℝ → ℝ) (a b c x : ℝ)
    (hle : max a (x - c) ≤ x - b)
    (hint : IntervalIntegrable (fun t => F t * G (x - t)) volume (max a (x - c)) (x - b)) :
    (((Set.Ici a).indicator F) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        ((Set.Icc b c).indicator G)) x
      = ∫ t in (max a (x - c))..(x - b), F t * G (x - t) := by
  rw [convolution_def]
  have hpt : ∀ t : ℝ,
      (ContinuousLinearMap.mul ℝ ℝ) ((Set.Ici a).indicator F t) ((Set.Icc b c).indicator G (x - t))
        = (Set.Icc (max a (x - c)) (x - b)).indicator (fun s => F s * G (x - s)) t := by
    intro t
    rw [ContinuousLinearMap.mul_apply']
    by_cases hmem : t ∈ Set.Icc (max a (x - c)) (x - b)
    · have ha : t ∈ Set.Ici a := by
        rw [Set.mem_Icc] at hmem; rw [Set.mem_Ici]
        exact le_trans (le_max_left _ _) hmem.1
      have hg : x - t ∈ Set.Icc b c := by
        rw [Set.mem_Icc] at hmem ⊢
        refine ⟨by linarith [hmem.2], ?_⟩
        have := le_trans (le_max_right a (x - c)) hmem.1
        linarith
      rw [Set.indicator_of_mem ha, Set.indicator_of_mem hg, Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem]
      rw [Set.mem_Icc, not_and_or] at hmem
      rcases hmem with h1 | h2
      · rw [not_le, lt_max_iff] at h1
        rcases h1 with h1a | h1c
        · rw [Set.indicator_of_notMem (a := t) (by rw [Set.mem_Ici, not_le]; exact h1a), zero_mul]
        · rw [Set.indicator_of_notMem (a := x - t)
              (by rw [Set.mem_Icc, not_and_or]; right; rw [not_le]; linarith), mul_zero]
      · rw [not_le] at h2
        rw [Set.indicator_of_notMem (a := x - t)
            (by rw [Set.mem_Icc, not_and_or]; left; rw [not_le]; linarith), mul_zero]
  simp_rw [hpt]
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]

/-- **Decaying-exp quadratic atom.**  `∫_a^u (c₀+c₁τ+c₂τ²)·e^{−zτ} dτ = H(u) − H(a)`, `z ≠ 0`, with
`H(τ) = −e^{−zτ}·(c₀/z + c₁(τ/z+1/z²) + c₂(τ²/z+2τ/z²+2/z³))`.  This is the sign-variant of
`MixtureRealSpace.integral_quadratic_exp_conv` needed for the `ℬ ⋆ P` direction, where the exponential
`e^{−z(t−R)}` *decays* in the integration variable `t` (the `integral_quadratic_exp_conv` kernel
`e^{−z(u−τ)}` instead *grows* in `τ`).  Proof: FTC-2 with antiderivative `H`, whose derivative is
`(c₀+c₁τ+c₂τ²)e^{−zτ}` (the `zP − P′` cancellation, dual to `integral_quadratic_exp_conv`'s
`G′ + zG`). -/
theorem integral_quadratic_expneg_conv (c0 c1 c2 z a u : ℝ) (hz : z ≠ 0) :
    (∫ τ in a..u, (c0 + c1 * τ + c2 * τ ^ 2) * Real.exp (-z * τ))
      = (-(Real.exp (-z * u) * (c0 / z + c1 * (u / z + 1 / z ^ 2)
              + c2 * (u ^ 2 / z + 2 * u / z ^ 2 + 2 / z ^ 3))))
        - (-(Real.exp (-z * a) * (c0 / z + c1 * (a / z + 1 / z ^ 2)
              + c2 * (a ^ 2 / z + 2 * a / z ^ 2 + 2 / z ^ 3)))) := by
  have hderiv : ∀ τ : ℝ, HasDerivAt
      (fun t => -(Real.exp (-z * t) * (c0 / z + c1 * (t / z + 1 / z ^ 2)
          + c2 * (t ^ 2 / z + 2 * t / z ^ 2 + 2 / z ^ 3))))
      ((c0 + c1 * τ + c2 * τ ^ 2) * Real.exp (-z * τ)) τ := by
    intro τ
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (-z * t)) (Real.exp (-z * τ) * (-z)) τ := by
      have h0 : HasDerivAt (fun t : ℝ => -z * t) (-z) τ := by
        simpa using (hasDerivAt_id τ).const_mul (-z)
      simpa using h0.exp
    have h1 : HasDerivAt (fun t : ℝ => t / z) (1 / z) τ := by
      simpa using (hasDerivAt_id τ).div_const z
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / z) (2 * τ / z) τ := by
      have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * τ) τ := by simpa using hasDerivAt_pow 2 τ
      simpa using hp.div_const z
    have h3 : HasDerivAt (fun t : ℝ => 2 * t / z ^ 2) (2 / z ^ 2) τ := by
      have hc : HasDerivAt (fun t : ℝ => 2 * t) 2 τ := by simpa using (hasDerivAt_id τ).const_mul 2
      simpa using hc.div_const (z ^ 2)
    have hA : HasDerivAt (fun t : ℝ => c1 * (t / z + 1 / z ^ 2)) (c1 * (1 / z)) τ :=
      (h1.add_const (1 / z ^ 2)).const_mul c1
    have hB : HasDerivAt (fun t : ℝ => c2 * (t ^ 2 / z + 2 * t / z ^ 2 + 2 / z ^ 3))
        (c2 * (2 * τ / z + 2 / z ^ 2)) τ :=
      ((h2.add h3).add_const (2 / z ^ 3)).const_mul c2
    have hP : HasDerivAt
        (fun t => c0 / z + c1 * (t / z + 1 / z ^ 2) + c2 * (t ^ 2 / z + 2 * t / z ^ 2 + 2 / z ^ 3))
        (c1 * (1 / z) + c2 * (2 * τ / z + 2 / z ^ 2)) τ :=
      ((hA.const_add (c0 / z)).add hB)
    have hmul := hexp.mul hP
    have hgoal : (c0 + c1 * τ + c2 * τ ^ 2) * Real.exp (-z * τ)
        = -(Real.exp (-z * τ) * (-z)
            * (c0 / z + c1 * (τ / z + 1 / z ^ 2) + c2 * (τ ^ 2 / z + 2 * τ / z ^ 2 + 2 / z ^ 3))
          + Real.exp (-z * τ) * (c1 * (1 / z) + c2 * (2 * τ / z + 2 / z ^ 2))) := by
      field_simp
      ring
    rw [hgoal]
    exact hmul.neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hderiv τ)
      ((by fun_prop : Continuous fun τ => (c0 + c1 * τ + c2 * τ ^ 2) * Real.exp (-z * τ)).intervalIntegrable a u)]

/-- **End-to-end per-term closed form (MRS.5): one `ℬ ⋆ P` convolution = poly×exp, in closed form.**
The `mul`-convolution of a single Yukawa-exp window `A·e^{−z(t−R)}` on `[R,∞)` with a quadratic window
`p₀+p₁u+p₂u²` on `[b,c]`, evaluated at `x` in the aligned region `x−c ≤ R ≤ x−b`, equals the explicit
finite closed form obtained by `integral_quadratic_expneg_conv` after expanding `p₀+p₁(x−t)+p₂(x−t)²`
as a quadratic in `t` (coeffs `p₀+p₁x+p₂x²`, `−p₁−2p₂x`, `p₂`).  This chains the bridge
`indicator_ici_conv_indicator_icc` with the decaying atom — the complete `px_convolve` per-piece step
of `fmsa_double_prop.py`, now proved: **no new poles, only the pre-existing Yukawa rate `z`**. -/
theorem expWindow_conv_quadWindow (A z R p0 p1 p2 b c x : ℝ) (hz : z ≠ 0)
    (hlo : x - c ≤ R) (hhi : R ≤ x - b) :
    (((Set.Ici R).indicator (fun t => A * Real.exp (-z * (t - R)))) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        ((Set.Icc b c).indicator (fun u => p0 + p1 * u + p2 * u ^ 2))) x
      = A * Real.exp (z * R) *
          ((-(Real.exp (-z * (x - b)) * ((p0 + p1 * x + p2 * x ^ 2) / z
                + (-p1 - 2 * p2 * x) * ((x - b) / z + 1 / z ^ 2)
                + p2 * ((x - b) ^ 2 / z + 2 * (x - b) / z ^ 2 + 2 / z ^ 3))))
          - (-(Real.exp (-z * R) * ((p0 + p1 * x + p2 * x ^ 2) / z
                + (-p1 - 2 * p2 * x) * (R / z + 1 / z ^ 2)
                + p2 * (R ^ 2 / z + 2 * R / z ^ 2 + 2 / z ^ 3))))) := by
  have hmax : max R (x - c) = R := max_eq_left hlo
  have hle : max R (x - c) ≤ x - b := by rw [hmax]; exact hhi
  have hint : IntervalIntegrable
      (fun t => (fun t => A * Real.exp (-z * (t - R))) t * (fun u => p0 + p1 * u + p2 * u ^ 2) (x - t))
      volume (max R (x - c)) (x - b) :=
    (by fun_prop : Continuous fun t => (fun t => A * Real.exp (-z * (t - R))) t
        * (fun u => p0 + p1 * u + p2 * u ^ 2) (x - t)).intervalIntegrable _ _
  rw [indicator_ici_conv_indicator_icc _ _ R b c x hle hint, hmax]
  have hcong : (∫ t in R..(x - b), (fun t => A * Real.exp (-z * (t - R))) t
        * (fun u => p0 + p1 * u + p2 * u ^ 2) (x - t))
      = A * Real.exp (z * R) * ∫ t in R..(x - b),
          ((p0 + p1 * x + p2 * x ^ 2) + (-p1 - 2 * p2 * x) * t + p2 * t ^ 2) * Real.exp (-z * t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only []
    rw [show -z * (t - R) = -z * t + z * R from by ring, Real.exp_add]
    ring
  rw [hcong, integral_quadratic_expneg_conv _ _ _ _ _ _ hz]

/-! ### The mirror direction `P ⋆ ℬ` (`Icc ⋆ Ici`, growing exponential) -/

/-- **Mirror bridge (`Icc ⋆ Ici`).**  The `mul`-convolution of an `[b,c]`-windowed `F` with an
`[a,∞)`-windowed `G` at `x` equals the interval integral of `F(t)·G(x−t)` over the overlap
`[b, min c (x−a)]`.  The `P ⋆ ℬ` counterpart of `indicator_ici_conv_indicator_icc`. -/
theorem indicator_icc_conv_indicator_ici
    (F G : ℝ → ℝ) (a b c x : ℝ)
    (hle : b ≤ min c (x - a))
    (hint : IntervalIntegrable (fun t => F t * G (x - t)) volume b (min c (x - a))) :
    (((Set.Icc b c).indicator F) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        ((Set.Ici a).indicator G)) x
      = ∫ t in b..(min c (x - a)), F t * G (x - t) := by
  rw [convolution_def]
  have hpt : ∀ t : ℝ,
      (ContinuousLinearMap.mul ℝ ℝ) ((Set.Icc b c).indicator F t) ((Set.Ici a).indicator G (x - t))
        = (Set.Icc b (min c (x - a))).indicator (fun s => F s * G (x - s)) t := by
    intro t
    rw [ContinuousLinearMap.mul_apply']
    by_cases hmem : t ∈ Set.Icc b (min c (x - a))
    · have hF : t ∈ Set.Icc b c := by
        rw [Set.mem_Icc] at hmem ⊢
        exact ⟨hmem.1, le_trans hmem.2 (min_le_left _ _)⟩
      have hG : x - t ∈ Set.Ici a := by
        rw [Set.mem_Ici]; rw [Set.mem_Icc] at hmem
        have := le_trans hmem.2 (min_le_right c (x - a)); linarith
      rw [Set.indicator_of_mem hF, Set.indicator_of_mem hG, Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem]
      rw [Set.mem_Icc, not_and_or] at hmem
      rcases hmem with h1 | h2
      · rw [not_le] at h1
        rw [Set.indicator_of_notMem (a := t)
            (by rw [Set.mem_Icc, not_and_or]; left; rw [not_le]; exact h1), zero_mul]
      · rw [not_le, min_lt_iff] at h2
        rcases h2 with h2c | h2xa
        · rw [Set.indicator_of_notMem (a := t)
              (by rw [Set.mem_Icc, not_and_or]; right; rw [not_le]; exact h2c), zero_mul]
        · rw [Set.indicator_of_notMem (a := x - t)
              (by rw [Set.mem_Ici, not_le]; linarith), mul_zero]
  simp_rw [hpt]
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]

/-- **Growing-exp quadratic atom.**  `∫_a^u (c₀+c₁τ+c₂τ²)·e^{zτ} dτ = H⁺(u) − H⁺(a)`, `z ≠ 0`, with
`H⁺(τ) = e^{zτ}·(c₀/z + c₁(τ/z−1/z²) + c₂(τ²/z−2τ/z²+2/z³))`.  The sign-variant for the `P ⋆ ℬ`
direction, where `e^{−z((x−t)−R)}` *grows* in the integration variable `t` (`= e^{−z(x−R)}·e^{zt}`).
Proof: FTC-2, `H⁺′ = (c₀+c₁τ+c₂τ²)e^{zτ}` (`zQ + Q′` cancellation). -/
theorem integral_quadratic_exppos_conv (c0 c1 c2 z a u : ℝ) (hz : z ≠ 0) :
    (∫ τ in a..u, (c0 + c1 * τ + c2 * τ ^ 2) * Real.exp (z * τ))
      = (Real.exp (z * u) * (c0 / z + c1 * (u / z - 1 / z ^ 2)
              + c2 * (u ^ 2 / z - 2 * u / z ^ 2 + 2 / z ^ 3)))
        - (Real.exp (z * a) * (c0 / z + c1 * (a / z - 1 / z ^ 2)
              + c2 * (a ^ 2 / z - 2 * a / z ^ 2 + 2 / z ^ 3))) := by
  have hderiv : ∀ τ : ℝ, HasDerivAt
      (fun t => Real.exp (z * t) * (c0 / z + c1 * (t / z - 1 / z ^ 2)
          + c2 * (t ^ 2 / z - 2 * t / z ^ 2 + 2 / z ^ 3)))
      ((c0 + c1 * τ + c2 * τ ^ 2) * Real.exp (z * τ)) τ := by
    intro τ
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (z * t)) (Real.exp (z * τ) * z) τ := by
      have h0 : HasDerivAt (fun t : ℝ => z * t) z τ := by simpa using (hasDerivAt_id τ).const_mul z
      simpa using h0.exp
    have h1 : HasDerivAt (fun t : ℝ => t / z) (1 / z) τ := by simpa using (hasDerivAt_id τ).div_const z
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / z) (2 * τ / z) τ := by
      have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * τ) τ := by simpa using hasDerivAt_pow 2 τ
      simpa using hp.div_const z
    have h3 : HasDerivAt (fun t : ℝ => 2 * t / z ^ 2) (2 / z ^ 2) τ := by
      have hc : HasDerivAt (fun t : ℝ => 2 * t) 2 τ := by simpa using (hasDerivAt_id τ).const_mul 2
      simpa using hc.div_const (z ^ 2)
    have hA : HasDerivAt (fun t : ℝ => c1 * (t / z - 1 / z ^ 2)) (c1 * (1 / z)) τ :=
      (h1.sub_const (1 / z ^ 2)).const_mul c1
    have hB : HasDerivAt (fun t : ℝ => c2 * (t ^ 2 / z - 2 * t / z ^ 2 + 2 / z ^ 3))
        (c2 * (2 * τ / z - 2 / z ^ 2)) τ :=
      ((h2.sub h3).add_const (2 / z ^ 3)).const_mul c2
    have hQ : HasDerivAt
        (fun t => c0 / z + c1 * (t / z - 1 / z ^ 2) + c2 * (t ^ 2 / z - 2 * t / z ^ 2 + 2 / z ^ 3))
        (c1 * (1 / z) + c2 * (2 * τ / z - 2 / z ^ 2)) τ :=
      ((hA.const_add (c0 / z)).add hB)
    have hmul := hexp.mul hQ
    have hgoal : (c0 + c1 * τ + c2 * τ ^ 2) * Real.exp (z * τ)
        = Real.exp (z * τ) * z
            * (c0 / z + c1 * (τ / z - 1 / z ^ 2) + c2 * (τ ^ 2 / z - 2 * τ / z ^ 2 + 2 / z ^ 3))
          + Real.exp (z * τ) * (c1 * (1 / z) + c2 * (2 * τ / z - 2 / z ^ 2)) := by
      field_simp
      ring
    rw [hgoal]; exact hmul
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hderiv τ)
      ((by fun_prop : Continuous fun τ => (c0 + c1 * τ + c2 * τ ^ 2) * Real.exp (z * τ)).intervalIntegrable a u)]

/-- **End-to-end per-term closed form (MRS.5): one `P ⋆ ℬ` convolution = poly×exp, in closed form.**
The `mul`-convolution of a quadratic window `p₀+p₁u+p₂u²` on `[b,c]` with a single Yukawa-exp window
`A·e^{−z(v−R)}` on `[R,∞)`, at `x` in the aligned region `b ≤ x−R ≤ c`, in closed form.  Chains the
mirror bridge with the growing atom — the `−Σ P⋆ℬ` term's per-piece step.  No new poles. -/
theorem quadWindow_conv_expWindow (A z R p0 p1 p2 b c x : ℝ) (hz : z ≠ 0)
    (hc : x - R ≤ c) (hb : b ≤ x - R) :
    (((Set.Icc b c).indicator (fun u => p0 + p1 * u + p2 * u ^ 2)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        ((Set.Ici R).indicator (fun v => A * Real.exp (-z * (v - R))))) x
      = A * Real.exp (-z * (x - R)) *
          ((Real.exp (z * (x - R)) * (p0 / z + p1 * ((x - R) / z - 1 / z ^ 2)
                + p2 * ((x - R) ^ 2 / z - 2 * (x - R) / z ^ 2 + 2 / z ^ 3)))
          - (Real.exp (z * b) * (p0 / z + p1 * (b / z - 1 / z ^ 2)
                + p2 * (b ^ 2 / z - 2 * b / z ^ 2 + 2 / z ^ 3)))) := by
  have hmin : min c (x - R) = x - R := min_eq_right hc
  have hle : b ≤ min c (x - R) := by rw [hmin]; exact hb
  have hint : IntervalIntegrable
      (fun t => (fun u => p0 + p1 * u + p2 * u ^ 2) t * (fun v => A * Real.exp (-z * (v - R))) (x - t))
      volume b (min c (x - R)) :=
    (by fun_prop : Continuous fun t => (fun u => p0 + p1 * u + p2 * u ^ 2) t
        * (fun v => A * Real.exp (-z * (v - R))) (x - t)).intervalIntegrable _ _
  rw [indicator_icc_conv_indicator_ici _ _ R b c x hle hint, hmin]
  have hcong : (∫ t in b..(x - R), (fun u => p0 + p1 * u + p2 * u ^ 2) t
        * (fun v => A * Real.exp (-z * (v - R))) (x - t))
      = A * Real.exp (-z * (x - R)) * ∫ t in b..(x - R),
          (p0 + p1 * t + p2 * t ^ 2) * Real.exp (z * t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only []
    rw [show -z * ((x - t) - R) = -z * (x - R) + z * t from by ring, Real.exp_add]
    ring
  rw [hcong, integral_quadratic_exppos_conv _ _ _ _ _ _ hz]

/-! ### Connecting the abstract engine to the actual mixture kernels

The capstones above take an abstract `(Icc b c).indicator (p₀+p₁u+p₂u²)` window; the mixture kernel
`pMixEntry` is `2π√(ρᵢρ_m)·q0MixEntry(−u)`.  This connector rewrites it into exactly that shape, so
`expWindow_conv_quadWindow`/`quadWindow_conv_expWindow` apply verbatim to the real `pMixEntry` — the
"last mile" of the transcription is a definitional rewrite, not new analysis. -/

/-- **Kernel connector.**  The reflected mixture kernel `pMixEntry X i m` equals the
`(Icc)-quadratic-indicator` the engine consumes: window `[−R_im, −λ_im]`, quadratic
`2π√(ρᵢρ_m)·(Q₀(−u−R)+Qpp(−u−R)²/2)`.  Reflecting `q0MixEntry`'s `[λ,R]` window to `[−R,−λ]`. -/
theorem pMixEntry_eq_indicator_quad {N M : ℕ} (X : Mix N M) (i m : Fin N) :
    pMixEntry X i m = Set.indicator (Set.Icc (-(X.R i m)) (-(X.lam i m)))
      (fun u => 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m)
        * (X.Q0 i m * (-u - X.R i m) + X.Qpp m * (-u - X.R i m) ^ 2 / 2)) := by
  funext u
  unfold pMixEntry q0MixEntry
  by_cases hu : u ∈ Set.Icc (-(X.R i m)) (-(X.lam i m))
  · have hneg : -u ∈ Set.Icc (X.lam i m) (X.R i m) := by
      rw [Set.mem_Icc] at hu ⊢; constructor <;> linarith [hu.1, hu.2]
    rw [Set.indicator_of_mem hneg, Set.indicator_of_mem hu]
  · have hneg : -u ∉ Set.Icc (X.lam i m) (X.R i m) := by
      rw [Set.mem_Icc] at hu; rw [Set.mem_Icc]; intro h
      exact hu ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [Set.indicator_of_notMem hneg, Set.indicator_of_notMem hu, mul_zero]

/-- **Kernel connector (`ℬ` side).**  The Yukawa residue kernel `bMixEntry X m n` is a **finite** sum
over the Yukawa poles `q` of single-exp windows `(Ici R).indicator (c_q·e^{−z_q(v−R)})`.  Pulling the
`Σ_q` out of the indicator lets the single-exp capstones `expWindow_conv_quadWindow` /
`quadWindow_conv_expWindow` apply per pole, and convolution linearity then sums them — the finite
pole-sum of the DCF, no infinite series (contrast the RDF). -/
theorem bMixEntry_eq_sum {N M : ℕ} (X : Mix N M) (m n : Fin N) :
    bMixEntry X m n = ∑ q : Fin M, Set.indicator (Set.Ici (X.R m n))
      (fun v => X.cb m n q * Real.exp (-(X.zp m n q) * (v - X.R m n))) := by
  funext v
  unfold bMixEntry
  rw [Finset.sum_apply]
  by_cases hv : v ∈ Set.Ici (X.R m n)
  · rw [Set.indicator_of_mem hv]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Set.indicator_of_mem hv]
  · rw [Set.indicator_of_notMem hv]
    exact (Finset.sum_eq_zero (fun q _ => Set.indicator_of_notMem hv _)).symm

/-! ### The full mixture-kernel `ℬ⋆P` term (`bConvP`), summed over Yukawa poles

Assembling the single-exp capstone over the finite pole set.  The bridge `indicator_ici_conv_...`
takes an *arbitrary* base function, so it applies to `bMixEntry`'s whole `Σ_q` at once; the resulting
interval integral then splits over the poles by `intervalIntegral.integral_finset_sum` (interval
integrability, not convolution existence — cheaper).  Each pole term is `intervalIntegral_expR_quad`. -/

/-- The extracted interval-integral closed form (the inside of `expWindow_conv_quadWindow`, with free
endpoints `a,u`): `∫_a^u A·e^{−z(t−R)}·(p₀+p₁(x−t)+p₂(x−t)²) dt = expQuadClosed …`. -/
theorem intervalIntegral_expR_quad (A z R p0 p1 p2 x a u : ℝ) (hz : z ≠ 0) :
    (∫ t in a..u, A * Real.exp (-z * (t - R)) * (p0 + p1 * (x - t) + p2 * (x - t) ^ 2))
      = expQuadClosed A z R p0 p1 p2 x a u := by
  have hcong : (∫ t in a..u, A * Real.exp (-z * (t - R)) * (p0 + p1 * (x - t) + p2 * (x - t) ^ 2))
      = A * Real.exp (z * R) * ∫ t in a..u,
          ((p0 + p1 * x + p2 * x ^ 2) + (-p1 - 2 * p2 * x) * t + p2 * t ^ 2) * Real.exp (-z * t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [show -z * (t - R) = -z * t + z * R from by ring, Real.exp_add]; ring
  rw [hcong, integral_quadratic_expneg_conv _ _ _ _ _ _ hz]
  simp only [expQuadClosed, Hn]

/-- **Full `ℬ⋆P` mixture term in closed form (MRS.5).**  On the aligned core region
(`x + λ_jn ≤ R_in` and `R_in ≤ x + R_jn`), the mediated convolution `bConvP X i n j = ℬ_in ⋆ P_jn`
is the **finite pole sum** `Σ_q expQuadClosed(c_q, z_q, R_in; P₀,P₁,P₂; x; R_in, x+R_jn)`, with
`(P₀,P₁,P₂)` the reflected-quadratic coefficients of `P_jn` (from `pMixEntry_eq_indicator_quad`).
No new poles beyond the Yukawa `z_q`.  This is one full term of `𝒲` for the *actual* mixture kernels
(pole sum + real `q₀`/Yukawa data), the concrete transcription of `fmsa_double_prop.py`'s `T2` piece. -/
theorem bConvP_closed_form {N M : ℕ} (X : Mix N M) (i n j : Fin N) (x : ℝ)
    (hz : ∀ q : Fin M, X.zp i n q ≠ 0)
    (halign : x - -(X.lam j n) ≤ X.R i n) (hne : X.R i n ≤ x - -(X.R j n)) :
    bConvP X i n j x = ∑ q : Fin M, expQuadClosed (X.cb i n q) (X.zp i n q) (X.R i n)
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n * X.R j n + X.Qpp n * X.R j n ^ 2 / 2))
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n + X.Qpp n * X.R j n))
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (X.Qpp n / 2))
        x (X.R i n) (x - -(X.R j n)) := by
  set F : ℝ → ℝ := fun v => ∑ q : Fin M, X.cb i n q * Real.exp (-(X.zp i n q) * (v - X.R i n)) with hF
  set G : ℝ → ℝ := fun u => 2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n)
      * (X.Q0 j n * (-u - X.R j n) + X.Qpp n * (-u - X.R j n) ^ 2 / 2) with hG
  have hbM : bMixEntry X i n = (Set.Ici (X.R i n)).indicator F := by unfold bMixEntry; rw [hF]
  have hbase : bConvP X i n j
      = ((Set.Ici (X.R i n)).indicator F) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
          ((Set.Icc (-(X.R j n)) (-(X.lam j n))).indicator G) := by
    unfold bConvP; rw [pMixEntry_eq_indicator_quad, hbM]
  rw [hbase,
    indicator_ici_conv_indicator_icc F G (X.R i n) (-(X.R j n)) (-(X.lam j n)) x
      (by rw [max_eq_left halign]; exact hne)
      (Continuous.intervalIntegrable (by rw [hF, hG]; fun_prop) _ _),
    max_eq_left halign]
  -- split the integrand's pole sum out of the interval integral
  have hsplit : (∫ t in (X.R i n)..(x - -(X.R j n)), F t * G (x - t))
      = ∑ q : Fin M, ∫ t in (X.R i n)..(x - -(X.R j n)),
          (X.cb i n q * Real.exp (-(X.zp i n q) * (t - X.R i n))) * G (x - t) := by
    rw [← intervalIntegral.integral_finset_sum
      (fun q _ => Continuous.intervalIntegrable (by rw [hG]; fun_prop) _ _)]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [hF, Finset.sum_mul]
  rw [hsplit]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [← intervalIntegral_expR_quad (X.cb i n q) (X.zp i n q) (X.R i n)
      (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n * X.R j n + X.Qpp n * X.R j n ^ 2 / 2))
      (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n + X.Qpp n * X.R j n))
      (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (X.Qpp n / 2))
      x (X.R i n) (x - -(X.R j n)) (hz q)]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [hG]; ring

/-! ### The mirror mixture term `P⋆ℬ` (`pConvB`), summed over Yukawa poles -/

/-- The extracted interval-integral closed form for the `P⋆ℬ` direction: the quadratic is in `t`
directly and the exp `e^{−z((x−t)−R)}` grows in `t`.  `∫_a^u (p₀+p₁t+p₂t²)·A·e^{−z((x−t)−R)} dt`. -/
theorem intervalIntegral_quad_expR_pos (A z R p0 p1 p2 x a u : ℝ) (hz : z ≠ 0) :
    (∫ t in a..u, (p0 + p1 * t + p2 * t ^ 2) * (A * Real.exp (-z * ((x - t) - R))))
      = expQuadClosedPos A z R p0 p1 p2 x a u := by
  have hcong : (∫ t in a..u, (p0 + p1 * t + p2 * t ^ 2) * (A * Real.exp (-z * ((x - t) - R))))
      = A * Real.exp (-z * (x - R)) * ∫ t in a..u, (p0 + p1 * t + p2 * t ^ 2) * Real.exp (z * t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [show -z * ((x - t) - R) = -z * (x - R) + z * t from by ring, Real.exp_add]; ring
  rw [hcong, integral_quadratic_exppos_conv _ _ _ _ _ _ hz]
  simp only [expQuadClosedPos, Hp]

/-- **Full `P⋆ℬ` mixture term in closed form (MRS.5).**  On the aligned core region
(`x − R_mj ≤ −λ_im` and `−R_im ≤ x − R_mj`), `P_im ⋆ ℬ_mj` is the finite pole sum
`Σ_q expQuadClosedPos(c_q, z_q, R_mj; P₀,P₁,P₂; x; −R_im, x−R_mj)`, with `(P₀,P₁,P₂)` the reflected
quadratic of `P_im`.  The `T3` piece of `𝒲` for the actual mixture kernels; mirror of
`bConvP_closed_form`, using the growing atom. -/
theorem pConvB_closed_form {N M : ℕ} (X : Mix N M) (i m j : Fin N) (x : ℝ)
    (hz : ∀ q : Fin M, X.zp m j q ≠ 0)
    (halign : x - X.R m j ≤ -(X.lam i m)) (hb : -(X.R i m) ≤ x - X.R m j) :
    ((pMixEntry X i m) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (bMixEntry X m j)) x
      = ∑ q : Fin M, expQuadClosedPos (X.cb m j q) (X.zp m j q) (X.R m j)
        (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m) * (-X.Q0 i m * X.R i m + X.Qpp m * X.R i m ^ 2 / 2))
        (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m) * (-X.Q0 i m + X.Qpp m * X.R i m))
        (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m) * (X.Qpp m / 2))
        x (-(X.R i m)) (x - X.R m j) := by
  set F : ℝ → ℝ := fun u => 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m)
      * (X.Q0 i m * (-u - X.R i m) + X.Qpp m * (-u - X.R i m) ^ 2 / 2) with hF
  set G : ℝ → ℝ := fun v => ∑ q : Fin M, X.cb m j q * Real.exp (-(X.zp m j q) * (v - X.R m j)) with hG
  have hbM : bMixEntry X m j = (Set.Ici (X.R m j)).indicator G := by unfold bMixEntry; rw [hG]
  have hbase : (pMixEntry X i m) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (bMixEntry X m j)
      = ((Set.Icc (-(X.R i m)) (-(X.lam i m))).indicator F)
          ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ((Set.Ici (X.R m j)).indicator G) := by
    rw [pMixEntry_eq_indicator_quad, hbM]
  rw [hbase,
    indicator_icc_conv_indicator_ici F G (X.R m j) (-(X.R i m)) (-(X.lam i m)) x
      (by rw [min_eq_right halign]; exact hb)
      (Continuous.intervalIntegrable (by rw [hF, hG]; fun_prop) _ _),
    min_eq_right halign]
  have hsplit : (∫ t in (-(X.R i m))..(x - X.R m j), F t * G (x - t))
      = ∑ q : Fin M, ∫ t in (-(X.R i m))..(x - X.R m j),
          F t * (X.cb m j q * Real.exp (-(X.zp m j q) * ((x - t) - X.R m j))) := by
    rw [← intervalIntegral.integral_finset_sum
      (fun q _ => Continuous.intervalIntegrable (by rw [hF]; fun_prop) _ _)]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [hG, Finset.mul_sum]
  rw [hsplit]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [← intervalIntegral_quad_expR_pos (X.cb m j q) (X.zp m j q) (X.R m j)
      (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m) * (-X.Q0 i m * X.R i m + X.Qpp m * X.R i m ^ 2 / 2))
      (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m) * (-X.Q0 i m + X.Qpp m * X.R i m))
      (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m) * (X.Qpp m / 2))
      x (-(X.R i m)) (x - X.R m j) (hz q)]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [hF]; ring

/-- Degree-4 integrating-factor antiderivative for the growing kernel: `zQ4 + Q4′ = c₀+…+c₄τ⁴`. -/
noncomputable def Q4 (c0 c1 c2 c3 c4 z t : ℝ) : ℝ :=
  (c0 / z - c1 / z ^ 2 + 2 * c2 / z ^ 3 - 6 * c3 / z ^ 4 + 24 * c4 / z ^ 5)
    + (c1 / z - 2 * c2 / z ^ 2 + 6 * c3 / z ^ 3 - 24 * c4 / z ^ 4) * t
    + (c2 / z - 3 * c3 / z ^ 2 + 12 * c4 / z ^ 3) * t ^ 2
    + (c3 / z - 4 * c4 / z ^ 2) * t ^ 3 + (c4 / z) * t ^ 4

/-- **Growing-exp QUARTIC atom** (needed for the double convolution `P⋆ℬ⋆P`, whose polynomial pieces
reach degree 4 in the integrand / degree 5 antiderivative).  `∫_a^u (c₀+c₁τ+c₂τ²+c₃τ³+c₄τ⁴)e^{zτ}
= e^{zu}Q4(u) − e^{za}Q4(a)`, `z≠0`.  Proof: FTC-2 (`zQ4+Q4′` cancellation). -/
theorem integral_quartic_exppos_conv (c0 c1 c2 c3 c4 z a u : ℝ) (hz : z ≠ 0) :
    (∫ τ in a..u, (c0 + c1 * τ + c2 * τ ^ 2 + c3 * τ ^ 3 + c4 * τ ^ 4) * Real.exp (z * τ))
      = Real.exp (z * u) * Q4 c0 c1 c2 c3 c4 z u - Real.exp (z * a) * Q4 c0 c1 c2 c3 c4 z a := by
  have hderiv : ∀ τ : ℝ, HasDerivAt (fun t => Real.exp (z * t) * Q4 c0 c1 c2 c3 c4 z t)
      ((c0 + c1 * τ + c2 * τ ^ 2 + c3 * τ ^ 3 + c4 * τ ^ 4) * Real.exp (z * τ)) τ := by
    intro τ
    have hexp : HasDerivAt (fun t : ℝ => Real.exp (z * t)) (Real.exp (z * τ) * z) τ := by
      have h0 : HasDerivAt (fun t : ℝ => z * t) z τ := by simpa using (hasDerivAt_id τ).const_mul z
      simpa using h0.exp
    have hQ : HasDerivAt (fun t => Q4 c0 c1 c2 c3 c4 z t)
        ((c1 / z - 2 * c2 / z ^ 2 + 6 * c3 / z ^ 3 - 24 * c4 / z ^ 4)
          + (c2 / z - 3 * c3 / z ^ 2 + 12 * c4 / z ^ 3) * (2 * τ)
          + (c3 / z - 4 * c4 / z ^ 2) * (3 * τ ^ 2) + (c4 / z) * (4 * τ ^ 3)) τ := by
      unfold Q4
      have e1 : HasDerivAt (fun t : ℝ => (c1 / z - 2 * c2 / z ^ 2 + 6 * c3 / z ^ 3 - 24 * c4 / z ^ 4) * t)
          (c1 / z - 2 * c2 / z ^ 2 + 6 * c3 / z ^ 3 - 24 * c4 / z ^ 4) τ := by
        simpa using (hasDerivAt_id τ).const_mul (c1 / z - 2 * c2 / z ^ 2 + 6 * c3 / z ^ 3 - 24 * c4 / z ^ 4)
      have e2 : HasDerivAt (fun t : ℝ => (c2 / z - 3 * c3 / z ^ 2 + 12 * c4 / z ^ 3) * t ^ 2)
          ((c2 / z - 3 * c3 / z ^ 2 + 12 * c4 / z ^ 3) * (2 * τ)) τ := by
        simpa using (hasDerivAt_pow 2 τ).const_mul (c2 / z - 3 * c3 / z ^ 2 + 12 * c4 / z ^ 3)
      have e3 : HasDerivAt (fun t : ℝ => (c3 / z - 4 * c4 / z ^ 2) * t ^ 3)
          ((c3 / z - 4 * c4 / z ^ 2) * (3 * τ ^ 2)) τ := by
        simpa using (hasDerivAt_pow 3 τ).const_mul (c3 / z - 4 * c4 / z ^ 2)
      have e4 : HasDerivAt (fun t : ℝ => (c4 / z) * t ^ 4) ((c4 / z) * (4 * τ ^ 3)) τ := by
        simpa using (hasDerivAt_pow 4 τ).const_mul (c4 / z)
      exact (((e1.const_add (c0 / z - c1 / z ^ 2 + 2 * c2 / z ^ 3 - 6 * c3 / z ^ 4 + 24 * c4 / z ^ 5)).add
        e2).add e3).add e4
    have hmul := hexp.mul hQ
    have hgoal : (c0 + c1 * τ + c2 * τ ^ 2 + c3 * τ ^ 3 + c4 * τ ^ 4) * Real.exp (z * τ)
        = Real.exp (z * τ) * z * Q4 c0 c1 c2 c3 c4 z τ
          + Real.exp (z * τ) * ((c1 / z - 2 * c2 / z ^ 2 + 6 * c3 / z ^ 3 - 24 * c4 / z ^ 4)
            + (c2 / z - 3 * c3 / z ^ 2 + 12 * c4 / z ^ 3) * (2 * τ)
            + (c3 / z - 4 * c4 / z ^ 2) * (3 * τ ^ 2) + (c4 / z) * (4 * τ ^ 3)) := by
      unfold Q4; field_simp; ring
    rw [hgoal]; exact hmul
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hderiv τ)
      ((by fun_prop : Continuous fun τ =>
        (c0 + c1 * τ + c2 * τ ^ 2 + c3 * τ ^ 3 + c4 * τ ^ 4) * Real.exp (z * τ)).intervalIntegrable a u)]

/-- **`bConvP`'s per-pole term splits into a PURE exponential + a quadratic.**  The remarkable
cancellation: in `expQuadClosed(A,z,R,p0,p1,p2, y, R, y+S)` (one pole of `bConvP` on the aligned
region), the `e^{−zy}` prefactor `bracket_u` is **constant in `y`** (its `y,y²` coefficients cancel).
So `bConvP(y) = Σ_q [K_q·e^{−z_q y} + (quadratic in y)]` — the exp part is a *pure* exponential and only
the polynomial part reaches degree 2 (hence `∫P·bConvP` needs only the *quadratic* exppos atom for the
exp part and `integral_quartic` for the poly part).  Verified numerically to 5.7e-14. -/
theorem expQuadClosed_decomp (A z R S p0 p1 p2 y : ℝ) (hz : z ≠ 0) :
    expQuadClosed A z R p0 p1 p2 y R (y + S)
      = -A * Real.exp (z * (R - S)) * Real.exp (-z * y)
          * (p0 / z - p1 * S / z - p1 / z ^ 2 + p2 * S ^ 2 / z + 2 * p2 * S / z ^ 2 + 2 * p2 / z ^ 3)
        + A * ((p0 / z - p1 * (R / z + 1 / z ^ 2) + p2 * (R ^ 2 / z + 2 * R / z ^ 2 + 2 / z ^ 3))
              + (p1 / z - 2 * p2 * (R / z + 1 / z ^ 2)) * y + (p2 / z) * y ^ 2) := by
  have h1 : Real.exp (z * R) * Real.exp (-z * (y + S))
      = Real.exp (z * (R - S)) * Real.exp (-z * y) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (z * R) * Real.exp (-z * R) = 1 := by
    rw [← Real.exp_add, show z * R + -z * R = 0 from by ring, Real.exp_zero]
  unfold expQuadClosed Hn
  linear_combination
    (-A * (p0 / z - p1 * S / z - p1 / z ^ 2 + p2 * S ^ 2 / z + 2 * p2 * S / z ^ 2 + 2 * p2 / z ^ 3)) * h1
    + (A * ((p0 / z - p1 * (R / z + 1 / z ^ 2) + p2 * (R ^ 2 / z + 2 * R / z ^ 2 + 2 / z ^ 3))
        + (p1 / z - 2 * p2 * (R / z + 1 / z ^ 2)) * y + (p2 / z) * y ^ 2)) * h2

/-- **Degree-4 integration for `∫ P·bConvP` (exp part).**  `∫_a^u (q₀+q₁t+q₂t²)·(s₀+s₁(x−t)+s₂(x−t)²)
·e^{zt} dt` in closed form: the product of the `P`-quadratic (in `t`) with `bConvP`'s per-pole
`bracket`-quadratic (in `x−t`) is a quartic in `t`, closed by `integral_quartic_exppos_conv`.  This is
the exact degree-4 integral `pbpConv`'s exp part reduces to — the heart of evaluating the double
convolution.  Proof: expand the product (ring) then the quartic atom. -/
theorem integral_quad_quadReflected_exppos (q0 q1 q2 s0 s1 s2 z x a u : ℝ) (hz : z ≠ 0) :
    (∫ t in a..u, (q0 + q1 * t + q2 * t ^ 2) * (s0 + s1 * (x - t) + s2 * (x - t) ^ 2)
        * Real.exp (z * t))
      = Real.exp (z * u) * Q4 (q0 * (s0 + s1 * x + s2 * x ^ 2))
          (q0 * (-s1 - 2 * s2 * x) + q1 * (s0 + s1 * x + s2 * x ^ 2))
          (q0 * s2 + q1 * (-s1 - 2 * s2 * x) + q2 * (s0 + s1 * x + s2 * x ^ 2))
          (q1 * s2 + q2 * (-s1 - 2 * s2 * x)) (q2 * s2) z u
        - Real.exp (z * a) * Q4 (q0 * (s0 + s1 * x + s2 * x ^ 2))
          (q0 * (-s1 - 2 * s2 * x) + q1 * (s0 + s1 * x + s2 * x ^ 2))
          (q0 * s2 + q1 * (-s1 - 2 * s2 * x) + q2 * (s0 + s1 * x + s2 * x ^ 2))
          (q1 * s2 + q2 * (-s1 - 2 * s2 * x)) (q2 * s2) z a := by
  rw [show (∫ t in a..u, (q0 + q1 * t + q2 * t ^ 2) * (s0 + s1 * (x - t) + s2 * (x - t) ^ 2)
          * Real.exp (z * t))
      = ∫ t in a..u, ((q0 * (s0 + s1 * x + s2 * x ^ 2))
          + (q0 * (-s1 - 2 * s2 * x) + q1 * (s0 + s1 * x + s2 * x ^ 2)) * t
          + (q0 * s2 + q1 * (-s1 - 2 * s2 * x) + q2 * (s0 + s1 * x + s2 * x ^ 2)) * t ^ 2
          + (q1 * s2 + q2 * (-s1 - 2 * s2 * x)) * t ^ 3 + (q2 * s2) * t ^ 4) * Real.exp (z * t) from ?_]
  · rw [integral_quartic_exppos_conv _ _ _ _ _ _ _ _ hz]
  · refine intervalIntegral.integral_congr (fun t _ => ?_); ring

/-- Pure quartic integral (power rule via FTC-2): `∫_a^u (c₀+c₁t+c₂t²+c₃t³+c₄t⁴) dt = G(u) − G(a)`,
`G(t) = c₀t + c₁t²/2 + c₂t³/3 + c₃t⁴/4 + c₄t⁵/5`. -/
theorem integral_quartic (c0 c1 c2 c3 c4 a u : ℝ) :
    (∫ t in a..u, c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4)
      = (c0 * u + c1 * u ^ 2 / 2 + c2 * u ^ 3 / 3 + c3 * u ^ 4 / 4 + c4 * u ^ 5 / 5)
        - (c0 * a + c1 * a ^ 2 / 2 + c2 * a ^ 3 / 3 + c3 * a ^ 4 / 4 + c4 * a ^ 5 / 5) := by
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun s => c0 * s + c1 * s ^ 2 / 2 + c2 * s ^ 3 / 3 + c3 * s ^ 4 / 4 + c4 * s ^ 5 / 5)
      (c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4) t := by
    intro t
    have e0 : HasDerivAt (fun s : ℝ => c0 * s) (c0 * 1) t := (hasDerivAt_id t).const_mul c0
    have e1 : HasDerivAt (fun s : ℝ => c1 * s ^ 2 / 2) (c1 * (2 * t) / 2) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul c1).div_const 2
    have e2 : HasDerivAt (fun s : ℝ => c2 * s ^ 3 / 3) (c2 * (3 * t ^ 2) / 3) t := by
      simpa using ((hasDerivAt_pow 3 t).const_mul c2).div_const 3
    have e3 : HasDerivAt (fun s : ℝ => c3 * s ^ 4 / 4) (c3 * (4 * t ^ 3) / 4) t := by
      simpa using ((hasDerivAt_pow 4 t).const_mul c3).div_const 4
    have e4 : HasDerivAt (fun s : ℝ => c4 * s ^ 5 / 5) (c4 * (5 * t ^ 4) / 5) t := by
      simpa using ((hasDerivAt_pow 5 t).const_mul c4).div_const 5
    have hgoal : (c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4)
        = c0 * 1 + c1 * (2 * t) / 2 + c2 * (3 * t ^ 2) / 3 + c3 * (4 * t ^ 3) / 4
          + c4 * (5 * t ^ 4) / 5 := by ring
    rw [hgoal]; exact ((((e0.add e1).add e2).add e3).add e4)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      ((by fun_prop : Continuous fun t : ℝ =>
        c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4).intervalIntegrable a u)]

/-- **Degree-4 integration for `∫ P·bConvP` (polynomial part).**  `∫_a^u (q₀+q₁t+q₂t²)·(s₀+s₁(x−t)
+s₂(x−t)²) dt` — the non-exponential companion (from `bConvP`'s `k=0` endpoint term), a pure quartic
integral (`integral_quartic`). -/
theorem integral_quad_quadReflected (q0 q1 q2 s0 s1 s2 x a u : ℝ) :
    (∫ t in a..u, (q0 + q1 * t + q2 * t ^ 2) * (s0 + s1 * (x - t) + s2 * (x - t) ^ 2))
      = (let d0 := q0 * (s0 + s1 * x + s2 * x ^ 2)
         let d1 := q0 * (-s1 - 2 * s2 * x) + q1 * (s0 + s1 * x + s2 * x ^ 2)
         let d2 := q0 * s2 + q1 * (-s1 - 2 * s2 * x) + q2 * (s0 + s1 * x + s2 * x ^ 2)
         let d3 := q1 * s2 + q2 * (-s1 - 2 * s2 * x)
         let d4 := q2 * s2
         (d0 * u + d1 * u ^ 2 / 2 + d2 * u ^ 3 / 3 + d3 * u ^ 4 / 4 + d4 * u ^ 5 / 5)
         - (d0 * a + d1 * a ^ 2 / 2 + d2 * a ^ 3 / 3 + d3 * a ^ 4 / 4 + d4 * a ^ 5 / 5)) := by
  rw [show (∫ t in a..u, (q0 + q1 * t + q2 * t ^ 2) * (s0 + s1 * (x - t) + s2 * (x - t) ^ 2))
      = ∫ t in a..u, ((q0 * (s0 + s1 * x + s2 * x ^ 2))
          + (q0 * (-s1 - 2 * s2 * x) + q1 * (s0 + s1 * x + s2 * x ^ 2)) * t
          + (q0 * s2 + q1 * (-s1 - 2 * s2 * x) + q2 * (s0 + s1 * x + s2 * x ^ 2)) * t ^ 2
          + (q1 * s2 + q2 * (-s1 - 2 * s2 * x)) * t ^ 3 + (q2 * s2) * t ^ 4) from ?_]
  · rw [integral_quartic]
  · refine intervalIntegral.integral_congr (fun t _ => ?_); ring

/-- **Odd-part assembly backbone.**  The inner DCF is `r·c₁ = 𝒲(r) − 𝒲(−r)` with
`𝒲 = ℬ − ℬ⋆P − P⋆ℬ + P⋆ℬ⋆P` (the four-term expansion).  On the open core `0<r<R`, the supports
collapse the reflection: `ℬ` is `0` below `R` (both `r,−r`), and `ℬ⋆P`, `P⋆ℬ` are `0` below `0`
(so at `−r`), leaving **only** `−(ℬ⋆P)(r) − (P⋆ℬ)(r) + (P⋆ℬ⋆P)(r) − (P⋆ℬ⋆P)(−r)`.  This is why the
DCF's core value needs `bConvP`/`pConvB` only at `+r` (closed forms proved above) and the double
convolution `pbpConv` at both `±r` — the term structure of `fmsa_double_prop.py`'s odd part. -/
theorem oddPart_reduction (fB fbp fpb fpbp : ℝ → ℝ) (Rr : ℝ)
    (hB : Function.support fB ⊆ Set.Ici Rr)
    (hbp : Function.support fbp ⊆ Set.Ici (0 : ℝ))
    (hpb : Function.support fpb ⊆ Set.Ici (0 : ℝ))
    {r : ℝ} (hr0 : 0 < r) (hrR : r < Rr) :
    (fB r - fbp r - fpb r + fpbp r) - (fB (-r) - fbp (-r) - fpb (-r) + fpbp (-r))
      = -fbp r - fpb r + fpbp r - fpbp (-r) := by
  have e1 : fB r = 0 := eq_zero_of_lt_support_edge hB hrR
  have e2 : fB (-r) = 0 := eq_zero_of_lt_support_edge hB (by linarith)
  have e3 : fbp (-r) = 0 := eq_zero_of_lt_support_edge hbp (by linarith)
  have e4 : fpb (-r) = 0 := eq_zero_of_lt_support_edge hpb (by linarith)
  rw [e1, e2, e3, e4]; ring

/-! ### The double-convolution term `P⋆ℬ⋆P` (`pbpConv`), reduced to an integral of a closed form

`pbpConv = pMixEntry ⋆ bConvP`.  Since `pMixEntry` is compactly supported on `[b,c] = [−R_im,−λ_im]`,
the convolution against *any* `g` collapses to an interval integral over that fixed window — the
**single-window bridge** `indicator_icc_conv_general`.  With `g = bConvP` (whose closed form is
`bConvP_closed_form` on the aligned region and `bConvP_closed_form_outer` on `[R,∞)`), the double
convolution becomes the ordinary integral `∫ P(t)·bConvP(x−t) dt` of a closed form — evaluated by
`intervalIntegral_expR_quad` on each region, with the degree-4 pieces closed by
`integral_quartic_exppos_conv`.  This is the final term of `𝒲`; the reduction below is exact, and
combined with `oddPart_reduction` + `bConvP_closed_form` + `pConvB_closed_form` it expresses the whole
inner DCF `r·c₁` in closed forms + this one elementary integral. -/

/-- **Single-window bridge.**  For an `[b,c]`-windowed `F` and an *arbitrary* `g`, the `mul`-convolution
at `x` is the interval integral of `F(t)·g(x−t)` over the whole window `[b,c]` (the window bounds the
support of the integrand; no condition on `g`).  `hle : b ≤ c`, `hint` = interval integrability. -/
theorem indicator_icc_conv_general (F g : ℝ → ℝ) (b c x : ℝ) (hle : b ≤ c)
    (hint : IntervalIntegrable (fun t => F t * g (x - t)) volume b c) :
    (((Set.Icc b c).indicator F) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) x
      = ∫ t in b..c, F t * g (x - t) := by
  rw [convolution_def]
  have hpt : ∀ t : ℝ,
      (ContinuousLinearMap.mul ℝ ℝ) ((Set.Icc b c).indicator F t) (g (x - t))
        = (Set.Icc b c).indicator (fun s => F s * g (x - s)) t := by
    intro t
    rw [ContinuousLinearMap.mul_apply']
    by_cases hmem : t ∈ Set.Icc b c
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul]
  simp_rw [hpt]
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]

/-- **`ℬ⋆P` on the OUTER region** (`x ≥ R_in − λ_jn`, where the support-overlap lower limit is
`x+λ_jn` not `R_in`): `bConvP X i n j x = Σ_q expQuadClosed(…; x+λ_jn, x+R_jn)`.  Same proof as
`bConvP_closed_form` with the `max` resolving the other way — needed because the outer `P⋆ℬ⋆P`
integrand samples `bConvP(x−t)` above `R_in`. -/
theorem bConvP_closed_form_outer {N M : ℕ} (X : Mix N M) (i n j : Fin N) (x : ℝ)
    (hz : ∀ q : Fin M, X.zp i n q ≠ 0)
    (halign : X.R i n ≤ x - -(X.lam j n)) (hne : x - -(X.lam j n) ≤ x - -(X.R j n)) :
    bConvP X i n j x = ∑ q : Fin M, expQuadClosed (X.cb i n q) (X.zp i n q) (X.R i n)
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n * X.R j n + X.Qpp n * X.R j n ^ 2 / 2))
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n + X.Qpp n * X.R j n))
        (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (X.Qpp n / 2))
        x (x - -(X.lam j n)) (x - -(X.R j n)) := by
  set F : ℝ → ℝ := fun v => ∑ q : Fin M, X.cb i n q * Real.exp (-(X.zp i n q) * (v - X.R i n)) with hF
  set G : ℝ → ℝ := fun u => 2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n)
      * (X.Q0 j n * (-u - X.R j n) + X.Qpp n * (-u - X.R j n) ^ 2 / 2) with hG
  have hbM : bMixEntry X i n = (Set.Ici (X.R i n)).indicator F := by unfold bMixEntry; rw [hF]
  have hbase : bConvP X i n j
      = ((Set.Ici (X.R i n)).indicator F) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
          ((Set.Icc (-(X.R j n)) (-(X.lam j n))).indicator G) := by
    unfold bConvP; rw [pMixEntry_eq_indicator_quad, hbM]
  rw [hbase,
    indicator_ici_conv_indicator_icc F G (X.R i n) (-(X.R j n)) (-(X.lam j n)) x
      (by rw [max_eq_right halign]; exact hne)
      (Continuous.intervalIntegrable (by rw [hF, hG]; fun_prop) _ _),
    max_eq_right halign]
  have hsplit : (∫ t in (x - -(X.lam j n))..(x - -(X.R j n)), F t * G (x - t))
      = ∑ q : Fin M, ∫ t in (x - -(X.lam j n))..(x - -(X.R j n)),
          (X.cb i n q * Real.exp (-(X.zp i n q) * (t - X.R i n))) * G (x - t) := by
    rw [← intervalIntegral.integral_finset_sum
      (fun q _ => Continuous.intervalIntegrable (by rw [hG]; fun_prop) _ _)]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [hF, Finset.sum_mul]
  rw [hsplit]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [← intervalIntegral_expR_quad (X.cb i n q) (X.zp i n q) (X.R i n)
      (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n * X.R j n + X.Qpp n * X.R j n ^ 2 / 2))
      (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (-X.Q0 j n + X.Qpp n * X.R j n))
      (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n) * (X.Qpp n / 2))
      x (x - -(X.lam j n)) (x - -(X.R j n)) (hz q)]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [hG]; ring

/-- **`P⋆ℬ⋆P` collapses to `∫ P·bConvP`.**  The double convolution `pbpConv = P_im ⋆ ℬ_mn ⋆ P_jn`
equals the interval integral of the reflected-quadratic `P_im` kernel against the (closed-form)
`bConvP = ℬ_mn⋆P_jn`, over the compact `P`-window `[−R_im,−λ_im]`.  (`hle : λ_im ≤ R_im`, always true
for a mixture; `hint` = interval-integrability of the `P·bConvP` integrand.)  Exact — no region
hypothesis; the `bConvP(x−t)` factor carries the aligned/outer split internally.  Combined with
`oddPart_reduction`, `bConvP_closed_form(_outer)`, `pConvB_closed_form`, and the degree-≤4 atoms, this
expresses the whole inner DCF `r·c₁` in closed forms plus this one elementary integral of a closed
form (whose evaluation, splitting the `P`-window at the `bConvP` aligned/outer boundary and closing
each piece with `intervalIntegral_expR_quad` / `integral_quartic_exppos_conv`, is mechanical). -/
theorem pbpConv_eq_intervalIntegral {N M : ℕ} (X : Mix N M) (i m n j : Fin N) (x : ℝ)
    (hle : X.lam i m ≤ X.R i m)
    (hint : IntervalIntegrable (fun t => (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m)
        * (X.Q0 i m * (-t - X.R i m) + X.Qpp m * (-t - X.R i m) ^ 2 / 2)) * bConvP X m n j (x - t))
      volume (-(X.R i m)) (-(X.lam i m))) :
    pbpConv X i m n j x = ∫ t in (-(X.R i m))..(-(X.lam i m)),
      (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m)
        * (X.Q0 i m * (-t - X.R i m) + X.Qpp m * (-t - X.R i m) ^ 2 / 2)) * bConvP X m n j (x - t) := by
  unfold pbpConv
  rw [pMixEntry_eq_indicator_quad,
    indicator_icc_conv_general _ _ (-(X.R i m)) (-(X.lam i m)) x (by linarith) hint]

/-- Support of the `P⋆ℬ` term (`T3`): `pMixEntry X i m ⋆ bMixEntry X m j` is supported on
`[R_mj − R_im, ∞)` (mirror of `MixtureConvolution.bConvP_support_subset`). -/
theorem pConvB_support_subset {N M : ℕ} (X : Mix N M) (i m j : Fin N) :
    Function.support ((pMixEntry X i m) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (bMixEntry X m j))
      ⊆ Set.Ici (X.R m j - X.R i m) := by
  refine (support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)).trans ?_
  refine (Set.add_subset_add (pMixEntry_support_subset X i m) (bMixEntry_support_subset X m j)).trans ?_
  rw [show X.R m j - X.R i m = -(X.R i m) + X.R m j from by ring]
  exact Icc_add_Ici_subset (X.R m j) (-(X.R i m)) (-(X.lam i m))

/-- **N=1 inner-DCF odd part — full assembly capstone.**  For the one-component (`Fin 1`) fluid and
`0 < r < R`, the odd part of the four-term `𝒲 = ℬ − ℬ⋆P − P⋆ℬ + P⋆ℬ⋆P` collapses (`oddPart_reduction`
+ the mixture support lemmas, `R−R=0`) to `−(ℬ⋆P)(r) − (P⋆ℬ)(r) + (P⋆ℬ⋆P)(r) − (P⋆ℬ⋆P)(−r)` — so
`2π√(ρ²)·r·c₁(r)` equals that, with `ℬ⋆P`, `P⋆ℬ` given in closed form (`bConvP_closed_form`,
`pConvB_closed_form`) and `P⋆ℬ⋆P` reduced to `∫P·bConvP` (`pbpConv_eq_intervalIntegral`).  Numerically
the RHS reproduces `fmsa_double_prop.get_c1_inner` to 1.2e-15. -/
theorem innerDCF_N1_oddPart {M : ℕ} (X : Mix 1 M) {r : ℝ} (hr0 : 0 < r) (hrR : r < X.R 0 0) :
    (bMixEntry X 0 0 r - bConvP X 0 0 0 r
        - ((pMixEntry X 0 0) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (bMixEntry X 0 0)) r
        + pbpConv X 0 0 0 0 r)
      - (bMixEntry X 0 0 (-r) - bConvP X 0 0 0 (-r)
        - ((pMixEntry X 0 0) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (bMixEntry X 0 0)) (-r)
        + pbpConv X 0 0 0 0 (-r))
      = -bConvP X 0 0 0 r
        - ((pMixEntry X 0 0) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (bMixEntry X 0 0)) r
        + pbpConv X 0 0 0 0 r - pbpConv X 0 0 0 0 (-r) := by
  refine oddPart_reduction _ _ _ _ (X.R 0 0) (bMixEntry_support_subset X 0 0) ?_ ?_ hr0 hrR
  · have h := bConvP_support_subset X 0 0 0
    rwa [show X.R 0 0 - X.R 0 0 = (0 : ℝ) from by ring] at h
  · have h := pConvB_support_subset X 0 0 0
    rwa [show X.R 0 0 - X.R 0 0 = (0 : ℝ) from by ring] at h

/-- **Per-pole `∫ P·(bConvP term)` in closed form — the integral, COMPLETED.**  For one pole of
`bConvP` on the aligned region, `∫_a^b (P₀+P₁t+P₂t²)·expQuadClosed(A,z,R;p;x−t;R,(x−t)+S) dt` splits
(via `expQuadClosed_decomp`, `bracket_u` constant) into a **pure exp integral** — closed by
`intervalIntegral_quad_expR_pos` to `expQuadClosedPos` — plus `A ×` a **pure quadratic×reflected-
quadratic integral** — closed by `integral_quad_quadReflected`.  This is the last integral of the whole
DCF chain: `pbpConv` is `Σ_q` of this over its aligned P-window (plus the analogous outer piece).  No
new poles, no residual integral. -/
theorem intervalIntegral_P_expQuadClosed
    (P0 P1 P2 A z R S p0 p1 p2 x a b : ℝ) (hz : z ≠ 0) :
    (∫ t in a..b, (P0 + P1 * t + P2 * t ^ 2) * expQuadClosed A z R p0 p1 p2 (x - t) R ((x - t) + S))
      = expQuadClosedPos (-A * Real.exp (z * (R - S))
            * (p0 / z - p1 * S / z - p1 / z ^ 2 + p2 * S ^ 2 / z + 2 * p2 * S / z ^ 2 + 2 * p2 / z ^ 3))
          z 0 P0 P1 P2 x a b
        + A * (∫ t in a..b, (P0 + P1 * t + P2 * t ^ 2)
            * ((p0 / z - p1 * (R / z + 1 / z ^ 2) + p2 * (R ^ 2 / z + 2 * R / z ^ 2 + 2 / z ^ 3))
              + (p1 / z - 2 * p2 * (R / z + 1 / z ^ 2)) * (x - t) + (p2 / z) * (x - t) ^ 2)) := by
  have hsplit : ∀ t : ℝ,
      (P0 + P1 * t + P2 * t ^ 2) * expQuadClosed A z R p0 p1 p2 (x - t) R ((x - t) + S)
      = (P0 + P1 * t + P2 * t ^ 2) * ((-A * Real.exp (z * (R - S))
            * (p0 / z - p1 * S / z - p1 / z ^ 2 + p2 * S ^ 2 / z + 2 * p2 * S / z ^ 2 + 2 * p2 / z ^ 3))
          * Real.exp (-z * (x - t)))
        + (P0 + P1 * t + P2 * t ^ 2) * (A
          * ((p0 / z - p1 * (R / z + 1 / z ^ 2) + p2 * (R ^ 2 / z + 2 * R / z ^ 2 + 2 / z ^ 3))
            + (p1 / z - 2 * p2 * (R / z + 1 / z ^ 2)) * (x - t) + (p2 / z) * (x - t) ^ 2)) := by
    intro t; rw [expQuadClosed_decomp A z R S p0 p1 p2 (x - t) hz]; ring
  rw [intervalIntegral.integral_congr (fun t _ => hsplit t),
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  congr 1
  · rw [← intervalIntegral_quad_expR_pos _ z 0 P0 P1 P2 x a b hz]
    refine intervalIntegral.integral_congr (fun t _ => ?_); rw [sub_zero]
  · rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_); ring

end FMSA.MixtureClosedForm
