/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.YukawaOZMix.MixtureConvolution
import LeanCode.YukawaOZMix.MixtureClosedForm

/-!
# Zeroth-order (hard-sphere) mixture DCF — reusing the PY-Baxter convolution machinery

The first-order DCF is the finite closed form `𝒞 = 𝒬⁻ ⋆ ℬ ⋆ (𝒬⁻)ᵀ` (Group MRS, `MixtureConvolution`
+ `MixtureDCFSmooth`, done).  The **zeroth-order** HS DCF `c^HS_ij` is the real-space image of
`Cmix0 = I − Q̂₀(k)·Q̂₀ᵀ(−k)` (`MixtureRealSpace.Cmix0`, MRS.6): the same PY-Baxter factor, one power
lower and **without the Yukawa kernel `ℬ`**.  This file builds the load-bearing convolution term with
the **existing** machinery (`WHSupports.q0MixEntry`, `MixtureConvolution.pMixEntry`, Mathlib's real
convolution `⋆`) rather than re-deriving anything.

The key structural point: `Q̂₀(k)·Q̂₀ᵀ(−k)` is **forward × reflected**, so its `(i,n),(j,n)` term is
`𝒬_in ⋆ (𝒬⁻)_jn` = `qFwd ⋆ pMixEntry`.  Its support edges are `λᵢₙ − Rⱼₙ = −Rᵢⱼ` and
`Rᵢₙ − λⱼₙ = Rᵢⱼ` — the intermediate species `n` **cancels** (exactly as `bConvP`'s `R_in − R_jn =
−λ_ij`), giving support `[−Rᵢⱼ, Rᵢⱼ]`.  (The both-reflected `pMixEntry ⋆ pMixEntry` does NOT cancel
`σₙ` — it is the wrong object; the forward factor is essential.)

Status: ✓ axiom-clean.  This is the zeroth-order backbone; the full `c^HS` assembly (delta cross-terms
+ odd part) builds on it.
-/

open MeasureTheory Set
open scoped Convolution Pointwise

namespace FMSA.MixtureHSDCF

open FMSA.InnerDecomp FMSA.WHSupports FMSA.MixtureConvolution FMSA.MixtureClosedForm

noncomputable section

variable {N M : ℕ}

/-- Minkowski arithmetic: `[a,b] + [c,d] ⊆ [a+c, b+d]`. -/
theorem Icc_add_Icc_subset (a b c d : ℝ) :
    Set.Icc a b + Set.Icc c d ⊆ Set.Icc (a + c) (b + d) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hz
  rw [Set.mem_Icc] at hx hy ⊢
  exact ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩

/-- **Forward `𝒬`-kernel (non-delta part)** `2π√(ρᵢρₘ)·q₀ᵢₘ(u)`, supported on `[λᵢₘ, Rᵢₘ]` — the
un-reflected counterpart of `pMixEntry` (`= 𝒬⁻` non-delta, supported on `[−Rᵢₘ, −λᵢₘ]`). -/
noncomputable def qFwd (X : Mix N M) (i m : Fin N) (u : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m) * q0MixEntry X i m u

theorem qFwd_support_subset (X : Mix N M) (i m : Fin N) :
    Function.support (qFwd X i m) ⊆ Set.Icc (X.lam i m) (X.R i m) := by
  intro x hx
  rw [Function.mem_support] at hx
  have hq : q0MixEntry X i m x ≠ 0 := by
    intro h; apply hx; unfold qFwd; rw [h]; ring
  exact q0MixEntry_support_subset X i m (Function.mem_support.mpr hq)

/-- **Zeroth-order self-convolution term** `𝒬_in ⋆ (𝒬⁻)_jn` (forward × reflected) — the real-space
`(i,n),(j,n)` term of `Q̂₀(k)·Q̂₀ᵀ(−k)`, whose species sum is the zeroth-order Baxter product; the
zeroth-order analog of `bConvP`, built from the existing `qFwd`/`pMixEntry` and Mathlib's `⋆`. -/
noncomputable def qpConv (X : Mix N M) (i n j : Fin N) : ℝ → ℝ :=
  (qFwd X i n) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (pMixEntry X j n)

/-- **Support geometry — the intermediate species `n` cancels.**  `𝒬_in ⋆ (𝒬⁻)_jn` is supported on
`[−Rᵢⱼ, Rᵢⱼ]`: the forward `[λᵢₙ, Rᵢₙ]` and reflected `[−Rⱼₙ, −λⱼₙ]` supports add to
`[λᵢₙ−Rⱼₙ, Rᵢₙ−λⱼₙ] = [−Rᵢⱼ, Rᵢⱼ]`, `σₙ` cancelling (unlike the both-reflected `pMixEntry ⋆ pMixEntry`,
whose edges keep `σₙ`).  So the zeroth-order DCF support edge is exactly `±Rᵢⱼ` — the forward factor is
what makes the σₙ cancel. -/
theorem qpConv_support_subset (X : Mix N M) (i n j : Fin N) :
    Function.support (qpConv X i n j) ⊆ Set.Icc (-(X.R i j)) (X.R i j) := by
  have hedge1 : X.lam i n + -(X.R j n) = -(X.R i j) := by simp only [Mix.R, Mix.lam]; ring
  have hedge2 : X.R i n + -(X.lam j n) = X.R i j := by simp only [Mix.R, Mix.lam]; ring
  unfold qpConv
  refine (support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)).trans ?_
  refine (Set.add_subset_add (qFwd_support_subset X i n)
    (pMixEntry_support_subset X j n)).trans ?_
  have hmink := Icc_add_Icc_subset (X.lam i n) (X.R i n) (-(X.R j n)) (-(X.lam j n))
  rw [hedge1, hedge2] at hmink
  exact hmink

/-- **Real-space zeroth-order (HS) mixture DCF entry** — the non-delta part of `[Cmix0]_ij` inverse
transform.  Expanding `Cmix0 = I − Q̂₀(k)·Q̂₀ᵀ(−k)` with `Q̂₀_il ↔ δ_il·δ − qFwd_il` (and its `−k`
reflection `↔ δ_il·δ − pMixEntry_il`), the identity/delta parts collapse and the surviving real-space
combination is

  `[Cmix0]_ij(t) = qFwd_ij(t) + pMixEntry_ji(t) − ∑ₗ (qFwd_il ⋆ pMixEntry_jl)(t)`   (for `t ≠ 0`).

This is the matrix HS DCF `c^HS_ij` (up to the standard `2π√(ρᵢρⱼ)·t` normalization), built entirely
from the existing PY-Baxter kernels — the zeroth-order analog of the first-order `𝒲_ij`.  Its
identification with the momentum `Cmix0` (the inverse-transform theorem) is the next step, parallel to
how the first-order `(★)` is a proven identity. -/
noncomputable def cHSmixRaw (X : Mix N M) (i j : Fin N) (t : ℝ) : ℝ :=
  qFwd X i j t + pMixEntry X j i t - ∑ l, qpConv X i l j t

/-- **Support of the HS DCF entry** — `c^HS_ij` is supported inside the core `[−Rᵢⱼ, Rᵢⱼ]`: each of
the three pieces (`qFwd_ij` on `[λᵢⱼ,Rᵢⱼ]`, `pMixEntry_ji` on `[−Rᵢⱼ,λᵢⱼ]`, and every `qpConv` term on
`[−Rᵢⱼ,Rᵢⱼ]`) sits inside it (needs only the diameters `> 0`). -/
theorem cHSmixRaw_support_subset (X : Mix N M) (i j : Fin N) :
    Function.support (cHSmixRaw X i j) ⊆ Set.Icc (-(X.R i j)) (X.R i j) := by
  have hqf : Function.support (qFwd X i j) ⊆ Set.Icc (-(X.R i j)) (X.R i j) :=
    (qFwd_support_subset X i j).trans
      (Set.Icc_subset_Icc (by simp only [Mix.R, Mix.lam]; linarith [X.hσ j]) le_rfl)
  have hpm : Function.support (pMixEntry X j i) ⊆ Set.Icc (-(X.R i j)) (X.R i j) :=
    (pMixEntry_support_subset X j i).trans
      (Set.Icc_subset_Icc (by simp only [Mix.R]; linarith)
        (by simp only [Mix.R, Mix.lam]; linarith [X.hσ i]))
  have hsum : Function.support (fun t => ∑ l, qpConv X i l j t) ⊆ Set.Icc (-(X.R i j)) (X.R i j) := by
    intro t ht
    rw [Function.mem_support] at ht
    obtain ⟨l, _, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
    exact qpConv_support_subset X i l j (Function.mem_support.mpr hl)
  intro t ht
  rw [Function.mem_support] at ht
  by_contra hc
  apply ht
  have e1 : qFwd X i j t = 0 := Function.notMem_support.mp (fun h => hc (hqf h))
  have e2 : pMixEntry X j i t = 0 := Function.notMem_support.mp (fun h => hc (hpm h))
  have e3 : (∑ l, qpConv X i l j t) = 0 := Function.notMem_support.mp (fun h => hc (hsum h))
  show qFwd X i j t + pMixEntry X j i t - ∑ l, qpConv X i l j t = 0
  rw [e1, e2, e3]; ring

/-- **Zeroth-order inner HS DCF (odd part)** `cHSodd_ij(x) = cHSmixRaw_ij(x) − cHSmixRaw_ij(−x)` — the
odd extraction that isolates the physical DCF from the full real-space `[Cmix0]_ij`, mirroring the
first-order `MixtureDCFSmooth.dcfOdd` (`= 𝒲_ij(x) − 𝒲_ij(−x)`).  Under the same normalization it **is**
`2π√(ρᵢρⱼ)·r·c^HS_ij(r)` — the zeroth-order analog of `dcfOdd = 2π√ρ·r·c^(1)`.  (`r·c` is odd, so the
odd part of the assembly is exactly the DCF times `2π√ρ·r`; the even part is the delta/contact data.) -/
noncomputable def cHSodd (X : Mix N M) (i j : Fin N) : ℝ → ℝ :=
  fun x => cHSmixRaw X i j x - cHSmixRaw X i j (-x)

/-- `cHSodd` is odd — `cHSodd_ij(−x) = −cHSodd_ij(x)` (by construction). -/
theorem cHSodd_odd (X : Mix N M) (i j : Fin N) (x : ℝ) :
    cHSodd X i j (-x) = -(cHSodd X i j x) := by
  simp only [cHSodd, neg_neg]; ring

/-- Support of the odd inner DCF: `⊆ [−Rᵢⱼ, Rᵢⱼ]` (both `cHSmixRaw x` and `cHSmixRaw (−x)` vanish
outside it, `[−Rᵢⱼ,Rᵢⱼ]` being symmetric). -/
theorem cHSodd_support_subset (X : Mix N M) (i j : Fin N) :
    Function.support (cHSodd X i j) ⊆ Set.Icc (-(X.R i j)) (X.R i j) := by
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hc
  apply hx
  have e1 : cHSmixRaw X i j x = 0 :=
    Function.notMem_support.mp (fun h => hc (cHSmixRaw_support_subset X i j h))
  have e2 : cHSmixRaw X i j (-x) = 0 := by
    apply Function.notMem_support.mp
    intro h
    have hmem := Set.mem_Icc.mp (cHSmixRaw_support_subset X i j h)
    exact hc (Set.mem_Icc.mpr ⟨by linarith [hmem.2], by linarith [hmem.1]⟩)
  change cHSmixRaw X i j x - cHSmixRaw X i j (-x) = 0
  rw [e1, e2]; ring

/-! ### Convolution → interval-integral bridge (prerequisite for the closed form / core-seed) -/

/-- `qFwd` as an `Icc`-indicator of its quadratic (mirror of `pMixEntry_eq_indicator_quad`, un-reflected). -/
theorem qFwd_eq_indicator_quad (X : Mix N M) (i m : Fin N) :
    qFwd X i m = Set.indicator (Set.Icc (X.lam i m) (X.R i m))
      (fun u => 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ m)
        * (X.Q0 i m * (u - X.R i m) + X.Qpp m * (u - X.R i m) ^ 2 / 2)) := by
  funext u
  unfold qFwd q0MixEntry
  by_cases h : u ∈ Set.Icc (X.lam i m) (X.R i m)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

/-- **`𝒬_in ⋆ (𝒬⁻)_jn` collapses to `∫ (fwd quad)·pMixEntry`** over the forward `[λᵢₙ, Rᵢₙ]` window —
the zeroth-order analog of `pbpConv_eq_intervalIntegral`, via the same `indicator_icc_conv_general`
single-window bridge.  This turns the Mathlib `⋆` into an explicit interval integral of the reflected
`pMixEntry` kernel against the forward Baxter quadratic. -/
theorem qpConv_eq_intervalIntegral (X : Mix N M) (i n j : Fin N) (x : ℝ)
    (hle : X.lam i n ≤ X.R i n)
    (hint : IntervalIntegrable (fun t => (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ n)
        * (X.Q0 i n * (t - X.R i n) + X.Qpp n * (t - X.R i n) ^ 2 / 2)) * pMixEntry X j n (x - t))
      volume (X.lam i n) (X.R i n)) :
    qpConv X i n j x = ∫ t in (X.lam i n)..(X.R i n),
      (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ n)
        * (X.Q0 i n * (t - X.R i n) + X.Qpp n * (t - X.R i n) ^ 2 / 2)) * pMixEntry X j n (x - t) := by
  unfold qpConv
  rw [qFwd_eq_indicator_quad,
    indicator_icc_conv_general _ _ (X.lam i n) (X.R i n) x hle hint]

/-- `pMixEntry` is globally bounded (its quadratic is bounded on the compact support). -/
theorem pMixEntry_bounded (X : Mix N M) (j n : Fin N) :
    ∃ C, 0 ≤ C ∧ ∀ u, |pMixEntry X j n u| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -(X.R j n)) (b := -(X.lam j n))).exists_bound_of_continuousOn
    (f := fun u => 2 * Real.pi * Real.sqrt (X.ρ j * X.ρ n)
      * (X.Q0 j n * (-u - X.R j n) + X.Qpp n * (-u - X.R j n) ^ 2 / 2))
    (Continuous.continuousOn (by fun_prop))
  refine ⟨max C 0, le_max_right _ _, fun u => ?_⟩
  rw [pMixEntry_eq_indicator_quad]
  by_cases h : u ∈ Set.Icc (-(X.R j n)) (-(X.lam j n))
  · rw [Set.indicator_of_mem h, ← Real.norm_eq_abs]
    exact le_trans (hC u h) (le_max_left _ _)
  · rw [Set.indicator_of_notMem h, abs_zero]; exact le_max_right _ _

/-- **Integrand of `qpConv` is interval-integrable** — discharges the `hint` gate of
`qpConv_eq_intervalIntegral`.  The forward quadratic is continuous (bounded on the compact window),
`pMixEntry` is bounded measurable, so the product is bounded a.e.-measurable on `[λᵢₙ, Rᵢₙ]`. -/
theorem qpConv_integrand_intervalIntegrable (X : Mix N M) (i n j : Fin N) (x : ℝ) :
    IntervalIntegrable (fun t => (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ n)
        * (X.Q0 i n * (t - X.R i n) + X.Qpp n * (t - X.R i n) ^ 2 / 2)) * pMixEntry X j n (x - t))
      volume (X.lam i n) (X.R i n) := by
  obtain ⟨Cp, _, hCp⟩ := pMixEntry_bounded X j n
  obtain ⟨Cf, hCf⟩ := (isCompact_uIcc (a := X.lam i n) (b := X.R i n)).exists_bound_of_continuousOn
    (f := fun t => 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ n)
      * (X.Q0 i n * (t - X.R i n) + X.Qpp n * (t - X.R i n) ^ 2 / 2))
    (Continuous.continuousOn (by fun_prop))
  have hmeas : Measurable (fun t => (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ n)
      * (X.Q0 i n * (t - X.R i n) + X.Qpp n * (t - X.R i n) ^ 2 / 2)) * pMixEntry X j n (x - t)) := by
    refine Measurable.mul (by fun_prop) ?_
    have hpm : Measurable (pMixEntry X j n) := by
      rw [pMixEntry_eq_indicator_quad]
      exact Measurable.indicator (by fun_prop) measurableSet_Icc
    exact hpm.comp (by fun_prop)
  rw [intervalIntegrable_iff]
  have hfin : volume (Set.uIoc (X.lam i n) (X.R i n)) ≠ ⊤ :=
    ne_top_of_le_ne_top isCompact_uIcc.measure_ne_top (measure_mono Set.uIoc_subset_uIcc)
  refine Measure.integrableOn_of_bounded (M := Cf * Cp) hfin hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [Real.norm_eq_abs, abs_mul]
  have hf := hCf t (Set.uIoc_subset_uIcc ht)
  rw [Real.norm_eq_abs] at hf
  exact mul_le_mul hf (hCp _) (abs_nonneg _) (le_trans (abs_nonneg _) hf)

/-- **The poly ⋆ poly closed-form atom** — `∫_a^b (c₀+c₁t+c₂t²)(d₀+d₁t+d₂t²) dt` is a degree-5
polynomial in the endpoints (the zeroth-order analog of `MixtureRealSpace.integral_quadratic_exp_conv`,
with the exponential replaced by a second quadratic).  Once the reflected `pMixEntry` kernel is a
quadratic on the overlap window, the `qpConv` integrand is exactly this product, so its closed form is
this atom — no infinite sum, a finite piecewise polynomial. -/
theorem integral_quad_mul_quad (c0 c1 c2 d0 d1 d2 a b : ℝ) :
    (∫ t in a..b, (c0 + c1 * t + c2 * t ^ 2) * (d0 + d1 * t + d2 * t ^ 2))
      = ((c0 * d0) * b + (c0 * d1 + c1 * d0) * (b ^ 2 / 2)
          + (c0 * d2 + c1 * d1 + c2 * d0) * (b ^ 3 / 3)
          + (c1 * d2 + c2 * d1) * (b ^ 4 / 4) + (c2 * d2) * (b ^ 5 / 5))
        - ((c0 * d0) * a + (c0 * d1 + c1 * d0) * (a ^ 2 / 2)
          + (c0 * d2 + c1 * d1 + c2 * d0) * (a ^ 3 / 3)
          + (c1 * d2 + c2 * d1) * (a ^ 4 / 4) + (c2 * d2) * (a ^ 5 / 5)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => (c0 * d0) * t + (c0 * d1 + c1 * d0) * (t ^ 2 / 2)
          + (c0 * d2 + c1 * d1 + c2 * d0) * (t ^ 3 / 3)
          + (c1 * d2 + c2 * d1) * (t ^ 4 / 4) + (c2 * d2) * (t ^ 5 / 5))
      (fun x _ => by
        have h1 : HasDerivAt (fun t : ℝ => (c0 * d0) * t) (c0 * d0) x := by
          simpa using (hasDerivAt_id x).const_mul (c0 * d0)
        have h2 : HasDerivAt (fun t : ℝ => (c0 * d1 + c1 * d0) * (t ^ 2 / 2))
            ((c0 * d1 + c1 * d0) * x) x :=
          (((hasDerivAt_pow 2 x).div_const 2).const_mul (c0 * d1 + c1 * d0)).congr_deriv (by ring)
        have h3 : HasDerivAt (fun t : ℝ => (c0 * d2 + c1 * d1 + c2 * d0) * (t ^ 3 / 3))
            ((c0 * d2 + c1 * d1 + c2 * d0) * x ^ 2) x :=
          (((hasDerivAt_pow 3 x).div_const 3).const_mul
            (c0 * d2 + c1 * d1 + c2 * d0)).congr_deriv (by ring)
        have h4 : HasDerivAt (fun t : ℝ => (c1 * d2 + c2 * d1) * (t ^ 4 / 4))
            ((c1 * d2 + c2 * d1) * x ^ 3) x :=
          (((hasDerivAt_pow 4 x).div_const 4).const_mul (c1 * d2 + c2 * d1)).congr_deriv (by ring)
        have h5 : HasDerivAt (fun t : ℝ => (c2 * d2) * (t ^ 5 / 5)) ((c2 * d2) * x ^ 4) x :=
          (((hasDerivAt_pow 5 x).div_const 5).const_mul (c2 * d2)).congr_deriv (by ring)
        exact ((((h1.add h2).add h3).add h4).add h5).congr_deriv (by ring))
      ((by fun_prop : Continuous
        (fun t : ℝ => (c0 + c1 * t + c2 * t ^ 2) * (d0 + d1 * t + d2 * t ^ 2))).intervalIntegrable
          a b)]

/-- **N=1 headline — the zeroth-order HS DCF self-conv is a polynomial (hence `ContDiffOn`) on the
core `(0, R₀₀)`.**  For the one-component fluid `λ₀₀ = 0`, so the core is a single piece.  On `(0,R)`
the overlap resolves to `[x,R]` (the `[0,x]` part vanishes as `pMixEntry(x−t)=0` for `t<x`), and there
the integrand is `(fwd quad)·(pMixEntry quad)` ⇒ by `integral_quad_mul_quad` it is an explicit degree-5
polynomial in `x`, so `qpConv X 0 0 0` is `ContDiffOn` the core.  Zeroth-order analog of
`MixtureDCFSmooth.innerDCF_N1_contDiffOn`. -/
theorem qpConv_N1_contDiffOn {M : ℕ} (X : Mix 1 M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (qpConv X 0 0 0) (Set.Ioo (0 : ℝ) (X.R 0 0)) := by
  have hlam0 : X.lam 0 0 = 0 := by simp only [Mix.lam]; ring
  have hRpos : (0 : ℝ) < X.R 0 0 := by have := X.hσ 0; simp only [Mix.R]; linarith
  set rr := 2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) with hrr
  set Q := X.Q0 0 0 with hQ
  set P := X.Qpp 0 with hP
  set R := X.R 0 0 with hRdef
  set C0 := rr * (-Q * R + P * R ^ 2 / 2) with hC0
  set C1 := rr * (Q - P * R) with hC1
  set A2 := rr * (P / 2) with hA2
  set D0 : ℝ → ℝ := fun x => rr * (-Q * (x + R) + P * (x + R) ^ 2 / 2) with hD0
  set D1 : ℝ → ℝ := fun x => rr * (Q - P * (x + R)) with hD1
  -- the resolved integral is ContDiff in x (it equals the poly⋆poly closed-form atom)
  have hcd : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => ∫ t in x..R, (C0 + C1 * t + A2 * t ^ 2) * (D0 x + D1 x * t + A2 * t ^ 2)) := by
    have hEq : (fun x => ∫ t in x..R, (C0 + C1 * t + A2 * t ^ 2) * (D0 x + D1 x * t + A2 * t ^ 2))
        = fun x => _ := funext (fun x => integral_quad_mul_quad C0 C1 A2 (D0 x) (D1 x) A2 x R)
    rw [hEq, hD0, hD1]
    fun_prop
  -- closed form on the core: qpConv = the resolved integral
  have hclosed : ∀ x ∈ Set.Ioo (0 : ℝ) R, qpConv X 0 0 0 x
      = ∫ t in x..R, (C0 + C1 * t + A2 * t ^ 2) * (D0 x + D1 x * t + A2 * t ^ 2) := by
    intro x hx
    obtain ⟨hx0, hxR⟩ := hx
    rw [qpConv_eq_intervalIntegral X 0 0 0 x (by rw [hlam0]; exact hRpos.le)
        (qpConv_integrand_intervalIntegrable X 0 0 0 x), hlam0]
    have hint := qpConv_integrand_intervalIntegrable X 0 0 0 x
    rw [hlam0] at hint
    have hI0 := hint.mono_set (Set.uIcc_subset_uIcc
      (Set.mem_uIcc.mpr (Or.inl ⟨le_refl 0, hRpos.le⟩))
      (Set.mem_uIcc.mpr (Or.inl ⟨hx0.le, hxR.le⟩)) : Set.uIcc (0:ℝ) x ⊆ Set.uIcc 0 R)
    have hIx := hint.mono_set (Set.uIcc_subset_uIcc
      (Set.mem_uIcc.mpr (Or.inl ⟨hx0.le, hxR.le⟩))
      (Set.mem_uIcc.mpr (Or.inl ⟨hRpos.le, le_refl R⟩)) : Set.uIcc x R ⊆ Set.uIcc 0 R)
    rw [← intervalIntegral.integral_add_adjacent_intervals hI0 hIx]
    have hvanish : (∫ t in (0:ℝ)..x, (rr * (Q * (t - R) + P * (t - R) ^ 2 / 2))
        * pMixEntry X 0 0 (x - t)) = 0 := by
      rw [intervalIntegral.integral_congr_ae ?_, intervalIntegral.integral_zero]
      rw [Set.uIoc_of_le hx0.le]
      have hne : ∀ᵐ (y : ℝ), y ≠ x := by rw [MeasureTheory.ae_iff]; simp
      filter_upwards [hne] with t ht hmem
      have htlt : t < x := lt_of_le_of_ne hmem.2 ht
      have hpm0 : pMixEntry X 0 0 (x - t) = 0 := by
        apply Function.notMem_support.mp
        intro hs
        have hh := pMixEntry_support_subset X 0 0 hs
        rw [Set.mem_Icc, hlam0] at hh
        linarith [hh.2]
      simp only [hpm0, mul_zero]
    rw [hvanish, zero_add]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hxR.le] at ht
    have hmem : x - t ∈ Set.Icc (-(X.R 0 0)) (-(X.lam 0 0)) := by
      rw [Set.mem_Icc, hlam0]
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [pMixEntry_eq_indicator_quad, Set.indicator_of_mem hmem]
    simp only [hC0, hC1, hA2, hD0, hD1]
    ring
  exact (hcd.contDiffOn).congr hclosed

/-- **N=1 HS DCF assembly is `ContDiffOn` the core `(0, R₀₀)`.**  `cHSmixRaw X 0 0 = qFwd + pMixEntry −
qpConv` (the sum over the single species collapses); on `(0,R)` `qFwd` is the quadratic, `pMixEntry`
vanishes (support in `[−R,0]`), and `qpConv` is `ContDiffOn` (`qpConv_N1_contDiffOn`). -/
theorem cHSmixRaw_N1_contDiffOn {M : ℕ} (X : Mix 1 M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (cHSmixRaw X 0 0) (Set.Ioo (0 : ℝ) (X.R 0 0)) := by
  have hlam0 : X.lam 0 0 = 0 := by simp only [Mix.lam]; ring
  have hcm : cHSmixRaw X 0 0
      = fun x => qFwd X 0 0 x + pMixEntry X 0 0 x - qpConv X 0 0 0 x := by
    funext x; simp only [cHSmixRaw, Fin.sum_univ_one]
  have hqFwd : ContDiffOn ℝ (⊤ : ℕ∞) (qFwd X 0 0) (Set.Ioo (0 : ℝ) (X.R 0 0)) := by
    refine (ContDiff.contDiffOn (f := fun u => 2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0)
        * (X.Q0 0 0 * (u - X.R 0 0) + X.Qpp 0 * (u - X.R 0 0) ^ 2 / 2)) (by fun_prop)).congr ?_
    intro x hx
    rw [qFwd_eq_indicator_quad, Set.indicator_of_mem (Set.mem_Icc.mpr
      ⟨by rw [hlam0]; exact hx.1.le, hx.2.le⟩)]
  have hpMix : ContDiffOn ℝ (⊤ : ℕ∞) (pMixEntry X 0 0) (Set.Ioo (0 : ℝ) (X.R 0 0)) := by
    refine (contDiff_const (c := (0 : ℝ))).contDiffOn.congr ?_
    intro x hx
    apply Function.notMem_support.mp
    intro hs
    have hh := pMixEntry_support_subset X 0 0 hs
    rw [Set.mem_Icc, hlam0] at hh
    linarith [hh.2, hx.1]
  rw [hcm]
  exact (hqFwd.add hpMix).sub (qpConv_N1_contDiffOn X)

/-- **N=1 `qpConv` is `ContDiffOn` the reflected core `(−R₀₀, 0)`** — the mirror of
`qpConv_N1_contDiffOn`, needed for the odd part `cHSodd`.  For `y ∈ (−R,0)` the overlap resolves to
`[0, y+R]` (the `[y+R, R]` part vanishes: `pMixEntry(y−t)=0` for `t>y+R`). -/
theorem qpConv_N1_contDiffOn_neg {M : ℕ} (X : Mix 1 M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (qpConv X 0 0 0) (Set.Ioo (-(X.R 0 0)) (0 : ℝ)) := by
  have hlam0 : X.lam 0 0 = 0 := by simp only [Mix.lam]; ring
  have hRpos : (0 : ℝ) < X.R 0 0 := by have := X.hσ 0; simp only [Mix.R]; linarith
  set rr := 2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0) with hrr
  set Q := X.Q0 0 0 with hQ
  set P := X.Qpp 0 with hP
  set R := X.R 0 0 with hRdef
  set C0 := rr * (-Q * R + P * R ^ 2 / 2) with hC0
  set C1 := rr * (Q - P * R) with hC1
  set A2 := rr * (P / 2) with hA2
  set D0 : ℝ → ℝ := fun x => rr * (-Q * (x + R) + P * (x + R) ^ 2 / 2) with hD0
  set D1 : ℝ → ℝ := fun x => rr * (Q - P * (x + R)) with hD1
  have hcd : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => ∫ t in (0:ℝ)..(x + R), (C0 + C1 * t + A2 * t ^ 2) * (D0 x + D1 x * t + A2 * t ^ 2)) := by
    have hEq := funext (fun x => integral_quad_mul_quad C0 C1 A2 (D0 x) (D1 x) A2 0 (x + R))
    rw [hEq, hD0, hD1]
    fun_prop
  have hclosed : ∀ x ∈ Set.Ioo (-R) (0 : ℝ), qpConv X 0 0 0 x
      = ∫ t in (0:ℝ)..(x + R), (C0 + C1 * t + A2 * t ^ 2) * (D0 x + D1 x * t + A2 * t ^ 2) := by
    intro x hx
    obtain ⟨hxR, hx0⟩ := hx
    rw [qpConv_eq_intervalIntegral X 0 0 0 x (by rw [hlam0]; exact hRpos.le)
        (qpConv_integrand_intervalIntegrable X 0 0 0 x), hlam0]
    have hint := qpConv_integrand_intervalIntegrable X 0 0 0 x
    rw [hlam0] at hint
    have hI0 := hint.mono_set (Set.uIcc_subset_uIcc
      (Set.mem_uIcc.mpr (Or.inl ⟨le_refl 0, hRpos.le⟩))
      (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)) : Set.uIcc (0:ℝ) (x + R) ⊆ Set.uIcc 0 R)
    have hIx := hint.mono_set (Set.uIcc_subset_uIcc
      (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩))
      (Set.mem_uIcc.mpr (Or.inl ⟨hRpos.le, le_refl R⟩)) : Set.uIcc (x + R) R ⊆ Set.uIcc 0 R)
    rw [← intervalIntegral.integral_add_adjacent_intervals hI0 hIx]
    have hvanish : (∫ t in (x + R)..R, (rr * (Q * (t - R) + P * (t - R) ^ 2 / 2))
        * pMixEntry X 0 0 (x - t)) = 0 := by
      rw [intervalIntegral.integral_congr_ae ?_, intervalIntegral.integral_zero]
      rw [Set.uIoc_of_le (by linarith)]
      have hne : ∀ᵐ (y : ℝ), y ≠ x + R := by rw [MeasureTheory.ae_iff]; simp
      filter_upwards [hne] with t _ht hmem
      have htgt : x + R < t := hmem.1
      have hpm0 : pMixEntry X 0 0 (x - t) = 0 := by
        apply Function.notMem_support.mp
        intro hs
        have hh := pMixEntry_support_subset X 0 0 hs
        rw [Set.mem_Icc] at hh
        linarith [hh.1]
      simp only [hpm0, mul_zero]
    rw [hvanish, add_zero]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by linarith)] at ht
    have hmem : x - t ∈ Set.Icc (-(X.R 0 0)) (-(X.lam 0 0)) := by
      rw [Set.mem_Icc, hlam0]
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [pMixEntry_eq_indicator_quad, Set.indicator_of_mem hmem]
    simp only [hC0, hC1, hA2, hD0, hD1]
    ring
  exact (hcd.contDiffOn).congr hclosed

/-- `cHSmixRaw` is `ContDiffOn` the reflected core `(−R₀₀, 0)` (mirror of `cHSmixRaw_N1_contDiffOn`;
here `qFwd` vanishes and `pMixEntry` is the quadratic). -/
theorem cHSmixRaw_N1_contDiffOn_neg {M : ℕ} (X : Mix 1 M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (cHSmixRaw X 0 0) (Set.Ioo (-(X.R 0 0)) (0 : ℝ)) := by
  have hlam0 : X.lam 0 0 = 0 := by simp only [Mix.lam]; ring
  have hcm : cHSmixRaw X 0 0
      = fun x => qFwd X 0 0 x + pMixEntry X 0 0 x - qpConv X 0 0 0 x := by
    funext x; simp only [cHSmixRaw, Fin.sum_univ_one]
  have hqFwd : ContDiffOn ℝ (⊤ : ℕ∞) (qFwd X 0 0) (Set.Ioo (-(X.R 0 0)) (0 : ℝ)) := by
    refine (contDiff_const (c := (0 : ℝ))).contDiffOn.congr ?_
    intro x hx
    apply Function.notMem_support.mp
    intro hs
    have hh := qFwd_support_subset X 0 0 hs
    rw [Set.mem_Icc, hlam0] at hh
    linarith [hh.1, hx.2]
  have hpMix : ContDiffOn ℝ (⊤ : ℕ∞) (pMixEntry X 0 0) (Set.Ioo (-(X.R 0 0)) (0 : ℝ)) := by
    refine (ContDiff.contDiffOn (f := fun u => 2 * Real.pi * Real.sqrt (X.ρ 0 * X.ρ 0)
        * (X.Q0 0 0 * (-u - X.R 0 0) + X.Qpp 0 * (-u - X.R 0 0) ^ 2 / 2)) (by fun_prop)).congr ?_
    intro x hx
    rw [pMixEntry_eq_indicator_quad, Set.indicator_of_mem (Set.mem_Icc.mpr
      ⟨hx.1.le, by rw [hlam0]; linarith [hx.2]⟩)]
  rw [hcm]
  exact (hqFwd.add hpMix).sub (qpConv_N1_contDiffOn_neg X)

/-- **N=1 headline — the zeroth-order inner HS DCF `cHSodd` (`= 2π√ρ·r·c^HS`) is `ContDiffOn` the
core `(0, R₀₀)`.**  The DCF-side completion of Steps 1–2 for one component: `cHSodd(x) = cHSmixRaw(x) −
cHSmixRaw(−x)` is `ContDiffOn` because `cHSmixRaw` is `ContDiffOn` both `(0,R)` and (via `x ↦ −x`) the
reflected core `(−R,0)`.  Zeroth-order analog of `MixtureDCFSmooth.innerDCF_N1_contDiffOn`. -/
theorem cHSodd_N1_contDiffOn {M : ℕ} (X : Mix 1 M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (cHSodd X 0 0) (Set.Ioo (0 : ℝ) (X.R 0 0)) := by
  have hco : cHSodd X 0 0 = fun x => cHSmixRaw X 0 0 x - cHSmixRaw X 0 0 (-x) := rfl
  rw [hco]
  refine (cHSmixRaw_N1_contDiffOn X).sub ((cHSmixRaw_N1_contDiffOn_neg X).comp
    contDiff_neg.contDiffOn (fun x hx => ?_))
  simp only [Set.mem_Ioo] at hx ⊢
  exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-! ### General-N: the two-piece knot smoothness (`λᵢⱼ` splits the core) -/

/-- **General-N `qpConv X i k j` is `ContDiffOn` the upper core piece `(λᵢⱼ, Rᵢⱼ)`** (for `σⱼ ≥ σᵢ`,
i.e. `λᵢⱼ ≥ 0`).  The convolution window `[λᵢₖ, Rᵢₖ]` splits at `x+λⱼₖ` (`= x` shifted): below it
`pMixEntry(x−t)=0`, above it the integrand is `(fwd quad)·(pMixEntry quad)`, so by
`integral_quad_mul_quad` the value is a polynomial in `x` (`ContDiff`).  The knot edge `λᵢⱼ` and the
upper limit `Rᵢⱼ` are the k-free `Mix.lam`/`Mix.R` combinations (`λᵢₖ−λⱼₖ=λᵢⱼ`, `Rᵢₖ−λⱼₖ=Rᵢⱼ`), so
this piece is uniform over the intermediate species `k`. -/
theorem qpConv_contDiffOn_upper {N M : ℕ} (X : Mix N M) (i k j : Fin N) (hlam : 0 ≤ X.lam i j) :
    ContDiffOn ℝ (⊤ : ℕ∞) (qpConv X i k j) (Set.Ioo (X.lam i j) (X.R i j)) := by
  have hkR : X.lam i k ≤ X.R i k := by have := X.hσ i; simp only [Mix.lam, Mix.R]; linarith
  have hLid : X.lam i k - X.lam j k = X.lam i j := by simp only [Mix.lam]; ring
  have hRid : X.R i k - X.lam j k = X.R i j := by simp only [Mix.R, Mix.lam]; ring
  have hRRid : X.R i k - X.R j k = -(X.lam i j) := by simp only [Mix.R, Mix.lam]; ring
  set rri := 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ k) with hrri
  set rrj := 2 * Real.pi * Real.sqrt (X.ρ j * X.ρ k) with hrrj
  set Qi := X.Q0 i k with hQi
  set Qj := X.Q0 j k with hQj
  set Pk := X.Qpp k with hPk
  set Rik := X.R i k with hRik
  set Rjk := X.R j k with hRjk
  set Ljk := X.lam j k with hLjk
  set c0 := rri * (-Qi * Rik + Pk * Rik ^ 2 / 2) with hc0
  set c1 := rri * (Qi - Pk * Rik) with hc1
  set c2 := rri * (Pk / 2) with hc2
  set D0 : ℝ → ℝ := fun x => rrj * (-Qj * (x + Rjk) + Pk * (x + Rjk) ^ 2 / 2) with hD0
  set D1 : ℝ → ℝ := fun x => rrj * (Qj - Pk * (x + Rjk)) with hD1
  set d2 := rrj * (Pk / 2) with hd2
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ t in (x + Ljk)..Rik,
      (c0 + c1 * t + c2 * t ^ 2) * (D0 x + D1 x * t + d2 * t ^ 2)) := by
    have hEq := funext (fun x =>
      integral_quad_mul_quad c0 c1 c2 (D0 x) (D1 x) d2 (x + Ljk) Rik)
    rw [hEq]; simp only [hD0, hD1]; fun_prop
  have hclosed : ∀ x ∈ Set.Ioo (X.lam i j) (X.R i j), qpConv X i k j x
      = ∫ t in (x + Ljk)..Rik, (c0 + c1 * t + c2 * t ^ 2) * (D0 x + D1 x * t + d2 * t ^ 2) := by
    intro x hx
    obtain ⟨hxlo, hxhi⟩ := hx
    rw [qpConv_eq_intervalIntegral X i k j x hkR (qpConv_integrand_intervalIntegrable X i k j x)]
    have hint := qpConv_integrand_intervalIntegrable X i k j x
    have hlo : X.lam i k ≤ x + Ljk := by linarith [hLid]
    have hhi : x + Ljk ≤ Rik := by linarith [hRid]
    have hI0 := hint.mono_set (Set.uIcc_subset_uIcc
      (Set.mem_uIcc.mpr (Or.inl ⟨le_refl _, hkR⟩))
      (Set.mem_uIcc.mpr (Or.inl ⟨hlo, hhi⟩)) : Set.uIcc (X.lam i k) (x + Ljk) ⊆ Set.uIcc (X.lam i k) Rik)
    have hIx := hint.mono_set (Set.uIcc_subset_uIcc
      (Set.mem_uIcc.mpr (Or.inl ⟨hlo, hhi⟩))
      (Set.mem_uIcc.mpr (Or.inl ⟨hkR, le_refl _⟩)) : Set.uIcc (x + Ljk) Rik ⊆ Set.uIcc (X.lam i k) Rik)
    rw [← intervalIntegral.integral_add_adjacent_intervals hI0 hIx]
    have hvanish : (∫ t in (X.lam i k)..(x + Ljk), (rri * (Qi * (t - Rik) + Pk * (t - Rik) ^ 2 / 2))
        * pMixEntry X j k (x - t)) = 0 := by
      rw [intervalIntegral.integral_congr_ae ?_, intervalIntegral.integral_zero]
      rw [Set.uIoc_of_le hlo]
      have hne : ∀ᵐ (y : ℝ), y ≠ x + Ljk := by rw [MeasureTheory.ae_iff]; simp
      filter_upwards [hne] with t ht hmem
      have htlt : t < x + Ljk := lt_of_le_of_ne hmem.2 ht
      have hpm0 : pMixEntry X j k (x - t) = 0 := by
        apply Function.notMem_support.mp
        intro hs
        have hh := pMixEntry_support_subset X j k hs
        rw [Set.mem_Icc] at hh
        simp only [← hLjk, ← hRjk] at hh
        linarith [hh.2, htlt]
      simp only [hpm0, mul_zero]
    rw [hvanish, zero_add]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hhi] at ht
    have hmem : x - t ∈ Set.Icc (-(X.R j k)) (-(X.lam j k)) := by
      rw [Set.mem_Icc]
      refine ⟨?_, by simp only [← hLjk]; linarith [ht.1]⟩
      simp only [← hRjk]; have : Rik - Rjk = -(X.lam i j) := hRRid; linarith [ht.2, this, hlam]
    rw [pMixEntry_eq_indicator_quad, Set.indicator_of_mem hmem]
    simp only [hc0, hc1, hc2, hD0, hD1, hd2, ← hQj, ← hPk, ← hRjk]
    ring
  exact (hcd.contDiffOn).congr hclosed

/-- **General-N `qpConv X i k j` is `ContDiffOn` the lower core piece `(0, λᵢⱼ)`** (for `λᵢⱼ > 0`).
Here the *whole* window `[λᵢₖ, Rᵢₖ]` lies in the `pMixEntry` support (no split), so the integrand is
`(fwd quad)·(pMixEntry quad)` throughout and `qpConv` is the closed-form atom, a polynomial in `x`. -/
theorem qpConv_contDiffOn_lower {N M : ℕ} (X : Mix N M) (i k j : Fin N) (_hlam : 0 ≤ X.lam i j) :
    ContDiffOn ℝ (⊤ : ℕ∞) (qpConv X i k j) (Set.Ioo (0 : ℝ) (X.lam i j)) := by
  have hkR : X.lam i k ≤ X.R i k := by have := X.hσ i; simp only [Mix.lam, Mix.R]; linarith
  have hLid : X.lam i k - X.lam j k = X.lam i j := by simp only [Mix.lam]; ring
  have hRRid : X.R i k - X.R j k = -(X.lam i j) := by simp only [Mix.R, Mix.lam]; ring
  set rri := 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ k) with hrri
  set rrj := 2 * Real.pi * Real.sqrt (X.ρ j * X.ρ k) with hrrj
  set Qi := X.Q0 i k with hQi
  set Qj := X.Q0 j k with hQj
  set Pk := X.Qpp k with hPk
  set Rik := X.R i k with hRik
  set Rjk := X.R j k with hRjk
  set Ljk := X.lam j k with hLjk
  set c0 := rri * (-Qi * Rik + Pk * Rik ^ 2 / 2) with hc0
  set c1 := rri * (Qi - Pk * Rik) with hc1
  set c2 := rri * (Pk / 2) with hc2
  set D0 : ℝ → ℝ := fun x => rrj * (-Qj * (x + Rjk) + Pk * (x + Rjk) ^ 2 / 2) with hD0
  set D1 : ℝ → ℝ := fun x => rrj * (Qj - Pk * (x + Rjk)) with hD1
  set d2 := rrj * (Pk / 2) with hd2
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ t in (X.lam i k)..Rik,
      (c0 + c1 * t + c2 * t ^ 2) * (D0 x + D1 x * t + d2 * t ^ 2)) := by
    have hEq := funext (fun x =>
      integral_quad_mul_quad c0 c1 c2 (D0 x) (D1 x) d2 (X.lam i k) Rik)
    rw [hEq]; simp only [hD0, hD1]; fun_prop
  have hclosed : ∀ x ∈ Set.Ioo (0 : ℝ) (X.lam i j), qpConv X i k j x
      = ∫ t in (X.lam i k)..Rik, (c0 + c1 * t + c2 * t ^ 2) * (D0 x + D1 x * t + d2 * t ^ 2) := by
    intro x hx
    obtain ⟨hx0, hxlam⟩ := hx
    rw [qpConv_eq_intervalIntegral X i k j x hkR (qpConv_integrand_intervalIntegrable X i k j x)]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hkR] at ht
    have hmem : x - t ∈ Set.Icc (-(X.R j k)) (-(X.lam j k)) := by
      rw [Set.mem_Icc]
      refine ⟨?_, ?_⟩
      · simp only [← hRjk]; linarith [ht.2, hx0, hRRid]
      · simp only [← hLjk]; linarith [ht.1, hxlam, hLid]
    rw [pMixEntry_eq_indicator_quad, Set.indicator_of_mem hmem]
    simp only [hc0, hc1, hc2, hD0, hD1, hd2, ← hQj, ← hPk, ← hRjk]
    ring
  exact (hcd.contDiffOn).congr hclosed

/-- **General-N HS DCF assembly `cHSmixRaw` is `ContDiffOn` the upper piece `(λᵢⱼ, Rᵢⱼ)`.**
`cHSmixRaw = qFwd + pMixEntry − ∑ₖ qpConv`; on the upper piece `qFwd` is the quadratic, `pMixEntry`
(the `(j,i)` reflected kernel, supported in `[−Rᵢⱼ, λᵢⱼ]`) vanishes, and each `qpConv` is `ContDiffOn`
(`qpConv_contDiffOn_upper`) so the species sum is. -/
theorem cHSmixRaw_contDiffOn_upper {N M : ℕ} (X : Mix N M) (i j : Fin N) (hlam : 0 ≤ X.lam i j) :
    ContDiffOn ℝ (⊤ : ℕ∞) (cHSmixRaw X i j) (Set.Ioo (X.lam i j) (X.R i j)) := by
  have hqFwd : ContDiffOn ℝ (⊤ : ℕ∞) (qFwd X i j) (Set.Ioo (X.lam i j) (X.R i j)) := by
    refine (ContDiff.contDiffOn (f := fun u => 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ j)
        * (X.Q0 i j * (u - X.R i j) + X.Qpp j * (u - X.R i j) ^ 2 / 2)) (by fun_prop)).congr ?_
    intro x hx
    rw [qFwd_eq_indicator_quad, Set.indicator_of_mem (Set.mem_Icc.mpr ⟨hx.1.le, hx.2.le⟩)]
  have hpMix : ContDiffOn ℝ (⊤ : ℕ∞) (pMixEntry X j i) (Set.Ioo (X.lam i j) (X.R i j)) := by
    refine (contDiff_const (c := (0 : ℝ))).contDiffOn.congr ?_
    intro x hx
    apply Function.notMem_support.mp
    intro hs
    have hh := pMixEntry_support_subset X j i hs
    rw [Set.mem_Icc] at hh
    have hlji : -(X.lam j i) = X.lam i j := by simp only [Mix.lam]; ring
    rw [hlji] at hh
    linarith [hh.2, hx.1]
  have hsum : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ∑ k, qpConv X i k j x)
      (Set.Ioo (X.lam i j) (X.R i j)) :=
    ContDiffOn.sum (fun k _ => qpConv_contDiffOn_upper X i k j hlam)
  exact (hqFwd.add hpMix).sub hsum

/-- **General-N HS DCF assembly `cHSmixRaw` is `ContDiffOn` the lower piece `(0, λᵢⱼ)`.**  Here `qFwd`
vanishes (its support starts at `λᵢⱼ`), `pMixEntry` is the quadratic, and each `qpConv` is `ContDiffOn`
(`qpConv_contDiffOn_lower`). -/
theorem cHSmixRaw_contDiffOn_lower {N M : ℕ} (X : Mix N M) (i j : Fin N) (hlam : 0 ≤ X.lam i j) :
    ContDiffOn ℝ (⊤ : ℕ∞) (cHSmixRaw X i j) (Set.Ioo (0 : ℝ) (X.lam i j)) := by
  have hqFwd : ContDiffOn ℝ (⊤ : ℕ∞) (qFwd X i j) (Set.Ioo (0 : ℝ) (X.lam i j)) := by
    refine (contDiff_const (c := (0 : ℝ))).contDiffOn.congr ?_
    intro x hx
    apply Function.notMem_support.mp
    intro hs
    have hh := qFwd_support_subset X i j hs
    rw [Set.mem_Icc] at hh
    linarith [hh.1, hx.2]
  have hpMix : ContDiffOn ℝ (⊤ : ℕ∞) (pMixEntry X j i) (Set.Ioo (0 : ℝ) (X.lam i j)) := by
    refine (ContDiff.contDiffOn (f := fun u => 2 * Real.pi * Real.sqrt (X.ρ j * X.ρ i)
        * (X.Q0 j i * (-u - X.R j i) + X.Qpp i * (-u - X.R j i) ^ 2 / 2)) (by fun_prop)).congr ?_
    intro x hx
    have hmem : x ∈ Set.Icc (-(X.R j i)) (-(X.lam j i)) := by
      rw [Set.mem_Icc]
      refine ⟨?_, ?_⟩
      · have : (0 : ℝ) < X.R j i := by have := X.hσ i; have := X.hσ j; simp only [Mix.R]; linarith
        linarith [hx.1]
      · have hlji : -(X.lam j i) = X.lam i j := by simp only [Mix.lam]; ring
        rw [hlji]; exact hx.2.le
    rw [pMixEntry_eq_indicator_quad, Set.indicator_of_mem hmem]
  have hsum : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ∑ k, qpConv X i k j x) (Set.Ioo (0 : ℝ) (X.lam i j)) :=
    ContDiffOn.sum (fun k _ => qpConv_contDiffOn_lower X i k j hlam)
  exact (hqFwd.add hpMix).sub hsum

/-! ### Reflected core: the two-piece smoothness on `(−Rᵢⱼ, 0)` (for the odd part `cHSodd`) -/

/-- **Reflected upper piece** — `qpConv X i k j` is `ContDiffOn` `(−Rᵢⱼ, −λᵢⱼ)` (for `σⱼ ≥ σᵢ`, i.e.
`λᵢⱼ ≥ 0`).  Mirror of `qpConv_contDiffOn_upper` with the split at the **top**: the window `[λᵢₖ, Rᵢₖ]`
splits at `x+Rⱼₖ`, above which `pMixEntry(x−t)=0` (since `x−t < −Rⱼₖ`), so the value collapses to
`∫_{λᵢₖ}^{x+Rⱼₖ}` of the `quad·quad` product — a polynomial in `x` (`ContDiff`).  The knot edges are the
k-free combinations (`λᵢₖ−Rⱼₖ = −Rᵢⱼ`, `Rᵢₖ−Rⱼₖ = −λᵢⱼ`), so this piece is uniform over `k`. -/
theorem qpConv_contDiffOn_upper_neg {N M : ℕ} (X : Mix N M) (i k j : Fin N) (hlam : 0 ≤ X.lam i j) :
    ContDiffOn ℝ (⊤ : ℕ∞) (qpConv X i k j) (Set.Ioo (-(X.R i j)) (-(X.lam i j))) := by
  have hkR : X.lam i k ≤ X.R i k := by have := X.hσ i; simp only [Mix.lam, Mix.R]; linarith
  have hLid : X.lam i k - X.lam j k = X.lam i j := by simp only [Mix.lam]; ring
  have hLRid : X.lam i k - X.R j k = -(X.R i j) := by simp only [Mix.lam, Mix.R]; ring
  have hRRid : X.R i k - X.R j k = -(X.lam i j) := by simp only [Mix.R, Mix.lam]; ring
  set rri := 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ k) with hrri
  set rrj := 2 * Real.pi * Real.sqrt (X.ρ j * X.ρ k) with hrrj
  set Qi := X.Q0 i k with hQi
  set Qj := X.Q0 j k with hQj
  set Pk := X.Qpp k with hPk
  set Rik := X.R i k with hRik
  set Rjk := X.R j k with hRjk
  set Ljk := X.lam j k with hLjk
  set c0 := rri * (-Qi * Rik + Pk * Rik ^ 2 / 2) with hc0
  set c1 := rri * (Qi - Pk * Rik) with hc1
  set c2 := rri * (Pk / 2) with hc2
  set D0 : ℝ → ℝ := fun x => rrj * (-Qj * (x + Rjk) + Pk * (x + Rjk) ^ 2 / 2) with hD0
  set D1 : ℝ → ℝ := fun x => rrj * (Qj - Pk * (x + Rjk)) with hD1
  set d2 := rrj * (Pk / 2) with hd2
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ t in (X.lam i k)..(x + Rjk),
      (c0 + c1 * t + c2 * t ^ 2) * (D0 x + D1 x * t + d2 * t ^ 2)) := by
    have hEq := funext (fun x =>
      integral_quad_mul_quad c0 c1 c2 (D0 x) (D1 x) d2 (X.lam i k) (x + Rjk))
    rw [hEq]; simp only [hD0, hD1]; fun_prop
  have hclosed : ∀ x ∈ Set.Ioo (-(X.R i j)) (-(X.lam i j)), qpConv X i k j x
      = ∫ t in (X.lam i k)..(x + Rjk), (c0 + c1 * t + c2 * t ^ 2) * (D0 x + D1 x * t + d2 * t ^ 2) := by
    intro x hx
    obtain ⟨hxlo, hxhi⟩ := hx
    rw [qpConv_eq_intervalIntegral X i k j x hkR (qpConv_integrand_intervalIntegrable X i k j x)]
    have hint := qpConv_integrand_intervalIntegrable X i k j x
    have hlo : X.lam i k ≤ x + Rjk := by linarith [hLRid]
    have hhi : x + Rjk ≤ Rik := by linarith [hRRid]
    have hI0 := hint.mono_set (Set.uIcc_subset_uIcc
      (Set.mem_uIcc.mpr (Or.inl ⟨le_refl _, hkR⟩))
      (Set.mem_uIcc.mpr (Or.inl ⟨hlo, hhi⟩)) :
      Set.uIcc (X.lam i k) (x + Rjk) ⊆ Set.uIcc (X.lam i k) Rik)
    have hIx := hint.mono_set (Set.uIcc_subset_uIcc
      (Set.mem_uIcc.mpr (Or.inl ⟨hlo, hhi⟩))
      (Set.mem_uIcc.mpr (Or.inl ⟨hkR, le_refl _⟩)) :
      Set.uIcc (x + Rjk) Rik ⊆ Set.uIcc (X.lam i k) Rik)
    rw [← intervalIntegral.integral_add_adjacent_intervals hI0 hIx]
    have hvanish : (∫ t in (x + Rjk)..Rik, (rri * (Qi * (t - Rik) + Pk * (t - Rik) ^ 2 / 2))
        * pMixEntry X j k (x - t)) = 0 := by
      rw [intervalIntegral.integral_congr_ae ?_, intervalIntegral.integral_zero]
      refine ae_of_all _ (fun t hmem => ?_)
      rw [Set.uIoc_of_le hhi] at hmem
      have htgt : x + Rjk < t := hmem.1
      have hpm0 : pMixEntry X j k (x - t) = 0 := by
        apply Function.notMem_support.mp
        intro hs
        have hh := pMixEntry_support_subset X j k hs
        rw [Set.mem_Icc] at hh
        simp only [← hRjk] at hh
        linarith [hh.1, htgt]
      simp only [hpm0, mul_zero]
    rw [hvanish, add_zero]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hlo] at ht
    have hmem : x - t ∈ Set.Icc (-(X.R j k)) (-(X.lam j k)) := by
      rw [Set.mem_Icc]
      refine ⟨by simp only [← hRjk]; linarith [ht.2], ?_⟩
      simp only [← hLjk]; linarith [ht.1, hLid, hxhi, hlam]
    rw [pMixEntry_eq_indicator_quad, Set.indicator_of_mem hmem]
    simp only [hc0, hc1, hc2, hD0, hD1, hd2, ← hQj, ← hPk, ← hRjk]
    ring
  exact (hcd.contDiffOn).congr hclosed

/-- **Reflected lower piece** — `qpConv X i k j` is `ContDiffOn` `(−λᵢⱼ, 0)` (for `λᵢⱼ ≥ 0`).  Mirror
of `qpConv_contDiffOn_lower`: the *whole* window `[λᵢₖ, Rᵢₖ]` still lies in the `pMixEntry` support (no
split, since `x > −λᵢⱼ` keeps `x+Rⱼₖ > Rᵢₖ` and `x < 0 ≤ λᵢⱼ` keeps `x+λⱼₖ < λᵢₖ`), so the integrand is
`quad·quad` throughout and `qpConv` is the closed-form atom, a polynomial in `x`. -/
theorem qpConv_contDiffOn_lower_neg {N M : ℕ} (X : Mix N M) (i k j : Fin N) (_hlam : 0 ≤ X.lam i j) :
    ContDiffOn ℝ (⊤ : ℕ∞) (qpConv X i k j) (Set.Ioo (-(X.lam i j)) (0 : ℝ)) := by
  have hkR : X.lam i k ≤ X.R i k := by have := X.hσ i; simp only [Mix.lam, Mix.R]; linarith
  have hLid : X.lam i k - X.lam j k = X.lam i j := by simp only [Mix.lam]; ring
  have hRRid : X.R i k - X.R j k = -(X.lam i j) := by simp only [Mix.R, Mix.lam]; ring
  set rri := 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ k) with hrri
  set rrj := 2 * Real.pi * Real.sqrt (X.ρ j * X.ρ k) with hrrj
  set Qi := X.Q0 i k with hQi
  set Qj := X.Q0 j k with hQj
  set Pk := X.Qpp k with hPk
  set Rik := X.R i k with hRik
  set Rjk := X.R j k with hRjk
  set Ljk := X.lam j k with hLjk
  set c0 := rri * (-Qi * Rik + Pk * Rik ^ 2 / 2) with hc0
  set c1 := rri * (Qi - Pk * Rik) with hc1
  set c2 := rri * (Pk / 2) with hc2
  set D0 : ℝ → ℝ := fun x => rrj * (-Qj * (x + Rjk) + Pk * (x + Rjk) ^ 2 / 2) with hD0
  set D1 : ℝ → ℝ := fun x => rrj * (Qj - Pk * (x + Rjk)) with hD1
  set d2 := rrj * (Pk / 2) with hd2
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ t in (X.lam i k)..Rik,
      (c0 + c1 * t + c2 * t ^ 2) * (D0 x + D1 x * t + d2 * t ^ 2)) := by
    have hEq := funext (fun x =>
      integral_quad_mul_quad c0 c1 c2 (D0 x) (D1 x) d2 (X.lam i k) Rik)
    rw [hEq]; simp only [hD0, hD1]; fun_prop
  have hclosed : ∀ x ∈ Set.Ioo (-(X.lam i j)) (0 : ℝ), qpConv X i k j x
      = ∫ t in (X.lam i k)..Rik, (c0 + c1 * t + c2 * t ^ 2) * (D0 x + D1 x * t + d2 * t ^ 2) := by
    intro x hx
    obtain ⟨hxlo, hxhi⟩ := hx
    rw [qpConv_eq_intervalIntegral X i k j x hkR (qpConv_integrand_intervalIntegrable X i k j x)]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hkR] at ht
    have hmem : x - t ∈ Set.Icc (-(X.R j k)) (-(X.lam j k)) := by
      rw [Set.mem_Icc]
      refine ⟨?_, ?_⟩
      · simp only [← hRjk]; linarith [ht.2, hxlo, hRRid]
      · simp only [← hLjk]; linarith [ht.1, hxhi, hxlo, hLid]
    rw [pMixEntry_eq_indicator_quad, Set.indicator_of_mem hmem]
    simp only [hc0, hc1, hc2, hD0, hD1, hd2, ← hQj, ← hPk, ← hRjk]
    ring
  exact (hcd.contDiffOn).congr hclosed

/-- **Reflected HS DCF assembly** `cHSmixRaw` is `ContDiffOn` `(−Rᵢⱼ, −λᵢⱼ)`.  Here `qFwd_ij` vanishes
(its support `[λᵢⱼ,Rᵢⱼ]` is disjoint from the reflected piece), `pMixEntry_ji` (supported on
`[−Rᵢⱼ, λᵢⱼ]`) is the quadratic, and each `qpConv` is `ContDiffOn` (`qpConv_contDiffOn_upper_neg`). -/
theorem cHSmixRaw_contDiffOn_upper_neg {N M : ℕ} (X : Mix N M) (i j : Fin N) (hlam : 0 ≤ X.lam i j) :
    ContDiffOn ℝ (⊤ : ℕ∞) (cHSmixRaw X i j) (Set.Ioo (-(X.R i j)) (-(X.lam i j))) := by
  have hqFwd : ContDiffOn ℝ (⊤ : ℕ∞) (qFwd X i j) (Set.Ioo (-(X.R i j)) (-(X.lam i j))) := by
    refine (contDiff_const (c := (0 : ℝ))).contDiffOn.congr ?_
    intro x hx
    apply Function.notMem_support.mp
    intro hs
    have hh := qFwd_support_subset X i j hs
    rw [Set.mem_Icc] at hh
    linarith [hh.1, hx.2, hlam]
  have hpMix : ContDiffOn ℝ (⊤ : ℕ∞) (pMixEntry X j i) (Set.Ioo (-(X.R i j)) (-(X.lam i j))) := by
    refine (ContDiff.contDiffOn (f := fun u => 2 * Real.pi * Real.sqrt (X.ρ j * X.ρ i)
        * (X.Q0 j i * (-u - X.R j i) + X.Qpp i * (-u - X.R j i) ^ 2 / 2)) (by fun_prop)).congr ?_
    intro x hx
    have hmem : x ∈ Set.Icc (-(X.R j i)) (-(X.lam j i)) := by
      rw [Set.mem_Icc]
      refine ⟨?_, ?_⟩
      · have hRji : X.R j i = X.R i j := by simp only [Mix.R]; ring
        rw [hRji]; exact hx.1.le
      · have hlji : -(X.lam j i) = X.lam i j := by simp only [Mix.lam]; ring
        rw [hlji]; linarith [hx.2, hlam]
    rw [pMixEntry_eq_indicator_quad, Set.indicator_of_mem hmem]
  have hsum : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ∑ k, qpConv X i k j x)
      (Set.Ioo (-(X.R i j)) (-(X.lam i j))) :=
    ContDiffOn.sum (fun k _ => qpConv_contDiffOn_upper_neg X i k j hlam)
  exact (hqFwd.add hpMix).sub hsum

/-- **Reflected HS DCF assembly** `cHSmixRaw` is `ContDiffOn` `(−λᵢⱼ, 0)`.  Same structure as the
reflected upper piece: `qFwd_ij` vanishes, `pMixEntry_ji` is the quadratic, and each `qpConv` is
`ContDiffOn` (`qpConv_contDiffOn_lower_neg`). -/
theorem cHSmixRaw_contDiffOn_lower_neg {N M : ℕ} (X : Mix N M) (i j : Fin N) (hlam : 0 ≤ X.lam i j) :
    ContDiffOn ℝ (⊤ : ℕ∞) (cHSmixRaw X i j) (Set.Ioo (-(X.lam i j)) (0 : ℝ)) := by
  have hqFwd : ContDiffOn ℝ (⊤ : ℕ∞) (qFwd X i j) (Set.Ioo (-(X.lam i j)) (0 : ℝ)) := by
    refine (contDiff_const (c := (0 : ℝ))).contDiffOn.congr ?_
    intro x hx
    apply Function.notMem_support.mp
    intro hs
    have hh := qFwd_support_subset X i j hs
    rw [Set.mem_Icc] at hh
    linarith [hh.1, hx.2, hlam]
  have hpMix : ContDiffOn ℝ (⊤ : ℕ∞) (pMixEntry X j i) (Set.Ioo (-(X.lam i j)) (0 : ℝ)) := by
    refine (ContDiff.contDiffOn (f := fun u => 2 * Real.pi * Real.sqrt (X.ρ j * X.ρ i)
        * (X.Q0 j i * (-u - X.R j i) + X.Qpp i * (-u - X.R j i) ^ 2 / 2)) (by fun_prop)).congr ?_
    intro x hx
    have hmem : x ∈ Set.Icc (-(X.R j i)) (-(X.lam j i)) := by
      rw [Set.mem_Icc]
      refine ⟨?_, ?_⟩
      · have hRji : X.R j i = X.R i j := by simp only [Mix.R]; ring
        have hRge : X.lam i j ≤ X.R i j := by simp only [Mix.R, Mix.lam]; linarith [X.hσ i]
        rw [hRji]; linarith [hx.1, hRge]
      · have hlji : -(X.lam j i) = X.lam i j := by simp only [Mix.lam]; ring
        rw [hlji]; linarith [hx.2, hlam]
    rw [pMixEntry_eq_indicator_quad, Set.indicator_of_mem hmem]
  have hsum : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => ∑ k, qpConv X i k j x)
      (Set.Ioo (-(X.lam i j)) (0 : ℝ)) :=
    ContDiffOn.sum (fun k _ => qpConv_contDiffOn_lower_neg X i k j hlam)
  exact (hqFwd.add hpMix).sub hsum

/-! ### General-N odd inner HS DCF `cHSodd` — two-piece smoothness on the physical core -/

/-- **General-N `cHSodd` is `ContDiffOn` the upper physical-core piece `(λᵢⱼ, Rᵢⱼ)`** (for `σⱼ ≥ σᵢ`).
`cHSodd(x) = cHSmixRaw(x) − cHSmixRaw(−x)`: the first term is `ContDiffOn (λᵢⱼ,Rᵢⱼ)`
(`cHSmixRaw_contDiffOn_upper`) and `x ↦ −x` maps `(λᵢⱼ,Rᵢⱼ)` into the reflected upper piece
`(−Rᵢⱼ,−λᵢⱼ)` where `cHSmixRaw` is `ContDiffOn` (`cHSmixRaw_contDiffOn_upper_neg`).  General-N analog
of `cHSodd_N1_contDiffOn`. -/
theorem cHSodd_contDiffOn_upper {N M : ℕ} (X : Mix N M) (i j : Fin N) (hlam : 0 ≤ X.lam i j) :
    ContDiffOn ℝ (⊤ : ℕ∞) (cHSodd X i j) (Set.Ioo (X.lam i j) (X.R i j)) := by
  have hco : cHSodd X i j = fun x => cHSmixRaw X i j x - cHSmixRaw X i j (-x) := rfl
  rw [hco]
  refine (cHSmixRaw_contDiffOn_upper X i j hlam).sub
    ((cHSmixRaw_contDiffOn_upper_neg X i j hlam).comp contDiff_neg.contDiffOn (fun x hx => ?_))
  simp only [Set.mem_Ioo] at hx ⊢
  exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-- **General-N `cHSodd` is `ContDiffOn` the lower physical-core piece `(0, λᵢⱼ)`** (for `σⱼ ≥ σᵢ`).
Same route with the lower pieces: `cHSmixRaw_contDiffOn_lower` on `(0,λᵢⱼ)` and, via `x ↦ −x` into
`(−λᵢⱼ,0)`, `cHSmixRaw_contDiffOn_lower_neg`. -/
theorem cHSodd_contDiffOn_lower {N M : ℕ} (X : Mix N M) (i j : Fin N) (hlam : 0 ≤ X.lam i j) :
    ContDiffOn ℝ (⊤ : ℕ∞) (cHSodd X i j) (Set.Ioo (0 : ℝ) (X.lam i j)) := by
  have hco : cHSodd X i j = fun x => cHSmixRaw X i j x - cHSmixRaw X i j (-x) := rfl
  rw [hco]
  refine (cHSmixRaw_contDiffOn_lower X i j hlam).sub
    ((cHSmixRaw_contDiffOn_lower_neg X i j hlam).comp contDiff_neg.contDiffOn (fun x hx => ?_))
  simp only [Set.mem_Ioo] at hx ⊢
  exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

end
end FMSA.MixtureHSDCF
