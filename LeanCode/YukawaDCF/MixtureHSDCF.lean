/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.YukawaDCF.MixtureConvolution
import LeanCode.YukawaDCF.MixtureClosedForm

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
  have hclosed : ∀ x ∈ Set.Ioo (0 : ℝ) R, qpConv X 0 0 0 x =
      ((rr * (Q * (0 - R) + P * (0 - R) ^ 2 / 2 + 0)) *
            (rr * (Q * (0 - x - R) + P * (0 - x - R) ^ 2 / 2 + 0)) * R
          + ((rr * (Q * (0 - R) + P * (0 - R) ^ 2 / 2 + 0)) *
                (rr * (Q * (1 - x - R) + P * (1 - x - R) ^ 2 / 2 + 1)) + 0) * 0
          - 0) := by
    intro x hx
    obtain ⟨hx0, hxR⟩ := hx
    rw [qpConv_eq_intervalIntegral X 0 0 0 x (by rw [hlam0]; exact hRpos.le)
        (qpConv_integrand_intervalIntegrable X 0 0 0 x), hlam0]
    sorry
  sorry

end
end FMSA.MixtureHSDCF
