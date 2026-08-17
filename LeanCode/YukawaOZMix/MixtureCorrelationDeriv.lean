/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MixtureHSDCF

/-!
# Derivative of the mixture correlation `qpConv` (MIXCHS.7 building block)

`qpConv X i k j = qFwd(i,k) ⋆ pMixEntry(j,k)` is the real-space self-convolution term of the mixture
HS DCF (`matCorrFull = ∑ₖ qpConv/(2π)²`).  For the unequal-diameter Baxter ODE we need its
**derivative** on each smooth piece.  `MixtureHSDCF.qpConv_contDiffOn_upper` already shows `qpConv`
is `C^∞` on the upper core piece `(λᵢⱼ, Rᵢⱼ)` by exhibiting it there as the explicit degree-5
polynomial `integral_quad_mul_quad`.  This file lifts that closed form to a **named** lemma to read
`HasDerivAt`.

* `qpConv_upper_intervalForm` — on `(λᵢⱼ, Rᵢⱼ)`, `qpConv X i k j x` = `∫ t in (x+Ljk)..Rik,
  (fwd quad)·(pMix quad)` (overlap `[x+Ljk, Rik]`, moving lower limit).
* `qpConv_lower_intervalForm` — on `(0, λᵢⱼ)`, `qpConv X i k j x` = `∫ t in λᵢₖ..Rᵢₖ, (fwd
  quad)·(pMix quad)` (the whole window, FIXED limits — no split).
* `hasDerivAt_fixedConv_quadParam` — generic fixed-limit parametric quadratic-conv derivative.
* `hasDerivAt_qpConv_lower` — the **correlation derivative on the lower piece**:
  `(qpConv)'(x) = rrⱼ(−Qⱼ+Pₖ(x+Rⱼₖ))·∫Fwd + rrⱼ(−Pₖ)·∫Fwd·t` (parameter-Leibniz, no boundary term).

`integral_quad_mul_quad` turns either interval form into an explicit degree-5 polynomial; the
upper-piece derivative additionally carries the moving-lower-limit boundary term.

The coefficients (matching `qpConv_contDiffOn_upper`): `rri = 2π√(ρᵢρₖ)`, `rrj = 2π√(ρⱼρₖ)`,
`Qi = Q0 i k`, `Qj = Q0 j k`, `Pk = Qpp k`, `Rik = R i k`, `Rjk = R j k`, `Ljk = lam j k`;
`c0 = rri(−QiRik + PkRik²/2)`, `c1 = rri(Qi − PkRik)`, `c2 = rri·Pk/2`;
`D0 x = rrj(−Qj(x+Rjk) + Pk(x+Rjk)²/2)`, `D1 x = rrj(Qj − Pk(x+Rjk))`, `d2 = rrj·Pk/2`.
-/

set_option linter.style.longLine false

open MeasureTheory Set

namespace FMSA.MixtureHSDCF

open FMSA.InnerDecomp FMSA.WHSupports FMSA.MixtureConvolution FMSA.MixtureClosedForm

variable {N M : ℕ}

/-- **`qpConv` on the upper core piece is the two-quadratic overlap integral.**  For
`x ∈ (λᵢⱼ, Rᵢⱼ)` with `λᵢⱼ ≥ 0`, the self-convolution `qpConv X i k j x` equals
`∫ t in (x+Ljk)..Rik, (c0+c1 t+c2 t²)·(D0 x + D1 x·t + d2 t²) dt` — integrating the
`(fwd quad)·(pMixEntry quad)` integrand over the overlap `[x+Ljk, Rik]` (the `[λᵢₖ, x+Ljk]` part
vanishes since `pMixEntry(x−t)=0` there).  Standalone form of the `hclosed` step inside
`qpConv_contDiffOn_upper`; `integral_quad_mul_quad` evaluates it to a degree-5 polynomial. -/
theorem qpConv_upper_intervalForm (X : Mix N M) (i k j : Fin N) (hlam : 0 ≤ X.lam i j)
    {x : ℝ} (hx : x ∈ Set.Ioo (X.lam i j) (X.R i j)) :
    qpConv X i k j x
      = ∫ t in (x + X.lam j k)..(X.R i k),
          (2 * Real.pi * Real.sqrt (X.rho i * X.rho k)
              * (-X.Q0 i k * X.R i k + X.Qpp k * X.R i k ^ 2 / 2)
            + 2 * Real.pi * Real.sqrt (X.rho i * X.rho k) * (X.Q0 i k - X.Qpp k * X.R i k) * t
            + 2 * Real.pi * Real.sqrt (X.rho i * X.rho k) * (X.Qpp k / 2) * t ^ 2)
          * (2 * Real.pi * Real.sqrt (X.rho j * X.rho k)
              * (-X.Q0 j k * (x + X.R j k) + X.Qpp k * (x + X.R j k) ^ 2 / 2)
            + 2 * Real.pi * Real.sqrt (X.rho j * X.rho k) * (X.Q0 j k - X.Qpp k * (x + X.R j k)) * t
            + 2 * Real.pi * Real.sqrt (X.rho j * X.rho k) * (X.Qpp k / 2) * t ^ 2) := by
  have hkR : X.lam i k ≤ X.R i k := by have := X.hsigma i; simp only [Mix.lam, Mix.R]; linarith
  have hLid : X.lam i k - X.lam j k = X.lam i j := by simp only [Mix.lam]; ring
  have hRid : X.R i k - X.lam j k = X.R i j := by simp only [Mix.R, Mix.lam]; ring
  have hRRid : X.R i k - X.R j k = -(X.lam i j) := by simp only [Mix.R, Mix.lam]; ring
  obtain ⟨hxlo, hxhi⟩ := hx
  rw [qpConv_eq_intervalIntegral X i k j x hkR (qpConv_integrand_intervalIntegrable X i k j x)]
  have hint := qpConv_integrand_intervalIntegrable X i k j x
  have hlo : X.lam i k ≤ x + X.lam j k := by linarith [hLid]
  have hhi : x + X.lam j k ≤ X.R i k := by linarith [hRid]
  have hI0 := hint.mono_set (Set.uIcc_subset_uIcc
    (Set.mem_uIcc.mpr (Or.inl ⟨le_refl _, hkR⟩))
    (Set.mem_uIcc.mpr (Or.inl ⟨hlo, hhi⟩)) :
      Set.uIcc (X.lam i k) (x + X.lam j k) ⊆ Set.uIcc (X.lam i k) (X.R i k))
  have hIx := hint.mono_set (Set.uIcc_subset_uIcc
    (Set.mem_uIcc.mpr (Or.inl ⟨hlo, hhi⟩))
    (Set.mem_uIcc.mpr (Or.inl ⟨hkR, le_refl _⟩)) :
      Set.uIcc (x + X.lam j k) (X.R i k) ⊆ Set.uIcc (X.lam i k) (X.R i k))
  rw [← intervalIntegral.integral_add_adjacent_intervals hI0 hIx]
  have hvanish : (∫ t in (X.lam i k)..(x + X.lam j k), (2 * Real.pi * Real.sqrt (X.rho i * X.rho k)
        * (X.Q0 i k * (t - X.R i k) + X.Qpp k * (t - X.R i k) ^ 2 / 2))
          * pMixEntry X j k (x - t)) = 0 := by
    rw [intervalIntegral.integral_congr_ae ?_, intervalIntegral.integral_zero]
    rw [Set.uIoc_of_le hlo]
    have hne : ∀ᵐ (y : ℝ), y ≠ x + X.lam j k := by rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hne] with t ht hmem
    have htlt : t < x + X.lam j k := lt_of_le_of_ne hmem.2 ht
    have hpm0 : pMixEntry X j k (x - t) = 0 := by
      apply Function.notMem_support.mp
      intro hs
      have hh := pMixEntry_support_subset X j k hs
      rw [Set.mem_Icc] at hh
      linarith [hh.2, htlt]
    simp only [hpm0, mul_zero]
  rw [hvanish, zero_add]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le hhi] at ht
  have hmem : x - t ∈ Set.Icc (-(X.R j k)) (-(X.lam j k)) := by
    rw [Set.mem_Icc]
    refine ⟨?_, by linarith [ht.1]⟩
    have : X.R i k - X.R j k = -(X.lam i j) := hRRid; linarith [ht.2, this, hlam]
  rw [pMixEntry_eq_indicator_quad, Set.indicator_of_mem hmem]
  ring

/-- **`qpConv` on the lower core piece is the two-quadratic integral over the FULL window.**  For
`x ∈ (0, λᵢⱼ)` (with `λᵢⱼ ≥ 0`) the whole window `[λᵢₖ, Rᵢₖ]` lies inside the `pMixEntry` support,
so there is no overlap split: `qpConv X i k j x = ∫ t in (λᵢₖ)..(Rᵢₖ), (c0+c1 t+c2 t²)·(D0 x +
D1 x·t + d2 t²) dt` with **fixed** limits — `x` enters only through the `pMixEntry` quadratic.  So
on the lower piece the correlation derivative is the pure parameter-Leibniz `∫ (fwd quad)·∂ₓ(pMix
quad)` (no boundary term), unlike the upper piece's moving lower limit. -/
theorem qpConv_lower_intervalForm (X : Mix N M) (i k j : Fin N) (hlam : 0 ≤ X.lam i j)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (X.lam i j)) :
    qpConv X i k j x
      = ∫ t in (X.lam i k)..(X.R i k),
          (2 * Real.pi * Real.sqrt (X.rho i * X.rho k)
              * (-X.Q0 i k * X.R i k + X.Qpp k * X.R i k ^ 2 / 2)
            + 2 * Real.pi * Real.sqrt (X.rho i * X.rho k) * (X.Q0 i k - X.Qpp k * X.R i k) * t
            + 2 * Real.pi * Real.sqrt (X.rho i * X.rho k) * (X.Qpp k / 2) * t ^ 2)
          * (2 * Real.pi * Real.sqrt (X.rho j * X.rho k)
              * (-X.Q0 j k * (x + X.R j k) + X.Qpp k * (x + X.R j k) ^ 2 / 2)
            + 2 * Real.pi * Real.sqrt (X.rho j * X.rho k) * (X.Q0 j k - X.Qpp k * (x + X.R j k)) * t
            + 2 * Real.pi * Real.sqrt (X.rho j * X.rho k) * (X.Qpp k / 2) * t ^ 2) := by
  have hkR : X.lam i k ≤ X.R i k := by have := X.hsigma i; simp only [Mix.lam, Mix.R]; linarith
  have hLid : X.lam i k - X.lam j k = X.lam i j := by simp only [Mix.lam]; ring
  have hRRid : X.R i k - X.R j k = -(X.lam i j) := by simp only [Mix.R, Mix.lam]; ring
  obtain ⟨hx0, hxlam⟩ := hx
  rw [qpConv_eq_intervalIntegral X i k j x hkR (qpConv_integrand_intervalIntegrable X i k j x)]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le hkR] at ht
  have hmem : x - t ∈ Set.Icc (-(X.R j k)) (-(X.lam j k)) := by
    rw [Set.mem_Icc]
    refine ⟨by linarith [ht.2, hx0, hRRid], by linarith [ht.1, hxlam, hLid]⟩
  rw [pMixEntry_eq_indicator_quad, Set.indicator_of_mem hmem]
  ring

/-- **Fixed-limit parametric quadratic-convolution derivative (generic helper).**  For a continuous
`F` and parameter-dependent coefficients `A, B` (with `HasDerivAt`), the fixed-limit integral
`∫ F(t)·(A y + B y·t + C t²) dt` has derivative `A'·∫F + B'·∫F·t` — the `C t²` moment is constant,
so only `A, B` contribute.  (Pull the `y`-constants out of the integral, then differentiate.) -/
theorem hasDerivAt_fixedConv_quadParam {F : ℝ → ℝ} (hF : Continuous F) {A B : ℝ → ℝ}
    {C a' b' x : ℝ} (α β : ℝ) (hA : HasDerivAt A a' x) (hB : HasDerivAt B b' x) :
    HasDerivAt (fun y => ∫ t in α..β, F t * (A y + B y * t + C * t ^ 2))
      (a' * (∫ t in α..β, F t) + b' * (∫ t in α..β, F t * t)) x := by
  have iF : IntervalIntegrable F volume α β := hF.intervalIntegrable _ _
  have iFt : IntervalIntegrable (fun t => F t * t) volume α β :=
    (hF.mul continuous_id).intervalIntegrable _ _
  have iFt2 : IntervalIntegrable (fun t => F t * t ^ 2) volume α β :=
    (hF.mul (continuous_pow 2)).intervalIntegrable _ _
  have hsplit : ∀ y : ℝ, (∫ t in α..β, F t * (A y + B y * t + C * t ^ 2))
      = A y * (∫ t in α..β, F t) + B y * (∫ t in α..β, F t * t)
        + C * (∫ t in α..β, F t * t ^ 2) := by
    intro y
    rw [intervalIntegral.integral_congr
        (g := fun t => A y * F t + B y * (F t * t) + C * (F t * t ^ 2)) (fun t _ => by ring),
      intervalIntegral.integral_add ((iF.const_mul (A y)).add (iFt.const_mul (B y)))
        (iFt2.const_mul C),
      intervalIntegral.integral_add (iF.const_mul (A y)) (iFt.const_mul (B y)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  simp_rw [hsplit]
  exact ((hA.mul_const _).add (hB.mul_const _)).add_const _

/-- **The explicit lower-piece `qpConv` derivative value** `qpConvLowerDeriv X i k j x` — the value
`(qpConv X i k j)'(x)` takes on `(0, λᵢⱼ)` (see `hasDerivAt_qpConv_lower`): the two `pMixEntry`
coeff derivatives `rrⱼ(−Qⱼ+Pₖ(x+Rⱼₖ))`, `rrⱼ(−Pₖ)` against the constant forward-quadratic moments
`∫Fwd`, `∫Fwd·t`.  Named so the species sum `∑ₗ qpConvLowerDeriv/(2π)²` (= `matCorrFull'`) is
stateable. -/
noncomputable def qpConvLowerDeriv (X : Mix N M) (i k j : Fin N) (x : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt (X.rho j * X.rho k) * (-X.Q0 j k + X.Qpp k * (x + X.R j k))
      * (∫ t in (X.lam i k)..(X.R i k), 2 * Real.pi * Real.sqrt (X.rho i * X.rho k)
          * (-X.Q0 i k * X.R i k + X.Qpp k * X.R i k ^ 2 / 2)
        + 2 * Real.pi * Real.sqrt (X.rho i * X.rho k) * (X.Q0 i k - X.Qpp k * X.R i k) * t
        + 2 * Real.pi * Real.sqrt (X.rho i * X.rho k) * (X.Qpp k / 2) * t ^ 2)
    + 2 * Real.pi * Real.sqrt (X.rho j * X.rho k) * (-X.Qpp k)
      * (∫ t in (X.lam i k)..(X.R i k), (2 * Real.pi * Real.sqrt (X.rho i * X.rho k)
          * (-X.Q0 i k * X.R i k + X.Qpp k * X.R i k ^ 2 / 2)
        + 2 * Real.pi * Real.sqrt (X.rho i * X.rho k) * (X.Q0 i k - X.Qpp k * X.R i k) * t
        + 2 * Real.pi * Real.sqrt (X.rho i * X.rho k) * (X.Qpp k / 2) * t ^ 2) * t)

/-- **Correlation derivative on the lower piece.**  On `(0, λᵢⱼ)` the fixed-limit lower closed form
`qpConv X i k j x = ∫ Fwd(t)·(D0 x + D1 x·t + d2 t²) dt` differentiates by the parameter-Leibniz
rule alone (no boundary term, `hasDerivAt_fixedConv_quadParam`): only the `pMixEntry` coefficients
`D0 x, D1 x` depend on `x`, so `(qpConv)'(x) = qpConvLowerDeriv = D0'(x)·∫Fwd + D1'(x)·∫Fwd·t` with
`D0'(x) = rrⱼ(−Qⱼ+Pₖ(x+Rⱼₖ))`, `D1'(x) = rrⱼ(−Pₖ)`.  The unequal-σ analog of `hasDerivAt_corrM`. -/
theorem hasDerivAt_qpConv_lower (X : Mix N M) (i k j : Fin N) (hlam : 0 ≤ X.lam i j)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (X.lam i j)) :
    HasDerivAt (qpConv X i k j) (qpConvLowerDeriv X i k j x) x := by
  rw [qpConvLowerDeriv]
  -- the explicit forward quadratic `F` and the `x`-dependent `pMixEntry` coefficients `D0, D1`
  set F : ℝ → ℝ := fun t => 2 * Real.pi * Real.sqrt (X.rho i * X.rho k)
      * (-X.Q0 i k * X.R i k + X.Qpp k * X.R i k ^ 2 / 2)
    + 2 * Real.pi * Real.sqrt (X.rho i * X.rho k) * (X.Q0 i k - X.Qpp k * X.R i k) * t
    + 2 * Real.pi * Real.sqrt (X.rho i * X.rho k) * (X.Qpp k / 2) * t ^ 2 with hF
  set D0 : ℝ → ℝ := fun y => 2 * Real.pi * Real.sqrt (X.rho j * X.rho k)
    * (-X.Q0 j k * (y + X.R j k) + X.Qpp k * (y + X.R j k) ^ 2 / 2) with hD0
  set D1 : ℝ → ℝ := fun y => 2 * Real.pi * Real.sqrt (X.rho j * X.rho k)
    * (X.Q0 j k - X.Qpp k * (y + X.R j k)) with hD1
  have hFcont : Continuous F := by rw [hF]; fun_prop
  have hD0d : HasDerivAt D0
      (2 * Real.pi * Real.sqrt (X.rho j * X.rho k) * (-X.Q0 j k + X.Qpp k * (x + X.R j k))) x := by
    have h1 : HasDerivAt (fun y : ℝ => y + X.R j k) 1 x := (hasDerivAt_id x).add_const _
    have ha := h1.const_mul (-X.Q0 j k)
    have hb := ((h1.pow 2).const_mul (X.Qpp k)).div_const 2
    rw [hD0]
    exact ((ha.add hb).const_mul
      (2 * Real.pi * Real.sqrt (X.rho j * X.rho k))).congr_deriv (by ring)
  have hD1d : HasDerivAt D1
      (2 * Real.pi * Real.sqrt (X.rho j * X.rho k) * (-X.Qpp k)) x := by
    have h1 : HasDerivAt (fun y : ℝ => y + X.R j k) 1 x := (hasDerivAt_id x).add_const _
    have hb := (hasDerivAt_const x (X.Q0 j k)).sub (h1.const_mul (X.Qpp k))
    rw [hD1]
    exact (hb.const_mul (2 * Real.pi * Real.sqrt (X.rho j * X.rho k))).congr_deriv (by ring)
  have hbase := hasDerivAt_fixedConv_quadParam (F := F) hFcont (A := D0) (B := D1)
    (C := 2 * Real.pi * Real.sqrt (X.rho j * X.rho k) * (X.Qpp k / 2)) (X.lam i k) (X.R i k) hD0d hD1d
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  rw [qpConv_lower_intervalForm X i k j hlam hy]

end FMSA.MixtureHSDCF
