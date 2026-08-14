/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MixtureCorrelationDeriv

/-!
# The UPPER-piece `qpConv` derivative — moving-limit Leibniz (general `N`)

`MixtureCorrelationDeriv.lean` gave the LOWER-piece derivative `hasDerivAt_qpConv_lower`: on
`(0, λᵢⱼ)` the whole window `[λᵢₖ, Rᵢₖ]` sits inside the `pMixEntry` support, so the limits are
**fixed** and only the `pMixEntry` quadratic's coefficients depend on the parameter
(`hasDerivAt_fixedConv_quadParam`, no boundary term).

On the UPPER piece `(λᵢⱼ, Rᵢⱼ)` the overlap gives a **moving lower limit** `x + λⱼₖ`, so the
derivative picks up an FTC boundary term in addition to the parametric interior term.  This file
builds the moving-limit analog `hasDerivAt_movingConv_quadParam` (FTC-left `∘` the affine shift +
the fixed-limit parametric Leibniz) and hence `hasDerivAt_qpConv_upper` with the explicit derivative
`qpConvUpperDeriv`.
-/

open MeasureTheory intervalIntegral

namespace FMSA.MixtureHSDCF

open FMSA.InnerDecomp FMSA.WHSupports FMSA.MixtureConvolution

variable {N M : ℕ}

/-- **Moving-lower-limit parametric quadratic-convolution derivative (generic helper).**  For a
continuous `F` and parameter-dependent coefficients `A, B` (with `HasDerivAt`), the moving-limit
integral `∫ t in (y+c)..b, F(t)·(A y + B y·t + C t²) dt` differentiates as the fixed-limit Leibniz
`A'·∫F + B'·∫F·t` **plus** the FTC boundary term `−F(x+c)·(A x + B x(x+c) + C(x+c)²)` from the
moving lower limit `y+c`.  (Each moment differentiates by FTC-left `∘` the shift `y↦y+c`.) -/
theorem hasDerivAt_movingConv_quadParam {F : ℝ → ℝ} (hF : Continuous F) {A B : ℝ → ℝ}
    {C a' b' c b x : ℝ} (hA : HasDerivAt A a' x) (hB : HasDerivAt B b' x) :
    HasDerivAt (fun y => ∫ t in (y + c)..b, F t * (A y + B y * t + C * t ^ 2))
      (a' * (∫ t in (x + c)..b, F t) + b' * (∫ t in (x + c)..b, F t * t)
        - F (x + c) * (A x + B x * (x + c) + C * (x + c) ^ 2)) x := by
  have hinner : HasDerivAt (fun y : ℝ => y + c) 1 x := (hasDerivAt_id x).add_const c
  have mkM : ∀ (g : ℝ → ℝ), Continuous g →
      HasDerivAt (fun y => ∫ t in (y + c)..b, g t) (-(g (x + c))) x := by
    intro g hg
    have hi : IntervalIntegrable g volume (x + c) b := hg.intervalIntegrable _ _
    have hleft := (intervalIntegral.integral_hasStrictDerivAt_left hi
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt).hasDerivAt
    have hcomp : (fun y => ∫ t in (y + c)..b, g t)
        = (fun u => ∫ t in u..b, g t) ∘ (fun y => y + c) := rfl
    rw [hcomp]
    have h := hleft.comp x hinner
    rwa [mul_one] at h
  have hM0 := mkM F hF
  have hM1 := mkM (fun t => F t * t) (hF.mul continuous_id)
  have hM2 := mkM (fun t => F t * t ^ 2) (hF.mul (continuous_pow 2))
  have hsplit : (fun y => ∫ t in (y + c)..b, F t * (A y + B y * t + C * t ^ 2))
      = fun y => A y * (∫ t in (y + c)..b, F t) + B y * (∫ t in (y + c)..b, F t * t)
        + C * (∫ t in (y + c)..b, F t * t ^ 2) := by
    funext y
    have iF : IntervalIntegrable F volume (y + c) b := hF.intervalIntegrable _ _
    have iFt : IntervalIntegrable (fun t => F t * t) volume (y + c) b :=
      (hF.mul continuous_id).intervalIntegrable _ _
    have iFt2 : IntervalIntegrable (fun t => F t * t ^ 2) volume (y + c) b :=
      (hF.mul (continuous_pow 2)).intervalIntegrable _ _
    rw [intervalIntegral.integral_congr
        (g := fun t => A y * F t + B y * (F t * t) + C * (F t * t ^ 2)) (fun t _ => by ring),
      intervalIntegral.integral_add ((iF.const_mul (A y)).add (iFt.const_mul (B y)))
        (iFt2.const_mul C),
      intervalIntegral.integral_add (iF.const_mul (A y)) (iFt.const_mul (B y)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [hsplit]
  exact (((hA.mul hM0).add (hB.mul hM1)).add (hM2.const_mul C)).congr_deriv (by ring)

/-- **The explicit UPPER-piece `qpConv` derivative value** `qpConvUpperDeriv X i k j x` — the value
`(qpConv X i k j)'(x)` takes on `(λᵢⱼ, Rᵢⱼ)`: the two `pMixEntry` coefficient derivatives against
the forward-quadratic moments `∫Fwd`, `∫Fwd·t` over the **moving** window `[x+λⱼₖ, Rᵢₖ]`, **minus**
the FTC boundary term (the forward quadratic times the shifted quadratic, both at the moving edge
`x+λⱼₖ`). -/
noncomputable def qpConvUpperDeriv (X : Mix N M) (i k j : Fin N) (x : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt (X.ρ j * X.ρ k) * (-X.Q0 j k + X.Qpp k * (x + X.R j k))
      * (∫ t in (x + X.lam j k)..(X.R i k), 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ k)
          * (-X.Q0 i k * X.R i k + X.Qpp k * X.R i k ^ 2 / 2)
        + 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ k) * (X.Q0 i k - X.Qpp k * X.R i k) * t
        + 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ k) * (X.Qpp k / 2) * t ^ 2)
    + 2 * Real.pi * Real.sqrt (X.ρ j * X.ρ k) * (-X.Qpp k)
      * (∫ t in (x + X.lam j k)..(X.R i k), (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ k)
          * (-X.Q0 i k * X.R i k + X.Qpp k * X.R i k ^ 2 / 2)
        + 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ k) * (X.Q0 i k - X.Qpp k * X.R i k) * t
        + 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ k) * (X.Qpp k / 2) * t ^ 2) * t)
    - (2 * Real.pi * Real.sqrt (X.ρ i * X.ρ k)
          * (-X.Q0 i k * X.R i k + X.Qpp k * X.R i k ^ 2 / 2)
        + 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ k) * (X.Q0 i k - X.Qpp k * X.R i k)
            * (x + X.lam j k)
        + 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ k) * (X.Qpp k / 2) * (x + X.lam j k) ^ 2)
      * (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ k)
          * (-X.Q0 j k * (x + X.R j k) + X.Qpp k * (x + X.R j k) ^ 2 / 2)
        + 2 * Real.pi * Real.sqrt (X.ρ j * X.ρ k) * (X.Q0 j k - X.Qpp k * (x + X.R j k))
            * (x + X.lam j k)
        + 2 * Real.pi * Real.sqrt (X.ρ j * X.ρ k) * (X.Qpp k / 2) * (x + X.lam j k) ^ 2)

/-- **Correlation derivative on the upper piece.**  On `(λᵢⱼ, Rᵢⱼ)` the upper interval form
`qpConv X i k j x = ∫ t in (x+λⱼₖ)..(Rᵢₖ), Fwd(t)·(A x + B x·t + C t²)` has a moving lower limit, so
it differentiates by `hasDerivAt_movingConv_quadParam`: `(qpConv)'(x) = qpConvUpperDeriv`.  The
unequal-σ UPPER analog of `hasDerivAt_qpConv_lower`. -/
theorem hasDerivAt_qpConv_upper (X : Mix N M) (i k j : Fin N) (hlam : 0 ≤ X.lam i j)
    {x : ℝ} (hx : x ∈ Set.Ioo (X.lam i j) (X.R i j)) :
    HasDerivAt (qpConv X i k j) (qpConvUpperDeriv X i k j x) x := by
  rw [qpConvUpperDeriv]
  set F : ℝ → ℝ := fun t => 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ k)
      * (-X.Q0 i k * X.R i k + X.Qpp k * X.R i k ^ 2 / 2)
    + 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ k) * (X.Q0 i k - X.Qpp k * X.R i k) * t
    + 2 * Real.pi * Real.sqrt (X.ρ i * X.ρ k) * (X.Qpp k / 2) * t ^ 2 with hF
  set A : ℝ → ℝ := fun y => 2 * Real.pi * Real.sqrt (X.ρ j * X.ρ k)
    * (-X.Q0 j k * (y + X.R j k) + X.Qpp k * (y + X.R j k) ^ 2 / 2) with hA
  set B : ℝ → ℝ := fun y => 2 * Real.pi * Real.sqrt (X.ρ j * X.ρ k)
    * (X.Q0 j k - X.Qpp k * (y + X.R j k)) with hB
  have hFcont : Continuous F := by rw [hF]; fun_prop
  have hAd : HasDerivAt A
      (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ k) * (-X.Q0 j k + X.Qpp k * (x + X.R j k))) x := by
    have h1 : HasDerivAt (fun y : ℝ => y + X.R j k) 1 x := (hasDerivAt_id x).add_const _
    have ha := h1.const_mul (-X.Q0 j k)
    have hb := ((h1.pow 2).const_mul (X.Qpp k)).div_const 2
    rw [hA]
    exact ((ha.add hb).const_mul
      (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ k))).congr_deriv (by ring)
  have hBd : HasDerivAt B
      (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ k) * (-X.Qpp k)) x := by
    have h1 : HasDerivAt (fun y : ℝ => y + X.R j k) 1 x := (hasDerivAt_id x).add_const _
    have hb := (hasDerivAt_const x (X.Q0 j k)).sub (h1.const_mul (X.Qpp k))
    rw [hB]
    exact (hb.const_mul (2 * Real.pi * Real.sqrt (X.ρ j * X.ρ k))).congr_deriv (by ring)
  have hbase := hasDerivAt_movingConv_quadParam (F := F) hFcont (A := A) (B := B)
    (C := 2 * Real.pi * Real.sqrt (X.ρ j * X.ρ k) * (X.Qpp k / 2)) (c := X.lam j k)
    (b := X.R i k) hAd hBd
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  rw [qpConv_upper_intervalForm X i k j hlam hy]

end FMSA.MixtureHSDCF
