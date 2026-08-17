/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MixtureDCFAEInjective
import LeanCode.HardSphere.BaxterForcingDeriv
import LeanCode.HSMixture.PhysHSMixRhoWeight

/-!
# The mixture Baxter ODE at equal diameters — closing MRS.8's `shellForcing = c_HS` gap

The whole open Baxter–Wiener–Hopf content of MRS.8 (the OZ★ value route) was reduced in
`MixtureDCFAEInjective.lean` to the single pointwise ODE
`(matDCFreCore/ρ)'(s) = −2π·s·c_HS(s)` on `(0,σ)` (`shellForcing_eq_cHS_of_baxterODE`), and the
**scalar N=1 case** of that ODE was proved in `BaxterForcingDeriv.lean` (`baxterODE_n1`).

This file closes the gap at **equal diameters** by reducing the mixture ODE to the scalar one.
At equal diameters the physical Baxter entry `q0MixEntry(physMix)ᵢₖ` is INDEPENDENT of the pair
`(i,k)` — a single windowed quadratic `Qbar = 1[0,σ]·q0_poly(η,σ,1)`
(`q0MixEntry_physMix_eq_indicator`, from `Q0phys_equalDiam`/`Qppphys_equalDiam`) — and the ρ-geo
product relation `rgᵢₘ·rgₖₘ = ρₘ·rgᵢₖ` (`rhoGeoPhys_mul_eq`) collapses the correlation
`matCorrFull(qWeighted)ᵢₖ` to `rgᵢₖ·(∑ρ)·(Qbar ⋆ Qbar)`.  The convolution `Qbar ⋆ Qbar` reindexes
to the scalar autocorrelation `∫₀^σ q0_poly(t+v)q0_poly(t)` of `baxterODE_n1`
(`q0_poly_indicator_conv`, a support/shift argument).  Hence

  `matDCFreCore(η,σ)ᵢₖ = (rgᵢₖ/∑ρ)·(q0_poly(∑ρ) − ∫₀^σ q0_poly(∑ρ)(t+·)q0_poly(∑ρ)(t))`

on `(0,σ)`, and `matDCFreCoreᵢₖ'(s) = −2π·rgᵢₖ·s·c_HS(s)` follows by scaling `baxterODE_n1`
(`matDCFreCore_hasDerivAt_equalDiam`).  Feeding this into `shellForcing_eq_cHS_of_baxterODE` with the
per-entry normalization `ρ = rgᵢₖ` gives `shellForcing rgᵢₖ i k = c_HS` UNCONDITIONALLY at equal
diameters (`shellForcing_eq_cHS_equalDiam`) — the open Baxter–WH input of MRS.8, discharged.
-/

open MeasureTheory Set

namespace FMSA.MixtureBaxter
open FMSA.HardSphere

/-- `q0_poly` is linear in the density amplitude `ρ`: `q0_poly η σ ρ r = ρ·q0_poly η σ 1 r`. -/
theorem q0_poly_eq_rho_smul (eta sigma rho r : ℝ) :
    q0_poly eta sigma rho r = rho * q0_poly eta sigma 1 r := by
  simp only [q0_poly]; ring

/-- `q0_poly` vanishes at and beyond the core edge: `q0_poly η σ ρ y = 0` for `σ ≤ y`. -/
theorem q0_poly_zero_of_ge {eta sigma rho y : ℝ} (hy : sigma ≤ y) : q0_poly eta sigma rho y = 0 := by
  rcases hy.lt_or_eq with h | h
  · exact q0_poly_outer h
  · subst h; rw [q0_poly_inner le_rfl]; ring

/-- **The windowed-quadratic convolution reindex.**  For `0 < v < σ` the full-line autocorrelation
of the windowed Baxter quadratic `1[0,σ]·q0_poly(η,σ,1)` equals the scalar interval autocorrelation
`∫₀^σ q0_poly(t+v)·q0_poly(t)` used in `baxterODE_n1`: the supports intersect in `[v,σ]`, a shift
sends it to `[0,σ−v]`, and the missing tail `(σ−v,σ]` vanishes since `q0_poly(t+v)=0` for `t+v≥σ`. -/
theorem q0_poly_indicator_conv {eta sigma : ℝ} (hs0 : 0 < sigma) {v : ℝ}
    (hv0 : 0 < v) (hvs : v < sigma) :
    (∫ t, Set.indicator (Set.Icc (0 : ℝ) sigma) (q0_poly eta sigma 1) t
            * Set.indicator (Set.Icc (0 : ℝ) sigma) (q0_poly eta sigma 1) (t - v))
      = ∫ t in (0 : ℝ)..sigma, q0_poly eta sigma 1 (t + v) * q0_poly eta sigma 1 t := by
  set f1 := q0_poly eta sigma 1 with hf1
  have hcont : Continuous f1 := q0_poly_continuous eta sigma 1
  have hfz : ∀ y, sigma ≤ y → f1 y = 0 := fun y hy => q0_poly_zero_of_ge hy
  have hIcont : Continuous (fun t => f1 (t + v) * f1 t) :=
    (hcont.comp (continuous_id.add continuous_const)).mul hcont
  -- pointwise: the indicator product is the indicator of the overlap `[v,σ]`
  have hff : ∀ t, Set.indicator (Set.Icc (0 : ℝ) sigma) f1 t
        * Set.indicator (Set.Icc (0 : ℝ) sigma) f1 (t - v)
      = Set.indicator (Set.Icc v sigma) (fun u => f1 u * f1 (u - v)) t := by
    intro t
    by_cases ht : t ∈ Set.Icc v sigma
    · rw [Set.indicator_of_mem ht]
      obtain ⟨htv, hts⟩ := Set.mem_Icc.mp ht
      rw [Set.indicator_of_mem (Set.mem_Icc.mpr ⟨le_trans hv0.le htv, hts⟩),
          Set.indicator_of_mem (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)]
    · rw [Set.indicator_of_notMem ht]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with ht | ht
      · rw [Set.indicator_of_notMem (a := t - v)
          (by rw [Set.mem_Icc]; push_neg; intro _; linarith), mul_zero]
      · rw [Set.indicator_of_notMem (a := t)
          (by rw [Set.mem_Icc]; push_neg; intro _; linarith), zero_mul]
  calc (∫ t, Set.indicator (Set.Icc (0 : ℝ) sigma) f1 t
            * Set.indicator (Set.Icc (0 : ℝ) sigma) f1 (t - v))
      = ∫ t, Set.indicator (Set.Icc v sigma) (fun u => f1 u * f1 (u - v)) t := by
        simp_rw [hff]
    _ = ∫ t in Set.Icc v sigma, f1 t * f1 (t - v) := by
        rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ = ∫ t in Set.Ioc v sigma, f1 t * f1 (t - v) := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = ∫ t in v..sigma, f1 t * f1 (t - v) := by
        rw [intervalIntegral.integral_of_le hvs.le]
    _ = ∫ u in (0 : ℝ)..(sigma - v), f1 (u + v) * f1 u := by
        have hc : (∫ u in (0 : ℝ)..(sigma - v), f1 (u + v) * f1 u)
            = ∫ t in v..sigma, f1 t * f1 (t - v) := by
          have h := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := sigma - v)
            (fun t => f1 t * f1 (t - v)) v
          simp only [zero_add, sub_add_cancel, add_sub_cancel_right] at h
          exact h
        exact hc.symm
    _ = ∫ t in (0 : ℝ)..sigma, f1 (t + v) * f1 t := by
        have hz : (∫ t in (sigma - v)..sigma, f1 (t + v) * f1 t) = 0 := by
          rw [← intervalIntegral.integral_zero (a := sigma - v) (b := sigma)]
          refine intervalIntegral.integral_congr (fun u hu => ?_)
          rw [Set.uIcc_of_le (by linarith : sigma - v ≤ sigma), Set.mem_Icc] at hu
          rw [hfz (u + v) (by linarith), zero_mul]
        have hi1 : IntervalIntegrable (fun t => f1 (t + v) * f1 t) volume 0 (sigma - v) :=
          hIcont.intervalIntegrable _ _
        have hi2 : IntervalIntegrable (fun t => f1 (t + v) * f1 t) volume (sigma - v) sigma :=
          hIcont.intervalIntegrable _ _
        have hadj := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
        rw [hz, add_zero] at hadj
        exact hadj

end FMSA.MixtureBaxter

namespace FMSA.MixtureBaxter
open FMSA.MixtureOzStar

open FMSA.HardSphere FMSA.HSMix FMSA.MatrixQ0 FMSA.WHSupports FMSA.InnerDecomp MeasureTheory Set

/-- **Equal-diameter closed form of the physical Baxter entry.**  With all `σₖ = σ`, the Lebowitz
`q0MixEntry(physMix)ₐᵦ` is INDEPENDENT of `(a,b)`: the windowed scalar quadratic
`1[0,σ]·q0_poly(η,σ,1)` (from `Q0phys_equalDiam`/`Qppphys_equalDiam`). -/
theorem q0MixEntry_physMix_eq_indicator {rho sigma : Fin 2 → ℝ} {s : ℝ}
    (hsig : ∀ k, 0 < sigma k) (hs : ∀ k, sigma k = s) (hs0 : 0 < s)
    (hvac : vacMix rho sigma ≠ 0) (a b : Fin 2) :
    q0MixEntry (physMix rho sigma hsig) a b
      = Set.indicator (Set.Icc (0 : ℝ) s) (q0_poly (etaMix rho sigma) s 1) := by
  funext v
  have hR : (physMix rho sigma hsig).R a b = s := by
    simp only [physMix, Mix.R, hs a, hs b]; ring
  have hlam : (physMix rho sigma hsig).lam a b = 0 := by
    simp only [physMix, Mix.lam, hs a, hs b]; ring
  rw [FMSA.WHSupports.q0MixEntry, hR, hlam]
  by_cases hv : v ∈ Set.Icc (0 : ℝ) s
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
    have hvs : v ≤ s := hv.2
    rw [q0_poly_inner hvs]
    simp only [physMix]
    rw [Q0phys_equalDiam hs hs0 hvac a b, Qppphys_equalDiam hs hs0 hvac 0 b]
    ring
  · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]

/-- **Equal-diameter collapse of the physical correlation.**  Using pair-independence of
`q0MixEntry(physMix)` and `rgᵢₘ·rgₖₘ = ρₘ·rgᵢₖ`, the full-line correlation collapses to
`rgᵢₖ·(∑ρ)·(scalar autocorrelation)` for `0 < v < σ`. -/
theorem matCorrFull_qWeighted_equalDiam {rho sigma : Fin 2 → ℝ} {s : ℝ}
    (hsig : ∀ k, 0 < sigma k) (hs : ∀ k, sigma k = s) (hs0 : 0 < s)
    (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i) (i k : Fin 2)
    {v : ℝ} (hv0 : 0 < v) (hvs : v < s) :
    matCorrFull (qWeighted rho sigma hsig) i k v
      = rhoGeoPhys rho i k * (∑ l, rho l)
        * ∫ t in (0 : ℝ)..s, q0_poly (etaMix rho sigma) s 1 (t + v)
            * q0_poly (etaMix rho sigma) s 1 t := by
  have hL1 : ∀ a b, q0MixEntry (physMix rho sigma hsig) a b
      = Set.indicator (Set.Icc (0 : ℝ) s) (q0_poly (etaMix rho sigma) s 1) :=
    fun a b => q0MixEntry_physMix_eq_indicator hsig hs hs0 hvac a b
  have hCval : (∫ t, Set.indicator (Set.Icc (0 : ℝ) s) (q0_poly (etaMix rho sigma) s 1) t
        * Set.indicator (Set.Icc (0 : ℝ) s) (q0_poly (etaMix rho sigma) s 1) (t - v))
      = ∫ t in (0 : ℝ)..s, q0_poly (etaMix rho sigma) s 1 (t + v)
          * q0_poly (etaMix rho sigma) s 1 t :=
    q0_poly_indicator_conv hs0 hv0 hvs
  simp only [matCorrFull]
  have hsummand : ∀ m,
      (∫ t, qWeighted rho sigma hsig i m t * qWeighted rho sigma hsig k m (t - v))
      = (rhoGeoPhys rho i m * rhoGeoPhys rho k m)
        * (∫ t, Set.indicator (Set.Icc (0 : ℝ) s) (q0_poly (etaMix rho sigma) s 1) t
            * Set.indicator (Set.Icc (0 : ℝ) s) (q0_poly (etaMix rho sigma) s 1) (t - v)) := by
    intro m
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    simp only [qWeighted, hL1 i m, hL1 k m]
    ring
  simp_rw [hsummand]
  rw [← Finset.sum_mul, hCval]
  have hsum : (∑ m, rhoGeoPhys rho i m * rhoGeoPhys rho k m)
      = (∑ l, rho l) * rhoGeoPhys rho i k := by
    rw [show (∑ m, rhoGeoPhys rho i m * rhoGeoPhys rho k m)
          = ∑ m, rho m * rhoGeoPhys rho i k from
        Finset.sum_congr rfl (fun m _ => rhoGeoPhys_mul_eq rho hrho i k m), ← Finset.sum_mul]
  rw [hsum]; ring

/-- **Equal-diameter collapse of the mixture DCF core to the scalar Baxter forcing function.**  On
`(0,σ)`, `matDCFreCoreᵢₖ = (rgᵢₖ/∑ρ)·(baxterODE_n1's function at ρ = ∑ρ)`. -/
theorem matDCFreCore_equalDiam_eq {rho sigma : Fin 2 → ℝ} {s : ℝ}
    (hsig : ∀ k, 0 < sigma k) (hs : ∀ k, sigma k = s) (hs0 : 0 < s)
    (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i) (hρT : (∑ l, rho l) ≠ 0)
    (i k : Fin 2) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) s) :
    matDCFreCore rho sigma hsig i k x
      = (rhoGeoPhys rho i k / (∑ l, rho l))
        * (q0_poly (etaMix rho sigma) s (∑ l, rho l) x
           - ∫ t in (0 : ℝ)..s, q0_poly (etaMix rho sigma) s (∑ l, rho l) (t + x)
               * q0_poly (etaMix rho sigma) s (∑ l, rho l) t) := by
    obtain ⟨hx0, hxs⟩ := hx
    have hlin : qWeighted rho sigma hsig i k x
        = rhoGeoPhys rho i k * q0_poly (etaMix rho sigma) s 1 x := by
      simp only [qWeighted, q0MixEntry_physMix_eq_indicator hsig hs hs0 hvac i k]
      rw [Set.indicator_of_mem (Set.mem_Icc.mpr ⟨hx0.le, hxs.le⟩)]
    have hrefl : qWeighted rho sigma hsig k i (-x) = 0 := by
      simp only [qWeighted, q0MixEntry_physMix_eq_indicator hsig hs hs0 hvac k i]
      rw [Set.indicator_of_notMem (by rw [Set.mem_Icc]; push_neg; intro _; linarith), mul_zero]
    have hcorr := matCorrFull_qWeighted_equalDiam hsig hs hs0 hvac hrho i k hx0 hxs
    have hInt : (∫ t in (0 : ℝ)..s, q0_poly (etaMix rho sigma) s (∑ l, rho l) (t + x)
          * q0_poly (etaMix rho sigma) s (∑ l, rho l) t)
        = (∑ l, rho l) ^ 2 * ∫ t in (0 : ℝ)..s, q0_poly (etaMix rho sigma) s 1 (t + x)
            * q0_poly (etaMix rho sigma) s 1 t := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      rw [q0_poly_eq_rho_smul (etaMix rho sigma) s (∑ l, rho l) (t + x),
          q0_poly_eq_rho_smul (etaMix rho sigma) s (∑ l, rho l) t]
      ring
    rw [← matDCFfoldKernel_qWeighted_eq_matDCFreCore]
    simp only [matDCFfoldKernel]
    rw [hlin, hrefl, hcorr,
        q0_poly_eq_rho_smul (etaMix rho sigma) s (∑ l, rho l) x, hInt]
    field_simp
    ring

/-- **⭐ The mixture Baxter ODE at equal diameters.**  `matDCFreCoreᵢₖ'(x) = −2π·rgᵢₖ·x·c_HS(x)` on
`(0,σ)` — the mixture case of the Baxter–WH differential relation, obtained by scaling the proved
scalar `baxterODE_n1` through the equal-diameter collapse `matDCFreCore_equalDiam_eq`. -/
theorem matDCFreCore_hasDerivAt_equalDiam {rho sigma : Fin 2 → ℝ} {s : ℝ}
    (hsig : ∀ k, 0 < sigma k) (hs : ∀ k, sigma k = s) (hs0 : 0 < s)
    (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i) (hρT : (∑ l, rho l) ≠ 0)
    (hetalt : etaMix rho sigma < 1) (i k : Fin 2) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) s) :
    HasDerivAt (fun w => matDCFreCore rho sigma hsig i k w)
      (-(2 * Real.pi * rhoGeoPhys rho i k * x * c_HS (etaMix rho sigma) s x)) x := by
  have heta0 : 0 ≤ etaMix rho sigma := by
    unfold etaMix
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun i _ => mul_nonneg (hrho i) (pow_nonneg (hsig i).le 3)))
  have hetadef : etaMix rho sigma = Real.pi * (∑ l, rho l) * s ^ 3 / 6 := by
    have hsum : (∑ l, rho l * sigma l ^ 3) = (∑ l, rho l) * s ^ 3 := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun l _ => by rw [hs l])
    simp only [etaMix, hsum]; ring
  have hG := baxterODE_n1 (etaMix rho sigma) s (∑ l, rho l) hs0 heta0 hetalt hetadef hx
  have hGc := hG.const_mul (rhoGeoPhys rho i k / (∑ l, rho l))
  have hev : (fun w => matDCFreCore rho sigma hsig i k w)
      =ᶠ[nhds x] (fun w => (rhoGeoPhys rho i k / (∑ l, rho l))
        * (q0_poly (etaMix rho sigma) s (∑ l, rho l) w
           - ∫ t in (0 : ℝ)..s, q0_poly (etaMix rho sigma) s (∑ l, rho l) (t + w)
               * q0_poly (etaMix rho sigma) s (∑ l, rho l) t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with w hw
    exact matDCFreCore_equalDiam_eq hsig hs hs0 hvac hrho hρT i k hw
  have hval : (rhoGeoPhys rho i k / (∑ l, rho l))
        * (-(2 * Real.pi * (∑ l, rho l) * x * c_HS (etaMix rho sigma) s x))
      = -(2 * Real.pi * rhoGeoPhys rho i k * x * c_HS (etaMix rho sigma) s x) := by
    field_simp
  rw [← hval]
  exact hGc.congr_of_eventuallyEq hev

/-- **⭐⭐ MRS.8's open Baxter–WH gap, CLOSED at equal diameters.**  With the per-entry physical
normalization `ρ = rgᵢₖ = √(ρᵢρₖ)`, the shell-inverse forcing IS the physical DCF:
`shellForcing rgᵢₖ i k v = c_HS(η,σ,v)` on `(0,σ)`, UNCONDITIONALLY at equal diameters.  This is the
sole remaining open input of the OZ★ value route (`shellForcing_eq_cHS_of_baxterODE`), discharged
from the proved mixture ODE `matDCFreCore_hasDerivAt_equalDiam`. -/
theorem shellForcing_eq_cHS_equalDiam {rho sigma : Fin 2 → ℝ} {s : ℝ}
    (hsig : ∀ k, 0 < sigma k) (hs : ∀ k, sigma k = s) (hs0 : 0 < s)
    (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i) (hρT : (∑ l, rho l) ≠ 0)
    (hetalt : etaMix rho sigma < 1) (i k : Fin 2) (hrg : rhoGeoPhys rho i k ≠ 0)
    {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) s) :
    shellForcing rho sigma hsig (rhoGeoPhys rho i k) i k v = c_HS (etaMix rho sigma) s v := by
  refine shellForcing_eq_cHS_of_baxterODE rho sigma hsig hs hrg
    (eta := etaMix rho sigma) i k (fun s' hs' => ?_) hv
  have hD := matDCFreCore_hasDerivAt_equalDiam hsig hs hs0 hvac hrho hρT hetalt i k hs'
  have hd2 := hD.div_const (rhoGeoPhys rho i k)
  have hval : (-(2 * Real.pi * rhoGeoPhys rho i k * s' * c_HS (etaMix rho sigma) s s'))
        / rhoGeoPhys rho i k
      = -(2 * Real.pi * s'
          * -(py_a0 (etaMix rho sigma) + py_a1 (etaMix rho sigma) * (s' / s)
              + py_a3 (etaMix rho sigma) * (s' / s) ^ 3)) := by
    rw [← c_HS_inner hs'.2]
    field_simp
  rw [hval] at hd2
  exact hd2

end FMSA.MixtureBaxter
