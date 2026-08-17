/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterKernelDeriv
import LeanCode.HardSphere.BaxterRenewal
import LeanCode.Analysis.ConvolutionLeibniz

/-!
# Derivative of the renewal forcing `baxterForcing` — step 2 of (★DIFF)

`baxterForcing r = ∫ s in 0..σ, q0_poly(r − s) · (−s)` has **fixed** limits, so its derivative is the
pure parameter-differentiation case of `MA.16`
(`FMSA.Analysis.hasDerivAt_intervalIntegral_param`, `Analysis/ConvolutionLeibniz.lean`):

  `baxterForcing'(r) = ∫ s in 0..σ, q0PolyDeriv(r − s) · (−s)`.

All four of `MA.16`'s hypotheses on the kernel are supplied by `BaxterKernelDeriv.lean`:
`q0_poly_continuous`, `hasDerivAt_q0_poly_ae` (a.e. — `q0_poly` has a kink at `σ`),
`q0PolyDeriv_measurable`, and `q0_poly_lipschitzOnWith`.
-/

set_option linter.style.longLine false

open MeasureTheory Set Filter Topology

namespace FMSA.HardSphere

noncomputable section

/-- `q0_poly` is Lipschitz on any closed interval, with an explicit constant. -/
theorem q0_poly_lipschitzOnWith_Icc (eta sigma rho lo hi : ℝ) (hlohi : lo ≤ hi) :
    LipschitzOnWith
      (Real.nnabs (|rho * q_prime_py eta sigma|
        + |rho * q_doubleprime_py eta| * ((hi - lo) + |lo - sigma|)))
      (q0_poly eta sigma rho) (Icc lo hi) := by
  refine q0_poly_lipschitzOnWith ?_ (fun x hx => ?_)
  · have : (0:ℝ) ≤ hi - lo := by linarith
    have := abs_nonneg (lo - sigma)
    linarith
  · have h1 : x - sigma = (x - lo) + (lo - sigma) := by ring
    rw [h1]
    refine le_trans (abs_add_le _ _) ?_
    have h2 : |x - lo| ≤ hi - lo := by
      rw [abs_of_nonneg (by linarith [(mem_Icc.mp hx).1] : (0:ℝ) ≤ x - lo)]
      linarith [(mem_Icc.mp hx).2]
    linarith

/-- **Step 2 of (★DIFF): the forcing is differentiable**, with
`baxterForcing'(r) = ∫ s in 0..σ, q0PolyDeriv(r − s)·(−s)`.  Fixed limits, so this is `MA.16`'s
parameter case; the kernel hypotheses come from `BaxterKernelDeriv.lean`. -/
theorem hasDerivAt_baxterForcing (eta sigma rho : ℝ) (hsigma : 0 ≤ sigma) (r : ℝ) :
    HasDerivAt (baxterForcing eta sigma rho)
      (∫ s in (0:ℝ)..sigma, q0PolyDeriv eta sigma rho (r - s) * (-s)) r := by
  have hlip := q0_poly_lipschitzOnWith_Icc eta sigma rho (r - 1 - sigma) (r + 1 - 0)
    (by linarith)
  exact FMSA.Analysis.hasDerivAt_intervalIntegral_param (K := q0_poly eta sigma rho)
    (K' := q0PolyDeriv eta sigma rho) (φ := fun s => -s)
    (by norm_num) hsigma
    (q0_poly_continuous eta sigma rho) (continuous_neg)
    (hasDerivAt_q0_poly_ae eta sigma rho) (q0PolyDeriv_measurable eta sigma rho)
    hlip

/-- **⭐ Scalar Baxter CORRELATION derivative (N=1) — the `matCorrFull'` at one component.**  The
`q0_poly` autocorrelation `s ↦ ∫₀^σ q0_poly(t−s)·q0_poly(t) dt` (the scalar analog of the mixture
`matCorrFull`) is differentiable, derivative `∫₀^σ −q0PolyDeriv(t−s)·q0_poly(t)`.  This is MA.16
(`hasDerivAt_intervalIntegral_param`) applied with the REFLECTED kernel `K = q0_poly∘neg`
(`K(x−t) = q0_poly(t−x)`), its kernel data (continuity, a.e. derivative, measurability, Lipschitz)
derived from `BaxterKernelDeriv` by composing with `neg`.  This is the Leibniz differentiation step
of the N=1 Baxter ODE `matDCFreCore'(s) = −2πρ·s·c_HS(s)`: with `matDCFreCore = q0_poly − (this
correlation)`, the ODE reduces (via an IBP relating this correlation's derivative to the
`baxter_factorization_inner` integral) to the proved scalar `baxter_factorization_inner`. -/
theorem hasDerivAt_q0Corr (eta sigma rho : ℝ) (hsigma : 0 ≤ sigma) (r : ℝ) :
    HasDerivAt
      (fun x => ∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho (t - x) * q0_poly eta sigma rho t)
      (∫ t in (0:ℝ)..sigma, -(q0PolyDeriv eta sigma rho (t - r)) * q0_poly eta sigma rho t) r := by
  set K : ℝ → ℝ := fun y => q0_poly eta sigma rho (-y) with hK
  set K' : ℝ → ℝ := fun u => -(q0PolyDeriv eta sigma rho (-u)) with hK'
  have hKcont : Continuous K := (q0_poly_continuous eta sigma rho).comp continuous_neg
  have hKderiv : ∀ᵐ u, HasDerivAt K (K' u) u := by
    have hnull : ∀ᵐ u : ℝ, u ≠ -sigma := by
      rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hnull] with u hu
    have hne : -u ≠ sigma := fun h => hu (by rw [← h]; ring)
    have hd := hasDerivAt_q0_poly_of_ne (eta := eta) (rho := rho) sigma hne
    have hc : HasDerivAt K (q0PolyDeriv eta sigma rho (-u) * (-1)) u :=
      hd.comp u ((hasDerivAt_id u).neg)
    rw [hK']; convert hc using 1; ring
  have hK'meas : Measurable K' :=
    ((q0PolyDeriv_measurable eta sigma rho).comp measurable_neg).neg
  have hmaps : Set.MapsTo (fun y : ℝ => -y) (Icc (r - 1 - sigma) (r + 1 - 0))
      (Icc (-(r + 1 - 0)) (-(r - 1 - sigma))) := by
    intro y hy; rw [Set.mem_Icc] at hy ⊢; constructor <;> linarith [hy.1, hy.2]
  have hKlip := (q0_poly_lipschitzOnWith_Icc eta sigma rho (-(r + 1 - 0)) (-(r - 1 - sigma))
    (by linarith)).comp (LipschitzWith.id.neg.lipschitzOnWith) hmaps
  have hmain := FMSA.Analysis.hasDerivAt_intervalIntegral_param (K := K) (K' := K')
    (φ := q0_poly eta sigma rho)
    (by norm_num) hsigma hKcont (q0_poly_continuous eta sigma rho) hKderiv hK'meas hKlip
  simp only [hK, hK', neg_sub] at hmain
  exact hmain

/-- **⭐ IBP connecting the two Baxter cross-correlations (N=1).**  On `[s,σ]` (`0<s<σ`), integrating
`∫ q0_poly(t)·q0PolyDeriv(t−s)` by parts (both factors coincide with the smooth quadratic `P` there,
`q0_poly(σ)=0` killing the top boundary) gives the Baxter integral `∫ q0PolyDeriv(t)·q0_poly(t−s)`
plus the `−q0_poly(s)·q0_poly(0)` boundary.  This is the step that connects `hasDerivAt_q0Corr`'s
correlation derivative to `baxter_factorization_inner`'s integral: in the N=1 ODE derivation the
`−q0_poly(s)·q0_poly(0)` boundary here CANCELS the Leibniz boundary from the variable lower
limit. -/
theorem q0_ibp (eta sigma rho s : ℝ) (hs : 0 < s) (hssigma : s < sigma) :
    (∫ t in s..sigma, q0_poly eta sigma rho t * q0PolyDeriv eta sigma rho (t - s))
    = -(q0_poly eta sigma rho s * q0_poly eta sigma rho 0)
      - ∫ t in s..sigma, q0PolyDeriv eta sigma rho t * q0_poly eta sigma rho (t - s) := by
  set P : ℝ → ℝ := fun t => rho * q_prime_py eta sigma * (t - sigma)
    + rho * q_doubleprime_py eta * (t - sigma) ^ 2 / 2 with hP
  set P' : ℝ → ℝ := fun t => rho * q_prime_py eta sigma
    + rho * q_doubleprime_py eta * (t - sigma) with hP'
  have hPd : ∀ t, HasDerivAt P (P' t) t := by
    intro t
    have hsub : HasDerivAt (fun y : ℝ => y - sigma) (1 : ℝ) t := (hasDerivAt_id t).sub_const _
    have hsq : HasDerivAt (fun y : ℝ => (y - sigma) ^ 2) (2 * (t - sigma) ^ 1 * 1) t := hsub.pow 2
    have hA : HasDerivAt (fun y => rho * q_prime_py eta sigma * (y - sigma))
        (rho * q_prime_py eta sigma * 1) t := hsub.const_mul _
    have hB : HasDerivAt (fun y => rho * q_doubleprime_py eta * (y - sigma) ^ 2 / 2)
        (rho * q_doubleprime_py eta * (2 * (t - sigma) ^ 1 * 1) / 2) t :=
      (hsq.const_mul _).div_const 2
    have hadd := hA.add hB
    have heq : rho * q_prime_py eta sigma * 1
        + rho * q_doubleprime_py eta * (2 * (t - sigma) ^ 1 * 1) / 2 = P' t := by
      simp only [hP']; ring
    rw [hP, ← heq]; exact hadd
  have hq0P : ∀ t : ℝ, t ≤ sigma → q0_poly eta sigma rho t = P t := fun t ht => by
    rw [q0_poly_inner ht]
  have hdP : ∀ t : ℝ, t < sigma → q0PolyDeriv eta sigma rho t = P' t := fun t ht => by
    simp only [q0PolyDeriv, phi1_real, hP', if_pos ht, if_pos (le_of_lt ht)]; ring
  have hLHS : (∫ t in s..sigma, q0_poly eta sigma rho t * q0PolyDeriv eta sigma rho (t - s))
      = ∫ t in s..sigma, P t * P' (t - s) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hssigma.le, Set.mem_Icc] at ht
    rw [hq0P t ht.2, hdP (t - s) (by linarith [ht.2])]
  have hvd : ∀ x : ℝ, HasDerivAt (fun t => P (t - s)) (P' (x - s)) x := by
    intro x
    have hsub : HasDerivAt (fun t : ℝ => t - s - sigma) (1 : ℝ) x := by
      simpa using ((hasDerivAt_id x).sub_const s).sub_const sigma
    have hsq : HasDerivAt (fun t : ℝ => (t - s - sigma) ^ 2) (2 * (x - s - sigma) ^ 1 * 1) x :=
      hsub.pow 2
    have hA : HasDerivAt (fun t => rho * q_prime_py eta sigma * (t - s - sigma))
        (rho * q_prime_py eta sigma * 1) x := hsub.const_mul _
    have hB : HasDerivAt (fun t => rho * q_doubleprime_py eta * (t - s - sigma) ^ 2 / 2)
        (rho * q_doubleprime_py eta * (2 * (x - s - sigma) ^ 1 * 1) / 2) x :=
      (hsq.const_mul _).div_const 2
    have hadd := hA.add hB
    have heq : rho * q_prime_py eta sigma * 1
        + rho * q_doubleprime_py eta * (2 * (x - s - sigma) ^ 1 * 1) / 2 = P' (x - s) := by
      simp only [hP']; ring
    rw [hP]
    exact heq ▸ hadd
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := P) (u' := P') (v := fun t => P (t - s)) (v' := fun t => P' (t - s))
    (fun x _ => hPd x) (fun x _ => hvd x)
    ((by simp only [hP']; fun_prop : Continuous P').intervalIntegrable s sigma)
    ((by simp only [hP']; fun_prop : Continuous fun t => P' (t - s)).intervalIntegrable s sigma)
  rw [hLHS, hIBP]
  have hPsigma : P sigma = 0 := by simp only [hP]; ring
  rw [hPsigma, zero_mul, zero_sub]
  congr 1
  · rw [sub_self, ← hq0P s hssigma.le, ← hq0P 0 (by linarith)]
  · refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le hssigma.le]
    have hne : ∀ᵐ t : ℝ, t ≠ sigma := by rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hne] with t htne hmem
    rw [Set.mem_Ioc] at hmem
    rw [← hdP t (lt_of_le_of_ne hmem.2 htne), ← hq0P (t - s) (by linarith [hmem.2])]

/-- **⭐ Derivative of the scalar `matCorrFull` `corrM` (N=1).**  `corrM(s) = ∫₀^σ
q0_poly(t+s)·q0_poly(t)` (the extended fixed-limit form of the `q0M` autocorrelation, the cutoff
factor) is differentiable with derivative `∫₀^σ q0PolyDeriv(t+s)·q0_poly(t)`.  It equals
`hasDerivAt_q0Corr`'s function at `−s`, so the derivative is the chain rule (`∘ neg`) applied to the
already-proved fixed-limit correlation derivative — NO variable-limit Leibniz machinery needed (the
`q0_poly(σ)=0`-driven extension turns the variable lower limit into a fixed one). -/
theorem hasDerivAt_corrM (eta sigma rho : ℝ) (hsigma : 0 ≤ sigma) (s : ℝ) :
    HasDerivAt
      (fun x => ∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho (t + x) * q0_poly eta sigma rho t)
      (∫ t in (0:ℝ)..sigma, q0PolyDeriv eta sigma rho (t + s) * q0_poly eta sigma rho t) s := by
  have hcomp : (fun x : ℝ =>
        ∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho (t + x) * q0_poly eta sigma rho t)
      = (fun y : ℝ =>
          ∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho (t - y) * q0_poly eta sigma rho t)
        ∘ (fun x => -x) := by
    funext x; simp only [Function.comp, sub_neg_eq_add]
  rw [hcomp]
  have h : HasDerivAt ((fun y : ℝ =>
        ∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho (t - y) * q0_poly eta sigma rho t)
          ∘ (fun x => -x))
      ((∫ t in (0:ℝ)..sigma, -(q0PolyDeriv eta sigma rho (t - -s)) * q0_poly eta sigma rho t) * -1)
      s :=
    (hasDerivAt_q0Corr eta sigma rho hsigma (-s)).comp s ((hasDerivAt_id s).neg)
  convert h using 1
  simp only [sub_neg_eq_add, neg_mul, intervalIntegral.integral_neg]; ring

/-- `q0PolyDeriv` equals the smooth quadratic derivative `ρq'_py + ρq''_py(x−σ)` for `x < σ`. -/
theorem q0PolyDeriv_of_lt {eta rho : ℝ} (sigma : ℝ) {x : ℝ} (hx : x < sigma) :
    q0PolyDeriv eta sigma rho x
      = rho * q_prime_py eta sigma + rho * q_doubleprime_py eta * (x - sigma) := by
  simp only [q0PolyDeriv, phi1_real, if_pos hx, if_pos (le_of_lt hx)]; ring

/-- `q0PolyDeriv` vanishes at and beyond `σ` (both the step and the kink shut off there). -/
theorem q0PolyDeriv_eq_zero_of_ge {eta rho : ℝ} (sigma : ℝ) {x : ℝ} (hx : sigma ≤ x) :
    q0PolyDeriv eta sigma rho x = 0 := by
  rcases eq_or_lt_of_le hx with h | h
  · simp only [q0PolyDeriv, ← h, phi1_real, if_neg (lt_irrefl sigma), if_pos (le_refl sigma),
      sub_self, mul_zero, add_zero]
  · exact q0PolyDeriv_eq_zero_of_gt sigma h

/-- The integrand `q0PolyDeriv(x)·q0_poly(x−s)` is interval-integrable (a.e. equal to a continuous
function below `σ`, a.e. `0` above — `q0PolyDeriv` is bounded and measurable). -/
theorem q0PolyDeriv_q0_poly_iintegr (eta sigma rho s a b : ℝ) :
    IntervalIntegrable (fun x => q0PolyDeriv eta sigma rho x * q0_poly eta sigma rho (x - s))
      volume a b := by
  rw [intervalIntegrable_iff]
  have hmeas : Measurable (fun x => q0PolyDeriv eta sigma rho x * q0_poly eta sigma rho (x - s)) :=
    (q0PolyDeriv_measurable eta sigma rho).mul
      ((q0_poly_continuous eta sigma rho).comp (by fun_prop)).measurable
  have hcont : Continuous (fun x => (rho * q_prime_py eta sigma
      + rho * q_doubleprime_py eta * (x - sigma)) * q0_poly eta sigma rho (x - s)) :=
    (by fun_prop : Continuous fun x : ℝ =>
        rho * q_prime_py eta sigma + rho * q_doubleprime_py eta * (x - sigma)).mul
      ((q0_poly_continuous eta sigma rho).comp (by fun_prop))
  obtain ⟨C, hC⟩ :=
    (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn hcont.continuousOn
  have hfin : volume (Set.uIoc a b) ≠ ⊤ :=
    ne_top_of_le_ne_top isCompact_uIcc.measure_ne_top (measure_mono Set.uIoc_subset_uIcc)
  refine Measure.integrableOn_of_bounded (M := max C 0) hfin hmeas.aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with x hx
  rw [Real.norm_eq_abs]
  have hxuIcc : x ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hx
  by_cases hxsigma : x < sigma
  · rw [q0PolyDeriv_of_lt sigma hxsigma]
    have := hC x hxuIcc; rw [Real.norm_eq_abs] at this
    exact le_trans this (le_max_left _ _)
  · rw [q0PolyDeriv_eq_zero_of_ge sigma (not_lt.mp hxsigma), zero_mul, abs_zero]
    exact le_max_right _ _

/-- **⭐ N=1 Baxter ODE — the capstone.**  The scalar DCF-core `q0_poly(s) − corrM(s)` (`corrM` the
`q0M`-autocorrelation `∫₀^σ q0_poly(t+s)·q0_poly(t)`) satisfies `d/ds = −2πρ·s·c_HS(s)` on `(0,σ)`:
the N=1 case of the Baxter–WH differential relation `matDCFreCore'(s) = −2πρ·s·c_HS(s)`.  Assembled
from `hasDerivAt_q0_poly_of_ne` + `hasDerivAt_corrM` (the two derivatives), a shift
(`integral_comp_add_right`) + `q0PolyDeriv=0` tail vanishing carrying `corrM'` onto the Baxter
integral, and the closed-form `baxter_factorization_inner`. -/
theorem baxterODE_n1 (eta sigma rho : ℝ) (hsigma : 0 < sigma) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) sigma) :
    HasDerivAt (fun x => q0_poly eta sigma rho x
        - ∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho (t + x) * q0_poly eta sigma rho t)
      (-(2 * Real.pi * rho * s * c_HS eta sigma s)) s := by
  have hA : (∫ t in (0:ℝ)..sigma, q0PolyDeriv eta sigma rho (t + s) * q0_poly eta sigma rho t)
      = ∫ r' in s..sigma, q0_poly eta sigma rho (r' - s)
          * (rho * q_prime_py eta sigma + rho * q_doubleprime_py eta * (r' - sigma)) := by
    have e1 : (∫ t in (0:ℝ)..sigma, q0PolyDeriv eta sigma rho (t + s) * q0_poly eta sigma rho t)
        = ∫ x in s..(sigma + s), q0PolyDeriv eta sigma rho x * q0_poly eta sigma rho (x - s) := by
      have h := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := sigma)
        (f := fun x => q0PolyDeriv eta sigma rho x * q0_poly eta sigma rho (x - s)) s
      simp only [zero_add, add_sub_cancel_right] at h
      exact h
    rw [e1, ← intervalIntegral.integral_add_adjacent_intervals
      (q0PolyDeriv_q0_poly_iintegr eta sigma rho s s sigma)
      (q0PolyDeriv_q0_poly_iintegr eta sigma rho s sigma (sigma + s))]
    have hvanish : (∫ x in sigma..(sigma + s),
        q0PolyDeriv eta sigma rho x * q0_poly eta sigma rho (x - s)) = 0 := by
      rw [show (∫ x in sigma..(sigma + s),
          q0PolyDeriv eta sigma rho x * q0_poly eta sigma rho (x - s))
          = ∫ _x in sigma..(sigma + s), (0:ℝ) from ?_, intervalIntegral.integral_zero]
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [Set.uIcc_of_le (by linarith [hs.1] : sigma ≤ sigma + s), Set.mem_Icc] at hx
      rw [q0PolyDeriv_eq_zero_of_ge sigma hx.1, zero_mul]
    rw [hvanish, add_zero]
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le hs.2.le]
    have hne : ∀ᵐ x : ℝ, x ≠ sigma := by rw [MeasureTheory.ae_iff]; simp
    filter_upwards [hne] with x hxne hmem
    rw [Set.mem_Ioc] at hmem
    rw [q0PolyDeriv_of_lt sigma (lt_of_le_of_ne hmem.2 hxne)]; ring
  have hval : q0PolyDeriv eta sigma rho s
      - ∫ t in (0:ℝ)..sigma, q0PolyDeriv eta sigma rho (t + s) * q0_poly eta sigma rho t
      = -(2 * Real.pi * rho * s * c_HS eta sigma s) := by
    rw [hA, q0PolyDeriv_of_lt sigma hs.2]
    have hbax := baxter_factorization_inner hsigma heta0 heta1 heta_def s hs
    linarith [hbax]
  rw [← hval]
  exact (hasDerivAt_q0_poly_of_ne (eta := eta) (rho := rho) sigma (ne_of_lt hs.2)).sub
    (hasDerivAt_corrM eta sigma rho hsigma.le s)

end

end FMSA.HardSphere
