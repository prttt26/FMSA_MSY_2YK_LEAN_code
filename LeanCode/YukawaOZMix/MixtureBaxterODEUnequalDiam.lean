/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MixtureDCFAEInjective
import LeanCode.YukawaOZMix.MixtureBaxterODEEqualDiam
import LeanCode.YukawaOZMix.MixtureCorrelationDeriv
import LeanCode.YukawaOZMix.MixtureHSDCFFin1

/-!
# The mixture Baxter ODE at UNEQUAL diameters — foundations (MIXCHS.7)

At equal diameters (`MixtureBaxterODEEqualDiam.lean`) the physical DCF core `matDCFreCore` is a
single windowed quadratic and its Baxter ODE reduces to the scalar `baxterODE_n1`.  At **unequal**
diameters (say `σᵢ < σₖ`, so `λᵢₖ = (σₖ−σᵢ)/2 > 0`) there is no scalar collapse: `matDCFreCore i k`
is a genuinely **two-piece** object with a knot at `λᵢₖ`,

  `matDCFreCore i k v = qWeighted i k v + qWeighted k i (−v) − matCorrFull(qWeighted) i k v`,

where the **forward** linear term `qWeighted i k(v)` is supported on `[λᵢₖ, Rᵢₖ]` and the
**reflected** term `qWeighted k i(−v)` on `[−Rᵢₖ, λᵢₖ]`.  So on `(0, λᵢₖ)` only the reflected term
is active, on `(λᵢₖ, Rᵢₖ)` only the forward term, and the correlation is active throughout.

Numerical fact (`mixdcf_unequal_value_check.py`, 2026-08-13): the shell-inverse of this
`matDCFreCore` IS the true PY-HS mixture DCF at unequal σ — the equal-σ value proof generalizes,
no renewal needed.

This file builds the unequal-σ foundations:
* `q0MixEntry_physMix_leftEdge` — the explicit value of the physical Baxter kernel at its left edge
  `λᵢₖ`, namely `−π σᵢ σₖ / vac`, **symmetric in `i,k`** — this is what makes the forward/reflected
  jumps CANCEL, so `matDCFreCore` has matching one-sided limits across the knot;
* the two-piece structural decomposition (`matDCFreCore_upper_eq` / `matDCFreCore_lower_eq`).

⚠ **Point-spike at the knot.**  With the closed-`Icc` indicator convention, BOTH linear terms are
"on" at the single point `v = λᵢₖ` (`λᵢₖ` is the left edge of `[λᵢₖ,Rᵢₖ]` AND, via `−λᵢₖ = λₖᵢ`, the
left edge of `qWeighted k i`'s support), so `matDCFreCore i k λᵢₖ = 2·rgᵢₖ·leftEdge − matCorrFull`
whereas the two-sided limit is `rgᵢₖ·leftEdge − matCorrFull`.  This removable spike is a
measure-zero artifact (irrelevant to the Laplace/shell integrals and every a.e. statement), but it
means the shell-kernel FTC at unequal σ must run on the **continuous representative**, not
`matDCFreCore` verbatim — the remaining step for the value capstone (`shellForcing i k = c_ij`,
whose target is numerically confirmed physical). -/

open MeasureTheory Set

namespace FMSA.MixtureOzStar

open FMSA.HardSphere FMSA.MatrixQ0 FMSA.WHSupports FMSA.InnerDecomp

/-- **The physical Baxter kernel at its left edge is `−π σᵢ σₖ / vac`.**  At `r = λᵢₖ = (σₖ−σᵢ)/2`
(the left endpoint of the window `[λᵢₖ, Rᵢₖ]`, where the indicator is `1`), the Lebowitz quadratic
`Q0phys_ik·(r−Rᵢₖ) + Qppphys_k·(r−Rᵢₖ)²/2` evaluates to `−π σᵢ σₖ / vac` — **manifestly symmetric
in `i,k`**.  (`λᵢₖ − Rᵢₖ = −σᵢ`; the `π ξ₂` cross terms cancel.)  This symmetry is exactly what
makes the forward jump of `qWeighted i k` at `λᵢₖ` cancel the reflected jump of `qWeighted k i(−·)`,
so `matDCFreCore` has matching one-sided limits across the knot. -/
theorem q0MixEntry_physMix_leftEdge (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin 2) :
    q0MixEntry (physMix rho sigma hsig) i k ((sigma k - sigma i) / 2)
      = -(Real.pi * sigma i * sigma k) / vacMix rho sigma := by
  have hmem : (sigma k - sigma i) / 2 ∈ Set.Icc ((physMix rho sigma hsig).lam i k)
      ((physMix rho sigma hsig).R i k) := by
    simp only [physMix, Mix.lam, Mix.R]
    rw [Set.mem_Icc]; constructor <;> [rfl; linarith [hsig i]]
  rw [FMSA.WHSupports.q0MixEntry, Set.indicator_of_mem hmem]
  simp only [physMix, Mix.R, Q0phys, Qppphys, vacMix]
  field_simp
  ring

/-- The forward Baxter term `qWeighted i k` vanishes on `(0, λᵢₖ)` (its support starts at `λᵢₖ`). -/
theorem qWeighted_forward_eq_zero_of_lt_lam (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin 2) {v : ℝ} (hv : v < (sigma k - sigma i) / 2) :
    qWeighted rho sigma hsig i k v = 0 :=
  qWeighted_eq_zero_of_notMem rho sigma hsig i k
    (fun hmem => by rw [Set.mem_Icc] at hmem; linarith [hmem.1])

/-- The reflected Baxter term `qWeighted k i(−v)` vanishes on `(λᵢₖ, ∞)` (for `v > λᵢₖ`,
`−v < −λᵢₖ = (σᵢ−σₖ)/2 = λₖᵢ`, below the support `[λₖᵢ, Rₖᵢ]` of `qWeighted k i`). -/
theorem qWeighted_reflected_eq_zero_of_gt_lam (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin 2) {v : ℝ} (hv : (sigma k - sigma i) / 2 < v) :
    qWeighted rho sigma hsig k i (-v) = 0 :=
  qWeighted_eq_zero_of_notMem rho sigma hsig k i
    (fun hmem => by rw [Set.mem_Icc] at hmem; linarith [hmem.1])

/-- **Two-piece decomposition — UPPER piece `(λᵢₖ, Rᵢₖ)`.**  For `v > λᵢₖ` the reflected term
vanishes, so `matDCFreCore i k v = qWeighted i k v − matCorrFull i k v` (forward quadratic minus the
correlation). -/
theorem matDCFreCore_upper_eq (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin 2)
    {v : ℝ} (hv : (sigma k - sigma i) / 2 < v) :
    matDCFreCore rho sigma hsig i k v
      = qWeighted rho sigma hsig i k v - matCorrFull (qWeighted rho sigma hsig) i k v := by
  rw [← matDCFfoldKernel_qWeighted_eq_matDCFreCore]
  simp only [matDCFfoldKernel]
  rw [qWeighted_reflected_eq_zero_of_gt_lam rho sigma hsig i k hv]; ring

/-- **Two-piece decomposition — LOWER piece `(0, λᵢₖ)`.**  For `v < λᵢₖ` the forward term vanishes,
so `matDCFreCore i k v = qWeighted k i(−v) − matCorrFull i k v` (reflected quadratic minus the
correlation). -/
theorem matDCFreCore_lower_eq (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin 2)
    {v : ℝ} (hv : v < (sigma k - sigma i) / 2) :
    matDCFreCore rho sigma hsig i k v
      = qWeighted rho sigma hsig k i (-v) - matCorrFull (qWeighted rho sigma hsig) i k v := by
  rw [← matDCFfoldKernel_qWeighted_eq_matDCFreCore]
  simp only [matDCFfoldKernel]
  rw [qWeighted_forward_eq_zero_of_lt_lam rho sigma hsig i k hv]; ring

/-- FTC for a bare quadratic over an interval. -/
theorem intervalIntegral_quad (A B C a b : ℝ) :
    (∫ t in a..b, A + B * t + C * t ^ 2)
      = A * b + B * b ^ 2 / 2 + C * b ^ 3 / 3 - (A * a + B * a ^ 2 / 2 + C * a ^ 3 / 3) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => A * t + B * t ^ 2 / 2 + C * t ^ 3 / 3)
      (fun x _ => by
        have h1 : HasDerivAt (fun t : ℝ => A * t) A x := by
          simpa using (hasDerivAt_id x).const_mul A
        have h2 : HasDerivAt (fun t : ℝ => B * t ^ 2 / 2) (B * x) x :=
          (((hasDerivAt_pow 2 x).const_mul B).div_const 2).congr_deriv (by ring)
        have h3 : HasDerivAt (fun t : ℝ => C * t ^ 3 / 3) (C * x ^ 2) x :=
          (((hasDerivAt_pow 3 x).const_mul C).div_const 3).congr_deriv (by ring)
        exact ((h1.add h2).add h3).congr_deriv (by ring))
      ((by fun_prop : Continuous fun t : ℝ => A + B * t + C * t ^ 2).intervalIntegrable a b)]

/-- FTC for a bare quadratic times `t` over an interval. -/
theorem intervalIntegral_quad_mul_id (A B C a b : ℝ) :
    (∫ t in a..b, (A + B * t + C * t ^ 2) * t)
      = A * b ^ 2 / 2 + B * b ^ 3 / 3 + C * b ^ 4 / 4
        - (A * a ^ 2 / 2 + B * a ^ 3 / 3 + C * a ^ 4 / 4) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => A * t ^ 2 / 2 + B * t ^ 3 / 3 + C * t ^ 4 / 4)
      (fun x _ => by
        have h1 : HasDerivAt (fun t : ℝ => A * t ^ 2 / 2) (A * x) x :=
          (((hasDerivAt_pow 2 x).const_mul A).div_const 2).congr_deriv (by ring)
        have h2 : HasDerivAt (fun t : ℝ => B * t ^ 3 / 3) (B * x ^ 2) x :=
          (((hasDerivAt_pow 3 x).const_mul B).div_const 3).congr_deriv (by ring)
        have h3 : HasDerivAt (fun t : ℝ => C * t ^ 4 / 4) (C * x ^ 3) x :=
          (((hasDerivAt_pow 4 x).const_mul C).div_const 4).congr_deriv (by ring)
        exact ((h1.add h2).add h3).congr_deriv (by ring))
      ((by fun_prop : Continuous fun t : ℝ => (A + B * t + C * t ^ 2) * t).intervalIntegrable a b)]

/-- `√(ρₖρₗ)·√(ρᵢρₗ) = ρₗ·√(ρᵢρₖ)` — the ρ-geo product used to cancel the sqrt factors in the
lower-piece correlation derivative. -/
theorem sqrt_rho_prod (rho : Fin 2 → ℝ) (hrho : ∀ n, 0 ≤ rho n) (i k l : Fin 2) :
    Real.sqrt (rho k * rho l) * Real.sqrt (rho i * rho l)
      = rho l * Real.sqrt (rho i * rho k) := by
  rw [← Real.sqrt_mul (mul_nonneg (hrho k) (hrho l)),
    show rho k * rho l * (rho i * rho l) = rho l ^ 2 * (rho i * rho k) from by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hrho l)]

open FMSA.MixtureHSDCF in
/-- **Correlation derivative on the lower piece (physical mixture).**  `matCorrFull(qWeighted)ᵢₖ =
∑ₗ qpConv(physMix)ᵢₗₖ/(2π)²` (`matCorrFull_eq_qpConv`), so on `(0, λᵢₖ)` its derivative is the
species sum of the per-`l` lower-piece `qpConv` derivatives (via `hasDerivAt_qpConv_lower`):
`matCorrFull'(v) = ∑ₗ qpConvLowerDeriv(physMix)ᵢₗₖ(v)/(2π)²`.  This is the correlation half of the
lower-piece mixture Baxter ODE's LHS. -/
theorem matCorrFull_hasDerivAt_lower (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin 2)
    (hlam : 0 ≤ (sigma k - sigma i) / 2)
    {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) ((sigma k - sigma i) / 2)) :
    HasDerivAt (fun w => matCorrFull (qWeighted rho sigma hsig) i k w)
      (∑ l, qpConvLowerDeriv (physMix rho sigma hsig) i l k v / (2 * Real.pi) ^ 2) v := by
  have heq : (fun w => matCorrFull (qWeighted rho sigma hsig) i k w)
      = fun w => ∑ l, qpConv (physMix rho sigma hsig) i l k w / (2 * Real.pi) ^ 2 :=
    funext (fun w => matCorrFull_eq_qpConv rho sigma hsig i k w)
  rw [heq]
  refine HasDerivAt.fun_sum (fun l _ => ?_)
  have hlam' : (0 : ℝ) ≤ (physMix rho sigma hsig).lam i k := by
    simp only [physMix, Mix.lam]; linarith [hlam]
  have hv' : v ∈ Set.Ioo (0 : ℝ) ((physMix rho sigma hsig).lam i k) := by
    simp only [physMix, Mix.lam]; exact hv
  exact (hasDerivAt_qpConv_lower (physMix rho sigma hsig) i l k hlam' hv').div_const _

open FMSA.MixtureHSDCF FMSA.MixtureHSDCFFin1 in
/-- **⭐ Mixture Baxter ODE LHS on the lower piece.**  On `(0, λᵢₖ)` (σᵢ < σₖ) the DCF core is
`matDCFreCore i k = qWeighted k i(−·) − matCorrFull i k` (`matDCFreCore_lower_eq`, forward term
off), so its derivative is the reflected-quadratic chain rule minus the correlation sum:
`matDCFreCore'(v) = −rgₖᵢ·q0MixDeriv(physMix) k i(−v) − ∑ₗ qpConvLowerDeriv(physMix)ᵢₗₖ(v)/(2π)²`.
Both parts are explicit (reflected via `hasDerivAt_q0MixEntry`, correlation via
`matCorrFull_hasDerivAt_lower`); matching this to `−2π·rgᵢₖ·v·c_ij(v)` is the lower-piece mixture
Baxter factorization (the remaining polynomial identity for the value capstone). -/
theorem matDCFreCore_hasDerivAt_lower (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin 2) (hlam : 0 ≤ (sigma k - sigma i) / 2)
    {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) ((sigma k - sigma i) / 2)) :
    HasDerivAt (matDCFreCore rho sigma hsig i k)
      (-(rhoGeoPhys rho k i * q0MixDeriv (physMix rho sigma hsig) k i (-v))
        - ∑ l, qpConvLowerDeriv (physMix rho sigma hsig) i l k v / (2 * Real.pi) ^ 2) v := by
  have hmem : -v ∈ Set.Ioo ((physMix rho sigma hsig).lam k i) ((physMix rho sigma hsig).R k i) := by
    simp only [physMix, Mix.lam, Mix.R]
    exact ⟨by linarith [hv.2], by linarith [hv.1, hsig i, hsig k]⟩
  have hcomp := (hasDerivAt_q0MixEntry (physMix rho sigma hsig) k i hmem).comp v
    ((hasDerivAt_id v).neg)
  have hrefl : HasDerivAt (fun w => qWeighted rho sigma hsig k i (-w))
      (rhoGeoPhys rho k i * (q0MixDeriv (physMix rho sigma hsig) k i (-v) * -1)) v := by
    have heq : (fun w => qWeighted rho sigma hsig k i (-w))
        = fun w => rhoGeoPhys rho k i * q0MixEntry (physMix rho sigma hsig) k i (-w) := by
      funext w; simp only [qWeighted]
    rw [heq]; exact hcomp.const_mul (rhoGeoPhys rho k i)
  have hcorr := matCorrFull_hasDerivAt_lower rho sigma hsig i k hlam hv
  refine ((hrefl.sub hcorr).congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hv] with w hw
  exact matDCFreCore_lower_eq rho sigma hsig i k hw.2

/-- **The explicit Lebowitz mixture DCF on the lower piece — a CONSTANT.**  For the pair `(i,k)`
with `σᵢ < σₖ`, on `(0, λᵢₖ)` the physical PY-HS mixture DCF `c_ij` is the explicit constant
`cLowerPiece` in `vac = 1−η` and the pair diameters/densities (derived symbolically from
`matDCFreCore_hasDerivAt_lower` and triple-verified, `mixdcf_lebowitz_cij.py`; the `v⁰` term of
`−matDCFreCore'/(2πv)` vanishes by the `ξ₂` identity ⇒ no `1/v` pole).  Reduces to the scalar
`c_HS(η)` at equal diameters. -/
noncomputable def cLowerPiece (rho sigma : Fin 2 → ℝ) (i k : Fin 2) : ℝ :=
  -(24 * vacMix rho sigma ^ 3
      + Real.pi * vacMix rho sigma ^ 2
        * (28 * rho i * sigma i ^ 3 + 4 * rho k * sigma i ^ 3
          + 12 * rho k * sigma i ^ 2 * sigma k + 12 * rho k * sigma i * sigma k ^ 2)
      + Real.pi ^ 2 * vacMix rho sigma
        * (10 * rho i ^ 2 * sigma i ^ 6 + 4 * rho i * rho k * sigma i ^ 5 * sigma k
          + 16 * rho i * rho k * sigma i ^ 4 * sigma k ^ 2
          + 4 * rho k ^ 2 * sigma i ^ 3 * sigma k ^ 3
          + 6 * rho k ^ 2 * sigma i ^ 2 * sigma k ^ 4)
      + Real.pi ^ 3
        * (rho i ^ 3 * sigma i ^ 9 + 3 * rho i ^ 2 * rho k * sigma i ^ 7 * sigma k ^ 2
          + 3 * rho i * rho k ^ 2 * sigma i ^ 5 * sigma k ^ 4
          + rho k ^ 3 * sigma i ^ 3 * sigma k ^ 6))
    / (24 * vacMix rho sigma ^ 4)

open FMSA.MixtureHSDCF FMSA.MixtureHSDCFFin1 in
/-- **⭐ The lower-piece mixture Baxter ODE — DISCHARGED.**
`matDCFreCore'(v) = −2π·rgᵢₖ·v·cLowerPiece` on `(0, λᵢₖ)`.  From `matDCFreCore_hasDerivAt_lower`,
evaluate the moment integrals
(`intervalIntegral_quad`/`_mul_id`); `fin_cases` on the pair collapses the diagonal `√(ρₗρₗ)=ρₗ`
leaving a single `√(ρ₀ρ₁)` factor, and the sqrt-free polynomial identity (with the `ξ₂` v⁰
cancellation) closes by `field_simp; ring`.  The lower-piece mixture Baxter factorization. -/
theorem matDCFreCore_hasDerivAt_lower_cLower (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hrho : ∀ n, 0 ≤ rho n) (hvac : vacMix rho sigma ≠ 0) (i k : Fin 2)
    (hlam : 0 ≤ (sigma k - sigma i) / 2)
    {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) ((sigma k - sigma i) / 2)) :
    HasDerivAt (fun w => matDCFreCore rho sigma hsig i k w)
      (-(2 * Real.pi * rhoGeoPhys rho i k * v * cLowerPiece rho sigma i k)) v := by
  refine (matDCFreCore_hasDerivAt_lower rho sigma hsig i k hlam hv).congr_deriv ?_
  fin_cases i <;> fin_cases k <;> simp only [Fin.isValue, Fin.reduceFinMk] <;>
    first
    | (exfalso; simp only [Fin.isValue, sub_self, zero_div, Set.mem_Ioo] at hv;
       exact absurd hv.2 (not_lt.mpr hv.1.le))
    | (simp only [Fin.isValue, qpConvLowerDeriv, Fin.sum_univ_two, intervalIntegral_quad,
         intervalIntegral_quad_mul_id, q0MixDeriv, physMix, Q0phys, Qppphys, Mix.R, Mix.lam,
         rhoGeoPhys, cLowerPiece, xi2, Real.sqrt_mul_self (hrho 0), Real.sqrt_mul_self (hrho 1),
         show rho 1 * rho 0 = rho 0 * rho 1 from mul_comm _ _]
       field_simp
       ring)

/-- **Shell-inverse forcing FROM the Baxter ODE (any piece, any forcing value `c`).**  If
`matDCFreCore'(v) = −2π·rgᵢₖ·v·c` at `v > 0` (the mixture Baxter factorization with forcing value
`c`), then `shellForcing rgᵢₖ i k v = c`.  Immediate from `shellForcing = −matDCFreCore'/(rgᵢₖ·2πv)`
(no shell integral needed — `shellForcing` is defined pointwise via `deriv`).  Both the lower-piece
capstone (`c = cLowerPiece`, discharged) and the upper piece (`c = cUpperPiece v`, the remaining
degree-5 discharge) plug into this single tool. -/
theorem shellForcing_eq_of_baxterODE (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin 2) (hrg : rhoGeoPhys rho i k ≠ 0) {v : ℝ} (hv : 0 < v) {c : ℝ}
    (hODE : HasDerivAt (fun w => matDCFreCore rho sigma hsig i k w)
      (-(2 * Real.pi * rhoGeoPhys rho i k * v * c)) v) :
    shellForcing rho sigma hsig (rhoGeoPhys rho i k) i k v = c := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [shellForcing, hODE.deriv]
  field_simp

/-- **Lower-piece value capstone (conditional on the lower-piece Baxter ODE).**  Specialization of
`shellForcing_eq_of_baxterODE` to the discharged lower-piece ODE (`c = cLowerPiece`). -/
theorem shellForcing_lower_eq_of_baxterODE (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin 2) (hrg : rhoGeoPhys rho i k ≠ 0) {v : ℝ} (hv : 0 < v)
    (hODE : HasDerivAt (fun w => matDCFreCore rho sigma hsig i k w)
      (-(2 * Real.pi * rhoGeoPhys rho i k * v * cLowerPiece rho sigma i k)) v) :
    shellForcing rho sigma hsig (rhoGeoPhys rho i k) i k v = cLowerPiece rho sigma i k :=
  shellForcing_eq_of_baxterODE rho sigma hsig i k hrg hv hODE

/-- **⭐⭐ Lower-piece value capstone — UNCONDITIONAL.**  At unequal diameters (`σᵢ < σₖ`), on the
lower piece `(0, λᵢₖ)` the OZ★ shell-inverse forcing IS the explicit constant physical mixture DCF:
`shellForcing rgᵢₖ i k v = cLowerPiece`.  Combines the discharged lower-piece mixture Baxter ODE
(`matDCFreCore_hasDerivAt_lower_cLower`) with `shellForcing_lower_eq_of_baxterODE`.  The first piece
of the unequal-σ value route, std-3. -/
theorem shellForcing_lower_eq (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hrho : ∀ n, 0 ≤ rho n) (hvac : vacMix rho sigma ≠ 0) (i k : Fin 2)
    (hrg : rhoGeoPhys rho i k ≠ 0) (hlam : 0 ≤ (sigma k - sigma i) / 2)
    {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) ((sigma k - sigma i) / 2)) :
    shellForcing rho sigma hsig (rhoGeoPhys rho i k) i k v = cLowerPiece rho sigma i k :=
  shellForcing_lower_eq_of_baxterODE rho sigma hsig i k hrg hv.1
    (matDCFreCore_hasDerivAt_lower_cLower rho sigma hsig hrho hvac i k hlam hv)

end FMSA.MixtureOzStar
