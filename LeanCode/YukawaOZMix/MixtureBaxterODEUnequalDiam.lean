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

end FMSA.MixtureOzStar
