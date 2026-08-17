/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MixtureDCFAEInjective
import LeanCode.YukawaOZMix.MixtureBaxterODEUnequalDiam
import LeanCode.YukawaOZMix.MixtureCorrelationDeriv
import LeanCode.YukawaOZMix.MixtureCorrelationDerivUpper
import LeanCode.YukawaOZMix.MixtureHSDCFFin1

/-!
# The mixture Baxter ODE at UNEQUAL diameters — GENERAL `N` (MIXCHS.7-N)

`MixtureBaxterODEUnequalDiam.lean` closed the unequal-σ value route for a **binary** mixture
(`Fin 2`).  Its proofs collapsed the species sum `∑ₗ` by `fin_cases i <;> fin_cases k` and
hard-coded the pre-summed DCF coefficients.  This file lifts the whole route to a **general
`N`-component** mixture (`Fin N`), where the correlation `∑ₗ` genuinely ranges over all species.

The key structural change: keep the species sum **symbolic**.  The `√`-collapse
`√(ρᵢρₗ)·√(ρₖρₗ) = ρₗ·√(ρᵢρₖ)` (`rhoGeoPhys_mul_eq`, general `N`) fires for **every** `l` without
`fin_cases`, so the per-species contribution to the DCF is a single ring identity under the sum.

This foundations layer generalizes the `Fin 2` objects to `Fin N`:
* `physMixN` — the physical (Lebowitz/PY) `Mix N 0` (`Q0phys`/`Qppphys`, `Qpp` row-independent);
* `qWeightedN`, `matDCFreCoreN` — the `√ρ`-weighted Baxter factor and the real DCF core
  `matDCFreCoreN i k v = qWeightedN i k v + qWeightedN k i(−v) − matCorrFull(qWeightedN) i k v`
  (the structural form of `Re(matDCFfull)`; all `q0MixEntry` real);
* `matCorrFull_eq_qpConvN` — the correlation as the species sum of `qpConv/(2π)²`;
* `matDCFreCoreN_upper_eq` / `_lower_eq` — the two-piece decomposition.
-/

open MeasureTheory Set

namespace FMSA.MixtureBaxter
open FMSA.MixtureOzStar

open FMSA.HardSphere FMSA.MatrixQ0 FMSA.WHSupports FMSA.InnerDecomp
open FMSA.MixtureHSDCF FMSA.MixtureConvolution

/-- **The `√ρ`-weighted Baxter factor** `qWeightedNᵢₖ(v) = rgᵢₖ·q0MixEntry(physMixN)ᵢₖ(v)`.
(`physMixN` = the general-`N` physical `Mix N 0`, `MixtureDCFAEInjective.lean`.) -/
noncomputable def qWeightedN {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) :
    Matrix (Fin N) (Fin N) (ℝ → ℝ) :=
  fun i k => fun v => rhoGeoPhys rho i k * q0MixEntry (physMixN rho sigma hsig) i k v

/-- **The DCF core at general `N`** — `matDCFreCoreN i k v = qWeightedN i k v + qWeightedN k i(−v)
− matCorrFull(qWeightedN) i k v`.  This is the structural form of `Re(matDCFfull)` (the two `√ρ`
linear Baxter terms minus the correlation); all `q0MixEntry` values are real, so no `Re`-bookkeeping
is needed.  At `N = 2` it agrees with `matDCFreCore`. -/
noncomputable def matDCFreCoreN {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) (v : ℝ) : ℝ :=
  qWeightedN rho sigma hsig i k v + qWeightedN rho sigma hsig k i (-v)
    - matCorrFull (qWeightedN rho sigma hsig) i k v

/-- `qWeightedN i k` vanishes off the support `[λᵢₖ, Rᵢₖ] = [(σₖ−σᵢ)/2, (σᵢ+σₖ)/2]`
(`q0MixEntry_support_subset`). -/
theorem qWeightedN_eq_zero_of_notMem {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) {v : ℝ} (hv : v ∉ Set.Icc ((sigma k - sigma i) / 2)
      ((sigma i + sigma k) / 2)) :
    qWeightedN rho sigma hsig i k v = 0 := by
  simp only [qWeightedN]
  have hsupp : v ∉ Function.support (q0MixEntry (physMixN rho sigma hsig) i k) := by
    intro hs
    have hmem := q0MixEntry_support_subset (physMixN rho sigma hsig) i k hs
    simp only [physMixN, Mix.lam, Mix.R] at hmem
    exact hv hmem
  rw [Function.notMem_support.mp hsupp, mul_zero]

/-- The forward Baxter term `qWeightedN i k` vanishes on `(−∞, λᵢₖ)`. -/
theorem qWeightedN_forward_eq_zero_of_lt_lam {N : ℕ} (rho sigma : Fin N → ℝ)
    (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) {v : ℝ} (hv : v < (sigma k - sigma i) / 2) :
    qWeightedN rho sigma hsig i k v = 0 :=
  qWeightedN_eq_zero_of_notMem rho sigma hsig i k
    (fun hmem => by rw [Set.mem_Icc] at hmem; linarith [hmem.1])

/-- The reflected Baxter term `qWeightedN k i(−v)` vanishes on `(λᵢₖ, ∞)` (for `v > λᵢₖ`,
`−v < λₖᵢ`, below the support of `qWeightedN k i`). -/
theorem qWeightedN_reflected_eq_zero_of_gt_lam {N : ℕ} (rho sigma : Fin N → ℝ)
    (hsig : ∀ k, 0 < sigma k) (i k : Fin N) {v : ℝ} (hv : (sigma k - sigma i) / 2 < v) :
    qWeightedN rho sigma hsig k i (-v) = 0 :=
  qWeightedN_eq_zero_of_notMem rho sigma hsig k i
    (fun hmem => by rw [Set.mem_Icc] at hmem; linarith [hmem.1])

open FMSA.MixtureHSDCF in
/-- **Correlation as the species sum of `qpConv/(2π)²`** (general `N`) —
`matCorrFull(qWeightedN)ᵢₖ = ∑ₗ qpConv(physMixN)ᵢₗₖ/(2π)²`.  Structural: `qFwd = 2π·qWeightedN` and
`pMixEntry = 2π·qWeightedN(−·)` per `l`, then `field_simp`.  (The `N = 2` proof verbatim.) -/
theorem matCorrFull_eq_qpConvN {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) (v : ℝ) :
    matCorrFull (qWeightedN rho sigma hsig) i k v
      = ∑ l, qpConv (physMixN rho sigma hsig) i l k v / (2 * Real.pi) ^ 2 := by
  simp only [matCorrFull]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hqFwd : ∀ t, qFwd (physMixN rho sigma hsig) i l t
      = 2 * Real.pi * qWeightedN rho sigma hsig i l t := by
    intro t; simp only [qFwd, qWeightedN, rhoGeoPhys, physMixN]; ring
  have hpMix : ∀ u, pMixEntry (physMixN rho sigma hsig) k l u
      = 2 * Real.pi * qWeightedN rho sigma hsig k l (-u) := by
    intro u; simp only [pMixEntry, qWeightedN, rhoGeoPhys, physMixN]; ring
  rw [show qpConv (physMixN rho sigma hsig) i l k v
      = ∫ t, qFwd (physMixN rho sigma hsig) i l t
          * pMixEntry (physMixN rho sigma hsig) k l (v - t) from rfl,
    ← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  rw [hqFwd, hpMix, show -(v - t) = t - v from by ring]
  have h2π : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  field_simp

/-- **Two-piece decomposition — UPPER piece `(λᵢₖ, Rᵢₖ)`** (general `N`).  For `v > λᵢₖ` the
reflected term vanishes: `matDCFreCoreN i k v = qWeightedN i k v − matCorrFull i k v`. -/
theorem matDCFreCoreN_upper_eq {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) {v : ℝ} (hv : (sigma k - sigma i) / 2 < v) :
    matDCFreCoreN rho sigma hsig i k v
      = qWeightedN rho sigma hsig i k v - matCorrFull (qWeightedN rho sigma hsig) i k v := by
  simp only [matDCFreCoreN]
  rw [qWeightedN_reflected_eq_zero_of_gt_lam rho sigma hsig i k hv]; ring

/-- **Two-piece decomposition — LOWER piece `(0, λᵢₖ)`** (general `N`).  For `v < λᵢₖ` the forward
term vanishes: `matDCFreCoreN i k v = qWeightedN k i(−v) − matCorrFull i k v`. -/
theorem matDCFreCoreN_lower_eq {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) {v : ℝ} (hv : v < (sigma k - sigma i) / 2) :
    matDCFreCoreN rho sigma hsig i k v
      = qWeightedN rho sigma hsig k i (-v) - matCorrFull (qWeightedN rho sigma hsig) i k v := by
  simp only [matDCFreCoreN]
  rw [qWeightedN_forward_eq_zero_of_lt_lam rho sigma hsig i k hv]; ring

open FMSA.MixtureHSDCF FMSA.MixtureHSDCFFin1 in
/-- **⭐ Mixture Baxter ODE LHS on the UPPER piece (general `N`).**  On `(λᵢₖ, Rᵢₖ)` the DCF core is
`matDCFreCoreN i k = qWeightedN i k − matCorrFull i k` (`matDCFreCoreN_upper_eq`, reflected off), so
its derivative is the forward-quadratic chain rule minus the species sum of upper-`qpConv`
derivatives: `matDCFreCoreN'(v) = rgᵢₖ·q0MixDeriv(physMixN) i k v
− ∑ₗ qpConvUpperDeriv(physMixN)ᵢₗₖ(v)/(2π)²` (forward via `hasDerivAt_q0MixEntry`, correlation via
`hasDerivAt_qpConv_upper` under the species sum).  The general-`N` upper analog of
`matDCFreCore_hasDerivAt_lower`; matching to `−2π·rgᵢₖ·v·c_ij(v)` is the upper-piece factorization
(with the `√`-collapse `rhoGeoPhys_mul_eq` firing per `l`). -/
theorem matDCFreCoreN_hasDerivAt_upper {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) (hlam : 0 ≤ (sigma k - sigma i) / 2)
    {v : ℝ} (hv : v ∈ Set.Ioo ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2)) :
    HasDerivAt (matDCFreCoreN rho sigma hsig i k)
      (rhoGeoPhys rho i k * q0MixDeriv (physMixN rho sigma hsig) i k v
        - ∑ l, qpConvUpperDeriv (physMixN rho sigma hsig) i l k v / (2 * Real.pi) ^ 2) v := by
  have hlam' : (0 : ℝ) ≤ (physMixN rho sigma hsig).lam i k := by
    simp only [physMixN, Mix.lam]; exact hlam
  have hv' : v ∈ Set.Ioo ((physMixN rho sigma hsig).lam i k)
      ((physMixN rho sigma hsig).R i k) := by
    simp only [physMixN, Mix.lam, Mix.R]; exact hv
  have hqw : HasDerivAt (fun w => qWeightedN rho sigma hsig i k w)
      (rhoGeoPhys rho i k * q0MixDeriv (physMixN rho sigma hsig) i k v) v :=
    (hasDerivAt_q0MixEntry (physMixN rho sigma hsig) i k hv').const_mul (rhoGeoPhys rho i k)
  have hcorr : HasDerivAt (fun w => matCorrFull (qWeightedN rho sigma hsig) i k w)
      (∑ l, qpConvUpperDeriv (physMixN rho sigma hsig) i l k v / (2 * Real.pi) ^ 2) v := by
    have heq : (fun w => matCorrFull (qWeightedN rho sigma hsig) i k w)
        = fun w => ∑ l, qpConv (physMixN rho sigma hsig) i l k w / (2 * Real.pi) ^ 2 :=
      funext (fun w => matCorrFull_eq_qpConvN rho sigma hsig i k w)
    rw [heq]
    refine HasDerivAt.fun_sum (fun l _ => ?_)
    exact (hasDerivAt_qpConv_upper (physMixN rho sigma hsig) i l k hlam' hv').div_const _
  have hEq : matDCFreCoreN rho sigma hsig i k
      =ᶠ[nhds v] (fun w => qWeightedN rho sigma hsig i k w
        - matCorrFull (qWeightedN rho sigma hsig) i k w) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with w hw
    exact matDCFreCoreN_upper_eq rho sigma hsig i k hw.1
  exact (hqw.sub hcorr).congr_of_eventuallyEq hEq


/-- **Upper-piece Lebowitz DCF coefficients (general `N`), as leading + per-species pieces.**
Derived + validated (`genN_coeffs.py`): the `(i,k)` LEADING term contributes only to `A,B`
(`cLeadANumN`, `cLeadBNumN`), and each species `l` contributes the four `cCorr*NumN(i,l,k)`
(each **linear in `ρₗ`**).  With `vacMix`/`xi2` kept opaque; at `N = 2`, `cLead + ∑_{l∈{i,k}}`
reproduces the binary `cUpperANum/BNum/C2Num/ENum`. -/
noncomputable def cLeadANumN {N : ℕ} (rho sigma : Fin N → ℝ) (i k : Fin N) : ℝ :=
  -768 * vacMix rho sigma^3 - 384 * vacMix rho sigma^2 * Real.pi * sigma k * xi2 rho sigma

noncomputable def cLeadBNumN {N : ℕ} (rho sigma : Fin N → ℝ) (i k : Fin N) : ℝ :=
  192 * vacMix rho sigma^2 * Real.pi * sigma k^2 * xi2 rho sigma

noncomputable def cCorrANumN {N : ℕ} (rho sigma : Fin N → ℝ) (i l k : Fin N) : ℝ :=
  -64 * vacMix rho sigma^2 * Real.pi * rho l * sigma i^3
    - 192 * vacMix rho sigma^2 * Real.pi * rho l * sigma i^2 * sigma l
    - 192 * vacMix rho sigma^2 * Real.pi * rho l * sigma i * sigma l^2
    - 64 * vacMix rho sigma^2 * Real.pi * rho l * sigma k^3
    - 192 * vacMix rho sigma^2 * Real.pi * rho l * sigma k^2 * sigma l
    + 192 * vacMix rho sigma^2 * Real.pi * rho l * sigma k * sigma l^2
    - 64 * vacMix rho sigma * Real.pi^2 * rho l * sigma i^3 * sigma l * xi2 rho sigma
    - 96 * vacMix rho sigma * Real.pi^2 * rho l * sigma i^2 * sigma l^2 * xi2 rho sigma
    - 64 * vacMix rho sigma * Real.pi^2 * rho l * sigma k^3 * sigma l * xi2 rho sigma
    - 96 * vacMix rho sigma * Real.pi^2 * rho l * sigma k^2 * sigma l^2 * xi2 rho sigma
    - 16 * Real.pi^3 * rho l * sigma i^3 * sigma l^2 * xi2 rho sigma^2
    - 16 * Real.pi^3 * rho l * sigma k^3 * sigma l^2 * xi2 rho sigma^2

noncomputable def cCorrBNumN {N : ℕ} (rho sigma : Fin N → ℝ) (i l k : Fin N) : ℝ :=
  12 * vacMix rho sigma^2 * Real.pi * rho l * sigma i^4
    + 48 * vacMix rho sigma^2 * Real.pi * rho l * sigma i^3 * sigma l
    - 24 * vacMix rho sigma^2 * Real.pi * rho l * sigma i^2 * sigma k^2
    - 48 * vacMix rho sigma^2 * Real.pi * rho l * sigma i^2 * sigma k * sigma l
    + 48 * vacMix rho sigma^2 * Real.pi * rho l * sigma i^2 * sigma l^2
    - 48 * vacMix rho sigma^2 * Real.pi * rho l * sigma i * sigma k^2 * sigma l
    - 96 * vacMix rho sigma^2 * Real.pi * rho l * sigma i * sigma k * sigma l^2
    + 12 * vacMix rho sigma^2 * Real.pi * rho l * sigma k^4
    + 48 * vacMix rho sigma^2 * Real.pi * rho l * sigma k^3 * sigma l
    - 144 * vacMix rho sigma^2 * Real.pi * rho l * sigma k^2 * sigma l^2
    + 12 * vacMix rho sigma * Real.pi^2 * rho l * sigma i^4 * sigma l * xi2 rho sigma
    + 24 * vacMix rho sigma * Real.pi^2 * rho l * sigma i^3 * sigma l^2 * xi2 rho sigma
    - 24 * vacMix rho sigma * Real.pi^2 * rho l * sigma i^2 * sigma k^2 * sigma l * xi2 rho sigma
    - 24 * vacMix rho sigma * Real.pi^2 * rho l * sigma i^2 * sigma k * sigma l^2 * xi2 rho sigma
    - 24 * vacMix rho sigma * Real.pi^2 * rho l * sigma i * sigma k^2 * sigma l^2 * xi2 rho sigma
    + 12 * vacMix rho sigma * Real.pi^2 * rho l * sigma k^4 * sigma l * xi2 rho sigma
    + 24 * vacMix rho sigma * Real.pi^2 * rho l * sigma k^3 * sigma l^2 * xi2 rho sigma
    + 3 * Real.pi^3 * rho l * sigma i^4 * sigma l^2 * xi2 rho sigma^2
    - 6 * Real.pi^3 * rho l * sigma i^2 * sigma k^2 * sigma l^2 * xi2 rho sigma^2
    + 3 * Real.pi^3 * rho l * sigma k^4 * sigma l^2 * xi2 rho sigma^2

noncomputable def cCorrC2NumN {N : ℕ} (rho sigma : Fin N → ℝ) (i l k : Fin N) : ℝ :=
  96 * vacMix rho sigma^2 * Real.pi * rho l * sigma i^2
    + 192 * vacMix rho sigma^2 * Real.pi * rho l * sigma i * sigma l
    + 96 * vacMix rho sigma^2 * Real.pi * rho l * sigma k^2
    + 192 * vacMix rho sigma^2 * Real.pi * rho l * sigma k * sigma l
    + 192 * vacMix rho sigma^2 * Real.pi * rho l * sigma l^2
    + 96 * vacMix rho sigma * Real.pi^2 * rho l * sigma i^2 * sigma l * xi2 rho sigma
    + 96 * vacMix rho sigma * Real.pi^2 * rho l * sigma i * sigma l^2 * xi2 rho sigma
    + 96 * vacMix rho sigma * Real.pi^2 * rho l * sigma k^2 * sigma l * xi2 rho sigma
    + 96 * vacMix rho sigma * Real.pi^2 * rho l * sigma k * sigma l^2 * xi2 rho sigma
    + 24 * Real.pi^3 * rho l * sigma i^2 * sigma l^2 * xi2 rho sigma^2
    + 24 * Real.pi^3 * rho l * sigma k^2 * sigma l^2 * xi2 rho sigma^2

noncomputable def cCorrENumN {N : ℕ} (rho sigma : Fin N → ℝ) (i l k : Fin N) : ℝ :=
  -64 * vacMix rho sigma^2 * Real.pi * rho l
    - 64 * vacMix rho sigma * Real.pi^2 * rho l * sigma l * xi2 rho sigma
    - 16 * Real.pi^3 * rho l * sigma l^2 * xi2 rho sigma^2


/-- Per-species contribution to the upper DCF `= (A + B/v + C₂v + E·v³)/(768·vac⁴)`. -/
noncomputable def cCorrPieceN {N : ℕ} (rho sigma : Fin N → ℝ) (i l k : Fin N) (v : ℝ) : ℝ :=
  (cCorrANumN rho sigma i l k + cCorrBNumN rho sigma i l k / v
      + cCorrC2NumN rho sigma i l k * v + cCorrENumN rho sigma i l k * v ^ 3)
    / (768 * vacMix rho sigma ^ 4)

/-- Leading `(i,k)` contribution to the upper DCF `= (A + B/v)/(768·vac⁴)`. -/
noncomputable def cLeadPieceN {N : ℕ} (rho sigma : Fin N → ℝ) (i k : Fin N) (v : ℝ) : ℝ :=
  (cLeadANumN rho sigma i k + cLeadBNumN rho sigma i k / v) / (768 * vacMix rho sigma ^ 4)

/-- **The general-`N` upper-piece Lebowitz mixture DCF** `c_ij(v) = cLeadPieceN + ∑ₗ cCorrPieceN`
— the two-piece DCF's outer branch with the full species sum (at `N = 2` it collapses to
`cUpperPiece`). -/
noncomputable def cUpperPieceN {N : ℕ} (rho sigma : Fin N → ℝ) (i k : Fin N) (v : ℝ) : ℝ :=
  cLeadPieceN rho sigma i k v + ∑ l, cCorrPieceN rho sigma i l k v

open FMSA.MixtureHSDCF in
set_option maxHeartbeats 2000000 in
/-- **⭐ Per-species upper-`qpConv`-derivative identity (the `√`-collapse).**  For each species `l`,
`qpConvUpperDeriv(physMixN)ᵢₗₖ(v)/(2π)² = 2π·rgᵢₖ·v·cCorrPieceN(i,l,k,v)`.  Key step:
`qpConvUpperDeriv = (2π)²·(√(ρᵢρₗ)·√(ρₖρₗ))·Il'(v)` with the `√` product a single subterm, which
`rhoGeoPhys_mul_eq` collapses to `ρₗ·√(ρᵢρₖ)` for **every** `l` (no `fin_cases`); the residue is a
`√`-free `field_simp; ring`.  `Il'` is the bare (`√`-free) moment-integral derivative. -/
theorem qpConvUpperDeriv_per_l {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hrho : ∀ n, 0 ≤ rho n) (hvac : vacMix rho sigma ≠ 0) (i l k : Fin N) {v : ℝ} (hv0 : v ≠ 0) :
    qpConvUpperDeriv (physMixN rho sigma hsig) i l k v / (2 * Real.pi) ^ 2
      = 2 * Real.pi * rhoGeoPhys rho i k * v * cCorrPieceN rho sigma i l k v := by
  have hab : Real.sqrt (rho i * rho l) * Real.sqrt (rho k * rho l)
      = rho l * Real.sqrt (rho i * rho k) := by
    have h := rhoGeoPhys_mul_eq rho hrho i k l
    simpa only [rhoGeoPhys] using h
  have hfac : qpConvUpperDeriv (physMixN rho sigma hsig) i l k v
      = (2 * Real.pi) ^ 2 * (Real.sqrt (rho i * rho l) * Real.sqrt (rho k * rho l))
        * (
        Real.pi^2 * sigma i^4/(32 * vacMix rho sigma^2)
        + Real.pi^2 * sigma i^3 * sigma l/(8 * vacMix rho sigma^2)
        - Real.pi^2 * sigma i^3 * v/(6 * vacMix rho sigma^2)
        - Real.pi^2 * sigma i^2 * sigma k^2/(16 * vacMix rho sigma^2)
        - Real.pi^2 * sigma i^2 * sigma k * sigma l/(8 * vacMix rho sigma^2)
        + Real.pi^2 * sigma i^2 * sigma l^2/(8 * vacMix rho sigma^2)
        - Real.pi^2 * sigma i^2 * sigma l * v/(2 * vacMix rho sigma^2)
        + Real.pi^2 * sigma i^2 * v^2/(4 * vacMix rho sigma^2)
        - Real.pi^2 * sigma i * sigma k^2 * sigma l/(8 * vacMix rho sigma^2)
        - Real.pi^2 * sigma i * sigma k * sigma l^2/(4 * vacMix rho sigma^2)
        - Real.pi^2 * sigma i * sigma l^2 * v/(2 * vacMix rho sigma^2)
        + Real.pi^2 * sigma i * sigma l * v^2/(2 * vacMix rho sigma^2)
        + Real.pi^2 * sigma k^4/(32 * vacMix rho sigma^2)
        + Real.pi^2 * sigma k^3 * sigma l/(8 * vacMix rho sigma^2)
        - Real.pi^2 * sigma k^3 * v/(6 * vacMix rho sigma^2)
        - 3 * Real.pi^2 * sigma k^2 * sigma l^2/(8 * vacMix rho sigma^2)
        - Real.pi^2 * sigma k^2 * sigma l * v/(2 * vacMix rho sigma^2)
        + Real.pi^2 * sigma k^2 * v^2/(4 * vacMix rho sigma^2)
        + Real.pi^2 * sigma k * sigma l^2 * v/(2 * vacMix rho sigma^2)
        + Real.pi^2 * sigma k * sigma l * v^2/(2 * vacMix rho sigma^2)
        + Real.pi^2 * sigma l^2 * v^2/(2 * vacMix rho sigma^2)
        - Real.pi^2 * v^4/(6 * vacMix rho sigma^2)
        + Real.pi^3 * sigma i^4 * sigma l * xi2 rho sigma/(32 * vacMix rho sigma^3)
        + Real.pi^3 * sigma i^3 * sigma l^2 * xi2 rho sigma/(16 * vacMix rho sigma^3)
        - Real.pi^3 * sigma i^3 * sigma l * v * xi2 rho sigma/(6 * vacMix rho sigma^3)
        - Real.pi^3 * sigma i^2 * sigma k^2 * sigma l * xi2 rho sigma/(16 * vacMix rho sigma^3)
        - Real.pi^3 * sigma i^2 * sigma k * sigma l^2 * xi2 rho sigma/(16 * vacMix rho sigma^3)
        - Real.pi^3 * sigma i^2 * sigma l^2 * v * xi2 rho sigma/(4 * vacMix rho sigma^3)
        + Real.pi^3 * sigma i^2 * sigma l * v^2 * xi2 rho sigma/(4 * vacMix rho sigma^3)
        - Real.pi^3 * sigma i * sigma k^2 * sigma l^2 * xi2 rho sigma/(16 * vacMix rho sigma^3)
        + Real.pi^3 * sigma i * sigma l^2 * v^2 * xi2 rho sigma/(4 * vacMix rho sigma^3)
        + Real.pi^3 * sigma k^4 * sigma l * xi2 rho sigma/(32 * vacMix rho sigma^3)
        + Real.pi^3 * sigma k^3 * sigma l^2 * xi2 rho sigma/(16 * vacMix rho sigma^3)
        - Real.pi^3 * sigma k^3 * sigma l * v * xi2 rho sigma/(6 * vacMix rho sigma^3)
        - Real.pi^3 * sigma k^2 * sigma l^2 * v * xi2 rho sigma/(4 * vacMix rho sigma^3)
        + Real.pi^3 * sigma k^2 * sigma l * v^2 * xi2 rho sigma/(4 * vacMix rho sigma^3)
        + Real.pi^3 * sigma k * sigma l^2 * v^2 * xi2 rho sigma/(4 * vacMix rho sigma^3)
        - Real.pi^3 * sigma l * v^4 * xi2 rho sigma/(6 * vacMix rho sigma^3)
        + Real.pi^4 * sigma i^4 * sigma l^2 * xi2 rho sigma^2/(128 * vacMix rho sigma^4)
        - Real.pi^4 * sigma i^3 * sigma l^2 * v * xi2 rho sigma^2/(24 * vacMix rho sigma^4)
        - Real.pi^4 * sigma i^2 * sigma k^2 * sigma l^2 * xi2 rho sigma^2/(64 * vacMix rho sigma^4)
        + Real.pi^4 * sigma i^2 * sigma l^2 * v^2 * xi2 rho sigma^2/(16 * vacMix rho sigma^4)
        + Real.pi^4 * sigma k^4 * sigma l^2 * xi2 rho sigma^2/(128 * vacMix rho sigma^4)
        - Real.pi^4 * sigma k^3 * sigma l^2 * v * xi2 rho sigma^2/(24 * vacMix rho sigma^4)
        + Real.pi^4 * sigma k^2 * sigma l^2 * v^2 * xi2 rho sigma^2/(16 * vacMix rho sigma^4)
        - Real.pi^4 * sigma l^2 * v^4 * xi2 rho sigma^2/(24 * vacMix rho sigma^4)
        ) := by
    rw [qpConvUpperDeriv, intervalIntegral_quad, intervalIntegral_quad_mul_id]
    simp only [physMixN, Q0phys, Qppphys, Mix.R, Mix.lam]
    field_simp
    ring
  rw [hfac, hab]
  simp only [rhoGeoPhys, cCorrPieceN, cCorrANumN, cCorrBNumN, cCorrC2NumN, cCorrENumN]
  field_simp
  ring

open FMSA.MixtureHSDCFFin1 in
set_option maxHeartbeats 2000000 in
/-- **Leading identity.**  `rgᵢₖ·q0MixDeriv(physMixN) i k v = −2π·rgᵢₖ·v·cLeadPieceN` — the forward
quadratic's slope IS the leading part of the upper Baxter forcing (√-free once `rgᵢₖ` is common). -/
theorem matDCFreCoreN_lead {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) {v : ℝ} (hv0 : v ≠ 0) :
    rhoGeoPhys rho i k * q0MixDeriv (physMixN rho sigma hsig) i k v
      = -(2 * Real.pi * rhoGeoPhys rho i k * v * cLeadPieceN rho sigma i k v) := by
  simp only [q0MixDeriv, physMixN, Q0phys, Qppphys, Mix.R, rhoGeoPhys, cLeadPieceN,
    cLeadANumN, cLeadBNumN]
  field_simp
  ring

open FMSA.MixtureHSDCF FMSA.MixtureHSDCFFin1 in
/-- **⭐⭐ General-`N` upper mixture Baxter ODE.**  `matDCFreCoreN'(v) = −2π·rgᵢₖ·v·cUpperPieceN(v)`
on `(λᵢₖ, Rᵢₖ)`.  Assembles `matDCFreCoreN_hasDerivAt_upper` (structural derivative) with the
leading identity and the per-species identity under the species sum (`Finset.sum_congr` +
`Finset.mul_sum`).  The general-`N` upper analog of `matDCFreCore_hasDerivAt_upper_cUpper`. -/
theorem matDCFreCoreN_hasDerivAt_upper_cUpper {N : ℕ} (rho sigma : Fin N → ℝ)
    (hsig : ∀ k, 0 < sigma k) (hrho : ∀ n, 0 ≤ rho n) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N)
    (hlam : 0 ≤ (sigma k - sigma i) / 2)
    {v : ℝ} (hv : v ∈ Set.Ioo ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2)) (hv0 : v ≠ 0) :
    HasDerivAt (matDCFreCoreN rho sigma hsig i k)
      (-(2 * Real.pi * rhoGeoPhys rho i k * v * cUpperPieceN rho sigma i k v)) v := by
  refine (matDCFreCoreN_hasDerivAt_upper rho sigma hsig i k hlam hv).congr_deriv ?_
  have hsum : (∑ l, qpConvUpperDeriv (physMixN rho sigma hsig) i l k v / (2 * Real.pi) ^ 2)
      = ∑ l, 2 * Real.pi * rhoGeoPhys rho i k * v * cCorrPieceN rho sigma i l k v :=
    Finset.sum_congr rfl (fun l _ =>
      qpConvUpperDeriv_per_l rho sigma hsig hrho hvac i l k hv0)
  rw [hsum, matDCFreCoreN_lead rho sigma hsig hvac i k hv0, cUpperPieceN, mul_add,
    Finset.mul_sum]
  ring

/-- **The constructed shell-forcing at general `N`** — `Φᶜᵢₖ(s) = −matDCFreCoreN'(i,k)(s)/(rg·2πs)`
(the shellKernel-inverse; the `N`-ary `shellForcing`). -/
noncomputable def shellForcingN {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (rg : ℝ) : Matrix (Fin N) (Fin N) (ℝ → ℝ) :=
  fun i k => fun s =>
    -(deriv (fun w => matDCFreCoreN rho sigma hsig i k w) s) / (rg * (2 * Real.pi * s))

/-- **Shell-inverse forcing FROM the Baxter ODE (general `N`).**  If `matDCFreCoreN'(v) =
−2π·rgᵢₖ·v·c` at `v > 0`, then `shellForcingN rgᵢₖ i k v = c` (pointwise, from the `deriv`). -/
theorem shellForcing_eq_of_baxterODEN {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) (hrg : rhoGeoPhys rho i k ≠ 0) {v : ℝ} (hv : 0 < v) {c : ℝ}
    (hODE : HasDerivAt (fun w => matDCFreCoreN rho sigma hsig i k w)
      (-(2 * Real.pi * rhoGeoPhys rho i k * v * c)) v) :
    shellForcingN rho sigma hsig (rhoGeoPhys rho i k) i k v = c := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [shellForcingN, hODE.deriv]
  field_simp

/-- **⭐⭐⭐ General-`N` upper-piece value capstone.**  For the ordered pair `σᵢ < σₖ`, on
`(λᵢₖ, Rᵢₖ)` the OZ★ shell-inverse forcing IS the explicit `N`-species-summed upper Lebowitz DCF:
`shellForcingN rgᵢₖ i k v = cUpperPieceN`.  The general-`N` analog of `shellForcing_upper_eq`. -/
theorem shellForcing_upper_eqN {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hrho : ∀ n, 0 ≤ rho n) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) (hlt : sigma i < sigma k)
    (hrg : rhoGeoPhys rho i k ≠ 0)
    {v : ℝ} (hv : v ∈ Set.Ioo ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2)) :
    shellForcingN rho sigma hsig (rhoGeoPhys rho i k) i k v = cUpperPieceN rho sigma i k v :=
  have hv0 : 0 < v := lt_trans (by linarith [hlt]) hv.1
  shellForcing_eq_of_baxterODEN rho sigma hsig i k hrg hv0
    (matDCFreCoreN_hasDerivAt_upper_cUpper rho sigma hsig hrho hvac i k (by linarith [hlt]) hv
      hv0.ne')


/-! ### The LOWER piece + full two-piece gluing (general `N`)

The lower piece mirrors the upper (`hasDerivAt_qpConv_lower` is already general-`N`, fixed limits),
with the reflected forward term `qWeightedN k i(−·)`.  The per-species lower DCF pieces carry a
`1/v` term each; they aggregate (over `∑ₗ` + leading) to the physical constant, but that
`constant`-form is a separate `∑ₗ`-moment identity (`ξ₁/ξ₃`, per-species continuity FALSE at the
knot).  The **value capstone** below needs no such aggregation. -/

/-- **Lower-piece Lebowitz DCF coefficients (general `N`)** — leading `(i,k)` + per-species
`(i,l,k)` contributions, each `= (A + B/v)/(768·vac⁴)` (no `C₂, E`: `Il_low'` is linear in `v`).
Derived + validated against the binary constant `cLowerPiece` (`genN_lower.py`). -/
noncomputable def cLowerLeadANumN {N : ℕ} (rho sigma : Fin N → ℝ) (i k : Fin N) : ℝ :=
  -768 * vacMix rho sigma^3 - 384 * vacMix rho sigma^2 * Real.pi * sigma i * xi2 rho sigma

noncomputable def cLowerLeadBNumN {N : ℕ} (rho sigma : Fin N → ℝ) (i k : Fin N) : ℝ :=
  -192 * vacMix rho sigma^2 * Real.pi * sigma i^2 * xi2 rho sigma

noncomputable def cLowerCorrANumN {N : ℕ} (rho sigma : Fin N → ℝ) (i l k : Fin N) : ℝ :=
  -128 * vacMix rho sigma^2 * Real.pi * rho l * sigma i^3
    - 384 * vacMix rho sigma^2 * Real.pi * rho l * sigma i^2 * sigma l
    - 128 * vacMix rho sigma * Real.pi^2 * rho l * sigma i^3 * sigma l * xi2 rho sigma
    - 192 * vacMix rho sigma * Real.pi^2 * rho l * sigma i^2 * sigma l^2 * xi2 rho sigma
    - 32 * Real.pi^3 * rho l * sigma i^3 * sigma l^2 * xi2 rho sigma^2

noncomputable def cLowerCorrBNumN {N : ℕ} (rho sigma : Fin N → ℝ) (i l k : Fin N) : ℝ :=
  192 * vacMix rho sigma^2 * Real.pi * rho l * sigma i^2 * sigma l^2


/-- Per-species lower DCF contribution `= (A + B/v)/(768·vac⁴)`. -/
noncomputable def cLowerCorrPieceN {N : ℕ} (rho sigma : Fin N → ℝ) (i l k : Fin N) (v : ℝ) : ℝ :=
  (cLowerCorrANumN rho sigma i l k + cLowerCorrBNumN rho sigma i l k / v)
    / (768 * vacMix rho sigma ^ 4)

/-- Leading `(i,k)` lower DCF contribution (the reflected forward slope). -/
noncomputable def cLowerLeadPieceN {N : ℕ} (rho sigma : Fin N → ℝ) (i k : Fin N) (v : ℝ) : ℝ :=
  (cLowerLeadANumN rho sigma i k + cLowerLeadBNumN rho sigma i k / v)
    / (768 * vacMix rho sigma ^ 4)

/-- **The general-`N` lower-piece Lebowitz mixture DCF** `= cLowerLeadPieceN + ∑ₗ cLowerCorrPieceN`
(aggregates to the physical constant; at `N = 2` reduces to `cLowerPiece`). -/
noncomputable def cLowerPieceN {N : ℕ} (rho sigma : Fin N → ℝ) (i k : Fin N) (v : ℝ) : ℝ :=
  cLowerLeadPieceN rho sigma i k v + ∑ l, cLowerCorrPieceN rho sigma i l k v

open FMSA.MixtureHSDCF in
set_option maxHeartbeats 2000000 in
/-- **Per-species lower-`qpConv`-derivative identity** — `qpConvLowerDeriv(physMixN)ᵢₗₖ(v)/(2π)² =
2π·rgᵢₖ·v·cLowerCorrPieceN`, the fixed-limit analog of `qpConvUpperDeriv_per_l`
(same `√`-collapse). -/
theorem qpConvLowerDeriv_per_l {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hrho : ∀ n, 0 ≤ rho n) (hvac : vacMix rho sigma ≠ 0) (i l k : Fin N) {v : ℝ} (hv0 : v ≠ 0) :
    qpConvLowerDeriv (physMixN rho sigma hsig) i l k v / (2 * Real.pi) ^ 2
      = 2 * Real.pi * rhoGeoPhys rho i k * v * cLowerCorrPieceN rho sigma i l k v := by
  have hab : Real.sqrt (rho i * rho l) * Real.sqrt (rho k * rho l)
      = rho l * Real.sqrt (rho i * rho k) := by
    have h := rhoGeoPhys_mul_eq rho hrho i k l
    simpa only [rhoGeoPhys] using h
  have hfac : qpConvLowerDeriv (physMixN rho sigma hsig) i l k v
      = (2 * Real.pi) ^ 2 * (Real.sqrt (rho i * rho l) * Real.sqrt (rho k * rho l))
        * (
        -Real.pi^2 * sigma i^3 * v/(3 * vacMix rho sigma^2)
        + Real.pi^2 * sigma i^2 * sigma l^2/(2 * vacMix rho sigma^2)
        - Real.pi^2 * sigma i^2 * sigma l * v/vacMix rho sigma^2
        - Real.pi^3 * sigma i^3 * sigma l * v * xi2 rho sigma/(3 * vacMix rho sigma^3)
        - Real.pi^3 * sigma i^2 * sigma l^2 * v * xi2 rho sigma/(2 * vacMix rho sigma^3)
        - Real.pi^4 * sigma i^3 * sigma l^2 * v * xi2 rho sigma^2/(12 * vacMix rho sigma^4)
        ) := by
    rw [qpConvLowerDeriv, intervalIntegral_quad, intervalIntegral_quad_mul_id]
    simp only [physMixN, Q0phys, Qppphys, Mix.R, Mix.lam]
    field_simp
    ring
  rw [hfac, hab]
  simp only [rhoGeoPhys, cLowerCorrPieceN, cLowerCorrANumN, cLowerCorrBNumN]
  field_simp
  ring

open FMSA.MixtureHSDCFFin1 in
set_option maxHeartbeats 2000000 in
/-- **Reflected leading identity (lower).**  `rgₖᵢ·q0MixDeriv(physMixN) k i(−v) = 2π·rgᵢₖ·v·
cLowerLeadPieceN` (`rgₖᵢ = rgᵢₖ` by `mul_comm` under the `√`). -/
theorem matDCFreCoreN_lead_lower {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) {v : ℝ} (hv0 : v ≠ 0) :
    rhoGeoPhys rho k i * q0MixDeriv (physMixN rho sigma hsig) k i (-v)
      = 2 * Real.pi * rhoGeoPhys rho i k * v * cLowerLeadPieceN rho sigma i k v := by
  simp only [q0MixDeriv, physMixN, Q0phys, Qppphys, Mix.R, rhoGeoPhys, cLowerLeadPieceN,
    cLowerLeadANumN, cLowerLeadBNumN, mul_comm (rho k) (rho i)]
  field_simp
  ring

open FMSA.MixtureHSDCF FMSA.MixtureHSDCFFin1 in
/-- **Mixture Baxter ODE LHS on the LOWER piece (general `N`)** — the reflected forward chain rule
minus the species sum of lower-`qpConv` derivatives (fixed limits; no boundary term). -/
theorem matDCFreCoreN_hasDerivAt_lower {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) (hlam : 0 ≤ (sigma k - sigma i) / 2)
    {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) ((sigma k - sigma i) / 2)) :
    HasDerivAt (matDCFreCoreN rho sigma hsig i k)
      (-(rhoGeoPhys rho k i * q0MixDeriv (physMixN rho sigma hsig) k i (-v))
        - ∑ l, qpConvLowerDeriv (physMixN rho sigma hsig) i l k v / (2 * Real.pi) ^ 2) v := by
  have hmem : -v ∈ Set.Ioo ((physMixN rho sigma hsig).lam k i)
      ((physMixN rho sigma hsig).R k i) := by
    simp only [physMixN, Mix.lam, Mix.R]
    exact ⟨by linarith [hv.2], by linarith [hv.1, hsig i, hsig k]⟩
  have hcomp := (hasDerivAt_q0MixEntry (physMixN rho sigma hsig) k i hmem).comp v
    ((hasDerivAt_id v).neg)
  have hrefl : HasDerivAt (fun w => qWeightedN rho sigma hsig k i (-w))
      (rhoGeoPhys rho k i * (q0MixDeriv (physMixN rho sigma hsig) k i (-v) * -1)) v := by
    have heq : (fun w => qWeightedN rho sigma hsig k i (-w))
        = fun w => rhoGeoPhys rho k i * q0MixEntry (physMixN rho sigma hsig) k i (-w) := by
      funext w; simp only [qWeightedN]
    rw [heq]; exact hcomp.const_mul (rhoGeoPhys rho k i)
  have hcorr : HasDerivAt (fun w => matCorrFull (qWeightedN rho sigma hsig) i k w)
      (∑ l, qpConvLowerDeriv (physMixN rho sigma hsig) i l k v / (2 * Real.pi) ^ 2) v := by
    have heq : (fun w => matCorrFull (qWeightedN rho sigma hsig) i k w)
        = fun w => ∑ l, qpConv (physMixN rho sigma hsig) i l k w / (2 * Real.pi) ^ 2 :=
      funext (fun w => matCorrFull_eq_qpConvN rho sigma hsig i k w)
    rw [heq]
    refine HasDerivAt.fun_sum (fun l _ => ?_)
    have hlam' : (0 : ℝ) ≤ (physMixN rho sigma hsig).lam i k := by
      simp only [physMixN, Mix.lam]; exact hlam
    have hv' : v ∈ Set.Ioo (0 : ℝ) ((physMixN rho sigma hsig).lam i k) := by
      simp only [physMixN, Mix.lam]; exact hv
    exact (hasDerivAt_qpConv_lower (physMixN rho sigma hsig) i l k hlam' hv').div_const _
  have hEq : matDCFreCoreN rho sigma hsig i k
      =ᶠ[nhds v] (fun w => qWeightedN rho sigma hsig k i (-w)
        - matCorrFull (qWeightedN rho sigma hsig) i k w) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with w hw
    exact matDCFreCoreN_lower_eq rho sigma hsig i k hw.2
  exact ((hrefl.sub hcorr).congr_deriv (by ring)).congr_of_eventuallyEq hEq

open FMSA.MixtureHSDCF FMSA.MixtureHSDCFFin1 in
/-- **⭐⭐ General-`N` lower mixture Baxter ODE** — `matDCFreCoreN'(v) = −2π·rgᵢₖ·v·cLowerPieceN(v)`
on `(0, λᵢₖ)` (reflected-leading identity + per-species identity under the species sum). -/
theorem matDCFreCoreN_hasDerivAt_lower_cLower {N : ℕ} (rho sigma : Fin N → ℝ)
    (hsig : ∀ k, 0 < sigma k) (hrho : ∀ n, 0 ≤ rho n) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N)
    (hlam : 0 ≤ (sigma k - sigma i) / 2)
    {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) ((sigma k - sigma i) / 2)) (hv0 : v ≠ 0) :
    HasDerivAt (matDCFreCoreN rho sigma hsig i k)
      (-(2 * Real.pi * rhoGeoPhys rho i k * v * cLowerPieceN rho sigma i k v)) v := by
  refine (matDCFreCoreN_hasDerivAt_lower rho sigma hsig i k hlam hv).congr_deriv ?_
  have hsum : (∑ l, qpConvLowerDeriv (physMixN rho sigma hsig) i l k v / (2 * Real.pi) ^ 2)
      = ∑ l, 2 * Real.pi * rhoGeoPhys rho i k * v * cLowerCorrPieceN rho sigma i l k v :=
    Finset.sum_congr rfl (fun l _ =>
      qpConvLowerDeriv_per_l rho sigma hsig hrho hvac i l k hv0)
  rw [hsum, matDCFreCoreN_lead_lower rho sigma hsig hvac i k hv0, cLowerPieceN, mul_add,
    Finset.mul_sum]
  ring

/-- **⭐⭐ General-`N` lower-piece value capstone** — `shellForcingN rgᵢₖ i k v = cLowerPieceN` on
`(0, λᵢₖ)`. -/
theorem shellForcing_lower_eqN {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hrho : ∀ n, 0 ≤ rho n) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N)
    (hlam : 0 ≤ (sigma k - sigma i) / 2) (hrg : rhoGeoPhys rho i k ≠ 0)
    {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) ((sigma k - sigma i) / 2)) :
    shellForcingN rho sigma hsig (rhoGeoPhys rho i k) i k v = cLowerPieceN rho sigma i k v :=
  shellForcing_eq_of_baxterODEN rho sigma hsig i k hrg hv.1
    (matDCFreCoreN_hasDerivAt_lower_cLower rho sigma hsig hrho hvac i k hlam hv hv.1.ne')

/-- **The general-`N` two-piece Lebowitz mixture DCF** — `cLowerPieceN` on `(0, λᵢₖ)`,
`cUpperPieceN` on `[λᵢₖ, Rᵢₖ)` (σᵢ < σₖ). -/
noncomputable def cMixDCFN {N : ℕ} (rho sigma : Fin N → ℝ) (i k : Fin N) (v : ℝ) : ℝ :=
  if v < (sigma k - sigma i) / 2 then cLowerPieceN rho sigma i k v
    else cUpperPieceN rho sigma i k v

/-- **⭐⭐⭐ General-`N` unequal-σ mixture DCF value — FULLY GLUED.**  For the ordered pair
`σᵢ < σₖ`, on all of `(0, Rᵢₖ)` off the knot, the OZ★ shell-inverse forcing IS the explicit
`N`-species-summed two-piece Lebowitz DCF: `shellForcingN rgᵢₖ i k v = cMixDCFN v`.  Combines the
lower and upper capstones (`shellForcing_lower_eqN` / `shellForcing_upper_eqN`). -/
theorem shellForcing_eq_cMixDCFN {N : ℕ} (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hrho : ∀ n, 0 ≤ rho n) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) (hlt : sigma i < sigma k)
    (hrg : rhoGeoPhys rho i k ≠ 0) {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) ((sigma i + sigma k) / 2))
    (hne : v ≠ (sigma k - sigma i) / 2) :
    shellForcingN rho sigma hsig (rhoGeoPhys rho i k) i k v = cMixDCFN rho sigma i k v := by
  rcases lt_or_gt_of_ne hne with hlow | hup
  · rw [cMixDCFN, if_pos hlow]
    exact shellForcing_lower_eqN rho sigma hsig hrho hvac i k (by linarith [hlt]) hrg ⟨hv.1, hlow⟩
  · rw [cMixDCFN, if_neg (not_lt.mpr hup.le)]
    exact shellForcing_upper_eqN rho sigma hsig hrho hvac i k hlt hrg ⟨hup, hv.2⟩


/-! ### Knot continuity at general `N` — the `∑ₗ` closes via `xi2` alone

Per-species continuity is FALSE, but the per-species difference
`cCorrPieceN(l)(λ) − cLowerCorrPieceN(l)(λ) = cKnotSlopeN·ρₗ·σₗ²` is **purely `σₗ²`** (the `σₗ⁰,σₗ¹`
parts cancel), so `∑ₗ` of it is `cKnotSlopeN·∑ₗρₗσₗ² = cKnotSlopeN·xi2` — only `xi2 = ξ₂` is
needed (no `ξ₀/ξ₁/ξ₃/ξ₄`).  The leading difference is `−cKnotSlopeN·xi2`, so they cancel. -/

/-- The knot-continuity slope `π·σᵢσₖ/(vac²·(σᵢ−σₖ))` — the common factor of both the per-species
`σₗ²` continuity defect and the (negated) leading defect. -/
noncomputable def cKnotSlopeN {N : ℕ} (rho sigma : Fin N → ℝ) (i k : Fin N) : ℝ :=
  Real.pi * sigma i * sigma k / (vacMix rho sigma ^ 2 * (sigma i - sigma k))

set_option maxHeartbeats 2000000 in
/-- **Per-species knot defect is purely `σₗ²`** — `cCorrPieceN(l)(λ) − cLowerCorrPieceN(l)(λ) =
cKnotSlopeN·(ρₗ·σₗ²)` at the knot `λ = (σₖ−σᵢ)/2`.  The `σₗ⁰,σₗ¹` parts of the per-species C¹ break
cancel, leaving only `σₗ²` (⇒ the species sum needs only `xi2`).  A √-free `field_simp; ring`. -/
theorem cCorrPieceN_sub_knot {N : ℕ} (rho sigma : Fin N → ℝ) (hvac : vacMix rho sigma ≠ 0)
    (i l k : Fin N) (hlt : sigma i < sigma k) :
    cCorrPieceN rho sigma i l k ((sigma k - sigma i) / 2)
        - cLowerCorrPieceN rho sigma i l k ((sigma k - sigma i) / 2)
      = cKnotSlopeN rho sigma i k * (rho l * sigma l ^ 2) := by
  have hsub : sigma i - sigma k ≠ 0 := sub_ne_zero_of_ne (ne_of_lt hlt)
  have hsub' : sigma k - sigma i ≠ 0 := sub_ne_zero_of_ne (ne_of_gt hlt)
  simp only [cCorrPieceN, cLowerCorrPieceN, cCorrANumN, cCorrBNumN, cCorrC2NumN, cCorrENumN,
    cLowerCorrANumN, cLowerCorrBNumN, cKnotSlopeN]
  field_simp
  ring

set_option maxHeartbeats 2000000 in
/-- **Leading knot defect** — `cLeadPieceN(λ) − cLowerLeadPieceN(λ) = −(cKnotSlopeN·xi2)`, exactly
the negative of the aggregated per-species defect. -/
theorem cLeadPieceN_sub_knot {N : ℕ} (rho sigma : Fin N → ℝ) (hvac : vacMix rho sigma ≠ 0)
    (i k : Fin N) (hlt : sigma i < sigma k) :
    cLeadPieceN rho sigma i k ((sigma k - sigma i) / 2)
        - cLowerLeadPieceN rho sigma i k ((sigma k - sigma i) / 2)
      = -(cKnotSlopeN rho sigma i k * xi2 rho sigma) := by
  have hsub : sigma i - sigma k ≠ 0 := sub_ne_zero_of_ne (ne_of_lt hlt)
  have hsub' : sigma k - sigma i ≠ 0 := sub_ne_zero_of_ne (ne_of_gt hlt)
  simp only [cLeadPieceN, cLowerLeadPieceN, cLeadANumN, cLeadBNumN, cLowerLeadANumN,
    cLowerLeadBNumN, cKnotSlopeN, xi2]
  field_simp
  ring

/-- **⭐⭐⭐ General-`N` mixture DCF is C⁰ across the knot** — `cLowerPieceN(λ) = cUpperPieceN(λ)`
for `σᵢ < σₖ`.  The species sum of the per-species `σₗ²` defects is `cKnotSlopeN·xi2`
(`∑ₗρₗσₗ² = xi2`, `Finset.mul_sum`), which the leading defect `−cKnotSlopeN·xi2` cancels.  So
`cMixDCFN` is continuous — the general-`N` analog of `cLowerPiece_eq_cUpperPiece_knot`, but here the
per-species continuity is FALSE and the closure is a genuine `∑ₗ`-moment identity in `xi2`. -/
theorem cLowerPiece_eq_cUpperPiece_knotN {N : ℕ} (rho sigma : Fin N → ℝ)
    (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) (hlt : sigma i < sigma k) :
    cLowerPieceN rho sigma i k ((sigma k - sigma i) / 2)
      = cUpperPieceN rho sigma i k ((sigma k - sigma i) / 2) := by
  rw [cUpperPieceN, cLowerPieceN]
  have hsum : (∑ l, cCorrPieceN rho sigma i l k ((sigma k - sigma i) / 2))
      - (∑ l, cLowerCorrPieceN rho sigma i l k ((sigma k - sigma i) / 2))
      = cKnotSlopeN rho sigma i k * xi2 rho sigma := by
    rw [← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun l _ => cCorrPieceN_sub_knot rho sigma hvac i l k hlt),
      ← Finset.mul_sum, xi2]
  have hlead := cLeadPieceN_sub_knot rho sigma hvac i k hlt
  linarith [hsum, hlead]

end FMSA.MixtureBaxter
