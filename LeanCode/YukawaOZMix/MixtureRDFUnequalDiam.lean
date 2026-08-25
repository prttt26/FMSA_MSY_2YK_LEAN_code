/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.YukawaOZMix.MixtureBaxterODEUnequalDiamN
import LeanCode.HSMixture.MixtureCoercivityReduction
import LeanCode.HSMixture.MixtureRDFUniqueness
import LeanCode.HSMixture.MatrixGramWienerHopf
import LeanCode.HSMixture.Q0HermitianAxis
import LeanCode.HSMixture.Q0OriginFactor

/-!
# General-`N` unequal-diameter mixture RDF — the value-route coercivity (MML.8)

The equal-diameter mixture RDF is closed by `matOzStar_equalDiam_unique`
(`MixtureRDFEqualDiam.lean`) via the rank-1 scalar coercivity.  This file ports that value route to
GENERAL `N` UNEQUAL diameters, where the coercivity `MatSymbolCoercive Φ ρ` rests on the full matrix
Baxter Wiener–Hopf factorization rather than a scalar reduction.

The path (4 parts), assembled here:

* **(A)** the shell-kernel↔DCF-core identity at general `N`:
  `shellKernel(Φᵢₖ)(v) = matDCFreCoreN(i,k)(v)/ρ` on `(0,σ)`, with `Φ` the derivative-defined
  forcing `shellForcingRhoN`.  Rests on the MRS.8 ODE `matDCFreCoreN'(v) = −2π·rg·v·cMixDCFN`
  (already general `N`) plus `matDCFreCoreN` C¹ regularity, boundary vanishing, and a knot-split FTC.
* **(B)** the even-part fold `Re(Cmix0ᵢₖ) = 2∫₀^σ matDCFreCoreN·cos` (quadratic-form level), from
  `matDCFfullN_laplace` (`𝓛(matDCFfullN)=Cmix0`) + the reflect-swap `matDCFfullN(i,k)(−v) =
  matDCFfullN(k,i)(v)` + `matDCFfullN` real.
* **(C)** the coercivity assembly via `matSymbolCoercive_of_gramFactors` (`Bfun = Q̂₀(ik)ᵀ`,
  Hermitian reality `Q0_mat_c_phys_neg_axis`, `det Q̂₀ ≠ 0` at origin + off-origin, tail decay).
* **(D)** the instantiation of `matOzStar_unique` — the general-`N` unequal-diameter RDF uniqueness.

This file builds (A) first (support + regularity + boundary + the FTC), the self-contained analytic
core, then (B)–(D).
-/

open MeasureTheory Set
namespace FMSA.MixtureBaxter

open FMSA.MatrixQ0 FMSA.MixtureHSDCF FMSA.HardSphere

variable {N : ℕ}

/-! ## Part A — support and regularity of `matDCFreCoreN` (general `N`) -/

/-- **Support of the full-line correlation (general `N`).**  `matCorrFull(qWeightedN)ᵢₖ` vanishes
for `|v| > Rᵢₖ = (σᵢ+σₖ)/2`: the two Baxter factors' supports (`[λᵢₘ,Rᵢₘ]`, `[λₖₘ,Rₖₘ]` shifted by
`v`) cannot overlap.  General-`N` port of `matCorrFull_qWeighted_eq_zero_of_R_lt_abs`. -/
theorem matCorrFullN_eq_zero_of_R_lt_abs (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) {v : ℝ} (hv : (sigma i + sigma k) / 2 < |v|) :
    matCorrFull (qWeightedN rho sigma hsig) i k v = 0 := by
  simp only [matCorrFull]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  have hz : (fun t => qWeightedN rho sigma hsig i m t * qWeightedN rho sigma hsig k m (t - v))
      = fun _ => (0 : ℝ) := by
    funext t
    by_contra hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hne
    have ht1 : t ∈ Set.Icc ((sigma m - sigma i) / 2) ((sigma i + sigma m) / 2) := by
      by_contra hc
      exact h1 (qWeightedN_eq_zero_of_notMem rho sigma hsig i m hc)
    have ht2 : t - v ∈ Set.Icc ((sigma m - sigma k) / 2) ((sigma k + sigma m) / 2) := by
      by_contra hc
      exact h2 (qWeightedN_eq_zero_of_notMem rho sigma hsig k m hc)
    rw [Set.mem_Icc] at ht1 ht2
    have hvle : |v| ≤ (sigma i + sigma k) / 2 := by
      rw [abs_le]; constructor <;> linarith [ht1.1, ht1.2, ht2.1, ht2.2]
    linarith [hv, hvle]
  rw [hz, integral_zero]

/-- **`qWeightedN` is `C^∞` on the open support** `(λᵢₖ, Rᵢₖ)` — a quadratic there.  General-`N`
port of `qWeighted_contDiffOn`. -/
theorem qWeightedN_contDiffOn (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin N) :
    ContDiffOn ℝ (⊤ : ℕ∞) (qWeightedN rho sigma hsig i k)
      (Set.Ioo ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2)) := by
  refine (ContDiff.contDiffOn (f := fun r => rhoGeoPhys rho i k
      * ((physMixN rho sigma hsig).Q0 i k * (r - (physMixN rho sigma hsig).R i k)
         + (physMixN rho sigma hsig).Qpp k * (r - (physMixN rho sigma hsig).R i k) ^ 2 / 2))
      (by fun_prop)).congr ?_
  intro x hx
  show rhoGeoPhys rho i k * (physMixN rho sigma hsig).q0MixEntry i k x = _
  rw [FMSA.HSMix.q0MixEntry, Set.indicator_of_mem (show x ∈ Set.Icc
    ((physMixN rho sigma hsig).lam i k) ((physMixN rho sigma hsig).R i k)
    from Set.mem_Icc.mpr ⟨hx.1.le, hx.2.le⟩)]

/-- On the upper piece `(λᵢₖ, Rᵢₖ)` the reflected linear term `qWeightedNₖᵢ(−·)` vanishes (its
support lies below), so it is `C^∞` (constant `0`).  Port of `qWeightedRefl_contDiffOn_upper`. -/
theorem qWeightedReflN_contDiffOn_upper (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v => qWeightedN rho sigma hsig k i (-v))
      (Set.Ioo ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2)) := by
  refine (contDiff_const (c := (0 : ℝ))).contDiffOn.congr (fun x hx => ?_)
  refine qWeightedN_eq_zero_of_notMem rho sigma hsig k i (fun hmem => ?_)
  rw [Set.mem_Icc] at hmem
  linarith [hmem.1, hx.1]

/-- **`matCorrFull(qWeightedN)ᵢₖ` is `C^∞` on the upper piece** `(λᵢₖ, Rᵢₖ)` — from
`qpConv_contDiffOn_upper` via `matCorrFull_eq_qpConvN`.  Port of `matCorrFull_contDiffOn_upper`. -/
theorem matCorrFullN_contDiffOn_upper (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) (hlam : 0 ≤ (sigma k - sigma i) / 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun v => matCorrFull (qWeightedN rho sigma hsig) i k v)
      (Set.Ioo ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2)) := by
  have heq : (fun v => matCorrFull (qWeightedN rho sigma hsig) i k v)
      = fun v => ∑ l, qpConv (physMixN rho sigma hsig) i l k v / (2 * Real.pi) ^ 2 := by
    funext v; exact matCorrFull_eq_qpConvN rho sigma hsig i k v
  rw [heq]
  exact ContDiffOn.sum (fun l _ =>
    (qpConv_contDiffOn_upper (physMixN rho sigma hsig) i l k hlam).div_const _)

/-- **`matDCFreCoreN` is `C^∞` on the upper piece** `(λᵢₖ, Rᵢₖ)` — the forward quadratic
`qWeightedN`, the (vanishing) reflected term, minus the smooth correlation.  Port of
`matDCFreCore_contDiffOn_of_corr`/`_upper`. -/
theorem matDCFreCoreN_contDiffOn_upper (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) (hlam : 0 ≤ (sigma k - sigma i) / 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (matDCFreCoreN rho sigma hsig i k)
      (Set.Ioo ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2)) := by
  have hlin := qWeightedN_contDiffOn rho sigma hsig i k
  have hrefl := qWeightedReflN_contDiffOn_upper rho sigma hsig i k
  have hcorr := matCorrFullN_contDiffOn_upper rho sigma hsig i k hlam
  refine ((hlin.add hrefl).sub hcorr).congr (fun x _ => ?_)
  simp only [matDCFreCoreN]

/-- **The physical Baxter kernel at its left edge is `−π σᵢ σₖ / vac` (general `N`).**  At
`r = λᵢₖ = (σₖ−σᵢ)/2` the Lebowitz quadratic evaluates to `−π σᵢ σₖ / vac`, **symmetric in `i,k`**
(`λᵢₖ − Rᵢₖ = −σᵢ`; the `π ξ₂` cross terms cancel).  This symmetry makes the forward jump of
`qWeightedN i k` at `λᵢₖ` cancel the reflected jump of `qWeightedN k i(−·)`, so `matDCFreCoreN` has
matching one-sided limits across the knot.  Port of `q0MixEntry_physMix_leftEdge`. -/
theorem q0MixEntryN_physMix_leftEdge (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) :
    (physMixN rho sigma hsig).q0MixEntry i k ((sigma k - sigma i) / 2)
      = -(Real.pi * sigma i * sigma k) / vacMix rho sigma := by
  have hmem : (sigma k - sigma i) / 2 ∈ Set.Icc ((physMixN rho sigma hsig).lam i k)
      ((physMixN rho sigma hsig).R i k) := by
    simp only [physMixN, HSMix.lam, HSMix.R]
    rw [Set.mem_Icc]; constructor <;> [rfl; linarith [hsig i]]
  rw [FMSA.HSMix.q0MixEntry, Set.indicator_of_mem hmem]
  simp only [physMixN, HSMix.R, Q0phys, Qppphys, vacMix]
  field_simp
  ring

/-- **The continuous representative of `matDCFreCoreN`.**  `matDCFreCoreN` carries a removable
point-spike at the knot `v = λᵢₖ` (both `Icc`-indicators fire there), so its verbatim values are not
continuous.  This representative uses the reflected linear term on `(−∞, λᵢₖ]` and the forward term
on `(λᵢₖ, ∞)` — the two two-piece formulas of `matDCFreCoreN_lower_eq`/`_upper_eq` — which agree at
`λᵢₖ` (left-edge symmetry `q0MixEntryN_physMix_leftEdge`).  It equals `matDCFreCoreN` off `λᵢₖ` and is
the object on which the shell-kernel FTC runs. -/
noncomputable def matDCFreCoreCont (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) (v : ℝ) : ℝ :=
  (if v ≤ (sigma k - sigma i) / 2 then qWeightedN rho sigma hsig k i (-v)
    else qWeightedN rho sigma hsig i k v) - matCorrFull (qWeightedN rho sigma hsig) i k v

/-- The continuous representative agrees with `matDCFreCoreN` off the knot `λᵢₖ`. -/
theorem matDCFreCoreCont_eq_of_ne (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin N)
    {v : ℝ} (hne : v ≠ (sigma k - sigma i) / 2) :
    matDCFreCoreCont rho sigma hsig i k v = matDCFreCoreN rho sigma hsig i k v := by
  unfold matDCFreCoreCont
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [if_pos hlt.le]; exact (matDCFreCoreN_lower_eq rho sigma hsig i k hlt).symm
  · rw [if_neg (not_le.mpr hgt)]; exact (matDCFreCoreN_upper_eq rho sigma hsig i k hgt).symm

/-- **Lower closed formula** — on `v ≤ λᵢₖ`, `matDCFreCoreCont = qWeightedNₖᵢ(−v) − matCorrFull`. -/
theorem matDCFreCoreCont_lower_formula (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin N)
    {v : ℝ} (hv : v ≤ (sigma k - sigma i) / 2) :
    matDCFreCoreCont rho sigma hsig i k v
      = qWeightedN rho sigma hsig k i (-v) - matCorrFull (qWeightedN rho sigma hsig) i k v := by
  rw [matDCFreCoreCont, if_pos hv]

/-- **Upper closed formula** — on `λᵢₖ ≤ v`, `matDCFreCoreCont = qWeightedNᵢₖ(v) − matCorrFull`.  At
`v = λᵢₖ` the two formulas agree by the left-edge symmetry (`q0MixEntryN_physMix_leftEdge`:
`qWeightedNₖᵢ(−λ) = qWeightedNᵢₖ(λ) = rgᵢₖ·(−πσᵢσₖ/vac)`). -/
theorem matDCFreCoreCont_upper_formula (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin N)
    {v : ℝ} (hv : (sigma k - sigma i) / 2 ≤ v) :
    matDCFreCoreCont rho sigma hsig i k v
      = qWeightedN rho sigma hsig i k v - matCorrFull (qWeightedN rho sigma hsig) i k v := by
  rcases eq_or_lt_of_le hv with heq | hlt
  · rw [matDCFreCoreCont, if_pos heq.ge, ← heq]
    have hcomm : rhoGeoPhys rho k i = rhoGeoPhys rho i k := by simp only [rhoGeoPhys, mul_comm]
    have hrefl : qWeightedN rho sigma hsig k i (-((sigma k - sigma i) / 2))
        = rhoGeoPhys rho i k * (-(Real.pi * sigma i * sigma k) / vacMix rho sigma) := by
      rw [qWeightedN, show -((sigma k - sigma i) / 2) = (sigma i - sigma k) / 2 from by ring,
        q0MixEntryN_physMix_leftEdge rho sigma hsig k i, hcomm]
      ring
    have hfwd : qWeightedN rho sigma hsig i k ((sigma k - sigma i) / 2)
        = rhoGeoPhys rho i k * (-(Real.pi * sigma i * sigma k) / vacMix rho sigma) := by
      rw [qWeightedN, q0MixEntryN_physMix_leftEdge rho sigma hsig i k]
    rw [hrefl, hfwd]
  · rw [matDCFreCoreCont, if_neg (not_le.mpr hlt)]

/-- **`matCorrFull(qWeightedN)ᵢₖ` is continuous** (general `N`) — a species sum of the continuous
correlation integrals `q0_corr_real_continuous`.  Port of `matCorrFull_qWeighted_continuous`. -/
theorem matCorrFullN_continuous (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin N) :
    Continuous (fun v => matCorrFull (qWeightedN rho sigma hsig) i k v) := by
  simp only [matCorrFull]
  refine continuous_finset_sum _ (fun m _ => ?_)
  have heq : (fun v => ∫ t, qWeightedN rho sigma hsig i m t * qWeightedN rho sigma hsig k m (t - v))
      = fun v => (rhoGeoPhys rho i m * rhoGeoPhys rho k m)
          * ∫ t, (physMixN rho sigma hsig).q0MixEntry i m t
              * (physMixN rho sigma hsig).q0MixEntry k m (t - v) := by
    funext v
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    simp only [qWeightedN]; ring
  rw [heq]
  exact continuous_const.mul (q0_corr_real_continuous (physMixN rho sigma hsig) i k m)

/-! ## Part A — boundary vanishing at `Rᵢₖ = (σᵢ+σₖ)/2` -/

/-- The physical Baxter quadratic vanishes at the contact edge `Rᵢₖ` (`r − Rᵢₖ = 0`). -/
theorem q0MixEntryN_at_R (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin N) :
    (physMixN rho sigma hsig).q0MixEntry i k ((sigma i + sigma k) / 2) = 0 := by
  rw [FMSA.HSMix.q0MixEntry]
  by_cases hmem : (sigma i + sigma k) / 2 ∈ Set.Icc ((physMixN rho sigma hsig).lam i k)
      ((physMixN rho sigma hsig).R i k)
  · rw [Set.indicator_of_mem hmem]; simp only [physMixN, HSMix.R]; ring
  · rw [Set.indicator_of_notMem hmem]

/-- `qWeightedNᵢₖ` vanishes for `v ≥ Rᵢₖ` (outside the support, and `0` at the edge `Rᵢₖ`). -/
theorem qWeightedN_eq_zero_of_R_le (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin N)
    {v : ℝ} (hv : (sigma i + sigma k) / 2 ≤ v) :
    qWeightedN rho sigma hsig i k v = 0 := by
  rcases eq_or_lt_of_le hv with heq | hlt
  · rw [qWeightedN, ← heq, q0MixEntryN_at_R rho sigma hsig i k, mul_zero]
  · exact qWeightedN_eq_zero_of_notMem rho sigma hsig i k
      (fun hmem => by rw [Set.mem_Icc] at hmem; linarith [hmem.2])

/-- **Correlation vanishes for `v ≥ Rᵢₖ`** (non-strict — the single overlap point at `v = Rᵢₖ` is
`t = Rᵢₘ`, where the forward factor vanishes).  Extends `matCorrFullN_eq_zero_of_R_lt_abs`. -/
theorem matCorrFullN_eq_zero_of_R_le (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) {v : ℝ} (hv : (sigma i + sigma k) / 2 ≤ v) :
    matCorrFull (qWeightedN rho sigma hsig) i k v = 0 := by
  simp only [matCorrFull]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  have hz : (fun t => qWeightedN rho sigma hsig i m t * qWeightedN rho sigma hsig k m (t - v))
      = fun _ => (0 : ℝ) := by
    funext t
    by_contra hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hne
    have ht1 : t ∈ Set.Icc ((sigma m - sigma i) / 2) ((sigma i + sigma m) / 2) := by
      by_contra hc; exact h1 (qWeightedN_eq_zero_of_notMem rho sigma hsig i m hc)
    have ht2 : t - v ∈ Set.Icc ((sigma m - sigma k) / 2) ((sigma k + sigma m) / 2) := by
      by_contra hc; exact h2 (qWeightedN_eq_zero_of_notMem rho sigma hsig k m hc)
    rw [Set.mem_Icc] at ht1 ht2
    have htR : t = (sigma i + sigma m) / 2 := le_antisymm ht1.2 (by linarith [ht2.1])
    exact h1 (qWeightedN_eq_zero_of_R_le rho sigma hsig i m (le_of_eq htR.symm))
  rw [hz, integral_zero]

/-- **Boundary vanishing** — `matDCFreCoreCont` is `0` for `v ≥ Rᵢₖ` (forward term and correlation
both vanish; the reflected term is off).  Supplies the FTC boundary `matDCFreCoreCont(σ) = 0`. -/
theorem matDCFreCoreCont_eq_zero_of_R_le (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i k : Fin N) {v : ℝ} (hv : (sigma i + sigma k) / 2 ≤ v) :
    matDCFreCoreCont rho sigma hsig i k v = 0 := by
  have hlam : (sigma k - sigma i) / 2 ≤ v := by linarith [hsig i, hv]
  rw [matDCFreCoreCont_upper_formula rho sigma hsig i k hlam,
    qWeightedN_eq_zero_of_R_le rho sigma hsig i k hv,
    matCorrFullN_eq_zero_of_R_le rho sigma hsig i k hv, sub_zero]

/-! ## Part A — continuity of the representative -/

/-- **`matDCFreCoreCont` is continuous** (general `N`).  Built from two globally continuous
surrogates — `fwd = rgᵢₖ·(if v ≤ Rᵢₖ then quadᵢₖ(v) else 0)` (matching `qWeightedNᵢₖ` on `Ici λᵢₖ`)
and `refl` (matching the reflected term on `Iic λᵢₖ`) — each continuous by `Continuous.if_le`
(`quad` vanishes at `Rᵢₖ`), glued at `λᵢₖ` by the left-edge symmetry, minus the continuous
`matCorrFull`.  This is the continuous representative on which the shell FTC runs. -/
theorem matDCFreCoreCont_continuous (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin N) :
    Continuous (matDCFreCoreCont rho sigma hsig i k) := by
  set X := physMixN rho sigma hsig with hX
  set fwd : ℝ → ℝ := fun v => rhoGeoPhys rho i k
    * (if v ≤ X.R i k then X.Q0 i k * (v - X.R i k) + X.Qpp k * (v - X.R i k) ^ 2 / 2 else 0) with hfwd
  set refl : ℝ → ℝ := fun v => rhoGeoPhys rho k i
    * (if -(X.R k i) ≤ v then X.Q0 k i * (-v - X.R k i) + X.Qpp i * (-v - X.R k i) ^ 2 / 2
        else 0) with hrefl
  have hfwdc : Continuous fwd := by
    refine continuous_const.mul (Continuous.if_le (by fun_prop) continuous_const continuous_id
      continuous_const (fun v hv => ?_))
    rw [hv]; ring
  have hreflc : Continuous refl := by
    refine continuous_const.mul (Continuous.if_le (by fun_prop) continuous_const continuous_const
      continuous_id (fun v hv => ?_))
    rw [← hv]; ring
  have hfwd_eq : ∀ v, (sigma k - sigma i) / 2 ≤ v → fwd v = qWeightedN rho sigma hsig i k v := by
    intro v hlv
    have hlam : X.lam i k = (sigma k - sigma i) / 2 := by simp only [hX, physMixN, HSMix.lam]
    simp only [hfwd, qWeightedN, FMSA.HSMix.q0MixEntry, ← hX]
    by_cases hR : v ≤ X.R i k
    · rw [if_pos hR, Set.indicator_of_mem (Set.mem_Icc.mpr ⟨by rw [hlam]; exact hlv, hR⟩)]
    · rw [if_neg hR, Set.indicator_of_notMem (fun hm => hR (Set.mem_Icc.mp hm).2), mul_zero]
  have hrefl_eq : ∀ v, v ≤ (sigma k - sigma i) / 2 → refl v = qWeightedN rho sigma hsig k i (-v) := by
    intro v hlv
    have hlam : X.lam k i = (sigma i - sigma k) / 2 := by simp only [hX, physMixN, HSMix.lam]
    have hRki : X.R k i = (sigma i + sigma k) / 2 := by simp only [hX, physMixN, HSMix.R]; ring
    simp only [hrefl, qWeightedN, FMSA.HSMix.q0MixEntry, ← hX]
    by_cases hR : -(X.R k i) ≤ v
    · rw [if_pos hR, Set.indicator_of_mem (Set.mem_Icc.mpr
        ⟨by rw [hlam]; linarith [hlv], by rw [hRki] at hR ⊢; linarith [hR]⟩)]
    · rw [if_neg hR, Set.indicator_of_notMem (fun hm => hR (by
        have := (Set.mem_Icc.mp hm).2; rw [hRki] at this ⊢; linarith [this])), mul_zero]
  have hglue : Continuous (fun v => if v ≤ (sigma k - sigma i) / 2 then refl v else fwd v) := by
    refine Continuous.if_le hreflc hfwdc continuous_id continuous_const (fun v hv => ?_)
    rw [hrefl_eq v hv.le, hfwd_eq v hv.ge, hv]
    have hcomm : rhoGeoPhys rho k i = rhoGeoPhys rho i k := by simp only [rhoGeoPhys, mul_comm]
    rw [qWeightedN, qWeightedN, ← hX,
      show -((sigma k - sigma i) / 2) = (sigma i - sigma k) / 2 from by ring,
      q0MixEntryN_physMix_leftEdge rho sigma hsig k i,
      q0MixEntryN_physMix_leftEdge rho sigma hsig i k, hcomm]
    ring
  have heq : matDCFreCoreCont rho sigma hsig i k
      = (fun v => if v ≤ (sigma k - sigma i) / 2 then refl v else fwd v)
        - fun v => matCorrFull (qWeightedN rho sigma hsig) i k v := by
    funext v
    simp only [matDCFreCoreCont, Pi.sub_apply]
    by_cases hv : v ≤ (sigma k - sigma i) / 2
    · rw [if_pos hv, if_pos hv, hrefl_eq v hv]
    · rw [if_neg hv, if_neg hv, hfwd_eq v (not_le.mp hv).le]
  rw [heq]
  exact hglue.sub (matCorrFullN_continuous rho sigma hsig i k)

/-! ## Part A — the derivative-defined forcing and the piece derivatives -/

/-- **The physical OZ★ forcing (ρ-weighted DCF), truncated at contact `Rᵢₖ`.**  `Φᵢₖ(v) =
(rgᵢₖ/ρ)·cMixDCFN(v)` on `(0,Rᵢₖ)`, `0` beyond — the density-weighted two-piece Lebowitz DCF that
the OZ★ equation forces.  It satisfies the ODE `(matDCFreCoreCont/ρ)'(v) = −2π·v·Φᵢₖ(v)` by MRS.8. -/
noncomputable def PhiUneq (rho sigma : Fin N → ℝ) (rhoTot : ℝ) (i k : Fin N) (v : ℝ) : ℝ :=
  if v < (sigma i + sigma k) / 2 then rhoGeoPhys rho i k / rhoTot * cMixDCFN rho sigma i k v else 0

/-- **The core ODE for the continuous representative** — on `(0,Rᵢₖ)` off the knot,
`HasDerivAt matDCFreCoreCont (−2π·rgᵢₖ·s·cMixDCFN(s)) s`, transferred from `matDCFreCoreN`'s MRS.8
two-piece ODE via the off-knot equality (`matDCFreCoreCont =ᶠ matDCFreCoreN`). -/
theorem hasDerivAt_matDCFreCoreCont (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hrho : ∀ n, 0 ≤ rho n) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N)
    (hlam : 0 ≤ (sigma k - sigma i) / 2) {s : ℝ} (hs0 : 0 < s) (hsR : s < (sigma i + sigma k) / 2)
    (hsne : s ≠ (sigma k - sigma i) / 2) :
    HasDerivAt (matDCFreCoreCont rho sigma hsig i k)
      (-(2 * Real.pi * rhoGeoPhys rho i k * s * cMixDCFN rho sigma i k s)) s := by
  have heq : matDCFreCoreCont rho sigma hsig i k =ᶠ[nhds s] matDCFreCoreN rho sigma hsig i k := by
    filter_upwards [compl_singleton_mem_nhds hsne] with v hv
    exact matDCFreCoreCont_eq_of_ne rho sigma hsig i k (Set.mem_compl_singleton_iff.mp hv)
  rcases lt_or_gt_of_ne hsne with hlt | hgt
  · rw [cMixDCFN, if_pos hlt]
    exact (matDCFreCoreN_hasDerivAt_lower_cLower rho sigma hsig hrho hvac i k hlam
      ⟨hs0, hlt⟩ hs0.ne').congr_of_eventuallyEq heq
  · rw [cMixDCFN, if_neg (not_lt.mpr hgt.le)]
    exact (matDCFreCoreN_hasDerivAt_upper_cUpper rho sigma hsig hrho hvac i k hlam
      ⟨hgt, hsR⟩ hs0.ne').congr_of_eventuallyEq heq

/-! ## Part A — continuity of the DCF pieces (for `v > 0`) and the split-FTC integrand -/

/-- `cUpperPieceN` is continuous for `v > 0` (rational in `v`, the `1/v` term forces `v ≠ 0`). -/
theorem cUpperPieceN_continuousOn (rho sigma : Fin N → ℝ) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) :
    ContinuousOn (cUpperPieceN rho sigma i k) (Set.Ioi (0 : ℝ)) := by
  refine fun x hx => (ContinuousAt.continuousWithinAt ?_)
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hD : (768 * vacMix rho sigma ^ 4) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 4 hvac)
  unfold cUpperPieceN cLeadPieceN cCorrPieceN
  fun_prop (disch := assumption)

/-- `cLowerPieceN` is continuous for `v > 0`. -/
theorem cLowerPieceN_continuousOn (rho sigma : Fin N → ℝ) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) :
    ContinuousOn (cLowerPieceN rho sigma i k) (Set.Ioi (0 : ℝ)) := by
  refine fun x hx => (ContinuousAt.continuousWithinAt ?_)
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hD : (768 * vacMix rho sigma ^ 4) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 4 hvac)
  unfold cLowerPieceN cLowerLeadPieceN cLowerCorrPieceN
  fun_prop (disch := assumption)

/-- **Lower-piece FTC** — `∫_w^λ (matDCFreCoreCont/ρ)' = F(λ) − F(w)` with the derivative given by the
lower-piece ODE `−2π·rg·s·cLowerPieceN/ρ` (continuous for `s > 0`). -/
theorem ftc_lower (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (hrho : ∀ n, 0 ≤ rho n)
    (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) (hlt : sigma i < sigma k) (rhoTot : ℝ)
    {w : ℝ} (hw0 : 0 < w) (hwlam : w ≤ (sigma k - sigma i) / 2) :
    (∫ s in w..((sigma k - sigma i) / 2),
        -(2 * Real.pi * rhoGeoPhys rho i k * s * cLowerPieceN rho sigma i k s) / rhoTot)
      = matDCFreCoreCont rho sigma hsig i k ((sigma k - sigma i) / 2) / rhoTot
        - matDCFreCoreCont rho sigma hsig i k w / rhoTot := by
  have hlam0 : 0 ≤ (sigma k - sigma i) / 2 := by linarith [hlt]
  have hlamR : (sigma k - sigma i) / 2 ≤ (sigma i + sigma k) / 2 := by linarith [hsig i]
  have hsub : Set.uIcc w ((sigma k - sigma i) / 2) ⊆ Set.Ioi (0 : ℝ) := by
    rw [Set.uIcc_of_le hwlam]; exact fun x hx => lt_of_lt_of_le hw0 hx.1
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hwlam
    ((matDCFreCoreCont_continuous rho sigma hsig i k).div_const rhoTot).continuousOn
    (fun x hx => ?_) ?_
  · have hx0 : 0 < x := lt_trans hw0 hx.1
    have hxlt : x < (sigma k - sigma i) / 2 := hx.2
    have hcm : cMixDCFN rho sigma i k x = cLowerPieceN rho sigma i k x := by rw [cMixDCFN, if_pos hxlt]
    have hd := hasDerivAt_matDCFreCoreCont rho sigma hsig hrho hvac i k hlam0 hx0
      (lt_of_lt_of_le hxlt hlamR) (ne_of_lt hxlt)
    rw [← hcm]
    exact (hd.div_const rhoTot).hasDerivWithinAt
  · apply ContinuousOn.intervalIntegrable
    exact (((continuousOn_const.mul continuousOn_id).mul
      ((cLowerPieceN_continuousOn rho sigma hvac i k).mono hsub)).neg).div_const rhoTot

/-- **Upper-piece FTC** — `∫_a^R (matDCFreCoreCont/ρ)' = F(R) − F(a)` from any `a ∈ [λ, R]`,
derivative `−2π·rg·s·cUpperPieceN/ρ`. -/
theorem ftc_upper (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (hrho : ∀ n, 0 ≤ rho n)
    (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) (hlt : sigma i < sigma k) (rhoTot : ℝ)
    {a : ℝ} (ha0 : 0 < a) (halam : (sigma k - sigma i) / 2 ≤ a) (haR : a ≤ (sigma i + sigma k) / 2) :
    (∫ s in a..((sigma i + sigma k) / 2),
        -(2 * Real.pi * rhoGeoPhys rho i k * s * cUpperPieceN rho sigma i k s) / rhoTot)
      = matDCFreCoreCont rho sigma hsig i k ((sigma i + sigma k) / 2) / rhoTot
        - matDCFreCoreCont rho sigma hsig i k a / rhoTot := by
  have hlam0 : 0 ≤ (sigma k - sigma i) / 2 := by linarith [hlt]
  have hsub : Set.uIcc a ((sigma i + sigma k) / 2) ⊆ Set.Ioi (0 : ℝ) := by
    rw [Set.uIcc_of_le haR]; exact fun x hx => lt_of_lt_of_le ha0 hx.1
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le haR
    ((matDCFreCoreCont_continuous rho sigma hsig i k).div_const rhoTot).continuousOn
    (fun x hx => ?_) ?_
  · have hx0 : 0 < x := lt_trans ha0 hx.1
    have hxgt : (sigma k - sigma i) / 2 < x := lt_of_le_of_lt halam hx.1
    have hcm : cMixDCFN rho sigma i k x = cUpperPieceN rho sigma i k x := by
      rw [cMixDCFN, if_neg (not_lt.mpr hxgt.le)]
    have hd := hasDerivAt_matDCFreCoreCont rho sigma hsig hrho hvac i k hlam0 hx0 hx.2
      (ne_of_gt hxgt)
    rw [← hcm]
    exact (hd.div_const rhoTot).hasDerivWithinAt
  · apply ContinuousOn.intervalIntegrable
    exact (((continuousOn_const.mul continuousOn_id).mul
      ((cUpperPieceN_continuousOn rho sigma hvac i k).mono hsub)).neg).div_const rhoTot

/-- **Shell piece ⟷ FTC integral.**  On `[a,b]` where `Φ = (rg/ρ)·branch`, the shell integrand
`2π·s·Φ` integrates to the negative of the FTC integrand `−2π·rg·s·branch/ρ` — a pure
`integral_const_mul` + a.e.-congr rearrangement (the `{b}` endpoint is null). -/
theorem shell_piece_eq (rho sigma : Fin N → ℝ) (rhoTot : ℝ) (i k : Fin N) (branch : ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (hbr : ∀ s ∈ Set.Ioo a b, PhiUneq rho sigma rhoTot i k s
      = rhoGeoPhys rho i k / rhoTot * branch s) :
    2 * Real.pi * (∫ s in a..b, s * PhiUneq rho sigma rhoTot i k s)
      = -(∫ s in a..b, -(2 * Real.pi * rhoGeoPhys rho i k * s * branch s) / rhoTot) := by
  have hcong : (∫ s in a..b, s * PhiUneq rho sigma rhoTot i k s)
      = ∫ s in a..b, s * (rhoGeoPhys rho i k / rhoTot * branch s) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton b)] with x hxb hmem
    rw [Set.uIoc_of_le hab] at hmem
    rw [hbr x ⟨hmem.1, lt_of_le_of_ne hmem.2 (Set.mem_compl_singleton_iff.mp hxb)⟩]
  have hconst : (∫ s in a..b, -(2 * Real.pi * rhoGeoPhys rho i k * s * branch s) / rhoTot)
      = -(2 * Real.pi) * ∫ s in a..b, s * (rhoGeoPhys rho i k / rhoTot * branch s) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun s _ => by ring)
  rw [hcong, hconst]; ring

/-! ## Part A capstone — the shell-kernel↔DCF-core identity `hShellDCF` at general `N` -/

/-- **`hShellDCF` (general `N`, unequal σ).**  `shellKernel(Φᵢₖ)(w) = matDCFreCoreCont(w)/ρ` on
`(0,σ)`.  Split-FTC over `[w,λ]∪[λ,R]∪[R,σ]` (`ftc_lower`/`ftc_upper`, per-piece continuity, the
knots handled by splitting so only open-interior derivatives are used), the shell↔FTC rearrangement
`shell_piece_eq`, and boundary vanishing `matDCFreCoreCont(R)=0`.  The continuous representative
absorbs the removable knot spike. -/
theorem hShellDCF_uneq (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (hrho : ∀ n, 0 ≤ rho n)
    (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) (hlt : sigma i < sigma k) (rhoTot : ℝ)
    {sigma_s : ℝ} (hRs : (sigma i + sigma k) / 2 ≤ sigma_s) {w : ℝ} (hw0 : 0 < w)
    (hws : w < sigma_s) :
    shellKernel (PhiUneq rho sigma rhoTot i k) sigma_s w
      = matDCFreCoreCont rho sigma hsig i k w / rhoTot := by
  have hlampos : 0 < (sigma k - sigma i) / 2 := by linarith [hlt]
  have hlamR : (sigma k - sigma i) / 2 ≤ (sigma i + sigma k) / 2 := by linarith [hsig i]
  have hFR : matDCFreCoreCont rho sigma hsig i k ((sigma i + sigma k) / 2) / rhoTot = 0 := by
    rw [matDCFreCoreCont_eq_zero_of_R_le rho sigma hsig i k (le_refl _), zero_div]
  have hint : ∀ (branch : ℝ → ℝ) (a b : ℝ), 0 < a → a ≤ b →
      ContinuousOn branch (Set.Ioi (0 : ℝ)) →
      (∀ s ∈ Set.Ioo a b, PhiUneq rho sigma rhoTot i k s = rhoGeoPhys rho i k / rhoTot * branch s) →
      IntervalIntegrable (fun s => s * PhiUneq rho sigma rhoTot i k s) MeasureTheory.volume a b := by
    intro branch a b ha0 hab hbc hbr
    have hsub : Set.uIcc a b ⊆ Set.Ioi (0 : ℝ) := by
      rw [Set.uIcc_of_le hab]; exact fun x hx => lt_of_lt_of_le ha0 hx.1
    have hf : IntervalIntegrable (fun s => s * (rhoGeoPhys rho i k / rhoTot * branch s))
        MeasureTheory.volume a b :=
      (continuousOn_id.mul (continuousOn_const.mul (hbc.mono hsub))).intervalIntegrable
    refine hf.congr_uIoo (fun s hs => ?_)
    rw [Set.uIoo_of_le hab] at hs
    rw [hbr s hs]
  have hbrLow : ∀ s ∈ Set.Ioo w ((sigma k - sigma i) / 2),
      PhiUneq rho sigma rhoTot i k s = rhoGeoPhys rho i k / rhoTot * cLowerPieceN rho sigma i k s := by
    intro s hs
    rw [PhiUneq, if_pos (by linarith [hs.2, hlamR]), cMixDCFN, if_pos hs.2]
  have hbrUp : ∀ (a : ℝ), (sigma k - sigma i) / 2 ≤ a → ∀ s ∈ Set.Ioo a ((sigma i + sigma k) / 2),
      PhiUneq rho sigma rhoTot i k s = rhoGeoPhys rho i k / rhoTot * cUpperPieceN rho sigma i k s := by
    intro a hla s hs
    rw [PhiUneq, if_pos hs.2, cMixDCFN, if_neg (by linarith [hs.1, hla])]
  have hzero : (∫ s in ((sigma i + sigma k) / 2)..sigma_s, s * PhiUneq rho sigma rhoTot i k s) = 0 := by
    have hz : Set.EqOn (fun s => s * PhiUneq rho sigma rhoTot i k s) (fun _ => (0 : ℝ))
        (Set.uIcc ((sigma i + sigma k) / 2) sigma_s) := by
      intro s hs; rw [Set.uIcc_of_le hRs] at hs
      simp only [PhiUneq, if_neg (not_lt.mpr hs.1), mul_zero]
    rw [intervalIntegral.integral_congr hz]; exact intervalIntegral.integral_zero
  have hi3 : IntervalIntegrable (fun s => s * PhiUneq rho sigma rhoTot i k s)
      MeasureTheory.volume ((sigma i + sigma k) / 2) sigma_s := by
    refine hint (fun _ => 0) _ _ (by linarith [hsig i, hsig k]) hRs continuousOn_const (fun s hs => ?_)
    rw [PhiUneq, if_neg (not_lt.mpr hs.1.le), mul_zero]
  unfold shellKernel
  rw [abs_of_pos hw0]
  by_cases hwR : (sigma i + sigma k) / 2 ≤ w
  · rw [matDCFreCoreCont_eq_zero_of_R_le rho sigma hsig i k hwR, zero_div]
    have hz : Set.EqOn (fun s => s * PhiUneq rho sigma rhoTot i k s) (fun _ => (0 : ℝ))
        (Set.uIcc w sigma_s) := by
      intro s hs; rw [Set.uIcc_of_le hws.le] at hs
      simp only [PhiUneq, if_neg (not_lt.mpr (le_trans hwR hs.1)), mul_zero]
    rw [intervalIntegral.integral_congr hz, intervalIntegral.integral_zero, mul_zero]
  · push_neg at hwR
    by_cases hwlam : w < (sigma k - sigma i) / 2
    · have hi1 := hint (cLowerPieceN rho sigma i k) w ((sigma k - sigma i) / 2) hw0 hwlam.le
        (cLowerPieceN_continuousOn rho sigma hvac i k) hbrLow
      have hi2 := hint (cUpperPieceN rho sigma i k) ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2) hlampos hlamR
        (cUpperPieceN_continuousOn rho sigma hvac i k) (hbrUp _ (le_refl _))
      have hsplit : (∫ s in w..sigma_s, s * PhiUneq rho sigma rhoTot i k s)
          = (∫ s in w..((sigma k - sigma i) / 2), s * PhiUneq rho sigma rhoTot i k s)
            + ((∫ s in ((sigma k - sigma i) / 2)..((sigma i + sigma k) / 2),
                  s * PhiUneq rho sigma rhoTot i k s)
              + (∫ s in ((sigma i + sigma k) / 2)..sigma_s, s * PhiUneq rho sigma rhoTot i k s)) := by
        rw [intervalIntegral.integral_add_adjacent_intervals hi2 hi3,
          intervalIntegral.integral_add_adjacent_intervals hi1 (hi2.trans hi3)]
      rw [hsplit, mul_add, mul_add,
        shell_piece_eq rho sigma rhoTot i k (cLowerPieceN rho sigma i k) hwlam.le hbrLow,
        shell_piece_eq rho sigma rhoTot i k (cUpperPieceN rho sigma i k) hlamR (hbrUp _ (le_refl _)),
        hzero, mul_zero,
        ftc_lower rho sigma hsig hrho hvac i k hlt rhoTot hw0 hwlam.le,
        ftc_upper rho sigma hsig hrho hvac i k hlt rhoTot hlampos (le_refl _) hlamR, hFR]
      ring
    · push_neg at hwlam
      have hi2 := hint (cUpperPieceN rho sigma i k) w ((sigma i + sigma k) / 2) hw0 hwR.le
        (cUpperPieceN_continuousOn rho sigma hvac i k) (hbrUp _ hwlam)
      have hsplit : (∫ s in w..sigma_s, s * PhiUneq rho sigma rhoTot i k s)
          = (∫ s in w..((sigma i + sigma k) / 2), s * PhiUneq rho sigma rhoTot i k s)
            + (∫ s in ((sigma i + sigma k) / 2)..sigma_s, s * PhiUneq rho sigma rhoTot i k s) := by
        rw [intervalIntegral.integral_add_adjacent_intervals hi2 hi3]
      rw [hsplit, mul_add,
        shell_piece_eq rho sigma rhoTot i k (cUpperPieceN rho sigma i k) hwR.le (hbrUp _ hwlam),
        hzero, mul_zero,
        ftc_upper rho sigma hsig hrho hvac i k hlt rhoTot hw0 hwlam hwR.le, hFR]
      ring

end FMSA.MixtureBaxter

namespace FMSA.MixtureBaxter

open FMSA.MatrixQ0 FMSA.MixtureHSDCF FMSA.HardSphere MeasureTheory

variable {N : ℕ}

/-! ## Part B — the even-part fold: `∑ᵢⱼ Cmix0ᵢⱼvᵢvⱼ = ρ∑ᵢⱼ radial_fourier(Φᵢⱼ)vᵢvⱼ` -/

/-- **Reflect-swap of the DCF core (general `N`).**  `matDCFreCoreN(i,j)(−v) = matDCFreCoreN(j,i)(v)`
— the forward/reflected linear terms swap and the correlation swaps via `matCorrFull_neg_swap`. -/
theorem matDCFreCoreN_reflect_swap (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (i j : Fin N)
    (v : ℝ) :
    matDCFreCoreN rho sigma hsig i j (-v) = matDCFreCoreN rho sigma hsig j i v := by
  simp only [matDCFreCoreN, neg_neg]
  rw [matCorrFull_neg_swap (qWeightedN rho sigma hsig) i j v]
  ring

/-- **The full-line DCF is the real cast of the DCF core.**  `matDCFfullN(i,j)(v) =
↑(matDCFreCoreN(i,j)(v))` — the two linear Baxter terms are real casts, and `matCorrWN` is the real
cast of `matCorrFull(qWeightedN)` (cast through the species sum and the convolution integral). -/
theorem matDCFfullN_eq_ofReal (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (i j : Fin N)
    (v : ℝ) :
    matDCFfullN rho sigma hsig i j v = ((matDCFreCoreN rho sigma hsig i j v : ℝ) : ℂ) := by
  simp only [matDCFfullN, matDCFreCoreN, qWeightedN]
  rw [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_mul]
  congr 1
  rw [matCorrWN, matCorrFull, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  simp only [qWeightedN]; push_cast; ring

/-- **`cMixDCFN` is continuous for `v > 0`** — the two pieces are continuous (`v > 0`) and glue at the
knot `λᵢₖ` by `cLowerPiece_eq_cUpperPiece_knotN`. -/
theorem cMixDCFN_continuousOn (rho sigma : Fin N → ℝ) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N)
    (hlt : sigma i < sigma k) :
    ContinuousOn (cMixDCFN rho sigma i k) (Set.Ioi (0 : ℝ)) := by
  have hlow := cLowerPieceN_continuousOn rho sigma hvac i k
  have hup := cUpperPieceN_continuousOn rho sigma hvac i k
  have hknot := cLowerPiece_eq_cUpperPiece_knotN rho sigma hvac i k hlt
  intro x hx
  rcases lt_trichotomy x ((sigma k - sigma i) / 2) with hx' | hx' | hx'
  · refine (hlow x hx).congr_of_eventuallyEq ?_ (by rw [cMixDCFN, if_pos hx'])
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hx')] with y hy
    rw [cMixDCFN, if_pos (Set.mem_Iio.mp hy)]
  · subst hx'
    have hset : (Set.Ioi (0 : ℝ) ∩ Set.Iic ((sigma k - sigma i) / 2))
        ∪ (Set.Ioi 0 ∩ Set.Ici ((sigma k - sigma i) / 2)) = Set.Ioi 0 := by
      rw [← Set.inter_union_distrib_left, Set.Iic_union_Ici, Set.inter_univ]
    rw [← hset]
    refine ContinuousWithinAt.union ?_ ?_
    · refine ((hlow _ hx).mono Set.inter_subset_left).congr (fun y hy => ?_) ?_
      · have hyle := Set.mem_Iic.mp hy.2
        by_cases hyc : y < (sigma k - sigma i) / 2
        · rw [cMixDCFN, if_pos hyc]
        · rw [cMixDCFN, if_neg hyc, le_antisymm hyle (not_lt.mp hyc), hknot]
      · simp only [cMixDCFN, lt_self_iff_false, if_false]; exact hknot.symm
    · refine ((hup _ hx).mono Set.inter_subset_left).congr (fun y hy => ?_) ?_
      · rw [cMixDCFN, if_neg (not_lt.mpr (Set.mem_Ici.mp hy.2))]
      · simp only [cMixDCFN, lt_self_iff_false, if_false]
  · refine (hup x hx).congr_of_eventuallyEq ?_ (by rw [cMixDCFN, if_neg (not_lt.mpr hx'.le)])
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hx')] with y hy
    rw [cMixDCFN, if_neg (not_lt.mpr hy.le)]

/-! ### `r·cPiece` is a polynomial (the `r` cancels the `1/v`) ⟹ interval-integrability -/

/-- Polynomial form of `r·cLowerPieceN` (linear in `r`; the `r` cancels the `B/v`). -/
noncomputable def rcLowerPoly (rho sigma : Fin N → ℝ) (i k : Fin N) (r : ℝ) : ℝ :=
  (r * cLowerLeadANumN rho sigma i k + cLowerLeadBNumN rho sigma i k) / (768 * vacMix rho sigma ^ 4)
    + ∑ l, (r * cLowerCorrANumN rho sigma i l k + cLowerCorrBNumN rho sigma i l k)
        / (768 * vacMix rho sigma ^ 4)

/-- Polynomial form of `r·cUpperPieceN` (degree 4). -/
noncomputable def rcUpperPoly (rho sigma : Fin N → ℝ) (i k : Fin N) (r : ℝ) : ℝ :=
  (r * cLeadANumN rho sigma i k + cLeadBNumN rho sigma i k) / (768 * vacMix rho sigma ^ 4)
    + ∑ l, (r * cCorrANumN rho sigma i l k + cCorrBNumN rho sigma i l k
        + cCorrC2NumN rho sigma i l k * r ^ 2 + cCorrENumN rho sigma i l k * r ^ 4)
        / (768 * vacMix rho sigma ^ 4)

theorem r_mul_cLowerPieceN_eq (rho sigma : Fin N → ℝ) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N)
    {r : ℝ} (hr : r ≠ 0) :
    r * cLowerPieceN rho sigma i k r = rcLowerPoly rho sigma i k r := by
  have hD : (768 * vacMix rho sigma ^ 4) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 4 hvac)
  simp only [cLowerPieceN, rcLowerPoly, mul_add, Finset.mul_sum]
  congr 1
  · rw [cLowerLeadPieceN]; field_simp
  · refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [cLowerCorrPieceN]; field_simp

theorem r_mul_cUpperPieceN_eq (rho sigma : Fin N → ℝ) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N)
    {r : ℝ} (hr : r ≠ 0) :
    r * cUpperPieceN rho sigma i k r = rcUpperPoly rho sigma i k r := by
  have hD : (768 * vacMix rho sigma ^ 4) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 4 hvac)
  simp only [cUpperPieceN, rcUpperPoly, mul_add, Finset.mul_sum]
  congr 1
  · rw [cLeadPieceN]; field_simp
  · refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [cCorrPieceN]; field_simp

theorem rcLowerPoly_continuous (rho sigma : Fin N → ℝ) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) :
    Continuous (rcLowerPoly rho sigma i k) := by
  have hD : (768 * vacMix rho sigma ^ 4) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 4 hvac)
  unfold rcLowerPoly; fun_prop (disch := assumption)

theorem rcUpperPoly_continuous (rho sigma : Fin N → ℝ) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) :
    Continuous (rcUpperPoly rho sigma i k) := by
  have hD : (768 * vacMix rho sigma ^ 4) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 4 hvac)
  unfold rcUpperPoly; fun_prop (disch := assumption)

theorem rcLower_intervalIntegrable (rho sigma : Fin N → ℝ) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N)
    (a b : ℝ) :
    IntervalIntegrable (fun r => r * cLowerPieceN rho sigma i k r) MeasureTheory.volume a b := by
  refine ((rcLowerPoly_continuous rho sigma hvac i k).intervalIntegrable a b).congr_ae ?_
  refine MeasureTheory.ae_restrict_of_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with r hr
  exact (r_mul_cLowerPieceN_eq rho sigma hvac i k (Set.mem_compl_singleton_iff.mp hr)).symm

theorem rcUpper_intervalIntegrable (rho sigma : Fin N → ℝ) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N)
    (a b : ℝ) :
    IntervalIntegrable (fun r => r * cUpperPieceN rho sigma i k r) MeasureTheory.volume a b := by
  refine ((rcUpperPoly_continuous rho sigma hvac i k).intervalIntegrable a b).congr_ae ?_
  refine MeasureTheory.ae_restrict_of_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with r hr
  exact (r_mul_cUpperPieceN_eq rho sigma hvac i k (Set.mem_compl_singleton_iff.mp hr)).symm

end FMSA.MixtureBaxter

namespace FMSA.MixtureBaxter

open FMSA.MatrixQ0 FMSA.MixtureHSDCF FMSA.HardSphere MeasureTheory intervalIntegral

variable {N : ℕ}

/-- The scaled DCF-piece derivative `−2π·rg·r·cPiece` is interval-integrable (via `rc*_intervalIntegrable`). -/
theorem odeDeriv_lower_intInt (rho sigma : Fin N → ℝ) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N)
    (a b : ℝ) :
    IntervalIntegrable
      (fun r => -(2 * Real.pi * rhoGeoPhys rho i k * r * cLowerPieceN rho sigma i k r))
      MeasureTheory.volume a b := by
  have h := (rcLower_intervalIntegrable rho sigma hvac i k a b).const_mul
    (-(2 * Real.pi * rhoGeoPhys rho i k))
  have heq : (fun r => -(2 * Real.pi * rhoGeoPhys rho i k) * (r * cLowerPieceN rho sigma i k r))
      = (fun r => -(2 * Real.pi * rhoGeoPhys rho i k * r * cLowerPieceN rho sigma i k r)) := by
    funext r; ring
  rwa [heq] at h

theorem odeDeriv_upper_intInt (rho sigma : Fin N → ℝ) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N)
    (a b : ℝ) :
    IntervalIntegrable
      (fun r => -(2 * Real.pi * rhoGeoPhys rho i k * r * cUpperPieceN rho sigma i k r))
      MeasureTheory.volume a b := by
  have h := (rcUpper_intervalIntegrable rho sigma hvac i k a b).const_mul
    (-(2 * Real.pi * rhoGeoPhys rho i k))
  have heq : (fun r => -(2 * Real.pi * rhoGeoPhys rho i k) * (r * cUpperPieceN rho sigma i k r))
      = (fun r => -(2 * Real.pi * rhoGeoPhys rho i k * r * cUpperPieceN rho sigma i k r)) := by
    funext r; ring
  rwa [heq] at h

/-- `HasDerivAt (sin (w·)) (w cos (w r)) r`. -/
theorem hasDerivAt_sin_wmul (w r : ℝ) : HasDerivAt (fun x => Real.sin (w * x)) (w * Real.cos (w * r)) r := by
  have hlin : HasDerivAt (fun x => w * x) w r := by simpa using (hasDerivAt_id r).const_mul w
  simpa [mul_comm] using hlin.sin

end FMSA.MixtureBaxter


namespace FMSA.MixtureBaxter

open FMSA.MatrixQ0 FMSA.MixtureHSDCF FMSA.HardSphere MeasureTheory intervalIntegral

variable {N : ℕ}

/-- **B1 core IBP** (piecewise RHS).  `∫₀^R matDCFreCoreCont·(w·cos) = ∫₀^λ (2π·rg·r·cLower)·sin +
∫_λ^R (2π·rg·r·cUpper)·sin`.  Per-piece integration by parts; boundary terms telescope/vanish
(`matDCFreCoreCont(R)=0`, `sin 0 = 0`). -/
theorem matDCFreCoreCont_ibp (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (hrho : ∀ n, 0 ≤ rho n)
    (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) (hlam0 : 0 ≤ (sigma k - sigma i) / 2) (w : ℝ) :
    (∫ r in (0:ℝ)..((sigma i + sigma k) / 2),
        matDCFreCoreCont rho sigma hsig i k r * (w * Real.cos (w * r)))
      = (∫ r in (0:ℝ)..((sigma k - sigma i) / 2),
          2 * Real.pi * rhoGeoPhys rho i k * r * cLowerPieceN rho sigma i k r * Real.sin (w * r))
        + (∫ r in ((sigma k - sigma i) / 2)..((sigma i + sigma k) / 2),
          2 * Real.pi * rhoGeoPhys rho i k * r * cUpperPieceN rho sigma i k r * Real.sin (w * r)) := by
  have hlamR : (sigma k - sigma i) / 2 ≤ (sigma i + sigma k) / 2 := by linarith [hsig i]
  have hFcont := matDCFreCoreCont_continuous rho sigma hsig i k
  have hvcont : Continuous (fun r : ℝ => Real.sin (w * r)) := by fun_prop
  have hvpcont : Continuous (fun r : ℝ => w * Real.cos (w * r)) := by fun_prop
  have ibpL := integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (a := (0:ℝ)) (b := (sigma k - sigma i) / 2) (u := matDCFreCoreCont rho sigma hsig i k)
    (v := fun r => Real.sin (w * r))
    (u' := fun r => -(2 * Real.pi * rhoGeoPhys rho i k * r * cLowerPieceN rho sigma i k r))
    (v' := fun r => w * Real.cos (w * r))
    hFcont.continuousOn hvcont.continuousOn
    (fun r hr => by
      rw [min_eq_left hlam0, max_eq_right hlam0] at hr
      have hd := hasDerivAt_matDCFreCoreCont rho sigma hsig hrho hvac i k hlam0 hr.1
        (lt_of_lt_of_le hr.2 hlamR) (ne_of_lt hr.2)
      rw [cMixDCFN, if_pos hr.2] at hd
      exact hd.hasDerivWithinAt)
    (fun r _ => (hasDerivAt_sin_wmul w r).hasDerivWithinAt)
    (odeDeriv_lower_intInt rho sigma hvac i k 0 _) (hvpcont.intervalIntegrable _ _)
  have ibpU := integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (a := (sigma k - sigma i) / 2) (b := (sigma i + sigma k) / 2)
    (u := matDCFreCoreCont rho sigma hsig i k) (v := fun r => Real.sin (w * r))
    (u' := fun r => -(2 * Real.pi * rhoGeoPhys rho i k * r * cUpperPieceN rho sigma i k r))
    (v' := fun r => w * Real.cos (w * r))
    hFcont.continuousOn hvcont.continuousOn
    (fun r hr => by
      rw [min_eq_left hlamR, max_eq_right hlamR] at hr
      have hd := hasDerivAt_matDCFreCoreCont rho sigma hsig hrho hvac i k hlam0
        (lt_of_le_of_lt hlam0 hr.1) hr.2 (ne_of_gt hr.1)
      rw [cMixDCFN, if_neg (not_lt.mpr hr.1.le)] at hd
      exact hd.hasDerivWithinAt)
    (fun r _ => (hasDerivAt_sin_wmul w r).hasDerivWithinAt)
    (odeDeriv_upper_intInt rho sigma hvac i k _ _) (hvpcont.intervalIntegrable _ _)
  have hFR : matDCFreCoreCont rho sigma hsig i k ((sigma i + sigma k) / 2) = 0 :=
    matDCFreCoreCont_eq_zero_of_R_le rho sigma hsig i k (le_refl _)
  have hIL : (∫ r in (0:ℝ)..((sigma k - sigma i) / 2),
        -(2 * Real.pi * rhoGeoPhys rho i k * r * cLowerPieceN rho sigma i k r) * Real.sin (w * r))
      = -(∫ r in (0:ℝ)..((sigma k - sigma i) / 2),
        2 * Real.pi * rhoGeoPhys rho i k * r * cLowerPieceN rho sigma i k r * Real.sin (w * r)) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr (fun r _ => by ring)
  have hIU : (∫ r in ((sigma k - sigma i) / 2)..((sigma i + sigma k) / 2),
        -(2 * Real.pi * rhoGeoPhys rho i k * r * cUpperPieceN rho sigma i k r) * Real.sin (w * r))
      = -(∫ r in ((sigma k - sigma i) / 2)..((sigma i + sigma k) / 2),
        2 * Real.pi * rhoGeoPhys rho i k * r * cUpperPieceN rho sigma i k r * Real.sin (w * r)) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr (fun r _ => by ring)
  have hcont : Continuous
      (fun r : ℝ => matDCFreCoreCont rho sigma hsig i k r * (w * Real.cos (w * r))) :=
    hFcont.mul hvpcont
  rw [← integral_add_adjacent_intervals
        (hcont.intervalIntegrable 0 ((sigma k - sigma i) / 2))
        (hcont.intervalIntegrable ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2)),
      ibpL, ibpU, hIL, hIU, hFR]
  simp only [mul_zero, Real.sin_zero]
  ring

end FMSA.MixtureBaxter


namespace FMSA.MixtureBaxter

open FMSA.MatrixQ0 FMSA.MixtureHSDCF FMSA.HardSphere MeasureTheory intervalIntegral

variable {N : ℕ}

/-- **B1 — the radial transform of the physical forcing.**  `radial_fourier(Φᵢₖ)(w) =
(2/ρ)·∫₀^R matDCFreCoreCont·cos`.  From `radial_fourier_eq_intervalIntegral_of_support`, the IBP
core, and `r·Φ = (rg/ρ)·r·cMixDCFN` (piecewise). -/
theorem radial_fourier_PhiUneq (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hrho : ∀ n, 0 ≤ rho n) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N)
    (hlam0 : 0 ≤ (sigma k - sigma i) / 2)
    {rhoTot : ℝ} (hrhoTot : rhoTot ≠ 0) {w : ℝ} (hw : w ≠ 0) :
    radial_fourier (PhiUneq rho sigma rhoTot i k) w
      = (2 / rhoTot) * ∫ r in (0:ℝ)..((sigma i + sigma k) / 2),
          matDCFreCoreCont rho sigma hsig i k r * Real.cos (w * r) := by
  have hlamR : (sigma k - sigma i) / 2 ≤ (sigma i + sigma k) / 2 := by linarith [hsig i]
  have hRpos : (0:ℝ) < (sigma i + sigma k) / 2 := by linarith [hsig i, hsig k]
  have hvcont : Continuous (fun r : ℝ => Real.sin (w * r)) := by fun_prop
  have houter : ∀ s, (sigma i + sigma k) / 2 ≤ s → PhiUneq rho sigma rhoTot i k s = 0 :=
    fun s hs => by rw [PhiUneq, if_neg (not_lt.mpr hs)]
  have hPhiL : IntervalIntegrable (fun r => r * PhiUneq rho sigma rhoTot i k r * Real.sin (w * r))
      MeasureTheory.volume 0 ((sigma k - sigma i) / 2) := by
    refine ((((rcLowerPoly_continuous rho sigma hvac i k).const_mul
      (rhoGeoPhys rho i k / rhoTot)).mul hvcont).intervalIntegrable 0 _).congr_uIoo (fun r hr => ?_)
    rw [uIoo_of_le hlam0] at hr
    simp only [Pi.mul_apply]
    rw [PhiUneq, if_pos (lt_of_lt_of_le hr.2 hlamR), cMixDCFN, if_pos hr.2,
      ← r_mul_cLowerPieceN_eq rho sigma hvac i k (ne_of_gt hr.1)]; ring
  have hPhiR : IntervalIntegrable (fun r => r * PhiUneq rho sigma rhoTot i k r * Real.sin (w * r))
      MeasureTheory.volume ((sigma k - sigma i) / 2) ((sigma i + sigma k) / 2) := by
    refine ((((rcUpperPoly_continuous rho sigma hvac i k).const_mul
      (rhoGeoPhys rho i k / rhoTot)).mul hvcont).intervalIntegrable _ _).congr_uIoo (fun r hr => ?_)
    rw [uIoo_of_le hlamR] at hr
    simp only [Pi.mul_apply]
    rw [PhiUneq, if_pos hr.2, cMixDCFN, if_neg (not_lt.mpr hr.1.le),
      ← r_mul_cUpperPieceN_eq rho sigma hvac i k (ne_of_gt (lt_of_le_of_lt hlam0 hr.1))]; ring
  have hpieceL : 2 * Real.pi * rhoTot * (∫ r in (0:ℝ)..((sigma k - sigma i) / 2),
        r * PhiUneq rho sigma rhoTot i k r * Real.sin (w * r))
      = ∫ r in (0:ℝ)..((sigma k - sigma i) / 2),
          2 * Real.pi * rhoGeoPhys rho i k * r * cLowerPieceN rho sigma i k r * Real.sin (w * r) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton ((sigma k - sigma i) / 2))] with r hr hmem
    rw [uIoc_of_le hlam0] at hmem
    have hrlam : r < (sigma k - sigma i) / 2 := lt_of_le_of_ne hmem.2 (Set.mem_compl_singleton_iff.mp hr)
    rw [PhiUneq, if_pos (lt_of_lt_of_le hrlam hlamR), cMixDCFN, if_pos hrlam]
    field_simp
  have hpieceU : 2 * Real.pi * rhoTot * (∫ r in ((sigma k - sigma i) / 2)..((sigma i + sigma k) / 2),
        r * PhiUneq rho sigma rhoTot i k r * Real.sin (w * r))
      = ∫ r in ((sigma k - sigma i) / 2)..((sigma i + sigma k) / 2),
          2 * Real.pi * rhoGeoPhys rho i k * r * cUpperPieceN rho sigma i k r * Real.sin (w * r) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton ((sigma i + sigma k) / 2))] with r hr hmem
    rw [uIoc_of_le hlamR] at hmem
    rw [PhiUneq, if_pos (lt_of_le_of_ne hmem.2 (Set.mem_compl_singleton_iff.mp hr)),
      cMixDCFN, if_neg (not_lt.mpr hmem.1.le)]
    field_simp
  have hkey : 2 * Real.pi * rhoTot * (∫ r in (0:ℝ)..((sigma i + sigma k) / 2),
        r * PhiUneq rho sigma rhoTot i k r * Real.sin (w * r))
      = w * ∫ r in (0:ℝ)..((sigma i + sigma k) / 2),
          matDCFreCoreCont rho sigma hsig i k r * Real.cos (w * r) := by
    rw [← integral_add_adjacent_intervals hPhiL hPhiR, mul_add, hpieceL, hpieceU,
      ← matDCFreCoreCont_ibp rho sigma hsig hrho hvac i k hlam0 w,
      ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun r _ => by ring)
  rw [radial_fourier_eq_intervalIntegral_of_support hRpos houter w]
  field_simp
  linear_combination 2 * hkey

end FMSA.MixtureBaxter

namespace FMSA.MixtureBaxter

open FMSA.MatrixQ0 FMSA.MixtureHSDCF FMSA.HardSphere FMSA.MRS MeasureTheory

variable {N : ℕ}

/-- Full-line reflect-swap (general `N`): `matDCFfullN(i,j)(−v) = matDCFfullN(j,i)(v)`. -/
theorem matDCFfullN_reflect_swap (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (i j : Fin N)
    (v : ℝ) :
    matDCFfullN rho sigma hsig i j (-v) = matDCFfullN rho sigma hsig j i v := by
  rw [matDCFfullN_eq_ofReal, matDCFfullN_eq_ofReal, matDCFreCoreN_reflect_swap]

/-- `matDCFfullN·(bounded continuous)` is integrable on `Ioi 0`. -/
theorem matDCFfullN_mul_integrableOn_Ioi (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i j : Fin N) (g : ℝ → ℂ) (hg : Continuous g) (c : ℝ) (hgb : ∀ v, ‖g v‖ ≤ c) :
    IntegrableOn (fun v => matDCFfullN rho sigma hsig i j v * g v) (Set.Ioi 0) :=
  ((matDCFfullN_integrable rho sigma hsig i j).mul_bdd hg.aestronglyMeasurable
    (Filter.Eventually.of_forall hgb)).integrableOn

/-- **Transform fold (general `N`)** — `Cmix0(ik)ᵢⱼ = ∫₀^∞ matDCFfullᵢⱼ·e^{−ikv} + ∫₀^∞
matDCFfullⱼᵢ·e^{ikv}`.  Port of `Cmix0_physMix_fold`. -/
theorem Cmix0_physMix_foldN (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (k : ℝ) (hk : k ≠ 0)
    (i j : Fin N) :
    Cmix0 (QphysN rho sigma) (Complex.I * (k : ℂ)) i j
      = (∫ v in Set.Ioi (0 : ℝ),
          matDCFfullN rho sigma hsig i j v * Complex.exp (-(Complex.I * (k : ℂ) * v)))
        + ∫ v in Set.Ioi (0 : ℝ),
          matDCFfullN rho sigma hsig j i v * Complex.exp (Complex.I * (k : ℂ) * v) := by
  have hz : Complex.I * (k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk)
  have hbound : ∀ w : ℝ, ‖Complex.exp (-(Complex.I * (k : ℂ) * (w : ℂ)))‖ ≤ 1 := fun w => by
    rw [Complex.norm_exp]
    have hre : (-(Complex.I * (k : ℂ) * (w : ℂ))).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  have hint : Integrable (fun v => matDCFfullN rho sigma hsig i j v
      * Complex.exp (-(Complex.I * (k : ℂ) * v))) :=
    (matDCFfullN_integrable rho sigma hsig i j).mul_bdd
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  rw [← matDCFfullN_laplace rho sigma hsig (Complex.I * (k : ℂ)) hz i j,
    ← integral_add_compl measurableSet_Ioi hint, Set.compl_Ioi]
  congr 1
  rw [show (∫ v in Set.Iic (0 : ℝ), matDCFfullN rho sigma hsig i j v
        * Complex.exp (-(Complex.I * (k : ℂ) * v)))
      = ∫ v in Set.Ioi (0 : ℝ), matDCFfullN rho sigma hsig i j (-v)
          * Complex.exp (-(Complex.I * (k : ℂ) * ((-v : ℝ) : ℂ))) from by
    have h := integral_comp_neg_Iic (0 : ℝ) (fun y : ℝ => matDCFfullN rho sigma hsig i j (-y)
      * Complex.exp (-(Complex.I * (k : ℂ) * ((-y : ℝ) : ℂ))))
    simpa using h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
  rw [matDCFfullN_reflect_swap rho sigma hsig i j v]
  push_cast; ring_nf

/-- **⭐ Quadratic-form cosine reduction of `Cmix0` (general `N`).**  `∑ᵢⱼ Cmix0(ik)ᵢⱼuᵢuⱼ =
∫₀^∞ (∑ᵢⱼ matDCFfullᵢⱼuᵢuⱼ)·2cos(kv)`.  Port of `Cmix0_quadForm_cos`. -/
theorem Cmix0_quadForm_cosN (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (k : ℝ) (hk : k ≠ 0)
    (u : Fin N → ℝ) :
    (∑ i, ∑ j, Cmix0 (QphysN rho sigma) (Complex.I * (k : ℂ)) i j * (u i : ℂ) * (u j : ℂ))
      = ∫ v in Set.Ioi (0 : ℝ),
          (∑ i, ∑ j, matDCFfullN rho sigma hsig i j v * (u i : ℂ) * (u j : ℂ))
            * (2 * Complex.cos ((k : ℂ) * v)) := by
  have hbm : ∀ v : ℝ, ‖Complex.exp (-(Complex.I * (k : ℂ) * (v : ℂ)))‖ ≤ 1 := fun v => by
    rw [Complex.norm_exp]
    have : (-(Complex.I * (k : ℂ) * (v : ℂ))).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_zero]
  have hbp : ∀ v : ℝ, ‖Complex.exp (Complex.I * (k : ℂ) * (v : ℂ))‖ ≤ 1 := fun v => by
    rw [Complex.norm_exp]
    have : (Complex.I * (k : ℂ) * (v : ℂ)).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_zero]
  have hcem : Continuous (fun v : ℝ => Complex.exp (-(Complex.I * (k : ℂ) * (v : ℂ)))) := by fun_prop
  have hcep : Continuous (fun v : ℝ => Complex.exp (Complex.I * (k : ℂ) * (v : ℂ))) := by fun_prop
  have hcos : ∀ v : ℝ, (2 : ℂ) * Complex.cos ((k : ℂ) * v)
      = Complex.exp (-(Complex.I * (k : ℂ) * v)) + Complex.exp (Complex.I * (k : ℂ) * v) := by
    intro v; rw [Complex.cos]; ring_nf
  have hc2 : Continuous (fun v : ℝ => (2 : ℂ) * Complex.cos ((k : ℂ) * v)) := by fun_prop
  have hc2b : ∀ v : ℝ, ‖(2 : ℂ) * Complex.cos ((k : ℂ) * v)‖ ≤ 2 := fun v => by
    rw [hcos v]; refine (norm_add_le _ _).trans ?_
    have := add_le_add (hbm v) (hbp v); linarith
  have iM : ∀ i j : Fin N, IntegrableOn (fun v => matDCFfullN rho sigma hsig i j v
      * (2 * Complex.cos ((k : ℂ) * v)) * (u i : ℂ) * (u j : ℂ)) (Set.Ioi 0) := fun i j =>
    ((matDCFfullN_mul_integrableOn_Ioi rho sigma hsig i j _ hc2 2 hc2b).mul_const
      (u i : ℂ)).mul_const (u j : ℂ)
  calc (∑ i, ∑ j, Cmix0 (QphysN rho sigma) (Complex.I * (k : ℂ)) i j * (u i : ℂ) * (u j : ℂ))
      = ∑ i, ∑ j, ((∫ v in Set.Ioi (0 : ℝ),
              matDCFfullN rho sigma hsig i j v * Complex.exp (-(Complex.I * (k : ℂ) * v))) * u i * u j
            + (∫ v in Set.Ioi (0 : ℝ),
              matDCFfullN rho sigma hsig j i v * Complex.exp (Complex.I * (k : ℂ) * v)) * u i * u j) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [Cmix0_physMix_foldN rho sigma hsig k hk i j]; ring
    _ = ∑ i, ∑ j, ((∫ v in Set.Ioi (0 : ℝ),
              matDCFfullN rho sigma hsig i j v * Complex.exp (-(Complex.I * (k : ℂ) * v))) * u i * u j
            + (∫ v in Set.Ioi (0 : ℝ),
              matDCFfullN rho sigma hsig i j v * Complex.exp (Complex.I * (k : ℂ) * v)) * u i * u j) := by
        simp only [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))
    _ = ∑ i, ∑ j, (∫ v in Set.Ioi (0 : ℝ),
              matDCFfullN rho sigma hsig i j v * (2 * Complex.cos ((k : ℂ) * v))) * u i * u j := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [← add_mul, ← add_mul, ← MeasureTheory.integral_add
          (matDCFfullN_mul_integrableOn_Ioi rho sigma hsig i j _ hcem 1 hbm)
          (matDCFfullN_mul_integrableOn_Ioi rho sigma hsig i j _ hcep 1 hbp)]
        congr 2
        refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
        rw [hcos v]; ring
    _ = ∫ v in Set.Ioi (0 : ℝ),
          (∑ i, ∑ j, matDCFfullN rho sigma hsig i j v * (u i : ℂ) * (u j : ℂ))
            * (2 * Complex.cos ((k : ℂ) * v)) := by
        simp only [← MeasureTheory.integral_mul_const]
        rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
              (integral_finset_sum (Finset.univ) (fun j _ => iM i j)).symm),
          ← integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => iM i j))]
        refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring

end FMSA.MixtureBaxter

namespace FMSA.MixtureBaxter

open FMSA.MatrixQ0 FMSA.MixtureHSDCF FMSA.HardSphere FMSA.MRS MeasureTheory

variable {N : ℕ}

/-! ## Part B-finish — T-symmetry (`matDCF_ae_symmN`) and the `Ioi 0 ↔ [0,R]` bridge -/

/-- `matDCFreCoreN(i,j)` vanishes for `v ≥ Rᵢⱼ` — off the knot it agrees with the continuous
representative, which is `0` there (`matDCFreCoreCont_eq_zero_of_R_le`). -/
theorem matDCFreCoreN_eq_zero_of_R_le (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i j : Fin N) {v : ℝ} (hv : (sigma i + sigma j) / 2 ≤ v) :
    matDCFreCoreN rho sigma hsig i j v = 0 := by
  have hne : v ≠ (sigma j - sigma i) / 2 := by
    have hlt : (sigma j - sigma i) / 2 < (sigma i + sigma j) / 2 := by linarith [hsig i]
    linarith [hv, hlt]
  rw [← matDCFreCoreCont_eq_of_ne rho sigma hsig i j hne]
  exact matDCFreCoreCont_eq_zero_of_R_le rho sigma hsig i j hv

/-- `matDCFreCoreN(i,j)` is integrable (real part of the integrable full-line DCF `matDCFfullN`). -/
theorem matDCFreCoreN_integrable (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (i j : Fin N) :
    Integrable (fun v => matDCFreCoreN rho sigma hsig i j v) := by
  have h : (fun v => matDCFreCoreN rho sigma hsig i j v)
      = fun v => (matDCFfullN rho sigma hsig i j v).re := by
    funext v; rw [matDCFfullN_eq_ofReal, Complex.ofReal_re]
  rw [h]; exact (matDCFfullN_integrable rho sigma hsig i j).re

/-- `matDCFreCoreN(i,j)·cos(w·)` is integrable (integrable `×` bounded continuous). -/
theorem matDCFreCoreN_cos_integrable (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (i j : Fin N)
    (w : ℝ) :
    Integrable (fun v => matDCFreCoreN rho sigma hsig i j v * Real.cos (w * v)) :=
  (matDCFreCoreN_integrable rho sigma hsig i j).mul_bdd
    (by fun_prop : Continuous (fun v => Real.cos (w * v))).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun v => by simpa using Real.abs_cos_le_one (w * v)))

/-- **T-symmetry (a.e.).**  `matDCFreCoreN(i,j) =ᵐ matDCFreCoreN(j,i)` — the real-cast of the general-`N`
DCF a.e.-symmetry `matDCF_ae_symmN` (momentum symmetry transferred to real space via Fourier
a.e.-injectivity). -/
theorem matDCFreCoreN_ae_symm (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hrho : ∀ n, 0 ≤ rho n) (hvac : vacMix rho sigma ≠ 0) (i j : Fin N) :
    (fun v => matDCFreCoreN rho sigma hsig i j v)
      =ᵐ[volume] (fun v => matDCFreCoreN rho sigma hsig j i v) := by
  filter_upwards [matDCF_ae_symmN rho sigma hsig hrho hvac i j] with v hv
  have hc : ((matDCFreCoreN rho sigma hsig i j v : ℝ) : ℂ)
      = ((matDCFreCoreN rho sigma hsig j i v : ℝ) : ℂ) := by
    rw [← matDCFfullN_eq_ofReal, ← matDCFfullN_eq_ofReal]; exact hv
  exact_mod_cast hc

/-- **T-symmetry of the cosine transform.**  `∫₀^∞ matDCFreCoreN(i,j)·cos = ∫₀^∞ matDCFreCoreN(j,i)·cos`
— integrating the a.e. symmetry against `cos`. -/
theorem intIoi_matDCFreCoreN_cos_symm (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hrho : ∀ n, 0 ≤ rho n) (hvac : vacMix rho sigma ≠ 0) (i j : Fin N) (w : ℝ) :
    (∫ v in Set.Ioi (0:ℝ), matDCFreCoreN rho sigma hsig i j v * Real.cos (w * v))
      = ∫ v in Set.Ioi (0:ℝ), matDCFreCoreN rho sigma hsig j i v * Real.cos (w * v) := by
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards [matDCFreCoreN_ae_symm rho sigma hsig hrho hvac i j] with v hv _
  rw [hv]

/-- **The `Ioi 0 ↔ [0,Rᵢⱼ]` bridge.**  `∫₀^R matDCFreCoreCont·cos = ∫₀^∞ matDCFreCoreN·cos`: the two
representatives agree a.e. (knot is null) and both vanish beyond `Rᵢⱼ`. -/
theorem intervalIntegral_matDCFreCoreCont_eq_intIoi (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i j : Fin N) (w : ℝ) :
    (∫ r in (0:ℝ)..((sigma i + sigma j) / 2),
        matDCFreCoreCont rho sigma hsig i j r * Real.cos (w * r))
      = ∫ v in Set.Ioi (0:ℝ), matDCFreCoreN rho sigma hsig i j v * Real.cos (w * v) := by
  have hR0 : (0:ℝ) ≤ (sigma i + sigma j) / 2 := by linarith [hsig i, hsig j]
  have hint := matDCFreCoreN_cos_integrable rho sigma hsig i j w
  have hcongr : (∫ r in (0:ℝ)..((sigma i + sigma j) / 2),
        matDCFreCoreCont rho sigma hsig i j r * Real.cos (w * r))
      = ∫ r in (0:ℝ)..((sigma i + sigma j) / 2),
        matDCFreCoreN rho sigma hsig i j r * Real.cos (w * r) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton ((sigma j - sigma i) / 2))] with r hr _
    rw [matDCFreCoreCont_eq_of_ne rho sigma hsig i j (Set.mem_compl_singleton_iff.mp hr)]
  rw [hcongr, intervalIntegral.integral_of_le hR0]
  have hsplit : Set.Ioc (0:ℝ) ((sigma i + sigma j) / 2) ∪ Set.Ioi ((sigma i + sigma j) / 2)
      = Set.Ioi (0:ℝ) := Set.Ioc_union_Ioi_eq_Ioi hR0
  have hdisj : Disjoint (Set.Ioc (0:ℝ) ((sigma i + sigma j) / 2))
      (Set.Ioi ((sigma i + sigma j) / 2)) := by
    rw [Set.disjoint_left]; rintro x hx1 hx2; exact absurd (Set.mem_Ioi.mp hx2) (not_lt.mpr hx1.2)
  have htail : (∫ v in Set.Ioi ((sigma i + sigma j) / 2),
      matDCFreCoreN rho sigma hsig i j v * Real.cos (w * v)) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero (fun v hv => ?_)
    rw [matDCFreCoreN_eq_zero_of_R_le rho sigma hsig i j (le_of_lt (Set.mem_Ioi.mp hv)), zero_mul]
  rw [← hsplit, setIntegral_union hdisj measurableSet_Ioi hint.integrableOn hint.integrableOn,
    htail, add_zero]

/-! ## Part B-finish — the symmetric forcing `PhiSymN` and its radial symbol -/

/-- **The symmetric physical OZ★ forcing** — `Φᵢⱼ = PhiUneq` on the σ-ordered representative of the
pair `{i,j}`.  So `Φ` is symmetric (= the physical DCF `c_ij`, symmetric a.e. by `matDCF_ae_symmN`)
and its radial transform is `B1`-computable on the forward (`σ≤`) pair for EVERY entry. -/
noncomputable def PhiSymN (rho sigma : Fin N → ℝ) (rhoTot : ℝ) :
    Matrix (Fin N) (Fin N) (ℝ → ℝ) :=
  fun i j => if sigma i ≤ sigma j then PhiUneq rho sigma rhoTot i j else PhiUneq rho sigma rhoTot j i

/-- **The radial symbol of `PhiSymN` is `(2/ρ)·` the DCF-core cosine transform, EVERY entry.**  Forward
branch = `B1` (`radial_fourier_PhiUneq`, `0≤λ`); reverse branch = `B1` on the swapped forward pair plus
T-symmetry `intIoi_matDCFreCoreN_cos_symm`.  The step that eliminates the reverse-geometry ODE. -/
theorem radial_fourier_PhiSymN (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hrho : ∀ n, 0 ≤ rho n) (hvac : vacMix rho sigma ≠ 0) (i j : Fin N)
    {rhoTot : ℝ} (hrhoTot : rhoTot ≠ 0) {w : ℝ} (hw : w ≠ 0) :
    radial_fourier (PhiSymN rho sigma rhoTot i j) w
      = (2 / rhoTot) * ∫ v in Set.Ioi (0:ℝ),
          matDCFreCoreN rho sigma hsig i j v * Real.cos (w * v) := by
  simp only [PhiSymN]
  by_cases h : sigma i ≤ sigma j
  · rw [if_pos h,
      radial_fourier_PhiUneq rho sigma hsig hrho hvac i j (by linarith [h]) hrhoTot hw,
      intervalIntegral_matDCFreCoreCont_eq_intIoi rho sigma hsig i j w]
  · push_neg at h
    rw [if_neg (not_le.mpr h),
      radial_fourier_PhiUneq rho sigma hsig hrho hvac j i (by linarith [h.le]) hrhoTot hw,
      intervalIntegral_matDCFreCoreCont_eq_intIoi rho sigma hsig j i w,
      intIoi_matDCFreCoreN_cos_symm rho sigma hsig hrho hvac j i w]

end FMSA.MixtureBaxter

namespace FMSA.MixtureBaxter

open FMSA.MatrixQ0 FMSA.MixtureHSDCF FMSA.HardSphere FMSA.MRS FMSA.MixtureOzStar MeasureTheory

variable {N : ℕ}

/-! ## Part C — the Gram input `hfack` and the coercivity for the physical mixture -/

/-- **The Gram input `hfack` for the physical unequal-σ mixture.**  The OZ symbol quadratic form of
`PhiSymN` equals the Baxter Gram squared norm `∑ₗ|(Q̂₀(ik)ᵀv)ₗ|²`.  Built from `radial_fourier_PhiSymN`
(symbol `= 2T/ρ`, `T` = DCF-core cosine transform), `Cmix0_quadForm_cosN` (`∑Cmix0vv = 2∑T·vv`),
`matGram_normSq_eq_QQ` + Hermitian reality `Q0_mat_c_phys_neg_axis`, and `Cmix0_factorization`.  The
`ρ` cancels (`Φ = (rg/ρ)·cDCF`), so it holds for any `ρ ≠ 0`. -/
theorem matDCF_hfack (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (hrho : ∀ n, 0 ≤ rho n)
    (hvac : vacMix rho sigma ≠ 0) {rho_s : ℝ} (hrho_s : rho_s ≠ 0) {k : ℝ} (hk : k ≠ 0)
    (v : Fin N → ℝ) :
    (∑ i, v i ^ 2) - rho_s * ∑ i, ∑ j,
        matRadialSymbol (PhiSymN rho sigma rho_s) k i j * v i * v j
      = ∑ l, Complex.normSq
          ((QphysN rho sigma (Complex.I * (k : ℂ))).transpose.mulVec (fun i => (v i : ℂ)) l) := by
  set T : Fin N → Fin N → ℝ :=
    fun i j => ∫ w in Set.Ioi (0:ℝ), matDCFreCoreN rho sigma hsig i j w * Real.cos (k * w) with hT
  have hAij : ∀ i j, rho_s * matRadialSymbol (PhiSymN rho sigma rho_s) k i j = 2 * T i j := by
    intro i j
    simp only [hT]
    rw [show matRadialSymbol (PhiSymN rho sigma rho_s) k i j
        = radial_fourier (PhiSymN rho sigma rho_s i j) k from rfl,
      radial_fourier_PhiSymN rho sigma hsig hrho hvac i j hrho_s hk]
    field_simp
  have hSreal : rho_s * ∑ i, ∑ j, matRadialSymbol (PhiSymN rho sigma rho_s) k i j * v i * v j
      = 2 * ∑ i, ∑ j, T i j * v i * v j := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    linear_combination (v i * v j) * hAij i j
  have hherm : QphysN rho sigma (-(Complex.I * (k : ℂ)))
      = (QphysN rho sigma (Complex.I * (k : ℂ))).map (starRingEnd ℂ) := by
    have h1 : (-(Complex.I * (k : ℂ)) : ℂ) = Complex.I * (-(k : ℂ)) := by ring
    rw [h1]; exact FMSA.MixtureGenN.Q0_mat_c_phys_neg_axis_map k sigma rho
  have hB : (∑ i, ∑ j, Cmix0 (QphysN rho sigma) (Complex.I * (k : ℂ)) i j * (v i : ℂ) * (v j : ℂ))
      = ((2 * ∑ i, ∑ j, T i j * v i * v j : ℝ) : ℂ) := by
    rw [Cmix0_quadForm_cosN rho sigma hsig k hk v]
    have hcast : (∫ w in Set.Ioi (0:ℝ),
          (∑ i, ∑ j, matDCFfullN rho sigma hsig i j w * (v i : ℂ) * (v j : ℂ))
            * (2 * Complex.cos ((k : ℂ) * w)))
        = ((∫ w in Set.Ioi (0:ℝ),
          (∑ i, ∑ j, matDCFreCoreN rho sigma hsig i j w * v i * v j) * (2 * Real.cos (k * w))
            : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioi (fun w _ => ?_)
      simp only [matDCFfullN_eq_ofReal]
      push_cast [Complex.ofReal_cos]
      ring
    have hreal : (∫ w in Set.Ioi (0:ℝ),
          (∑ i, ∑ j, matDCFreCoreN rho sigma hsig i j w * v i * v j) * (2 * Real.cos (k * w)))
        = 2 * ∑ i, ∑ j, T i j * v i * v j := by
      have hstep : (∫ w in Set.Ioi (0:ℝ),
            (∑ i, ∑ j, matDCFreCoreN rho sigma hsig i j w * v i * v j) * (2 * Real.cos (k * w)))
          = ∫ w in Set.Ioi (0:ℝ),
            ∑ i, ∑ j, (matDCFreCoreN rho sigma hsig i j w * Real.cos (k * w)) * (2 * v i * v j) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun w _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      rw [hstep]
      have hout : (∫ w in Set.Ioi (0:ℝ),
            ∑ i, ∑ j, (matDCFreCoreN rho sigma hsig i j w * Real.cos (k * w)) * (2 * v i * v j))
          = ∑ i, ∫ w in Set.Ioi (0:ℝ),
            ∑ j, (matDCFreCoreN rho sigma hsig i j w * Real.cos (k * w)) * (2 * v i * v j) :=
        integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
          ((matDCFreCoreN_cos_integrable rho sigma hsig i j k).mul_const
            (2 * v i * v j)).integrableOn))
      rw [hout]
      simp only [hT]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hin : (∫ w in Set.Ioi (0:ℝ),
            ∑ j, (matDCFreCoreN rho sigma hsig i j w * Real.cos (k * w)) * (2 * v i * v j))
          = ∑ j, ∫ w in Set.Ioi (0:ℝ),
            (matDCFreCoreN rho sigma hsig i j w * Real.cos (k * w)) * (2 * v i * v j) :=
        integral_finset_sum _ (fun j _ =>
          ((matDCFreCoreN_cos_integrable rho sigma hsig i j k).mul_const
            (2 * v i * v j)).integrableOn)
      rw [hin, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [integral_mul_const]
      ring
    rw [hcast, hreal]
  have hdiag : (∑ i, ∑ j, ((1 : Matrix (Fin N) (Fin N) ℂ) i j) * ((v i : ℂ) * (v j : ℂ)))
      = ∑ i, (v i : ℂ) ^ 2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i]
    · rw [Matrix.one_apply_eq]; ring
    · intro j _ hji; rw [Matrix.one_apply_ne (Ne.symm hji)]; ring
    · intro h; exact absurd (Finset.mem_univ i) h
  have hsub : (∑ i, ∑ j, (1 - Cmix0 (QphysN rho sigma) (Complex.I * (k : ℂ))) i j
        * ((v i : ℂ) * (v j : ℂ)))
      = (∑ i, (v i : ℂ) ^ 2)
        - ∑ i, ∑ j, Cmix0 (QphysN rho sigma) (Complex.I * (k : ℂ)) i j * (v i : ℂ) * (v j : ℂ) := by
    rw [← hdiag, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.sub_apply]; ring
  apply Complex.ofReal_injective
  rw [matGram_normSq_eq_QQ (QphysN rho sigma (Complex.I * (k : ℂ)))
      (QphysN rho sigma (-(Complex.I * (k : ℂ)))) hherm v,
    Cmix0_factorization (QphysN rho sigma) (Complex.I * (k : ℂ)), hsub, hB, hSreal]
  push_cast
  ring

/-! ## Part D — the general-`N` unequal-diameter mixture RDF uniqueness capstone -/

/-- **The physical symmetric forcing has support in `[0, σ_max]`.**  `PhiSymN i j t = 0` for
`t ≥ σ_max` (both branches truncate at `Rᵢⱼ = (σᵢ+σⱼ)/2 ≤ σ_max`). -/
theorem PhiSymN_eq_zero_of_le (rho sigma : Fin N → ℝ) (rhoTot : ℝ) {sigma_bd : ℝ}
    (hbd : ∀ n, sigma n ≤ sigma_bd) (i j : Fin N) {t : ℝ} (ht : sigma_bd ≤ t) :
    PhiSymN rho sigma rhoTot i j t = 0 := by
  have hR : (sigma i + sigma j) / 2 ≤ t := by linarith [hbd i, hbd j]
  have hRji : (sigma j + sigma i) / 2 ≤ t := by linarith [hbd i, hbd j]
  simp only [PhiSymN]
  by_cases h : sigma i ≤ sigma j
  · rw [if_pos h, PhiUneq, if_neg (not_lt.mpr hR)]
  · rw [if_neg h, PhiUneq, if_neg (not_lt.mpr hRji)]

/-- **⭐⭐⭐ General-`N` unequal-diameter mixture RDF — UNIQUE (given the coercive symbol).**  Two
`MatOZStar` solutions with the physical symmetric forcing `PhiSymN` coincide on `r > 0`, given
`MatSymbolCoercive (PhiSymN …) ρ` and the arbitrary solution's routine regularity.  Instantiates the
unconditional matrix `oz_fixed_pt_unique` (`matOzStar_unique`, resting on the bounded WH axiom
`matRadialShell_bounded_injective`) with `Φ = PhiSymN`, `hPhisupp` from `PhiSymN_eq_zero_of_le`.  The
coercivity's Gram input is the proven `matDCF_hfack` (via T-symmetry `matDCF_ae_symmN`, forward-only
`B1`); the general unequal-σ RDF is thus pinned by the coercive structure factor — MML.8. -/
theorem matOzStar_unequalDiam_unique (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    {sigma_bd : ℝ} (hsigma_bd : 0 < sigma_bd) (hbd : ∀ n, sigma n ≤ sigma_bd) {rho_s : ℝ}
    (hcoercive : MatSymbolCoercive (PhiSymN rho sigma rho_s) rho_s)
    {Psi1 Psi2 : Matrix (Fin N) (Fin N) (ℝ → ℝ)}
    (h1 : MatOZStar Psi1 (PhiSymN rho sigma rho_s) rho_s)
    (h2 : MatOZStar Psi2 (PhiSymN rho sigma rho_s) rho_s)
    (hlin : ∀ (i j : Fin N) (r : ℝ), 0 < r →
      matRadialConv (PhiSymN rho sigma rho_s) (fun k l => fun x => Psi1 k l x / x) r i j
        - matRadialConv (PhiSymN rho sigma rho_s) (fun k l => fun x => Psi2 k l x / x) r i j
        = matRadialConv (PhiSymN rho sigma rho_s)
            (fun k l => fun x => (Psi1 k l x - Psi2 k l x) / x) r i j)
    (hbdd : ∀ i j, ∃ M : ℝ, ∀ r : ℝ, |Psi1 i j r - Psi2 i j r| ≤ M)
    (hcont : ∀ i j, ContinuousOn (fun r => Psi1 i j r - Psi2 i j r) (Set.Ici sigma_bd))
    (hcore : ∀ (i j : Fin N) (r : ℝ), r < sigma_bd → Psi1 i j r - Psi2 i j r = 0) :
    ∀ (i j : Fin N) (r : ℝ), 0 < r → Psi1 i j r = Psi2 i j r :=
  matOzStar_unique hsigma_bd
    (fun i j t ht => PhiSymN_eq_zero_of_le rho sigma rho_s hbd i j ht)
    hcoercive h1 h2 hlin hbdd hcont hcore

end FMSA.MixtureBaxter

namespace FMSA.MixtureBaxter

open FMSA.MatrixQ0 FMSA.MixtureHSDCF FMSA.HardSphere FMSA.MRS FMSA.MixtureOzStar MeasureTheory

variable {N : ℕ}

/-! ## Part C — the unconditional coercivity `MatSymbolCoercive (PhiSymN …) ρ` -/

/-- **The DCF-core cosine transform is continuous in `k` (all of `ℝ`).**  `k ↦ ∫₀^∞
matDCFreCoreN(i,j)·cos(kv)` is continuous by dominated convergence (`|matDCFreCoreN|` integrable
dominates, `|cos| ≤ 1`).  Gives the continuous representative `Csym` of the symbol through `k = 0`. -/
theorem matDCFreCoreN_cos_setIntegral_continuous (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i j : Fin N) :
    Continuous (fun k : ℝ =>
      ∫ v in Set.Ioi (0:ℝ), matDCFreCoreN rho sigma hsig i j v * Real.cos (k * v)) := by
  apply continuous_of_dominated (μ := volume.restrict (Set.Ioi (0:ℝ)))
    (bound := fun v => |matDCFreCoreN rho sigma hsig i j v|)
  · intro k
    exact (matDCFreCoreN_cos_integrable rho sigma hsig i j k).aestronglyMeasurable.restrict
  · intro k
    filter_upwards with v
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · exact (matDCFreCoreN_integrable rho sigma hsig i j).abs.integrableOn
  · filter_upwards with v
    exact continuous_const.mul (Real.continuous_cos.comp (continuous_id.mul continuous_const))

/-- **The continuous symbol representative** `Csym k = (2/ρ)·`(DCF-core cosine transform), a
continuous extension of `matRadialSymbol (PhiSymN …)` through `k = 0`. -/
noncomputable def CsymN (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (rhoTot : ℝ) (k : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (2 / rhoTot) * ∫ v in Set.Ioi (0:ℝ),
    matDCFreCoreN rho sigma hsig i j v * Real.cos (k * v)

/-- `CsymN` is continuous in `k`, entrywise. -/
theorem CsymN_continuous (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (rhoTot : ℝ) (i j : Fin N) :
    Continuous (fun k => CsymN rho sigma hsig rhoTot k i j) :=
  continuous_const.mul (matDCFreCoreN_cos_setIntegral_continuous rho sigma hsig i j)

/-- `CsymN` agrees with the OZ symbol of `PhiSymN` for `k ≠ 0` (`radial_fourier_PhiSymN`). -/
theorem CsymN_eq_symbol (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (hrho : ∀ n, 0 ≤ rho n)
    (hvac : vacMix rho sigma ≠ 0) {rhoTot : ℝ} (hrhoTot : rhoTot ≠ 0) {k : ℝ} (hk : k ≠ 0)
    (i j : Fin N) :
    CsymN rho sigma hsig rhoTot k i j = matRadialSymbol (PhiSymN rho sigma rhoTot) k i j := by
  rw [show matRadialSymbol (PhiSymN rho sigma rhoTot) k i j
      = radial_fourier (PhiSymN rho sigma rhoTot i j) k from rfl,
    radial_fourier_PhiSymN rho sigma hsig hrho hvac i j hrhoTot hk, CsymN]

/-- **`hBfun`** — `det (Q̂₀(ik)ᵀ) ≠ 0` for real `k ≠ 0`, the PY-HS mixture no-spinodal
(`pyhs_mixture_no_spinodal`; `det Mᵀ = det M`, `QphysN = Q0_mat_c_phys` defeq). -/
theorem QphysN_transpose_det_ne_zero (rho sigma : Fin N → ℝ) (hsig : ∀ i, 0 < sigma i)
    (hrho : ∀ i, 0 < rho i) (heta : etaMix rho sigma < 1) {k : ℝ} (hk : k ≠ 0) :
    ((QphysN rho sigma (Complex.I * (k : ℂ))).transpose).det ≠ 0 := by
  rw [Matrix.det_transpose]
  exact FMSA.MixtureNoSpinodal.pyhs_mixture_no_spinodal hsig hrho heta hk

/-- **`hfac0` — the origin Gram factorization at `k = 0`.**  `∑vᵢ² − ρ·∑ CsymN(0)ᵢⱼvᵢvⱼ =
∑ₗ|((Q0_mat_c_repr 0)ᵀv)ₗ|²`.  Both sides are continuous in `k` and agree for `k ≠ 0` (`matDCF_hfack`
+ `CsymN_eq_symbol` + `Q0_mat_c_repr_eq_of_ne`), so by density of `{k ≠ 0}` (`Continuous.ext_on`) they
agree at `0`.  `B₀ = (Q0_mat_c_repr 0)ᵀ` is the finite Baxter factor whose `det ≠ 0` is the
removable compressibility point (`det_Q0_mat_c_repr_origin_ne_zero`). -/
theorem matDCF_hfac0 (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (hrho : ∀ n, 0 ≤ rho n)
    (hvac : vacMix rho sigma ≠ 0) {rho_s : ℝ} (hrho_s : rho_s ≠ 0) (v : Fin N → ℝ) :
    (∑ i, v i ^ 2) - rho_s * ∑ i, ∑ j, CsymN rho sigma hsig rho_s 0 i j * v i * v j
      = ∑ l, Complex.normSq
          ((FMSA.MixtureGenN.Q0_mat_c_repr 0 sigma rho).transpose.mulVec (fun i => (v i : ℂ)) l) := by
  set F : ℝ → ℝ := fun k => (∑ i, v i ^ 2)
    - rho_s * ∑ i, ∑ j, CsymN rho sigma hsig rho_s k i j * v i * v j with hFdef
  set G : ℝ → ℝ := fun k => ∑ l, Complex.normSq
    ((FMSA.MixtureGenN.Q0_mat_c_repr (Complex.I * (k : ℂ)) sigma rho).transpose.mulVec (fun i => (v i : ℂ)) l)
    with hGdef
  have hqc : Continuous (fun k : ℝ => FMSA.MixtureGenN.Q0_mat_c_repr (Complex.I * (k : ℂ)) sigma rho) :=
    (FMSA.MixtureGenN.continuous_Q0_mat_c_repr sigma rho).comp (continuous_const.mul Complex.continuous_ofReal)
  have hFcont : Continuous F := by
    rw [hFdef]
    refine continuous_const.sub (continuous_const.mul (continuous_finset_sum _ (fun i _ =>
      continuous_finset_sum _ (fun j _ => ?_))))
    exact ((CsymN_continuous rho sigma hsig rho_s i j).mul continuous_const).mul continuous_const
  have hGcont : Continuous G := by
    rw [hGdef]
    refine continuous_finset_sum _ (fun l _ => Complex.continuous_normSq.comp ?_)
    simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct]
    refine continuous_finset_sum _ (fun i _ => ?_)
    exact (((continuous_apply l).comp ((continuous_apply i).comp hqc)).mul continuous_const)
  have hFG : Set.EqOn F G {(0 : ℝ)}ᶜ := by
    intro k hk
    have hk0 : k ≠ 0 := Set.mem_compl_singleton_iff.mp hk
    have hIk : (Complex.I * (k : ℂ)) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hk0)
    have hrepr : FMSA.MixtureGenN.Q0_mat_c_repr (Complex.I * (k : ℂ)) sigma rho
        = QphysN rho sigma (Complex.I * (k : ℂ)) := FMSA.MixtureGenN.Q0_mat_c_repr_eq_of_ne hIk sigma rho
    simp only [hFdef, hGdef]
    rw [hrepr, show (∑ i, ∑ j, CsymN rho sigma hsig rho_s k i j * v i * v j)
        = ∑ i, ∑ j, matRadialSymbol (PhiSymN rho sigma rho_s) k i j * v i * v j from
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
        rw [CsymN_eq_symbol rho sigma hsig hrho hvac hrho_s hk0 i j])),
      matDCF_hfack rho sigma hsig hrho hvac hrho_s hk0 v]
  have h0 := congrFun (Continuous.ext_on (dense_compl_singleton 0) hFcont hGcont hFG) 0
  simp only [hFdef, hGdef, Complex.ofReal_zero, mul_zero] at h0
  exact h0

set_option maxHeartbeats 800000 in
/-- **The coercivity `MatSymbolCoercive (PhiSymN …) ρ`, modulo the tail decay `htail`.**  Wires
`matSymbolCoercive_of_gramFactors`: near-`0` from `CsymN` (continuous through `0`) + `matDCF_hfac0`
(origin Gram, `B₀ = (Q0_mat_c_repr 0)ᵀ`, `det ≠ 0`); middle `k ≠ 0` from `matDCF_hfack`
(`Bfun = Q̂₀(ik)ᵀ`, `det ≠ 0` no-spinodal); symbol continuity from `CsymN`.  Only `htail` (the `O(1/k)`
symbol decay) is a hypothesis here. -/
theorem matSymbolCoercive_PhiSymN_of_htail (rho sigma : Fin N → ℝ) (hsig : ∀ i, 0 < sigma i)
    (hrhopos : ∀ i, 0 < rho i) (heta : etaMix rho sigma < 1) {rho_s : ℝ} (hrho_s : 0 < rho_s)
    {bb : ℝ} (hbb : 0 < bb)
    (htail : ∃ δ : ℝ, 0 < δ ∧ ∀ (k : ℝ) (u : Fin N → ℝ), bb ≤ |k| → (∑ i, u i ^ 2) = 1 →
      δ ≤ (∑ i, u i ^ 2)
        - rho_s * ∑ i, ∑ j, matRadialSymbol (PhiSymN rho sigma rho_s) k i j * u i * u j) :
    MatSymbolCoercive (PhiSymN rho sigma rho_s) rho_s := by
  have hrho0 : ∀ n, 0 ≤ rho n := fun n => (hrhopos n).le
  have hvac : vacMix rho sigma ≠ 0 := ne_of_gt (by simp only [vacMix]; linarith [heta])
  have hagree : ∀ (k : ℝ), k ≠ 0 → ∀ i j,
      CsymN rho sigma hsig rho_s k i j = matRadialSymbol (PhiSymN rho sigma rho_s) k i j :=
    fun k hk i j => CsymN_eq_symbol rho sigma hsig hrho0 hvac hrho_s.ne' hk i j
  have hcn : ∀ i j, ContinuousOn (fun k => CsymN rho sigma hsig rho_s k i j) (Set.Icc (-1 : ℝ) 1) :=
    fun i j => (CsymN_continuous rho sigma hsig rho_s i j).continuousOn
  have hcs : ∀ i j, ContinuousOn (fun k => matRadialSymbol (PhiSymN rho sigma rho_s) k i j)
      {k : ℝ | k ≠ 0} :=
    fun i j => (CsymN_continuous rho sigma hsig rho_s i j).continuousOn.congr
      (fun k hk => (CsymN_eq_symbol rho sigma hsig hrho0 hvac hrho_s.ne' hk i j).symm)
  have hB0 : ((FMSA.MixtureGenN.Q0_mat_c_repr 0 sigma rho).transpose).det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact FMSA.MixtureGenN.det_Q0_mat_c_repr_origin_ne_zero hsig hrhopos heta
  have hfac0 : ∀ v : Fin N → ℝ, (∑ i, v i ^ 2)
        - rho_s * ∑ i, ∑ j, CsymN rho sigma hsig rho_s 0 i j * v i * v j
      = ∑ l, Complex.normSq
          ((FMSA.MixtureGenN.Q0_mat_c_repr 0 sigma rho).transpose.mulVec (fun i => (v i : ℂ)) l) :=
    fun v => matDCF_hfac0 rho sigma hsig hrho0 hvac hrho_s.ne' v
  have hBfun : ∀ (k : ℝ), k ≠ 0 →
      ((QphysN rho sigma (Complex.I * (k : ℂ))).transpose).det ≠ 0 :=
    fun k hk => QphysN_transpose_det_ne_zero rho sigma hsig hrhopos heta hk
  have hfack : ∀ (k : ℝ), k ≠ 0 → ∀ v : Fin N → ℝ, (∑ i, v i ^ 2)
        - rho_s * ∑ i, ∑ j, matRadialSymbol (PhiSymN rho sigma rho_s) k i j * v i * v j
      = ∑ l, Complex.normSq
          ((QphysN rho sigma (Complex.I * (k : ℂ))).transpose.mulVec (fun i => (v i : ℂ)) l) :=
    fun k hk v => matDCF_hfack rho sigma hsig hrho0 hvac hrho_s.ne' hk v
  exact matSymbolCoercive_of_gramFactors (PhiSymN rho sigma rho_s) rho_s
    (CsymN rho sigma hsig rho_s) (a₀ := 1) (b := bb) one_pos hbb hagree hcn hcs
    ((FMSA.MixtureGenN.Q0_mat_c_repr 0 sigma rho).transpose) hB0 hfac0
    (fun k => (QphysN rho sigma (Complex.I * (k : ℂ))).transpose) hBfun hfack htail

/-! ## Part C — discharging `htail` (the `O(1/k)` symbol decay) -/

/-- **`r·PhiUneq(a,b)` is integrable on `(0,∞)`** (`σₐ ≤ σ_b`) — a bounded piecewise polynomial
(`r·cPiece = rcPoly`) supported in `[0, Rₐᵦ]`.  Split `[0,λ]∪[λ,R]` (`congr_uIoo` from the continuous
`rcPoly`) + `0` beyond `R`.  Supplies the finite `L¹` weight `∫|r·Φ|` of the symbol tail bound. -/
theorem r_PhiUneq_integrableOn (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (hvac : vacMix rho sigma ≠ 0) (a b : Fin N) (hlam : sigma a ≤ sigma b) (rhoTot : ℝ) :
    IntegrableOn (fun r => r * PhiUneq rho sigma rhoTot a b r) (Set.Ioi (0:ℝ)) := by
  have hlam0 : (0:ℝ) ≤ (sigma b - sigma a) / 2 := by linarith [hlam]
  have hlamR : (sigma b - sigma a) / 2 ≤ (sigma a + sigma b) / 2 := by linarith [hsig a]
  have hR0 : (0:ℝ) ≤ (sigma a + sigma b) / 2 := by linarith [hsig a, hsig b]
  have hIL : IntervalIntegrable (fun r => r * PhiUneq rho sigma rhoTot a b r) volume 0
      ((sigma b - sigma a) / 2) := by
    refine (((rcLowerPoly_continuous rho sigma hvac a b).const_mul
      (rhoGeoPhys rho a b / rhoTot)).intervalIntegrable 0 _).congr_uIoo (fun r hr => ?_)
    rw [Set.uIoo_of_le hlam0] at hr
    show (rhoGeoPhys rho a b / rhoTot) * rcLowerPoly rho sigma a b r
        = r * PhiUneq rho sigma rhoTot a b r
    rw [PhiUneq, if_pos (lt_of_lt_of_le hr.2 hlamR), cMixDCFN, if_pos hr.2,
      ← r_mul_cLowerPieceN_eq rho sigma hvac a b (ne_of_gt hr.1)]
    ring
  have hIU : IntervalIntegrable (fun r => r * PhiUneq rho sigma rhoTot a b r) volume
      ((sigma b - sigma a) / 2) ((sigma a + sigma b) / 2) := by
    refine (((rcUpperPoly_continuous rho sigma hvac a b).const_mul
      (rhoGeoPhys rho a b / rhoTot)).intervalIntegrable _ _).congr_uIoo (fun r hr => ?_)
    rw [Set.uIoo_of_le hlamR] at hr
    show (rhoGeoPhys rho a b / rhoTot) * rcUpperPoly rho sigma a b r
        = r * PhiUneq rho sigma rhoTot a b r
    rw [PhiUneq, if_pos hr.2, cMixDCFN, if_neg (not_lt.mpr hr.1.le),
      ← r_mul_cUpperPieceN_eq rho sigma hvac a b (ne_of_gt (lt_of_le_of_lt hlam0 hr.1))]
    ring
  have hIoc : IntegrableOn (fun r => r * PhiUneq rho sigma rhoTot a b r)
      (Set.Ioc 0 ((sigma a + sigma b) / 2)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hR0).mp (hIL.trans hIU)
  have hIoiR : IntegrableOn (fun r => r * PhiUneq rho sigma rhoTot a b r)
      (Set.Ioi ((sigma a + sigma b) / 2)) :=
    integrableOn_zero.congr_fun
      (fun r hr => by rw [PhiUneq, if_neg (not_lt.mpr (le_of_lt (Set.mem_Ioi.mp hr))), mul_zero])
      measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi hR0]
  exact hIoc.union hIoiR

/-- **The symbol has an explicit `O(1/k)` bound.**  `|matRadialSymbol Φ k i j| ≤ (4π/|k|)·∫₀^∞|r·Φᵢⱼ|`
— the `1/k` is built into `matRadialSymbol = (4π/k)∫ r·Φ·sin(kr)`; `|sin| ≤ 1` and
`norm_integral_le_integral_norm` give the `L¹`-weighted decay. No IBP. -/
theorem abs_matRadialSymbol_le (Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (i j : Fin N)
    (hint : IntegrableOn (fun r => r * Phi i j r) (Set.Ioi (0:ℝ))) {k : ℝ} (hk : k ≠ 0) :
    |matRadialSymbol Phi k i j|
      ≤ (4 * Real.pi / |k|) * ∫ r in Set.Ioi (0:ℝ), |r * Phi i j r| := by
  have hsin_int : IntegrableOn (fun r => r * Phi i j r * Real.sin (k * r)) (Set.Ioi (0:ℝ)) :=
    hint.mul_bdd (by fun_prop) (Filter.Eventually.of_forall (fun r => by
      rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩))
  rw [show matRadialSymbol Phi k i j
      = (4 * Real.pi / k) * ∫ r in Set.Ioi (0:ℝ), r * Phi i j r * Real.sin (k * r) from rfl,
    abs_mul, abs_div, abs_of_pos (show (0:ℝ) < 4 * Real.pi by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc |∫ r in Set.Ioi (0:ℝ), r * Phi i j r * Real.sin (k * r)|
      = ‖∫ r in Set.Ioi (0:ℝ), r * Phi i j r * Real.sin (k * r)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ r in Set.Ioi (0:ℝ), ‖r * Phi i j r * Real.sin (k * r)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ r in Set.Ioi (0:ℝ), |r * Phi i j r| := by
        refine setIntegral_mono_on hsin_int.norm hint.abs measurableSet_Ioi (fun r _ => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _)
          (abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩)

/-- **⭐⭐⭐ The coercivity `MatSymbolCoercive (PhiSymN …) ρ` — UNCONDITIONAL.**  Discharges `htail` via
the symbol's `O(1/k)` decay (`abs_matRadialSymbol_le` + `r_PhiUneq_integrableOn` ⟹
`|matRadialSymbol| ≤ (4π/|k|)·Lᵢⱼ`, `Lᵢⱼ = ∫₀^∞|r·Φᵢⱼ|`) fed to `matSymbol_tail_bound` with the
threshold `b = 4π·ρ·(∑Lᵢⱼ)·N + 1` (so `ρMN = (b−1)/b < 1`).  Combined with the near-`0`/middle/continuity
already in `matSymbolCoercive_PhiSymN_of_htail`, the full mixture symbol is coercive. -/
theorem matSymbolCoercive_PhiSymN (rho sigma : Fin N → ℝ) (hsig : ∀ i, 0 < sigma i)
    (hrhopos : ∀ i, 0 < rho i) (heta : etaMix rho sigma < 1) {rho_s : ℝ} (hrho_s : 0 < rho_s) :
    MatSymbolCoercive (PhiSymN rho sigma rho_s) rho_s := by
  have hvac : vacMix rho sigma ≠ 0 := ne_of_gt (by simp only [vacMix]; linarith [heta])
  have hintPS : ∀ i j, IntegrableOn (fun r => r * PhiSymN rho sigma rho_s i j r) (Set.Ioi (0:ℝ)) := by
    intro i j
    by_cases h : sigma i ≤ sigma j
    · exact (r_PhiUneq_integrableOn rho sigma hsig hvac i j h rho_s).congr_fun
        (fun x _ => by simp only [PhiSymN, if_pos h]) measurableSet_Ioi
    · exact (r_PhiUneq_integrableOn rho sigma hsig hvac j i (not_le.mp h).le rho_s).congr_fun
        (fun x _ => by simp only [PhiSymN, if_neg h]) measurableSet_Ioi
  set L : Fin N → Fin N → ℝ :=
    fun i j => ∫ r in Set.Ioi (0:ℝ), |r * PhiSymN rho sigma rho_s i j r| with hLdef
  have hLnn : ∀ i j, 0 ≤ L i j := fun i j =>
    setIntegral_nonneg measurableSet_Ioi (fun r _ => abs_nonneg _)
  set Lsum : ℝ := ∑ i, ∑ j, L i j with hLsumdef
  have hLle : ∀ i j, L i j ≤ Lsum := fun i j =>
    (Finset.single_le_sum (fun j' _ => hLnn i j') (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun i' _ => Finset.sum_nonneg (fun j' _ => hLnn i' j'))
        (Finset.mem_univ i))
  have hLsum_nn : 0 ≤ Lsum := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hLnn i j))
  set bb : ℝ := 4 * Real.pi * rho_s * Lsum * (N : ℝ) + 1 with hbbdef
  have hbbpos : 0 < bb := by rw [hbbdef]; positivity
  set M : ℝ := (4 * Real.pi / bb) * Lsum with hMdef
  have hMbd : ∀ i j (k : ℝ), bb ≤ |k| →
      |matRadialSymbol (PhiSymN rho sigma rho_s) k i j| ≤ M := by
    intro i j k hk
    have hkne : k ≠ 0 := by intro h; rw [h, abs_zero] at hk; linarith [hbbpos]
    refine (abs_matRadialSymbol_le (PhiSymN rho sigma rho_s) i j (hintPS i j) hkne).trans ?_
    rw [hMdef]
    refine mul_le_mul ?_ (hLle i j) (hLnn i j) (by positivity)
    exact div_le_div_of_nonneg_left (by positivity) hbbpos hk
  have hMNbound : rho_s * M * (N : ℝ) < 1 := by
    have hkey : rho_s * M * (N : ℝ) = (4 * Real.pi * rho_s * Lsum * (N : ℝ)) / bb := by
      rw [hMdef]; field_simp
    rw [hkey, div_lt_one hbbpos, hbbdef]; linarith
  exact matSymbolCoercive_PhiSymN_of_htail rho sigma hsig hrhopos heta hrho_s hbbpos
    (matSymbol_tail_bound (PhiSymN rho sigma rho_s) hrho_s.le hMbd hMNbound)

/-- **⭐⭐⭐ General-`N` unequal-diameter mixture RDF — UNIQUE, UNCONDITIONALLY (MML.8).**  Two
`MatOZStar` solutions with the physical symmetric forcing `PhiSymN` coincide on `r > 0`, given only the
physical data (`0 < σᵢ`, `0 < ρᵢ`, packing `η < 1`, `0 < ρ`) and the arbitrary solution's routine
regularity.  The coercive structure factor is discharged by `matSymbolCoercive_PhiSymN` (near-`0` +
middle + tail), so this rests only on the bounded Wiener–Hopf axiom `matRadialShell_bounded_injective`
(= MA.15) and the PY-HS no-spinodal `pyhs_mixture_no_spinodal` — the same footing as the equal-diameter
capstone.  The general unequal-σ mixture RDF is pinned by its coercive structure factor. -/
theorem matOzStar_unequalDiam_unique_uncond (rho sigma : Fin N → ℝ) (hsig : ∀ i, 0 < sigma i)
    (hrhopos : ∀ i, 0 < rho i) (heta : etaMix rho sigma < 1) {rho_s : ℝ} (hrho_s : 0 < rho_s)
    {sigma_bd : ℝ} (hsigma_bd : 0 < sigma_bd) (hbd : ∀ n, sigma n ≤ sigma_bd)
    {Psi1 Psi2 : Matrix (Fin N) (Fin N) (ℝ → ℝ)}
    (h1 : MatOZStar Psi1 (PhiSymN rho sigma rho_s) rho_s)
    (h2 : MatOZStar Psi2 (PhiSymN rho sigma rho_s) rho_s)
    (hlin : ∀ (i j : Fin N) (r : ℝ), 0 < r →
      matRadialConv (PhiSymN rho sigma rho_s) (fun k l => fun x => Psi1 k l x / x) r i j
        - matRadialConv (PhiSymN rho sigma rho_s) (fun k l => fun x => Psi2 k l x / x) r i j
        = matRadialConv (PhiSymN rho sigma rho_s)
            (fun k l => fun x => (Psi1 k l x - Psi2 k l x) / x) r i j)
    (hbdd : ∀ i j, ∃ M : ℝ, ∀ r : ℝ, |Psi1 i j r - Psi2 i j r| ≤ M)
    (hcont : ∀ i j, ContinuousOn (fun r => Psi1 i j r - Psi2 i j r) (Set.Ici sigma_bd))
    (hcore : ∀ (i j : Fin N) (r : ℝ), r < sigma_bd → Psi1 i j r - Psi2 i j r = 0) :
    ∀ (i j : Fin N) (r : ℝ), 0 < r → Psi1 i j r = Psi2 i j r :=
  matOzStar_unequalDiam_unique rho sigma hsig hsigma_bd hbd
    (matSymbolCoercive_PhiSymN rho sigma hsig hrhopos heta hrho_s) h1 h2 hlin hbdd hcont hcore

end FMSA.MixtureBaxter
