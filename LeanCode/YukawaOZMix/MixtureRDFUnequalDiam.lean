/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.YukawaOZMix.MixtureBaxterODEUnequalDiamN
import LeanCode.HSMixture.MixtureCoercivityReduction
import LeanCode.HSMixture.MixtureRDFUniqueness

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

open FMSA.MatrixQ0 FMSA.MixtureHSDCF

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

end FMSA.MixtureBaxter
