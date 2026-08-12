/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/
import Mathlib
import LeanCode.YukawaOZMix.MixtureCorrectedSeed
import LeanCode.YukawaOZMix.MixtureRowSum
import LeanCode.YukawaOZMix.PhysMixRhoWeightRenewal

/-!
# Two-kernel `ρ_k`-weighted EXTENDED seed (unequal diameters)

The `ρ_k`-weighting of the extended seed genuinely needs TWO kernels because the seed's inner
convolution is *transposed* (`matBaxterUtExt` sums the FIRST index `Q m i` ⇒ weight `ρ_m`) while the
outer sums the SECOND (`Q i k` ⇒ weight `ρ_k`).  A single column-scaled kernel gives `ρ_i` (not
`ρ_m`) in the inner — wrong.  So:

* inner (`matBaxterUtExt`) uses the **row-scaled** kernel `rowScaleK ρ Q a b := ρ_a·Q a b`;
* outer uses the **column-scaled** kernel `colScaleK ρ Q a b := ρ_b·Q a b`.

`matBaxterUQmSymFullExtRho Ψ Q ρ i j r := matBaxterUtExt Ψ (rowScaleK ρ Q) i j r − ∑ₖ ∫_ℝ
(colScaleK ρ Q)ᵢₖ · matBaxterUtExt Ψ (rowScaleK ρ Q) ₖⱼ(r+t)`.

The two kernels are reconciled at symmetric `Q` (equal diameters) by the new **ρ-weighted transpose
bridge** `matBaxterUt_rowScale_eq_matBaxterU_colScale_of_symm` (the `ρ`-analog of
`matBaxterUt_of_symm`), which drives the equal-diameter collapse to the `ρ`-weighted WINDOWED seed
`matBaxterUQm (colScaleK ρ Q)` — hence to `r·c_HS`.  Outer-vanishing (`_zero_outer`, `σ−λ`)
holds at UNEQUAL diameters.
-/

namespace FMSA.MixtureOzStar

open MeasureTheory

variable {N : ℕ}

/-- **Row-scaled kernel** `(rowScaleK ρ Q) a b := ρ_a · Q a b` — weight the FIRST index; the correct
weight for the transposed inner convolution `matBaxterUtExt` (which sums the first index). -/
noncomputable def rowScaleK (rho : Fin N → ℝ) (Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) :
    Matrix (Fin N) (Fin N) (ℝ → ℝ) := fun a b => fun s => rho a * Q a b s

/-- **Column-scaled kernel** `(colScaleK ρ Q) a b := ρ_b · Q a b` — weight the SECOND/summed index;
the correct weight for the outer convolution (which sums the second index). -/
noncomputable def colScaleK (rho : Fin N → ℝ) (Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) :
    Matrix (Fin N) (Fin N) (ℝ → ℝ) := fun a b => fun s => rho b * Q a b s

/-- **The two-kernel `ρ_k`-weighted extended seed.**  Row-scaled inner (weight `ρ_m` on the summed
first index), column-scaled outer (weight `ρ_k` on the summed second index). -/
noncomputable def matBaxterUQmSymFullExtRho (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (rho : Fin N → ℝ) (i j : Fin N) (r : ℝ) : ℝ :=
  matBaxterUtExt Psi (rowScaleK rho Q) i j r
    - ∑ k, ∫ t, (colScaleK rho Q) i k t * matBaxterUtExt Psi (rowScaleK rho Q) k j (r + t)

/-- **⭐ ρ-weighted transpose bridge** — at symmetric `Q`, the row-scaled transposed convolution
equals the column-scaled untransposed one: `matBaxterUt Ψ (rowScaleK ρ Q) = matBaxterU Ψ
(colScaleK ρ Q)`.  The `ρ`-analog of `matBaxterUt_of_symm`; both carry the summed weight `ρ_m`,
and `Q m i = Q i m` (`hsym`) makes them coincide — what lets the two-kernel seed collapse at σ. -/
theorem matBaxterUt_rowScale_eq_matBaxterU_colScale_of_symm
    (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (rho : Fin N → ℝ) (sigma : ℝ)
    (hsym : ∀ i j, Q i j = Q j i) (i j : Fin N) (r : ℝ) :
    matBaxterUt Psi (rowScaleK rho Q) sigma i j r
      = matBaxterU Psi (colScaleK rho Q) sigma i j r := by
  unfold matBaxterUt matBaxterU
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  simp only [rowScaleK, colScaleK, hsym m i]

/-- **Outer-vanishing of the two-kernel `ρ`-weighted extended seed** (UNEQUAL diameters, `σ−λ`
bound).  Mirrors `matBaxterUQmSymFullExt_zero_outer`: for `r ≥ σ−λ` the leading `matBaxterUtExt`
term vanishes (`hUtouter`), and each outer integrand vanishes — below `λ` the column kernel is `0`
(`hQlam`), above `λ` the sample `r+t ≥ σ` kills `matBaxterUtExt`. -/
theorem matBaxterUQmSymFullExtRho_zero_outer (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (rho : Fin N → ℝ) (sigma lam : ℝ) (hlam : lam ≤ 0)
    (hUtouter : ∀ i j r, sigma ≤ r → matBaxterUtExt Psi (rowScaleK rho Q) i j r = 0)
    (hQlam : ∀ i k t, t < lam → Q i k t = 0)
    {r : ℝ} (hr : sigma - lam ≤ r) (i j : Fin N) :
    matBaxterUQmSymFullExtRho Psi Q rho i j r = 0 := by
  unfold matBaxterUQmSymFullExtRho
  rw [hUtouter i j r (by linarith), zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  have hz : (fun t => (colScaleK rho Q) i k t * matBaxterUtExt Psi (rowScaleK rho Q) k j (r + t))
      =ᵐ[volume] (fun _ => (0 : ℝ)) := by
    filter_upwards with t
    rcases lt_or_ge t lam with ht | ht
    · rw [show (colScaleK rho Q) i k t = 0 from by
        simp only [colScaleK, hQlam i k t ht, mul_zero], zero_mul]
    · rw [hUtouter k j (r + t) (by linarith), mul_zero]
  rw [integral_congr_ae hz, integral_zero]

/-- **Leading arm collapse** — for a symmetric factor supported in `[0,σ]`, the row-scaled extended
inner equals the column-scaled windowed `matBaxterU`: `matBaxterUtExt Ψ (rowScaleK ρ Q) = matBaxterU
Ψ (colScaleK ρ Q)`.  Support (`_eq_matBaxterUt_of_support`) + the ρ-transpose bridge. -/
theorem matBaxterUtExt_rowScale_eq_matBaxterU_colScale (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ))
    (rho : Fin N → ℝ) (sigma : ℝ) (hsigma : 0 ≤ sigma)
    (hQsupp : ∀ i k t, t < 0 ∨ sigma < t → Q i k t = 0) (hsym : ∀ i j, Q i j = Q j i)
    (i j : Fin N) (r : ℝ) :
    matBaxterUtExt Psi (rowScaleK rho Q) i j r = matBaxterU Psi (colScaleK rho Q) sigma i j r := by
  rw [matBaxterUtExt_eq_matBaxterUt_of_support Psi (rowScaleK rho Q) sigma hsigma
      (fun i' k' t ht => by simp only [rowScaleK, hQsupp i' k' t ht, mul_zero]) i j r,
    matBaxterUt_rowScale_eq_matBaxterU_colScale_of_symm Psi Q rho sigma hsym i j r]

/-- **⭐⭐ Equal-diameter collapse of the two-kernel `ρ`-weighted EXTENDED seed to the `ρ`-weighted
WINDOWED seed.**  For a symmetric factor supported in `[0,σ]` (the equal-diameter case), the
extended seed's `∫_ℝ` convolutions reduce to `∫₀^σ` and the transpose is invisible (`ρ`-bridge), so
`matBaxterUQmSymFullExtRho Ψ Q ρ = matBaxterUQm Ψ (colScaleK ρ Q) σ`.  Composed with
`matBaxterUQm_eq_rcHS_of_rowSum` (`∑ₖ (colScaleK ρ Q)ᵢₖ = ∑ₖ ρ_k Qᵢₖ = q0_poly`) this gives the
equal-diameter `= r·c_HS` for the `ρ`-weighted extended seed. -/
theorem matBaxterUQmSymFullExtRho_eq_matBaxterUQm_colScale
    (Psi Q : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (rho : Fin N → ℝ) (sigma : ℝ) (hsigma : 0 < sigma)
    (hQsupp : ∀ i k t, t < 0 ∨ sigma < t → Q i k t = 0) (hsym : ∀ i j, Q i j = Q j i)
    (i j : Fin N) (r : ℝ) :
    matBaxterUQmSymFullExtRho Psi Q rho i j r = matBaxterUQm Psi (colScaleK rho Q) sigma i j r := by
  unfold matBaxterUQmSymFullExtRho matBaxterUQm
  rw [matBaxterUtExt_rowScale_eq_matBaxterU_colScale Psi Q rho sigma hsigma.le hQsupp hsym i j r]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hUt : ∀ t, matBaxterUtExt Psi (rowScaleK rho Q) k j (r + t)
      = matBaxterU Psi (colScaleK rho Q) sigma k j (r + t) :=
    fun t => matBaxterUtExt_rowScale_eq_matBaxterU_colScale Psi Q rho sigma hsigma.le hQsupp hsym
      k j (r + t)
  simp_rw [hUt]
  rw [intervalIntegral.integral_of_le hsigma.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => ?_)).symm
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with ht | ht
  · rw [show (colScaleK rho Q) i k t = 0 from by
      simp only [colScaleK, hQsupp i k t (Or.inl ht), mul_zero], zero_mul]
  · rw [show (colScaleK rho Q) i k t = 0 from by
      simp only [colScaleK, hQsupp i k t (Or.inr ht), mul_zero], zero_mul]

/-- **`matBaxterU` depends only on the kernel restricted to the core `[0,σ]`.**  Since the windowed
`matBaxterU` samples `Q` only on `[0,σ]`, two kernels agreeing there give the same `matBaxterU`. 
This
bridges the compact `q0MixEntry`-seed kernel to the continuous `q0MixPoly` renewal kernel (which
coincide on `[0,σ]` at equal diameters). -/
theorem matBaxterU_core_congr (Psi K1 K2 : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hsigma : 0 ≤ sigma) (h : ∀ i k t, t ∈ Set.Icc (0 : ℝ) sigma → K1 i k t = K2 i k t)
    (i j : Fin N) (r : ℝ) :
    matBaxterU Psi K1 sigma i j r = matBaxterU Psi K2 sigma i j r := by
  unfold matBaxterU
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le hsigma] at ht
  rw [h i k t ht]

end FMSA.MixtureOzStar

namespace FMSA.HSMix

open MeasureTheory FMSA.MatrixQ0 FMSA.HardSphere FMSA.MixtureOzStar

variable {N : ℕ}

/-- **`q0MixEntry` is symmetric at equal diameters** — `R`/`λ` are `i,k`-independent (`s`/`0`), and
`Q0phys`/`Qppphys` collapse to the `i,k`-independent scalars `q'_py`/`q''_py`, so `q0MixEntry i k =
q0MixEntry k i`. -/
theorem q0MixEntry_symm_equalDiam {rho sigma : Fin N → ℝ} {s : ℝ} (hsig : ∀ k, 0 < sigma k)
    (hs : ∀ k, sigma k = s) (hs0 : 0 < s) (hvac : vacMix rho sigma ≠ 0) (i k : Fin N) :
    (physHSMixN rho sigma hsig).q0MixEntry i k = (physHSMixN rho sigma hsig).q0MixEntry k i := by
  funext t
  have hR : ∀ a b : Fin N, (physHSMixN rho sigma hsig).R a b = s := fun a b => by
    simp only [physHSMixN, FMSA.HSMix.R, hs a, hs b]; ring
  have hlam : ∀ a b : Fin N, (physHSMixN rho sigma hsig).lam a b = 0 := fun a b => by
    simp only [physHSMixN, FMSA.HSMix.lam, hs a, hs b]; ring
  have hQpp : (physHSMixN rho sigma hsig).Qpp k = (physHSMixN rho sigma hsig).Qpp i := by
    show Qppphys rho sigma k k = Qppphys rho sigma i i
    rw [Qppphys_equalDiam hs hs0 hvac k k, Qppphys_equalDiam hs hs0 hvac i i]
  have hQ0 : (physHSMixN rho sigma hsig).Q0 i k = (physHSMixN rho sigma hsig).Q0 k i := by
    show Q0phys rho sigma i k = Q0phys rho sigma k i
    simp only [Q0phys]; ring
  simp only [FMSA.HSMix.q0MixEntry, hR, hlam, hQpp, hQ0]

/-- **`q0MixEntry` vanishes off `[0,σ]` at equal diameters** — its support is `[λ,R] = [0,s]`. -/
theorem q0MixEntry_supp_equalDiam {rho sigma : Fin N → ℝ} {s : ℝ} (hsig : ∀ k, 0 < sigma k)
    (hs : ∀ k, sigma k = s) (i k : Fin N) {t : ℝ} (ht : t < 0 ∨ s < t) :
    (physHSMixN rho sigma hsig).q0MixEntry i k t = 0 := by
  have hnm : t ∉ Set.Icc ((physHSMixN rho sigma hsig).lam i k)
      ((physHSMixN rho sigma hsig).R i k) := by
    have hR : (physHSMixN rho sigma hsig).R i k = s := by
      simp only [physHSMixN, FMSA.HSMix.R, hs i, hs k]; ring
    have hlam : (physHSMixN rho sigma hsig).lam i k = 0 := by
      simp only [physHSMixN, FMSA.HSMix.lam, hs i, hs k]; ring
    rw [hR, hlam, Set.mem_Icc, not_and, not_le]
    intro h0; rcases ht with h | h
    · linarith
    · exact h
  simp only [FMSA.HSMix.q0MixEntry, Set.indicator_of_notMem hnm]

/-- **⭐⭐⭐ The two-kernel `ρ_k`-weighted EXTENDED seed reduces to `r·c_HS` at equal diameters.**  The
capstone for the extended seed: the two-kernel `ρ`-weighted extended seed (compact `q0MixEntry`
factor, constructed `ρ`-weighted renewal `physHSMixNPsiW`) equals `r·c_HS` at equal diameters. 
Chain:
`matBaxterUQmSymFullExtRho_eq_matBaxterUQm_colScale` (equal-diam collapse to the `ρ`-weighted
windowed
seed via the transpose bridge; `q0MixEntry` symmetric + supported at equal σ) →
`matBaxterUQm_eq_rcHS_
of_rowSum`, with `hUouter`/`hint` bridged from the compact `q0MixEntry` kernel to the continuous
`q0MixPolyMatW` renewal kernel (they coincide on `[0,σ]`, all `matBaxterU` samples) — the SAME two
kernels the extended seed reconciles.  Only physical-data hypotheses remain. -/
theorem matBaxterUQmSymFullExtRho_physHSMix_eq_rcHS {rho sigma : Fin N → ℝ} {s : ℝ}
    (hsig : ∀ k, 0 < sigma k) (hs : ∀ k, sigma k = s) (hs0 : 0 < s)
    (hvac : vacMix rho sigma ≠ 0) (hetalt : etaMix rho sigma < 1)
    {r : ℝ} (hr : 0 < r) (i j : Fin N) :
    matBaxterUQmSymFullExtRho (physHSMixNPsiW rho sigma hsig s)
      (fun a b => (physHSMixN rho sigma hsig).q0MixEntry a b) rho i j r
      = r * c_HS (etaMix rho sigma) s r := by
  set Kpoly : Matrix (Fin N) (Fin N) (ℝ → ℝ) :=
    fun a b => fun t => (q0MixPolyMatW (physHSMixN rho sigma hsig) t) a b with hKp
  have hQ : Continuous (q0MixPolyMatW (physHSMixN rho sigma hsig)) := q0MixPolyMatW_continuous _
  have hF : Continuous (matForcingCore (q0MixPolyMatW (physHSMixN rho sigma hsig)) s) :=
    matForcingCore_continuous _ s hQ
  have hRle : ∀ a b, (physHSMixN rho sigma hsig).R a b ≤ s := fun a b => by
    simp only [physHSMixN, FMSA.HSMix.R, hs a, hs b]; linarith
  have hetadef : etaMix rho sigma = Real.pi * (∑ k, rho k) * s ^ 3 / 6 := by
    have hsum : (∑ k, rho k * sigma k ^ 3) = (∑ k, rho k) * s ^ 3 := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun k _ => by rw [hs k])
    simp only [etaMix, hsum]; ring
  -- kernels coincide on the core `[0,s]`
  have hrhoeq : (physHSMixN rho sigma hsig).ρ = rho := rfl
  have hagree : ∀ (a b : Fin N) (t : ℝ), t ∈ Set.Icc (0 : ℝ) s →
      (colScaleK rho (fun a b => (physHSMixN rho sigma hsig).q0MixEntry a b)) a b t
        = Kpoly a b t := by
    intro a b t ht
    simp only [colScaleK, hKp, q0MixPolyMatW, Matrix.of_apply, hrhoeq]
    rw [q0MixPoly_eq_q0MixEntry_core hsig hs a b ht]
  rw [matBaxterUQmSymFullExtRho_eq_matBaxterUQm_colScale (physHSMixNPsiW rho sigma hsig s)
      (fun a b => (physHSMixN rho sigma hsig).q0MixEntry a b) rho s hs0
      (fun i' k' t ht => q0MixEntry_supp_equalDiam hsig hs i' k' ht)
      (fun i' k' => q0MixEntry_symm_equalDiam hsig hs hs0 hvac i' k') i j r]
  refine matBaxterUQm_eq_rcHS_of_rowSum (physHSMixNPsiW rho sigma hsig s)
    (colScaleK rho (fun a b => (physHSMixN rho sigma hsig).q0MixEntry a b)) hs0 hetalt hetadef
    ?_ ?_ ?_ ?_ ?_ ?_ hr i j
  · -- hUouter (bridge to the continuous q0MixPolyMatW renewal)
    intro i' j' r' hr'
    rw [matBaxterU_core_congr (physHSMixNPsiW rho sigma hsig s) _ Kpoly s hs0.le hagree i' j' r']
    exact matBaxterPsi_hUouter s hs0 (q0MixPolyMatW (physHSMixN rho sigma hsig))
      (matForcingCore (q0MixPolyMatW (physHSMixN rho sigma hsig)) s) hQ hF
      (fun v hv a b => q0MixPolyMatW_eq_zero_of_ge _ a b (le_trans (hRle a b) hv))
      (fun a b _ _ => by simp only [matForcingCore, Matrix.of_apply]) i' j' hr'
  · -- hint (bridge to the continuous kernel on the core via congr_uIoo)
    intro i' j' k' r'
    refine (matBaxterPsi_hint s hs0.le (q0MixPolyMatW (physHSMixN rho sigma hsig))
      (matForcingCore (q0MixPolyMatW (physHSMixN rho sigma hsig)) s) hQ hF
      i' k' j' r').congr_uIoo (fun t ht => ?_)
    have htmem : t ∈ Set.Icc (0 : ℝ) s :=
      Set.Ioo_subset_Icc_self (Set.uIoo_of_le hs0.le ▸ ht)
    rw [hagree i' k' t htmem, matBaxterU_core_congr (physHSMixNPsiW rho sigma hsig s) _ Kpoly s
      hs0.le hagree k' j' (r' + t)]
    simp only [hKp, physHSMixNPsiW]
  · -- hrow
    intro i' u hu
    simpa only [colScaleK, hrhoeq] using physHSMixN_rhoWeighted_rowSum hsig hs hs0 hvac i' u hu
  · -- hQ0
    intro i' k
    show IntervalIntegrable
      (fun t => rho k * (physHSMixN rho sigma hsig).q0MixEntry i' k t) volume 0 s
    exact (FMSA.HSMix.q0MixEntry_intervalIntegrable (physHSMixN rho sigma hsig) i' k 0 s).const_mul
      (rho k)
  · -- hQ1
    intro i' k
    have heq : (fun t => t * (colScaleK rho
        (fun a b => (physHSMixN rho sigma hsig).q0MixEntry a b)) i' k t)
        = fun t => rho k * (t * (physHSMixN rho sigma hsig).q0MixEntry i' k t) := by
      funext t; simp only [colScaleK]; ring
    rw [heq]
    exact (FMSA.HSMix.q0MixEntry_mul_id_intervalIntegrable (physHSMixN rho sigma hsig) i' k 0 s
      ).const_mul (rho k)
  · -- hcore
    intro k j' v hv
    exact matBaxterPsi_core _ _ k j' hv

end FMSA.HSMix

