/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/
import Mathlib
import LeanCode.HSMixture.HSMixWindowingBridge
import LeanCode.HSMixture.HSMixBaxterFactor
import LeanCode.HSMixture.MixtureSeedExtended
import LeanCode.HSMixture.PhysHSMix

/-!
# Physical HS-mixture windowing loss — constructed renewal + windowing-sum theorems (Yukawa-free)

The pure-HS instantiation of the seed-coupled windowing-loss bridges at the **physical** mixture
`physHSMix`/`physHSMixN`: the constructed Banach–Volterra renewal `physHSMix(N)Psiouter` (from the
continuous `q0MixPoly` kernel + `matForcingCore`), the integrability discharge for that renewal, the
hint-free `_of_cont` bridges, and the capstone windowing-sum theorems `physHSMix_windowing_sum`
(N=2) / `physHSMixN_windowing_sum` (general N) — the fold-kernel `Ĉ₀` windowing loss.

All Yukawa-free: the generic seed/renewal machinery lives at the HSMixture layer
(`MixtureSeedExtended`, `MixtureOzStar`), the structural facts on `HSMix` (`HSMixWindowing`,
`HSMixWindowingBridge`), and the physical mixture is `physHSMix`/`physHSMixN` (`PhysHSMix`).  The
Yukawa `Mix`-layer copies (`MixtureHSDCFFin1.lean`) delegate here through `toHSMix` /
`physMix.toHSMix = physHSMix`.
-/

set_option linter.style.longLine false

open MeasureTheory Set FMSA.MixtureOzStar

namespace FMSA.HSMix

variable {N : ℕ}

/-! ### The renewal kernel `q0MixPoly` (un-windowed Baxter polynomial, clamped at `Rᵢⱼ`) -/

/-- The `q0MixPoly` kernel `X.Q0ᵢⱼ·(min r Rᵢⱼ − Rᵢⱼ) + X.Qppⱼ·(min r Rᵢⱼ − Rᵢⱼ)²/2`. -/
noncomputable def q0MixPoly (X : FMSA.HSMix N) (i j : Fin N) (r : ℝ) : ℝ :=
  X.Q0 i j * (min r (X.R i j) - X.R i j)
    + X.Qpp j * (min r (X.R i j) - X.R i j) ^ 2 / 2

theorem q0MixPoly_continuous (X : FMSA.HSMix N) (i j : Fin N) :
    Continuous (X.q0MixPoly i j) := by
  unfold q0MixPoly; fun_prop

/-- `q0MixPoly X i j r = 0` for `r ≥ Rᵢⱼ` (the clamp freezes at `Rᵢⱼ`, quadratic `= 0` there). -/
theorem q0MixPoly_eq_zero_of_ge (X : FMSA.HSMix N) (i j : Fin N) {r : ℝ} (hr : X.R i j ≤ r) :
    X.q0MixPoly i j r = 0 := by
  simp only [q0MixPoly, min_eq_right hr, sub_self, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div, add_zero]

/-- The `q0MixPoly` matrix kernel `Qm r := (q0MixPoly X i j r)ᵢⱼ`. -/
noncomputable def q0MixPolyMat (X : FMSA.HSMix N) : ℝ → Matrix (Fin N) (Fin N) ℝ :=
  fun r => Matrix.of (fun i j => X.q0MixPoly i j r)

theorem q0MixPolyMat_continuous (X : FMSA.HSMix N) : Continuous X.q0MixPolyMat :=
  continuous_matrix (fun i j => by
    simp only [q0MixPolyMat, Matrix.of_apply]; exact q0MixPoly_continuous X i j)

/-! ### Integrability discharge for the constructed renewal -/

/-- **Full-line integrability of `q0MixEntry·g`** for any measurable `g` bounded on the support. -/
theorem q0MixEntry_mul_integrable (X : FMSA.HSMix N) (i k : Fin N) (g : ℝ → ℝ)
    (hg : Measurable g) {D : ℝ} (hgbdd : ∀ t ∈ Set.Icc (X.lam i k) (X.R i k), |g t| ≤ D) :
    Integrable (fun t => X.q0MixEntry i k t * g t) := by
  obtain ⟨C, hC0, hC⟩ := q0MixEntry_abs_le X i k
  have hsupp : Function.support (fun t => X.q0MixEntry i k t * g t)
      ⊆ Set.Icc (X.lam i k) (X.R i k) := fun t ht =>
    X.q0MixEntry_support_subset i k
      (Function.mem_support.mpr (left_ne_zero_of_mul (Function.mem_support.mp ht)))
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  refine Measure.integrableOn_of_bounded (M := C * max D 0) measure_Icc_lt_top.ne
    ((q0MixEntry_measurable X i k).mul hg).aestronglyMeasurable ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hC t) (le_trans (hgbdd t ht) (le_max_left _ _)) (abs_nonneg _) hC0

/-- **`hint` discharged for the constructed renewal `matBaxterPsi`.**  For continuous outer/core
data `Po,Pc`, `q0MixEntry X i k · matBaxterPsi Po Pc σ k j (r−·)` is integrable. -/
theorem q0MixEntry_matBaxterPsi_integrable (X : FMSA.HSMix N)
    (Po Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hPo : ∀ a b, Continuous (Po a b)) (hPc : ∀ a b, Continuous (Pc a b))
    (i k j : Fin N) (r : ℝ) :
    Integrable (fun t => X.q0MixEntry i k t * matBaxterPsi Po Pc sigma k j (r - t)) := by
  have hg : Measurable (fun t => matBaxterPsi Po Pc sigma k j (r - t)) :=
    (matBaxterPsi_entry_measurable Po Pc sigma (fun a b => (hPo a b).measurable)
      (fun a b => (hPc a b).measurable) k j).comp (measurable_const.sub measurable_id)
  obtain ⟨D, hD⟩ := matBaxterPsi_entry_bddOn Po Pc sigma hPo hPc k j
    (r - X.R i k) (r - X.lam i k)
  refine q0MixEntry_mul_integrable X i k _ hg (D := D) (fun t ht => ?_)
  rw [Set.mem_Icc] at ht
  exact hD (r - t) (Set.mem_uIcc.mpr (Or.inl ⟨by linarith [ht.2], by linarith [ht.1]⟩))

/-- Decoupled integrability with the kernel indices `(a,b)` independent of the `Ψ` indices `(p,q)`
(needed for the transposed arm). -/
theorem q0MixEntry_matBaxterPsi_integrable_gen (X : FMSA.HSMix N)
    (Po Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ)
    (hPo : ∀ a b, Continuous (Po a b)) (hPc : ∀ a b, Continuous (Pc a b))
    (a b p q : Fin N) (r : ℝ) :
    Integrable (fun t => X.q0MixEntry a b t * matBaxterPsi Po Pc sigma p q (r - t)) := by
  have hg : Measurable (fun t => matBaxterPsi Po Pc sigma p q (r - t)) :=
    (matBaxterPsi_entry_measurable Po Pc sigma (fun c d => (hPo c d).measurable)
      (fun c d => (hPc c d).measurable) p q).comp (measurable_const.sub measurable_id)
  obtain ⟨D, hD⟩ := matBaxterPsi_entry_bddOn Po Pc sigma hPo hPc p q
    (r - X.R a b) (r - X.lam a b)
  refine q0MixEntry_mul_integrable X a b _ hg (D := D) (fun t ht => ?_)
  rw [Set.mem_Icc] at ht
  exact hD (r - t) (Set.mem_uIcc.mpr (Or.inl ⟨by linarith [ht.2], by linarith [ht.1]⟩))

/-! ### Hint-free windowing bridges (constructed renewal `Ψ = matBaxterPsi Po Pc σ`) -/

/-- Smallest-species bridge, integrability discharged: NO windowing loss. -/
theorem matBaxterUExt_eq_matBaxterU_smallest_of_cont (X : FMSA.HSMix N)
    (Po Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma)
    (hPo : ∀ a b, Continuous (Po a b)) (hPc : ∀ a b, Continuous (Pc a b))
    (i j : Fin N) (r : ℝ) (hlam : ∀ k, 0 ≤ X.lam i k) (hRsigC : ∀ k, X.R i k ≤ sigma) :
    matBaxterUExt (matBaxterPsi Po Pc sigma) (fun a b => X.q0MixEntry a b) i j r
      = matBaxterU (matBaxterPsi Po Pc sigma) (fun a b => X.q0MixEntry a b) sigma i j r :=
  matBaxterUExt_eq_matBaxterU_of_row_lam_nonneg X (matBaxterPsi Po Pc sigma) sigma hsig0 i j r
    hlam hRsigC (fun k => q0MixEntry_matBaxterPsi_integrable X Po Pc sigma hPo hPc i k j r)

/-- Largest-species bridge, integrability discharged: EXPLICIT polynomial-moment loss. -/
theorem matBaxterUExt_sub_polyTail_of_cont (X : FMSA.HSMix N)
    (Po Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma)
    (hPo : ∀ a b, Continuous (Po a b)) (hPc : ∀ a b, Continuous (Pc a b))
    (i j : Fin N) (r : ℝ) (hlam : ∀ k, X.lam i k ≤ 0) (hRsigC : ∀ k, X.R i k ≤ sigma) :
    matBaxterUExt (matBaxterPsi Po Pc sigma) (fun a b => X.q0MixEntry a b) i j r
      = matBaxterU (matBaxterPsi Po Pc sigma) (fun a b => X.q0MixEntry a b) sigma i j r
        - ∑ k, ∫ t in (X.lam i k)..(0:ℝ),
            (X.Q0 i k * (t - X.R i k) + X.Qpp k * (t - X.R i k) ^ 2 / 2)
              * matBaxterPsi Po Pc sigma k j (r - t) :=
  matBaxterUExt_eq_matBaxterU_sub_polyTail X (matBaxterPsi Po Pc sigma) sigma hsig0 i j r
    hlam hRsigC (fun k => q0MixEntry_matBaxterPsi_integrable X Po Pc sigma hPo hPc i k j r)

/-- Transposed arm, hint-free (largest species): NO loss. -/
theorem matBaxterUtExt_eq_matBaxterUt_of_cont (X : FMSA.HSMix N)
    (Po Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma)
    (hPo : ∀ a b, Continuous (Po a b)) (hPc : ∀ a b, Continuous (Pc a b))
    (i j : Fin N) (r : ℝ) (hlam : ∀ k, 0 ≤ X.lam k i) (hRsigC : ∀ k, X.R k i ≤ sigma) :
    matBaxterUtExt (matBaxterPsi Po Pc sigma) (fun a b => X.q0MixEntry a b) i j r
      = matBaxterUt (matBaxterPsi Po Pc sigma) (fun a b => X.q0MixEntry a b) sigma i j r :=
  matBaxterUtExt_eq_matBaxterUt_of_row X (matBaxterPsi Po Pc sigma) sigma hsig0 i j r hlam hRsigC
    (fun k => q0MixEntry_matBaxterPsi_integrable_gen X Po Pc sigma hPo hPc k i k j r)

/-- Transposed arm, hint-free (smallest species): EXPLICIT loss. -/
theorem matBaxterUtExt_sub_polyTail_of_cont (X : FMSA.HSMix N)
    (Po Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma)
    (hPo : ∀ a b, Continuous (Po a b)) (hPc : ∀ a b, Continuous (Pc a b))
    (i j : Fin N) (r : ℝ) (hlam : ∀ k, X.lam k i ≤ 0) (hRsigC : ∀ k, X.R k i ≤ sigma) :
    matBaxterUtExt (matBaxterPsi Po Pc sigma) (fun a b => X.q0MixEntry a b) i j r
      = matBaxterUt (matBaxterPsi Po Pc sigma) (fun a b => X.q0MixEntry a b) sigma i j r
        - ∑ k, ∫ t in (X.lam k i)..(0:ℝ),
            (X.Q0 k i * (t - X.R k i) + X.Qpp i * (t - X.R k i) ^ 2 / 2)
              * matBaxterPsi Po Pc sigma k j (r - t) :=
  matBaxterUtExt_eq_matBaxterUt_sub_polyTail X (matBaxterPsi Po Pc sigma) sigma hsig0 i j r hlam hRsigC
    (fun k => q0MixEntry_matBaxterPsi_integrable_gen X Po Pc sigma hPo hPc k i k j r)

/-- Symmetric-kernel windowing loss, hint-free: the two arms' losses sum to the symmetrized tail. -/
theorem windowing_loss_sum_eq_symTail_of_cont (X : FMSA.HSMix N)
    (Po Pc : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (sigma : ℝ) (hsig0 : 0 ≤ sigma)
    (hPo : ∀ a b, Continuous (Po a b)) (hPc : ∀ a b, Continuous (Pc a b))
    (i j : Fin N) (r : ℝ) (hRun : ∀ k, X.R i k ≤ sigma) (hRt : ∀ k, X.R k i ≤ sigma) :
    (matBaxterU (matBaxterPsi Po Pc sigma) (fun a b => X.q0MixEntry a b) sigma i j r
       - matBaxterUExt (matBaxterPsi Po Pc sigma) (fun a b => X.q0MixEntry a b) i j r)
    + (matBaxterUt (matBaxterPsi Po Pc sigma) (fun a b => X.q0MixEntry a b) sigma i j r
       - matBaxterUtExt (matBaxterPsi Po Pc sigma) (fun a b => X.q0MixEntry a b) i j r)
    = ∑ k, ∫ t in Set.Iic (0:ℝ),
        (X.q0MixEntry i k t + X.q0MixEntry k i t) * matBaxterPsi Po Pc sigma k j (r - t) :=
  windowing_loss_sum_eq_symTail X (matBaxterPsi Po Pc sigma) sigma hsig0 i j r hRun hRt
    (fun k => q0MixEntry_matBaxterPsi_integrable_gen X Po Pc sigma hPo hPc i k k j r)
    (fun k => q0MixEntry_matBaxterPsi_integrable_gen X Po Pc sigma hPo hPc k i k j r)

/-! ### N=2 physical instantiation at `σ = max diameter` — the binary-mixture windowing loss -/

/-- Constructed Banach–Volterra outer renewal for the physical binary `physHSMix` at the seed scale
`σ = max(σ₀,σ₁)` (from the continuous `q0MixPoly` kernel + `matForcingCore`). -/
noncomputable def physHSMixPsiouter (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) :
    Matrix (Fin 2) (Fin 2) (ℝ → ℝ) :=
  fun a b r => (matBaxterPsiOuterFun (max (sigma 0) (sigma 1))
    (q0MixPolyMat (physHSMix rho sigma hsig))
    (matForcingCore (q0MixPolyMat (physHSMix rho sigma hsig)) (max (sigma 0) (sigma 1)))
    (q0MixPolyMat_continuous (physHSMix rho sigma hsig))
    (matForcingCore_continuous (q0MixPolyMat (physHSMix rho sigma hsig)) (max (sigma 0) (sigma 1))
      (q0MixPolyMat_continuous (physHSMix rho sigma hsig))) r) a b

theorem physHSMixPsiouter_continuous (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (a b : Fin 2) : Continuous (physHSMixPsiouter rho sigma hsig a b) := by
  unfold physHSMixPsiouter
  exact (matBaxterPsiOuterFun_continuous _ _ _ _ _).matrix_elem a b

theorem physHSMix_R_le_max (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i k : Fin 2) :
    (physHSMix rho sigma hsig).R i k ≤ max (sigma 0) (sigma 1) := by
  simp only [physHSMix, FMSA.HSMix.R]
  have hi : sigma i ≤ max (sigma 0) (sigma 1) := by fin_cases i <;> simp [le_max_left, le_max_right]
  have hk : sigma k ≤ max (sigma 0) (sigma 1) := by fin_cases k <;> simp [le_max_left, le_max_right]
  linarith

/-- **N=2 physical windowing loss — smallest species (σ = max diameter): NO loss.** -/
theorem physHSMix_windowing_smallest (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i j : Fin 2) (r : ℝ) (hsmall : ∀ k, sigma i ≤ sigma k) :
    matBaxterUExt (matBaxterPsi (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1)))
        (fun a b => (physHSMix rho sigma hsig).q0MixEntry a b) i j r
      = matBaxterU (matBaxterPsi (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1)))
        (fun a b => (physHSMix rho sigma hsig).q0MixEntry a b) (max (sigma 0) (sigma 1)) i j r := by
  refine matBaxterUExt_eq_matBaxterU_smallest_of_cont (physHSMix rho sigma hsig)
    (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v) (max (sigma 0) (sigma 1))
    (le_of_lt (lt_of_lt_of_le (hsig 0) (le_max_left _ _)))
    (physHSMixPsiouter_continuous rho sigma hsig) (fun _ _ => continuous_neg) i j r
    (fun k => by simp only [physHSMix, FMSA.HSMix.lam]; linarith [hsmall k])
    (physHSMix_R_le_max rho sigma hsig i)

/-- **N=2 physical windowing loss — largest species (σ = max diameter): EXPLICIT loss.** -/
theorem physHSMix_windowing_largest (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i j : Fin 2) (r : ℝ) (hlarge : ∀ k, sigma k ≤ sigma i) :
    matBaxterUExt (matBaxterPsi (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1)))
        (fun a b => (physHSMix rho sigma hsig).q0MixEntry a b) i j r
      = matBaxterU (matBaxterPsi (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1)))
        (fun a b => (physHSMix rho sigma hsig).q0MixEntry a b) (max (sigma 0) (sigma 1)) i j r
        - ∑ k, ∫ t in ((physHSMix rho sigma hsig).lam i k)..(0:ℝ),
            ((physHSMix rho sigma hsig).Q0 i k * (t - (physHSMix rho sigma hsig).R i k)
              + (physHSMix rho sigma hsig).Qpp k * (t - (physHSMix rho sigma hsig).R i k) ^ 2 / 2)
              * matBaxterPsi (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v)
                  (max (sigma 0) (sigma 1)) k j (r - t) := by
  refine matBaxterUExt_sub_polyTail_of_cont (physHSMix rho sigma hsig)
    (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v) (max (sigma 0) (sigma 1))
    (le_of_lt (lt_of_lt_of_le (hsig 0) (le_max_left _ _)))
    (physHSMixPsiouter_continuous rho sigma hsig) (fun _ _ => continuous_neg) i j r
    (fun k => by simp only [physHSMix, FMSA.HSMix.lam]; linarith [hlarge k])
    (physHSMix_R_le_max rho sigma hsig i)

/-- **N=2 physical transposed arm — largest species: NO loss.** -/
theorem physHSMix_windowing_t_largest (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i j : Fin 2) (r : ℝ) (hlarge : ∀ k, sigma k ≤ sigma i) :
    matBaxterUtExt (matBaxterPsi (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1)))
        (fun a b => (physHSMix rho sigma hsig).q0MixEntry a b) i j r
      = matBaxterUt (matBaxterPsi (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1)))
        (fun a b => (physHSMix rho sigma hsig).q0MixEntry a b) (max (sigma 0) (sigma 1)) i j r := by
  refine matBaxterUtExt_eq_matBaxterUt_of_cont (physHSMix rho sigma hsig)
    (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v) (max (sigma 0) (sigma 1))
    (le_of_lt (lt_of_lt_of_le (hsig 0) (le_max_left _ _)))
    (physHSMixPsiouter_continuous rho sigma hsig) (fun _ _ => continuous_neg) i j r
    (fun k => by simp only [physHSMix, FMSA.HSMix.lam]; linarith [hlarge k])
    (fun k => physHSMix_R_le_max rho sigma hsig k i)

/-- **N=2 physical transposed arm — smallest species: EXPLICIT loss.** -/
theorem physHSMix_windowing_t_smallest (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k)
    (i j : Fin 2) (r : ℝ) (hsmall : ∀ k, sigma i ≤ sigma k) :
    matBaxterUtExt (matBaxterPsi (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1)))
        (fun a b => (physHSMix rho sigma hsig).q0MixEntry a b) i j r
      = matBaxterUt (matBaxterPsi (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1)))
        (fun a b => (physHSMix rho sigma hsig).q0MixEntry a b) (max (sigma 0) (sigma 1)) i j r
        - ∑ k, ∫ t in ((physHSMix rho sigma hsig).lam k i)..(0:ℝ),
            ((physHSMix rho sigma hsig).Q0 k i * (t - (physHSMix rho sigma hsig).R k i)
              + (physHSMix rho sigma hsig).Qpp i * (t - (physHSMix rho sigma hsig).R k i) ^ 2 / 2)
              * matBaxterPsi (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v)
                  (max (sigma 0) (sigma 1)) k j (r - t) := by
  refine matBaxterUtExt_sub_polyTail_of_cont (physHSMix rho sigma hsig)
    (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v) (max (sigma 0) (sigma 1))
    (le_of_lt (lt_of_lt_of_le (hsig 0) (le_max_left _ _)))
    (physHSMixPsiouter_continuous rho sigma hsig) (fun _ _ => continuous_neg) i j r
    (fun k => by simp only [physHSMix, FMSA.HSMix.lam]; linarith [hsmall k])
    (fun k => physHSMix_R_le_max rho sigma hsig k i)

/-- **N=2 physical symmetric-kernel windowing loss (σ = max diameter).**  The two arms' losses sum
to the symmetrized `q0MixEntry` sub-zero tail — the fold-kernel `Ĉ₀` windowing loss. -/
theorem physHSMix_windowing_sum (rho sigma : Fin 2 → ℝ) (hsig : ∀ k, 0 < sigma k) (i j : Fin 2)
    (r : ℝ) :
    (matBaxterU (matBaxterPsi (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1))) (fun a b => (physHSMix rho sigma hsig).q0MixEntry a b)
        (max (sigma 0) (sigma 1)) i j r
       - matBaxterUExt (matBaxterPsi (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1))) (fun a b => (physHSMix rho sigma hsig).q0MixEntry a b) i j r)
    + (matBaxterUt (matBaxterPsi (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1))) (fun a b => (physHSMix rho sigma hsig).q0MixEntry a b)
        (max (sigma 0) (sigma 1)) i j r
       - matBaxterUtExt (matBaxterPsi (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v)
        (max (sigma 0) (sigma 1))) (fun a b => (physHSMix rho sigma hsig).q0MixEntry a b) i j r)
    = ∑ k, ∫ t in Set.Iic (0:ℝ),
        ((physHSMix rho sigma hsig).q0MixEntry i k t + (physHSMix rho sigma hsig).q0MixEntry k i t)
          * matBaxterPsi (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v)
              (max (sigma 0) (sigma 1)) k j (r - t) :=
  windowing_loss_sum_eq_symTail_of_cont (physHSMix rho sigma hsig)
    (physHSMixPsiouter rho sigma hsig) (fun _ _ v => -v) (max (sigma 0) (sigma 1))
    (le_of_lt (lt_of_lt_of_le (hsig 0) (le_max_left _ _)))
    (physHSMixPsiouter_continuous rho sigma hsig) (fun _ _ => continuous_neg) i j r
    (fun k => physHSMix_R_le_max rho sigma hsig i k)
    (fun k => physHSMix_R_le_max rho sigma hsig k i)

/-! ### General-N (N≥3) physical symmetric-kernel windowing loss -/

/-- Constructed Banach–Volterra outer renewal for the general-N physical `physHSMixN` at a seed
scale `sigmax` bounding every diameter. -/
noncomputable def physHSMixNPsiouter (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (sigmax : ℝ) : Matrix (Fin N) (Fin N) (ℝ → ℝ) :=
  fun a b r => (matBaxterPsiOuterFun sigmax (q0MixPolyMat (physHSMixN rho sigma hsig))
    (matForcingCore (q0MixPolyMat (physHSMixN rho sigma hsig)) sigmax)
    (q0MixPolyMat_continuous (physHSMixN rho sigma hsig))
    (matForcingCore_continuous (q0MixPolyMat (physHSMixN rho sigma hsig)) sigmax
      (q0MixPolyMat_continuous (physHSMixN rho sigma hsig))) r) a b

theorem physHSMixNPsiouter_continuous (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (sigmax : ℝ) (a b : Fin N) : Continuous (physHSMixNPsiouter rho sigma hsig sigmax a b) := by
  unfold physHSMixNPsiouter
  exact (matBaxterPsiOuterFun_continuous _ _ _ _ _).matrix_elem a b

theorem physHSMixN_R_le (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k) (sigmax : ℝ)
    (hsigmax : ∀ k, sigma k ≤ sigmax) (i k : Fin N) :
    (physHSMixN rho sigma hsig).R i k ≤ sigmax := by
  simp only [physHSMixN, FMSA.HSMix.R]; linarith [hsigmax i, hsigmax k]

/-- **General-N (N≥3) physical symmetric-kernel windowing loss.**  For `physHSMixN` (any `N`) with
the constructed renewal at a seed scale `sigmax` bounding every diameter, on ANY row the two arms'
losses sum to the symmetrized `q0MixEntry` sub-zero tail. -/
theorem physHSMixN_windowing_sum (rho sigma : Fin N → ℝ) (hsig : ∀ k, 0 < sigma k)
    (sigmax : ℝ) (hpos : 0 ≤ sigmax) (hsigmax : ∀ k, sigma k ≤ sigmax) (i j : Fin N) (r : ℝ) :
    (matBaxterU (matBaxterPsi (physHSMixNPsiouter rho sigma hsig sigmax) (fun _ _ v => -v) sigmax)
        (fun a b => (physHSMixN rho sigma hsig).q0MixEntry a b) sigmax i j r
       - matBaxterUExt (matBaxterPsi (physHSMixNPsiouter rho sigma hsig sigmax)
        (fun _ _ v => -v) sigmax)
        (fun a b => (physHSMixN rho sigma hsig).q0MixEntry a b) i j r)
    + (matBaxterUt (matBaxterPsi (physHSMixNPsiouter rho sigma hsig sigmax) (fun _ _ v => -v)
        sigmax)
        (fun a b => (physHSMixN rho sigma hsig).q0MixEntry a b) sigmax i j r
       - matBaxterUtExt (matBaxterPsi (physHSMixNPsiouter rho sigma hsig sigmax)
        (fun _ _ v => -v) sigmax)
        (fun a b => (physHSMixN rho sigma hsig).q0MixEntry a b) i j r)
    = ∑ k, ∫ t in Set.Iic (0:ℝ),
        ((physHSMixN rho sigma hsig).q0MixEntry i k t
          + (physHSMixN rho sigma hsig).q0MixEntry k i t)
          * matBaxterPsi (physHSMixNPsiouter rho sigma hsig sigmax) (fun _ _ v => -v) sigmax
              k j (r - t) :=
  windowing_loss_sum_eq_symTail_of_cont (physHSMixN rho sigma hsig)
    (physHSMixNPsiouter rho sigma hsig sigmax) (fun _ _ v => -v) sigmax hpos
    (physHSMixNPsiouter_continuous rho sigma hsig sigmax) (fun _ _ => continuous_neg) i j r
    (fun k => physHSMixN_R_le rho sigma hsig sigmax hsigmax i k)
    (fun k => physHSMixN_R_le rho sigma hsig sigmax hsigmax k i)

/-! ### Explicit closed form of the Lebowitz Baxter-quadratic poly moments (MIXCHS.4 ingredients)

The unequal-diameter windowing loss (MIXCHS.3) is a sum of poly moments of the Lebowitz Baxter
quadratic `Q0·(t−R) + Qpp·(t−R)²/2`.  Each such moment has an **explicit closed form** — pure
calculus, no OZ solution.  These are the ingredients of the classical Lebowitz `c_ij` value; the
full assembly (`= r·c_ij` via the matrix Wertheim–Thiele moment identity, without the
equal-diameter row-collapse) is the remaining open part of MIXCHS.4. -/

/-- **Definite integral of the Lebowitz Baxter quadratic** — the antiderivative
`Q0·(t−R)²/2 + Qpp·(t−R)³/6`, evaluated by the FTC. -/
theorem baxterQuad_integral (Q0 Qpp R a b : ℝ) :
    (∫ t in a..b, Q0 * (t - R) + Qpp * (t - R) ^ 2 / 2)
      = Q0 * ((b - R) ^ 2 - (a - R) ^ 2) / 2 + Qpp * ((b - R) ^ 3 - (a - R) ^ 3) / 6 := by
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt
      (fun s => Q0 * (s - R) ^ 2 / 2 + Qpp * (s - R) ^ 3 / 6)
      (Q0 * (t - R) + Qpp * (t - R) ^ 2 / 2) t := by
    intro t _
    have hb : HasDerivAt (fun s : ℝ => s - R) 1 t := (hasDerivAt_id t).sub_const R
    have h2 : HasDerivAt (fun s => Q0 * (s - R) ^ 2 / 2) (Q0 * (t - R)) t := by
      have e : Q0 * (t - R) = Q0 * ((2:ℕ) * (t - R) ^ (2 - 1) * 1) / 2 := by push_cast; ring
      rw [e]; exact ((hb.pow 2).const_mul Q0).div_const 2
    have h3 : HasDerivAt (fun s => Qpp * (s - R) ^ 3 / 6) (Qpp * (t - R) ^ 2 / 2) t := by
      have e : Qpp * (t - R) ^ 2 / 2 = Qpp * ((3:ℕ) * (t - R) ^ (3 - 1) * 1) / 6 := by
        push_cast; ring
      rw [e]; exact ((hb.pow 3).const_mul Qpp).div_const 6
    exact h2.add h3
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) a b)]
  ring

/-- Support ordering `λᵢₖ ≤ Rᵢₖ` (`Rᵢₖ − λᵢₖ = σᵢ > 0`). -/
theorem lam_le_R (X : FMSA.HSMix N) (i k : Fin N) : X.lam i k ≤ X.R i k := by
  simp only [FMSA.HSMix.lam, FMSA.HSMix.R]; linarith [X.hsigma i]

/-- **The Baxter-factor mass (M0) over its support `[λᵢₖ, Rᵢₖ]`, in closed form.** -/
theorem q0MixEntry_baxterMoment (X : FMSA.HSMix N) (i k : Fin N) :
    (∫ t in (X.lam i k)..(X.R i k), X.q0MixEntry i k t)
      = -(X.Q0 i k * (X.lam i k - X.R i k) ^ 2 / 2
          + X.Qpp k * (X.lam i k - X.R i k) ^ 3 / 6) := by
  have hcongr : (∫ t in (X.lam i k)..(X.R i k), X.q0MixEntry i k t)
      = ∫ t in (X.lam i k)..(X.R i k),
          X.Q0 i k * (t - X.R i k) + X.Qpp k * (t - X.R i k) ^ 2 / 2 := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (lam_le_R X i k), Set.mem_Icc] at ht
    exact q0MixEntry_inner_expand X i k (Set.mem_Icc.mpr ht)
  rw [hcongr, baxterQuad_integral]; ring

/-- **The sub-zero windowing-loss mass (`g = 1` poly moment) over `[λᵢₖ, 0]`, in closed form** — the
explicit value the larger-species windowing loss carries against a constant test function. -/
theorem q0MixEntry_subZeroTail_mass (X : FMSA.HSMix N) (i k : Fin N) (hlam : X.lam i k ≤ 0) :
    (∫ t in Set.Iic (0:ℝ), X.q0MixEntry i k t)
      = X.Q0 i k * ((0 - X.R i k) ^ 2 - (X.lam i k - X.R i k) ^ 2) / 2
        + X.Qpp k * ((0 - X.R i k) ^ 3 - (X.lam i k - X.R i k) ^ 3) / 6 := by
  have hint : Integrable (fun t => X.q0MixEntry i k t * (1:ℝ)) :=
    q0MixEntry_mul_integrable X i k (fun _ => (1:ℝ)) measurable_const (D := 1)
      (fun t _ => by norm_num)
  have h := q0MixEntry_subZeroTail_poly X i k (fun _ => (1:ℝ)) hlam hint
  simp only [mul_one] at h
  rw [h, baxterQuad_integral]

/-- **`t`-weighted definite integral of the Lebowitz Baxter quadratic** — the cubic `t·(Q0(t−R) +
Qpp(t−R)²/2)` integrated by the FTC (antiderivative in shifted `(t−R)` form). -/
theorem baxterQuad1_integral (Q0 Qpp R a b : ℝ) :
    (∫ t in a..b, t * (Q0 * (t - R) + Qpp * (t - R) ^ 2 / 2))
      = (Q0 * (b - R) ^ 3 / 3 + Q0 * R * (b - R) ^ 2 / 2 + Qpp * (b - R) ^ 4 / 8
          + Qpp * R * (b - R) ^ 3 / 6)
        - (Q0 * (a - R) ^ 3 / 3 + Q0 * R * (a - R) ^ 2 / 2 + Qpp * (a - R) ^ 4 / 8
          + Qpp * R * (a - R) ^ 3 / 6) := by
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt
      (fun s => Q0 * (s - R) ^ 3 / 3 + Q0 * R * (s - R) ^ 2 / 2 + Qpp * (s - R) ^ 4 / 8
        + Qpp * R * (s - R) ^ 3 / 6)
      (t * (Q0 * (t - R) + Qpp * (t - R) ^ 2 / 2)) t := by
    intro t _
    have hb : HasDerivAt (fun s : ℝ => s - R) 1 t := (hasDerivAt_id t).sub_const R
    have d3 := ((hb.pow 3).const_mul Q0).div_const 3
    have d2 := ((hb.pow 2).const_mul (Q0 * R)).div_const 2
    have d4 := ((hb.pow 4).const_mul Qpp).div_const 8
    have d3b := ((hb.pow 3).const_mul (Qpp * R)).div_const 6
    have e : t * (Q0 * (t - R) + Qpp * (t - R) ^ 2 / 2)
        = Q0 * ((3:ℕ) * (t - R) ^ (3 - 1) * 1) / 3 + Q0 * R * ((2:ℕ) * (t - R) ^ (2 - 1) * 1) / 2
          + Qpp * ((4:ℕ) * (t - R) ^ (4 - 1) * 1) / 8
          + Qpp * R * ((3:ℕ) * (t - R) ^ (3 - 1) * 1) / 6 := by push_cast; ring
    rw [e]; exact ((d3.add d2).add d4).add d3b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) a b)]

/-- **The `t`-weighted Baxter-factor moment (M1) over its support `[λᵢₖ, Rᵢₖ]`, in closed form.** -/
theorem q0MixEntry_baxterMoment1 (X : FMSA.HSMix N) (i k : Fin N) :
    (∫ t in (X.lam i k)..(X.R i k), t * X.q0MixEntry i k t)
      = -(X.Q0 i k * (X.lam i k - X.R i k) ^ 3 / 3
          + X.Q0 i k * X.R i k * (X.lam i k - X.R i k) ^ 2 / 2
          + X.Qpp k * (X.lam i k - X.R i k) ^ 4 / 8
          + X.Qpp k * X.R i k * (X.lam i k - X.R i k) ^ 3 / 6) := by
  have hcongr : (∫ t in (X.lam i k)..(X.R i k), t * X.q0MixEntry i k t)
      = ∫ t in (X.lam i k)..(X.R i k),
          t * (X.Q0 i k * (t - X.R i k) + X.Qpp k * (t - X.R i k) ^ 2 / 2) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (lam_le_R X i k), Set.mem_Icc] at ht
    rw [q0MixEntry_inner_expand X i k (Set.mem_Icc.mpr ht)]
  rw [hcongr, baxterQuad1_integral]; ring

/-- **Affine moment of the Baxter factor** — `∫ (A + B·t)·q0MixEntry = A·M0 + B·M1` (linearity), the
form the seed's coupling integrand `Qᵢₖ·((r+t)(S0ₖ−1) − S1ₖ)` takes.  With `q0MixEntry_baxterMoment`
(M0) and `_baxterMoment1` (M1) this is fully explicit. -/
theorem q0MixEntry_affineMoment (X : FMSA.HSMix N) (i k : Fin N) (A B : ℝ) :
    (∫ t in (X.lam i k)..(X.R i k), (A + B * t) * X.q0MixEntry i k t)
      = A * (∫ t in (X.lam i k)..(X.R i k), X.q0MixEntry i k t)
        + B * (∫ t in (X.lam i k)..(X.R i k), t * X.q0MixEntry i k t) := by
  have hi0 := q0MixEntry_intervalIntegrable X i k (X.lam i k) (X.R i k)
  have hi1 := q0MixEntry_mul_id_intervalIntegrable X i k (X.lam i k) (X.R i k)
  rw [← intervalIntegral.integral_const_mul A, ← intervalIntegral.integral_const_mul B,
    ← intervalIntegral.integral_add (hi0.const_mul A) (hi1.const_mul B)]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  ring

/-! ### Windowed moments and the `σ−r` truncation — the assembly bridges

The seed's moment expression (`matBaxterUQm_coreSeed_moment`) uses the *windowed* moments `∫₀^σ` and
the truncated coupling `∫₀^{σ−r}`.  These reduce to the explicit support moments (M0/M1/affine) plus
sub-zero-tail corrections, via the support `q0MixEntry ⊆ [λᵢₖ, Rᵢₖ]`. -/

/-- **Full-line = support-interval.**  `∫_ℝ q0MixEntry·g = ∫_{λᵢₖ}^{Rᵢₖ} q0MixEntry·g` (support
containment; needs no integrability — off-support the integrand is `0`). -/
theorem q0MixEntry_fullLine_mul (X : FMSA.HSMix N) (i k : Fin N) (g : ℝ → ℝ) :
    (∫ t, X.q0MixEntry i k t * g t)
      = ∫ t in (X.lam i k)..(X.R i k), X.q0MixEntry i k t * g t := by
  rw [intervalIntegral.integral_of_le (lam_le_R X i k),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => ?_)).symm
  have hq : X.q0MixEntry i k t = 0 := by
    by_contra hqne
    exact ht (X.q0MixEntry_support_subset i k (Function.mem_support.mpr hqne))
  rw [hq, zero_mul]

/-- **Windowed / deep-core-truncated integral = full support − sub-zero tail** (any upper bound
`b ≥ Rᵢₖ`).  Covers the windowed moment (`b = σ`) and the deep-core coupling truncation
(`b = σ−r ≥ R`); both RHS terms are explicit (support moment `−` sub-zero-tail moment). -/
theorem q0MixEntry_boundedIntegral_split (X : FMSA.HSMix N) (i k : Fin N) (g : ℝ → ℝ) {b : ℝ}
    (hb0 : 0 ≤ b) (hRb : X.R i k ≤ b)
    (hint : Integrable (fun t => X.q0MixEntry i k t * g t)) :
    (∫ t in (0:ℝ)..b, X.q0MixEntry i k t * g t)
      = (∫ t in (X.lam i k)..(X.R i k), X.q0MixEntry i k t * g t)
        - ∫ t in Set.Iic (0:ℝ), X.q0MixEntry i k t * g t := by
  have hs := q0MixEntry_intSplit X i k g b hb0 hRb hint
  rw [q0MixEntry_fullLine_mul X i k g] at hs
  linarith [hs]

/-- **Shallow-core truncation, larger species (`λᵢₖ ≤ 0`).**  For `0 ≤ b ≤ Rᵢₖ`, on `[0,b] ⊆ [λ,R]`
the kernel is the bare quadratic, so `∫₀^b q0MixEntry·g = ∫₀^b (poly)·g` — the truncated coupling
made explicit (for affine `g`, via `baxterQuad`/`baxterQuad1`). -/
theorem q0MixEntry_truncIntegral_poly (X : FMSA.HSMix N) (i k : Fin N) (g : ℝ → ℝ) {b : ℝ}
    (hlam : X.lam i k ≤ 0) (hb0 : 0 ≤ b) (hbR : b ≤ X.R i k) :
    (∫ t in (0:ℝ)..b, X.q0MixEntry i k t * g t)
      = ∫ t in (0:ℝ)..b,
          (X.Q0 i k * (t - X.R i k) + X.Qpp k * (t - X.R i k) ^ 2 / 2) * g t := by
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le hb0, Set.mem_Icc] at ht
  rw [q0MixEntry_inner_expand X i k
    (Set.mem_Icc.mpr ⟨le_trans hlam ht.1, le_trans ht.2 hbR⟩)]

/-- **Shallow-core truncation, smallest species (`λᵢₖ ≥ 0`).**  For `λ ≤ b ≤ Rᵢₖ`, the `[0,λ)` part
is below the support (contributes `0`; the `{λ}` endpoint is null), so `∫₀^b q0MixEntry·g = ∫_λ^b
(poly)·g` — explicit for affine `g`.  Completes the `σ−r` truncation over all species/regimes. -/
theorem q0MixEntry_truncIntegral_poly_smallest (X : FMSA.HSMix N) (i k : Fin N) (g : ℝ → ℝ) {b : ℝ}
    (hlam : 0 ≤ X.lam i k) (hlb : X.lam i k ≤ b) (hbR : b ≤ X.R i k)
    (hint : Integrable (fun t => X.q0MixEntry i k t * g t)) :
    (∫ t in (0:ℝ)..b, X.q0MixEntry i k t * g t)
      = ∫ t in (X.lam i k)..b,
          (X.Q0 i k * (t - X.R i k) + X.Qpp k * (t - X.R i k) ^ 2 / 2) * g t := by
  have hlow : (∫ t in (0:ℝ)..(X.lam i k), X.q0MixEntry i k t * g t) = 0 := by
    rw [intervalIntegral.integral_of_le hlam]
    refine MeasureTheory.integral_eq_zero_of_ae ?_
    have hne : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) (X.lam i k))), t ≠ X.lam i k :=
      ae_restrict_of_ae (by simpa [MeasureTheory.ae_iff] using measure_singleton (X.lam i k))
    filter_upwards [hne, ae_restrict_mem measurableSet_Ioc] with t htne htmem
    have hlt : t < X.lam i k := lt_of_le_of_ne htmem.2 htne
    have hq : X.q0MixEntry i k t = 0 := by
      by_contra hqe
      exact absurd (X.q0MixEntry_support_subset i k (Function.mem_support.mpr hqe)).1
        (not_le.mpr hlt)
    simp [hq]
  have hcut := intervalIntegral.integral_add_adjacent_intervals
    (a := (0:ℝ)) (b := X.lam i k) (c := b) hint.intervalIntegrable hint.intervalIntegrable
  rw [hlow, zero_add] at hcut
  rw [← hcut]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le hlb, Set.mem_Icc] at ht
  rw [q0MixEntry_inner_expand X i k (Set.mem_Icc.mpr ⟨ht.1, le_trans ht.2 hbR⟩)]

/-- **The truncated coupling integral `∫ₐᵇ poly·(A+B·t)`, explicit** — a quadratic against a linear,
i.e. a cubic; `= A·M0[a,b] + B·M1[a,b]` via `baxterQuad`/`baxterQuad1`.  With a variable upper bound
`b = σ−r` this is a **quartic in `r`**, the origin of the cubic `c_ij` (the `σ−r` truncation, not
the `r`-linear affine coefficient, carries the higher-order `r`-dependence — the "deep core"
`σ−r ≥ R` is empty at equal diameters). -/
theorem baxterQuadAffine_integral (A B Q0 Qpp R a b : ℝ) :
    (∫ t in a..b, (A + B * t) * (Q0 * (t - R) + Qpp * (t - R) ^ 2 / 2))
      = A * (Q0 * ((b - R) ^ 2 - (a - R) ^ 2) / 2 + Qpp * ((b - R) ^ 3 - (a - R) ^ 3) / 6)
        + B * ((Q0 * (b - R) ^ 3 / 3 + Q0 * R * (b - R) ^ 2 / 2 + Qpp * (b - R) ^ 4 / 8
                + Qpp * R * (b - R) ^ 3 / 6)
              - (Q0 * (a - R) ^ 3 / 3 + Q0 * R * (a - R) ^ 2 / 2 + Qpp * (a - R) ^ 4 / 8
                + Qpp * R * (a - R) ^ 3 / 6)) := by
  have hlin : (∫ t in a..b, (A + B * t) * (Q0 * (t - R) + Qpp * (t - R) ^ 2 / 2))
      = A * (∫ t in a..b, Q0 * (t - R) + Qpp * (t - R) ^ 2 / 2)
        + B * (∫ t in a..b, t * (Q0 * (t - R) + Qpp * (t - R) ^ 2 / 2)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) a b)
        (Continuous.intervalIntegrable (by fun_prop) a b)]
    refine intervalIntegral.integral_congr (fun t _ => ?_); ring
  rw [hlin, baxterQuad_integral, baxterQuad1_integral]

/-! ### Collecting `cMixMomentDCF` — the `q0MixPolyMat` renewal-kernel moments, piecewise at `b = R`

The physical grand assembly `matBaxterUQm_physMix_eq_rc` uses the `q0MixPolyMat`
(clamped-polynomial) kernel, so `cMixMomentDCF`'s integrals are `∫₀^b q0MixPoly·(affine)`.  Since
`q0MixPoly = poly` for `t ≤ R` (clamp inactive) and `= 0` for `t ≥ R`, each reduces to a
**bare-poly** integral — `∫₀^b poly` (shallow `b ≤ R`) or `∫₀^R poly` (full `b ≥ R`) — which
`baxterQuadAffine`
evaluates to an explicit polynomial.  The `b = R` breakpoint (i.e. `r = σ − R`) is exactly where the
piecewise `c_ij` switches. -/

/-- `q0MixPoly = the bare Baxter quadratic` for `r ≤ Rᵢₖ` (the `min` clamp is inactive). -/
theorem q0MixPoly_eq_poly_of_le (X : FMSA.HSMix N) (i k : Fin N) {r : ℝ} (hr : r ≤ X.R i k) :
    X.q0MixPoly i k r = X.Q0 i k * (r - X.R i k) + X.Qpp k * (r - X.R i k) ^ 2 / 2 := by
  simp only [q0MixPoly, min_eq_left hr]

/-- **Shallow renewal-kernel moment (`b ≤ R`).**  `∫₀^b q0MixPoly·(A+B·t) = ∫₀^b poly·(A+B·t)` — the
clamp is inactive on `[0,b]`; `baxterQuadAffine_integral` then gives the explicit polynomial. -/
theorem q0MixPoly_affineInt_le (X : FMSA.HSMix N) (i k : Fin N) (A B : ℝ) {b : ℝ}
    (hb0 : 0 ≤ b) (hbR : b ≤ X.R i k) :
    (∫ t in (0:ℝ)..b, (A + B * t) * X.q0MixPoly i k t)
      = ∫ t in (0:ℝ)..b,
          (A + B * t) * (X.Q0 i k * (t - X.R i k) + X.Qpp k * (t - X.R i k) ^ 2 / 2) := by
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le hb0, Set.mem_Icc] at ht
  rw [q0MixPoly_eq_poly_of_le X i k (le_trans ht.2 hbR)]

/-- **Full renewal-kernel moment (`b ≥ R`).**  `∫₀^b q0MixPoly·(A+B·t) = ∫₀^R poly·(A+B·t)` — the
clamp kills `[R,b]`; the upper limit freezes at `R` (so the `σ−r`-truncated coupling is `r`-constant
once `σ−r ≥ R`).  `baxterQuadAffine_integral` gives the explicit polynomial. -/
theorem q0MixPoly_affineInt_ge (X : FMSA.HSMix N) (i k : Fin N) (A B : ℝ) {b : ℝ}
    (hRb : X.R i k ≤ b) (hR0 : 0 ≤ X.R i k) :
    (∫ t in (0:ℝ)..b, (A + B * t) * X.q0MixPoly i k t)
      = ∫ t in (0:ℝ)..(X.R i k),
          (A + B * t) * (X.Q0 i k * (t - X.R i k) + X.Qpp k * (t - X.R i k) ^ 2 / 2) := by
  have hcont : Continuous (fun t => (A + B * t) * X.q0MixPoly i k t) :=
    (continuous_const.add (continuous_const.mul continuous_id)).mul (q0MixPoly_continuous X i k)
  have h1 : IntervalIntegrable (fun t => (A + B * t) * X.q0MixPoly i k t) volume 0 (X.R i k) :=
    hcont.intervalIntegrable 0 (X.R i k)
  have h2 : IntervalIntegrable (fun t => (A + B * t) * X.q0MixPoly i k t) volume (X.R i k) b :=
    hcont.intervalIntegrable (X.R i k) b
  have hhi : (∫ t in (X.R i k)..b, (A + B * t) * X.q0MixPoly i k t) = 0 := by
    rw [show (∫ t in (X.R i k)..b, (A + B * t) * X.q0MixPoly i k t)
        = ∫ _t in (X.R i k)..b, (0:ℝ) from ?_, intervalIntegral.integral_zero]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le hRb, Set.mem_Icc] at ht
    rw [q0MixPoly_eq_zero_of_ge X i k ht.1, mul_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, hhi, add_zero]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le hR0, Set.mem_Icc] at ht
  rw [q0MixPoly_eq_poly_of_le X i k ht.2]

/-- **Explicit windowed row-moment `M0`** — `∫₀^b q0MixPoly = −Q0ᵢₖ·Rᵢₖ²/2 + Qppₖ·Rᵢₖ³/6`
(`b ≥ Rᵢₖ`).  The `r`-independent constant in `cMixMomentDCF`'s leading term `r·(∑ₖM0−1) − ∑ₖM1`. -/
theorem q0MixPoly_windowM0 (X : FMSA.HSMix N) (i k : Fin N) {b : ℝ}
    (hRb : X.R i k ≤ b) (hR0 : 0 ≤ X.R i k) :
    (∫ t in (0:ℝ)..b, X.q0MixPoly i k t)
      = -(X.Q0 i k * (X.R i k) ^ 2 / 2) + X.Qpp k * (X.R i k) ^ 3 / 6 := by
  have h := q0MixPoly_affineInt_ge X i k 1 0 hRb hR0
  simp only [zero_mul, add_zero, one_mul] at h
  rw [h, baxterQuad_integral]; ring

/-- **Explicit windowed row-moment `M1`** — `∫₀^b t·q0MixPoly = −Q0ᵢₖ·Rᵢₖ³/6 + Qppₖ·Rᵢₖ⁴/24`
(`b ≥ Rᵢₖ`). -/
theorem q0MixPoly_windowM1 (X : FMSA.HSMix N) (i k : Fin N) {b : ℝ}
    (hRb : X.R i k ≤ b) (hR0 : 0 ≤ X.R i k) :
    (∫ t in (0:ℝ)..b, t * X.q0MixPoly i k t)
      = -(X.Q0 i k * (X.R i k) ^ 3 / 6) + X.Qpp k * (X.R i k) ^ 4 / 24 := by
  have h := q0MixPoly_affineInt_ge X i k 0 1 hRb hR0
  simp only [zero_add, one_mul] at h
  rw [h, baxterQuad1_integral]; ring

end FMSA.HSMix
