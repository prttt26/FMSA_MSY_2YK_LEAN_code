/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.Closures.ClosureExpansions
import LeanCode.YukawaOZMix.SpectralAmplitude
import LeanCode.YukawaOZMix.MixtureRealSpace
import LeanCode.Analysis.RadialFourierInversion
import LeanCode.HardSphere.BaxterWienerHopfComplex
import LeanCode.HardSphere.BaxterNoSpinodalEquiv
import LeanCode.HSMixture.MixtureNoSpinodal
import LeanCode.YukawaOZMix.MixtureDCFAEInjective

/-!
# The DP first-order-closure solution map  (Group PYE.2–PYE.7)

The **core-bound half** of the non-FMSA closure development (split from the dependency-free
closure definitions, `Closures/ClosureExpansions.lean`).  The doubly-propagated (DP) first-order
solution map `Ĉ₁ = Q̂₀·B₁·Q̂₀ᵀ` is linear in the outer closure (PYE.2); the DCF error equals the
DP map applied to the fit residual (PYE.3); the exact first-order-PY comparison and the `N=1`
PY-Baxter identification (PYE.4); the `k → r` real-space bridge (PYE.5); the density of finite
Yukawa-tail fits (PYE.7).  Builds on the closure definitions plus the FMSA core (`SpectralAmplitude`,
`MixtureRealSpace`, radial Fourier inversion, Baxter Wiener–Hopf, no-spinodal).
-/

set_option linter.style.longLine false

open Filter Topology FourierTransform
open scoped Matrix

namespace FMSA.FirstOrderClosure

/-! ## PYE.2 — the DP first-order solution map is linear in the outer closure

Stage 1 (outer transform, Y1.2), stage 2 (WH projection, Y1.3/Y1.5) and stage 3 ((★), MRS.3) are
each linear; the composite is bundled as `dpDCFLinear` / `dpTailsLinear`.
-/

/-- Stage 1 — the outer Yukawa transform of [LN] Eq. 46 as a function of the amplitude:
`U₁(k) = K·e^{−ikR}/(ik+z)`.  `OuterDCF.outerDCF_transform` (Y1.2) proves this **is** the half-line
integral `∫_R^∞ K e^{−z(r−R)} e^{−ikr} dr`; here we only need that it is linear in `K`. -/
noncomputable def outerTransform (z k R : ℝ) (K : ℂ) : ℂ :=
  K * Complex.exp (-Complex.I * k * R) / (Complex.I * k + z)

/-- Stage 1 is additive in the tail amplitude. -/
theorem outerTransform_add (z k R : ℝ) (K1 K2 : ℂ) :
    outerTransform z k R (K1 + K2) = outerTransform z k R K1 + outerTransform z k R K2 := by
  simp only [outerTransform]; ring

/-- Stage 1 is homogeneous in the tail amplitude. -/
theorem outerTransform_smul (z k R : ℝ) (c K : ℂ) :
    outerTransform z k R (c * K) = c * outerTransform z k R K := by
  simp only [outerTransform]; ring

/-- Stage 2 — the WH-projected first-order numerator `B₁` as a matrix-valued function of the Yukawa
coupling matrix `K`, i.e. Y1.5's `bMulti` read as a map `K ↦ B₁` (`Amat` is `A(z) = Q̂₀(z)⁻¹ − I`,
[LN] Eq. 70, and `zmat` the per-pair pole positions). -/
noncomputable def b1OfCoupling {N : ℕ} (Amat : Matrix (Fin N) (Fin N) ℂ)
    (zmat : Fin N → Fin N → ℂ) (s : ℂ) (Kmat : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => FMSA.SpectralAmplitude.bMulti Kmat Amat zmat s i j

@[simp] theorem b1OfCoupling_apply {N : ℕ} (Amat : Matrix (Fin N) (Fin N) ℂ)
    (zmat : Fin N → Fin N → ℂ) (s : ℂ) (Kmat : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    b1OfCoupling Amat zmat s Kmat i j = FMSA.SpectralAmplitude.bMulti Kmat Amat zmat s i j := rfl

/-- **PYE.2 (stage 2, additivity).**  `bMulti` is additive in the coupling matrix: each summand
`(I+A)_{im} K_{mp} (I+A)_{jp}/(s+z_{mp})` is. -/
theorem bMulti_add_K {N : ℕ} (K1 K2 Amat : Matrix (Fin N) (Fin N) ℂ)
    (zmat : Fin N → Fin N → ℂ) (s : ℂ) (i j : Fin N) :
    FMSA.SpectralAmplitude.bMulti (K1 + K2) Amat zmat s i j
      = FMSA.SpectralAmplitude.bMulti K1 Amat zmat s i j
        + FMSA.SpectralAmplitude.bMulti K2 Amat zmat s i j := by
  simp only [FMSA.SpectralAmplitude.bMulti, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- **PYE.2 (stage 2, homogeneity).**  `bMulti` is homogeneous in the coupling matrix. -/
theorem bMulti_smul_K {N : ℕ} (c : ℂ) (Kmat Amat : Matrix (Fin N) (Fin N) ℂ)
    (zmat : Fin N → Fin N → ℂ) (s : ℂ) (i j : Fin N) :
    FMSA.SpectralAmplitude.bMulti (c • Kmat) Amat zmat s i j
      = c * FMSA.SpectralAmplitude.bMulti Kmat Amat zmat s i j := by
  simp only [FMSA.SpectralAmplitude.bMulti, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun p _ => ?_
  ring

/-- **PYE.2 (stage 2, bundled).**  The WH projection `K ↦ B₁` is a `ℂ`-linear map. -/
noncomputable def b1OfCouplingLinear {N : ℕ} (Amat : Matrix (Fin N) (Fin N) ℂ)
    (zmat : Fin N → Fin N → ℂ) (s : ℂ) :
    Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ where
  toFun := b1OfCoupling Amat zmat s
  map_add' K1 K2 := by ext i j; simpa using bMulti_add_K K1 K2 Amat zmat s i j
  map_smul' c K := by ext i j; simpa using bMulti_smul_K c K Amat zmat s i j

@[simp] theorem b1OfCouplingLinear_apply {N : ℕ} (Amat : Matrix (Fin N) (Fin N) ℂ)
    (zmat : Fin N → Fin N → ℂ) (s : ℂ) (Kmat : Matrix (Fin N) (Fin N) ℂ) :
    b1OfCouplingLinear Amat zmat s Kmat = b1OfCoupling Amat zmat s Kmat := rfl

/-- Stage 3 — the (★) assembly `B₁ ↦ Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)` (MRS.3).  **No `Q̂₀⁻¹` appears**, which is
why the DCF carries only Yukawa poles (`star_entry_differentiableAt`). -/
noncomputable def starConjLinear {N : ℕ} (Qm : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ where
  toFun X := Qm * X * Qmᵀ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

@[simp] theorem starConjLinear_apply {N : ℕ} (Qm X : Matrix (Fin N) (Fin N) ℂ) :
    starConjLinear Qm X = Qm * X * Qmᵀ := rfl

/-- **PYE.2 — the DP first-order solution map** for one tail family: outer coupling `K` ↦ first-order
DCF `Ĉ₁ = Q̂₀(−k)·B₁(K)·Q̂₀ᵀ(−k)`.  This is the whole no-pull-back construction as a function of the
outer closure data (with the tail **rates fixed**). -/
noncomputable def dpDCF {N : ℕ} (Qm Amat : Matrix (Fin N) (Fin N) ℂ)
    (zmat : Fin N → Fin N → ℂ) (s : ℂ) (Kmat : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Qm * b1OfCoupling Amat zmat s Kmat * Qmᵀ

/-- **PYE.2 ⭐ — the DP solution map is linear in the outer closure** (fixed rates): it is the
composite of the linear stage 2 (`b1OfCouplingLinear`) and the linear stage 3 (`starConjLinear`). -/
noncomputable def dpDCFLinear {N : ℕ} (Qm Amat : Matrix (Fin N) (Fin N) ℂ)
    (zmat : Fin N → Fin N → ℂ) (s : ℂ) :
    Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ :=
  (starConjLinear Qm).comp (b1OfCouplingLinear Amat zmat s)

@[simp] theorem dpDCFLinear_apply {N : ℕ} (Qm Amat : Matrix (Fin N) (Fin N) ℂ)
    (zmat : Fin N → Fin N → ℂ) (s : ℂ) (Kmat : Matrix (Fin N) (Fin N) ℂ) :
    dpDCFLinear Qm Amat zmat s Kmat = dpDCF Qm Amat zmat s Kmat := rfl

/-- **PYE.2 — the fixed-rate multi-tail DP map.**  The outer closure is refit as `T` effective
Yukawa tails with **frozen** rates `zfam t`; the construction sums the per-tail DP maps, so it is
linear in the amplitude family `Kfam` — the `'linear'` `tail_mode` of `HNCB_FMSA_dp.py`.

⚠ With free rates this map is *not* linear (the rates enter the denominators `s + z_{mp}`); the
fixed-rate discipline is what makes PYE.3 a one-line consequence. -/
noncomputable def dpTailsLinear {N T : ℕ} (Qm Amat : Matrix (Fin N) (Fin N) ℂ)
    (zfam : Fin T → Fin N → Fin N → ℂ) (s : ℂ) :
    (Fin T → Matrix (Fin N) (Fin N) ℂ) →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ :=
  ∑ t, (dpDCFLinear Qm Amat (zfam t) s).comp
    (LinearMap.proj (R := ℂ) (φ := fun _ : Fin T => Matrix (Fin N) (Fin N) ℂ) t)

theorem dpTailsLinear_apply {N T : ℕ} (Qm Amat : Matrix (Fin N) (Fin N) ℂ)
    (zfam : Fin T → Fin N → Fin N → ℂ) (s : ℂ) (Kfam : Fin T → Matrix (Fin N) (Fin N) ℂ) :
    dpTailsLinear Qm Amat zfam s Kfam = ∑ t, dpDCF Qm Amat (zfam t) s (Kfam t) := by
  simp [dpTailsLinear, LinearMap.sum_apply]

/-! ## PYE.3 — the DCF error is the DP map applied to the fit residual

`DP[fit] − DP[exact] = DP[fit − exact]` is `map_sub`; the quantitative half is an explicit
operator bound (the task plan's `wh_solution_operator_bounded`, here **proved**).
-/

/-- **PYE.3 ⭐ (the identity).**  With exact `g_HS` and fixed rates, the DCF error of the
no-pull-back construction **equals** the DP solution map applied to the finite-Yukawa-tail *fit
residual* of the outer closure.  Formally the statement "the DP construction is exact; the sole
approximation is representing the outer closure by finitely many Yukawa tails". -/
theorem dp_error_eq_dp_of_residual {N T : ℕ} (Qm Amat : Matrix (Fin N) (Fin N) ℂ)
    (zfam : Fin T → Fin N → Fin N → ℂ) (s : ℂ)
    (Kfit Kexact : Fin T → Matrix (Fin N) (Fin N) ℂ) :
    dpTailsLinear Qm Amat zfam s Kfit - dpTailsLinear Qm Amat zfam s Kexact
      = dpTailsLinear Qm Amat zfam s (Kfit - Kexact) :=
  (map_sub (dpTailsLinear Qm Amat zfam s) Kfit Kexact).symm

/-- Entry bound for stage 2: `‖B₁(K)_{ij}‖ ≤ N²·Ab²·Kb/δ`, where `Ab` bounds the entries of
`I + A = Q̂₀(z)⁻¹`, `Kb` the coupling entries, and `δ > 0` the distance from the evaluation point `s`
to the Yukawa poles `−z_{mp}` (i.e. `δ ≤ ‖s + z_{mp}‖`). -/
theorem bMulti_entry_norm_le {N : ℕ} (Kmat Amat : Matrix (Fin N) (Fin N) ℂ)
    (zmat : Fin N → Fin N → ℂ) (s : ℂ) (i j : Fin N) {Ab Kb delta : ℝ}
    (hdelta : 0 < delta) (hden : ∀ m p, delta ≤ ‖s + zmat m p‖)
    (hA : ∀ a b, ‖(1 + Amat) a b‖ ≤ Ab) (hK : ∀ m p, ‖Kmat m p‖ ≤ Kb) :
    ‖FMSA.SpectralAmplitude.bMulti Kmat Amat zmat s i j‖ ≤ (N : ℝ) ^ 2 * (Ab ^ 2 * Kb) / delta := by
  have hAb : 0 ≤ Ab := le_trans (norm_nonneg _) (hA i i)
  have hKb : 0 ≤ Kb := le_trans (norm_nonneg _) (hK i i)
  have hterm : ∀ m p, ‖(1 + Amat) i m * Kmat m p * (1 + Amat) j p / (s + zmat m p)‖
      ≤ Ab ^ 2 * Kb / delta := by
    intro m p
    rw [norm_div, norm_mul, norm_mul]
    have h1 : ‖(1 + Amat) i m‖ * ‖Kmat m p‖ ≤ Ab * Kb :=
      mul_le_mul (hA i m) (hK m p) (norm_nonneg _) hAb
    have hnum : ‖(1 + Amat) i m‖ * ‖Kmat m p‖ * ‖(1 + Amat) j p‖ ≤ Ab ^ 2 * Kb := by
      calc ‖(1 + Amat) i m‖ * ‖Kmat m p‖ * ‖(1 + Amat) j p‖
          ≤ Ab * Kb * Ab := mul_le_mul h1 (hA j p) (norm_nonneg _) (by positivity)
        _ = Ab ^ 2 * Kb := by ring
    exact div_le_div₀ (by positivity) hnum hdelta (hden m p)
  unfold FMSA.SpectralAmplitude.bMulti
  calc ‖∑ m, ∑ p, (1 + Amat) i m * Kmat m p * (1 + Amat) j p / (s + zmat m p)‖
      ≤ ∑ m, ‖∑ p, (1 + Amat) i m * Kmat m p * (1 + Amat) j p / (s + zmat m p)‖ := norm_sum_le _ _
    _ ≤ ∑ _m : Fin N, ∑ _p : Fin N, (Ab ^ 2 * Kb / delta) := by
        refine Finset.sum_le_sum fun m _ => le_trans (norm_sum_le _ _) ?_
        exact Finset.sum_le_sum fun p _ => hterm m p
    _ = (N : ℝ) ^ 2 * (Ab ^ 2 * Kb) / delta := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Entry bound for stage 3 (the (★) conjugation): `‖(Q·X·Qᵀ)_{ij}‖ ≤ N²·Qb²·Xb`.  Uses MRS.3's
entry expansion `star_entry_eq`. -/
theorem starConj_entry_norm_le {N : ℕ} (Qm X : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) {Qb Xb : ℝ}
    (hQ : ∀ a b, ‖Qm a b‖ ≤ Qb) (hX : ∀ a b, ‖X a b‖ ≤ Xb) :
    ‖(Qm * X * Qmᵀ) i j‖ ≤ (N : ℝ) ^ 2 * (Qb ^ 2 * Xb) := by
  have hQb : 0 ≤ Qb := le_trans (norm_nonneg _) (hQ i i)
  have hXb : 0 ≤ Xb := le_trans (norm_nonneg _) (hX i i)
  have hterm : ∀ q p, ‖Qm i p * X p q * Qm j q‖ ≤ Qb ^ 2 * Xb := by
    intro q p
    rw [norm_mul, norm_mul]
    have h1 : ‖Qm i p‖ * ‖X p q‖ ≤ Qb * Xb := mul_le_mul (hQ i p) (hX p q) (norm_nonneg _) hQb
    calc ‖Qm i p‖ * ‖X p q‖ * ‖Qm j q‖
        ≤ Qb * Xb * Qb := mul_le_mul h1 (hQ j q) (norm_nonneg _) (by positivity)
      _ = Qb ^ 2 * Xb := by ring
  rw [FMSA.MixtureBaxterCore.star_entry_eq]
  calc ‖∑ q, ∑ p, Qm i p * X p q * Qm j q‖
      ≤ ∑ q, ‖∑ p, Qm i p * X p q * Qm j q‖ := norm_sum_le _ _
    _ ≤ ∑ _q : Fin N, ∑ _p : Fin N, (Qb ^ 2 * Xb) := by
        refine Finset.sum_le_sum fun q _ => le_trans (norm_sum_le _ _) ?_
        exact Finset.sum_le_sum fun p _ => hterm q p
    _ = (N : ℝ) ^ 2 * (Qb ^ 2 * Xb) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The explicit **Wiener-Hopf solution-operator bound** of the DP map: with `Qb` bounding the
entries of `Q̂₀(−k)`, `Ab` those of `Q̂₀(z)⁻¹ = I + A`, `δ` the distance to the Yukawa poles and `T`
the number of (fixed-rate) tails,
`‖DP[K]‖_∞ ≤ (T·N⁴·Qb²·Ab²/δ)·‖K‖_∞`. -/
noncomputable def whOperatorBound (N T : ℕ) (Qb Ab delta : ℝ) : ℝ :=
  (T : ℝ) * (N : ℝ) ^ 4 * Qb ^ 2 * Ab ^ 2 / delta

/-- **PYE.3 (boundedness, single tail family) — `wh_solution_operator_bounded` as a THEOREM.**  Each
entry of the DP-map output is bounded by `N⁴·Qb²·Ab²/δ` times the coupling bound.  (The task plan
listed this as a *new analytic input*; at the finite-tail level it is elementary — it becomes real
analysis only in PYE.4's function-space lift.) -/
theorem dpDCF_entry_norm_le {N : ℕ} (Qm Amat : Matrix (Fin N) (Fin N) ℂ)
    (zmat : Fin N → Fin N → ℂ) (s : ℂ) (Kmat : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N)
    {Qb Ab Kb delta : ℝ}
    (hdelta : 0 < delta) (hden : ∀ m p, delta ≤ ‖s + zmat m p‖)
    (hQ : ∀ a b, ‖Qm a b‖ ≤ Qb) (hA : ∀ a b, ‖(1 + Amat) a b‖ ≤ Ab)
    (hK : ∀ m p, ‖Kmat m p‖ ≤ Kb) :
    ‖dpDCF Qm Amat zmat s Kmat i j‖ ≤ (N : ℝ) ^ 4 * Qb ^ 2 * Ab ^ 2 * Kb / delta := by
  have hX : ∀ a b, ‖b1OfCoupling Amat zmat s Kmat a b‖ ≤ (N : ℝ) ^ 2 * (Ab ^ 2 * Kb) / delta :=
    fun a b => bMulti_entry_norm_le Kmat Amat zmat s a b hdelta hden hA hK
  have h := starConj_entry_norm_le Qm (b1OfCoupling Amat zmat s Kmat) i j hQ hX
  calc ‖dpDCF Qm Amat zmat s Kmat i j‖
      ≤ (N : ℝ) ^ 2 * (Qb ^ 2 * ((N : ℝ) ^ 2 * (Ab ^ 2 * Kb) / delta)) := h
    _ = (N : ℝ) ^ 4 * Qb ^ 2 * Ab ^ 2 * Kb / delta := by ring

/-- **PYE.3 (boundedness, fixed-rate tail family).**  Summing `T` tails multiplies the single-family
bound by `T`: `‖DP[Kfam]_{ij}‖ ≤ whOperatorBound N T Qb Ab δ · Kb`. -/
theorem dpTails_entry_norm_le {N T : ℕ} (Qm Amat : Matrix (Fin N) (Fin N) ℂ)
    (zfam : Fin T → Fin N → Fin N → ℂ) (s : ℂ) (Kfam : Fin T → Matrix (Fin N) (Fin N) ℂ)
    (i j : Fin N) {Qb Ab Kb delta : ℝ}
    (hdelta : 0 < delta) (hden : ∀ t m p, delta ≤ ‖s + zfam t m p‖)
    (hQ : ∀ a b, ‖Qm a b‖ ≤ Qb) (hA : ∀ a b, ‖(1 + Amat) a b‖ ≤ Ab)
    (hK : ∀ t m p, ‖Kfam t m p‖ ≤ Kb) :
    ‖dpTailsLinear Qm Amat zfam s Kfam i j‖ ≤ whOperatorBound N T Qb Ab delta * Kb := by
  rw [dpTailsLinear_apply, Matrix.sum_apply]
  calc ‖∑ t, dpDCF Qm Amat (zfam t) s (Kfam t) i j‖
      ≤ ∑ t, ‖dpDCF Qm Amat (zfam t) s (Kfam t) i j‖ := norm_sum_le _ _
    _ ≤ ∑ _t : Fin T, ((N : ℝ) ^ 4 * Qb ^ 2 * Ab ^ 2 * Kb / delta) := by
        refine Finset.sum_le_sum fun t _ => ?_
        exact dpDCF_entry_norm_le Qm Amat (zfam t) s (Kfam t) i j hdelta (hden t) hQ hA (hK t)
    _ = whOperatorBound N T Qb Ab delta * Kb := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          whOperatorBound]
        ring

/-- **PYE.3 ⭐⭐ — the headline.**  `‖DCF error‖ ≤ ‖WH solution operator‖ · ‖fit residual‖`: with
exact `g_HS` and fixed rates, the entire DCF error of the no-pull-back construction is controlled by
the finite-Yukawa-tail fit residual of the outer closure — **the only error source is the YK
re-approximation**. -/
theorem dp_error_entry_norm_le {N T : ℕ} (Qm Amat : Matrix (Fin N) (Fin N) ℂ)
    (zfam : Fin T → Fin N → Fin N → ℂ) (s : ℂ)
    (Kfit Kexact : Fin T → Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) {Qb Ab eps delta : ℝ}
    (hdelta : 0 < delta) (hden : ∀ t m p, delta ≤ ‖s + zfam t m p‖)
    (hQ : ∀ a b, ‖Qm a b‖ ≤ Qb) (hA : ∀ a b, ‖(1 + Amat) a b‖ ≤ Ab)
    (hres : ∀ t m p, ‖Kfit t m p - Kexact t m p‖ ≤ eps) :
    ‖(dpTailsLinear Qm Amat zfam s Kfit - dpTailsLinear Qm Amat zfam s Kexact) i j‖
      ≤ whOperatorBound N T Qb Ab delta * eps := by
  rw [dp_error_eq_dp_of_residual]
  exact dpTails_entry_norm_le Qm Amat zfam s (Kfit - Kexact) i j hdelta hden hQ hA
    (fun t m p => by simpa using hres t m p)

/-! ## PYE.3 / PYE.4 — against the **exact** first-order PY DCF

`star_of_first_order_oz` (MRS.2) characterizes *any* first-order DCF satisfying the first-order OZ
equation as `Ĉ₁ = Q̂₀(−k)·B₁·Q̂₀ᵀ(−k)`.  What makes it *PY* is that its WH datum `B₁^PY` is the
projection of the PY outer closure `g_HS·(−βu)` (PYE.1); what makes the construction *DP* is that
`B₁^fit` is the same projection of the finite-tail fit (Y1.5 `bMulti`).  So the two differ only
through their WH data — which is the precise form of "the only error is the YK re-approximation".
-/

/-- **PYE.3 (physical form) — DCF error = (★) assembly of the WH-datum residual.**  Let `C1py` be the
exact first-order PY DCF (characterized through MRS.2's hypotheses with WH datum `B1py`), and let
`B1fit` be the WH datum of the finite-tail construction.  Then
`DP[fit] − C₁^PY = Q̂₀(−k)·(B₁^fit − B₁^PY)·Q̂₀ᵀ(−k)`. -/
theorem dp_sub_py_first_order_eq_conj_residual {N : ℕ}
    (Qp Qm T0 S0 H1 C1py B1py B1fit : Matrix (Fin N) (Fin N) ℂ)
    (hoz : H1 * T0 = S0 * C1py) (hTS : T0 * S0 = 1)
    (hfact : T0 = Qp * Qmᵀ) (hT0symm : T0ᵀ = T0)
    (hB1 : B1py = Qpᵀ * H1 * Qp) :
    starConjLinear Qm B1fit - C1py = starConjLinear Qm (B1fit - B1py) := by
  have hpy : C1py = Qm * B1py * Qmᵀ :=
    FMSA.MixtureBaxterCore.star_of_first_order_oz Qp Qm T0 S0 H1 C1py B1py hoz hTS hfact hT0symm hB1
  rw [map_sub]
  simp only [starConjLinear_apply]
  rw [← hpy]

/-- **PYE.4 (exact-fit case).**  A finite-tail fit that is exact *in WH data* reproduces the first
order of the OZ+PY solution exactly — `DP-map[g_HS·(−βu)] = (OZ+PY)₁`.  (The content of PYE.4 is
that such a `B₁^PY` exists for the non-Yukawa outer closure; see `TailFitWHConvergent` below.) -/
theorem dp_eq_py_first_order_of_exact_fit {N : ℕ}
    (Qp Qm T0 S0 H1 C1py B1py B1fit : Matrix (Fin N) (Fin N) ℂ)
    (hoz : H1 * T0 = S0 * C1py) (hTS : T0 * S0 = 1)
    (hfact : T0 = Qp * Qmᵀ) (hT0symm : T0ᵀ = T0)
    (hB1 : B1py = Qpᵀ * H1 * Qp) (hexact : B1fit = B1py) :
    starConjLinear Qm B1fit = C1py := by
  subst hexact
  have h := dp_sub_py_first_order_eq_conj_residual Qp Qm T0 S0 H1 C1py B1fit B1fit hoz hTS hfact
    hT0symm hB1
  rw [sub_self, map_zero] at h
  exact sub_eq_zero.mp h

/-- **Non-vacuity of the MRS.2 hypothesis cluster** that every physical-form theorem above carries
(`hoz`, `hTS`, `hfact`, `hT0symm`, `hB1`).  Five simultaneous matrix equations are easy to state and
easy to make unsatisfiable; without a witness `dp_sub_py_first_order_eq_conj_residual`,
`dp_eq_py_first_order_of_exact_fit` and `dp_tendsto_py_first_order` would all be vacuously true.

The witness is **non-degenerate on purpose**: `Qm ≠ 1` and `C₁^PY ≠ 0`, so the cluster is not being
satisfied merely at the trivial `Q̂₀ = I` (dilute) point where `Ĉ₀ = 0`.  It is the general pattern
`T₀ = Q·Qᵀ`, `S₀ = T₀⁻¹`, `C₁ = Q·B₁·Qᵀ`, `H₁ = (Qᵀ)⁻¹·B₁·Q⁻¹` at `Q = !![2]` — note `hT0symm` is
*automatic* whenever `Qp = Qm` (`(Q·Qᵀ)ᵀ = Q·Qᵀ`), which is why the physical MRS.7 route has to work
for the genuinely distinct `Q̂₀(k)`, `Q̂₀(−k)`. -/
example : ∃ (Qp Qm T0 S0 H1 C1py B1py : Matrix (Fin 1) (Fin 1) ℂ),
    H1 * T0 = S0 * C1py ∧ T0 * S0 = 1 ∧ T0 = Qp * Qmᵀ ∧ T0ᵀ = T0 ∧
      B1py = Qpᵀ * H1 * Qp ∧ C1py ≠ 0 ∧ Qm ≠ 1 := by
  refine ⟨!![2], !![2], !![4], !![1/4], !![1/4], !![4], !![1], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i; fin_cases j; norm_num [Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; norm_num [Matrix.mul_apply, Matrix.one_apply]
  · ext i j; fin_cases i; fin_cases j; norm_num [Matrix.mul_apply]
  · ext i j; fin_cases i; fin_cases j; norm_num
  · ext i j; fin_cases i; fin_cases j; norm_num [Matrix.mul_apply]
  · intro hc; have := congrFun (congrFun hc 0) 0; norm_num at this
  · intro hc; have := congrFun (congrFun hc 0) 0; norm_num [Matrix.one_apply] at this

/-- **PYE.4 — the remaining input, as a hypothesis (not an axiom).**  `TailFitWHConvergent` says a
family of finite-tail WH data converges (entrywise, along a filter `l`) to the WH datum of the exact
PY outer closure.  This is the **function-space lift**: the exact outer closure `g_HS·(−βu)` is not a
finite Yukawa sum, so its WH projection lives in an `L¹`/`L²` completion of the finite-pole class.
Deliberately a `Prop` rather than an axiom (the `MixRDFInnerCollapse` discipline): held as a
hypothesis it is discharged only by an actual approximating family. -/
def TailFitWHConvergent {N : ℕ} {ι : Type*} (l : Filter ι)
    (B1fam : ι → Matrix (Fin N) (Fin N) ℂ) (B1py : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ p q, Tendsto (fun n => B1fam n p q) l (𝓝 (B1py p q))

/-- The (★) assembly is entrywise continuous in its WH datum (a finite sum of products). -/
theorem dpDCF_entry_tendsto {N : ℕ} {ι : Type*} {l : Filter ι} (Qm : Matrix (Fin N) (Fin N) ℂ)
    {B1fam : ι → Matrix (Fin N) (Fin N) ℂ} {B1lim : Matrix (Fin N) (Fin N) ℂ}
    (h : TailFitWHConvergent l B1fam B1lim) (i j : Fin N) :
    Tendsto (fun n => (starConjLinear Qm (B1fam n)) i j) l (𝓝 ((starConjLinear Qm B1lim) i j)) := by
  simp only [starConjLinear_apply, FMSA.MixtureBaxterCore.star_entry_eq]
  refine tendsto_finsetSum _ fun q _ => tendsto_finsetSum _ fun p _ => ?_
  exact ((h p q).const_mul (Qm i p)).mul_const (Qm j q)

/-- **PYE.4 (limit half) ⭐ — the finite-tail construction converges to the exact first-order PY
DCF.**  If the finite-tail WH data converge to the PY one, the DP DCFs converge entrywise to
`(OZ+PY)₁`.  Together with `dp_error_entry_norm_le` (the quantitative rate in terms of the fit
residual) this is the abstract equivalence `DP-map[g_HS·(−βu)] = (OZ+PY)₁`, modulo the existence of
`B₁^PY` — the function-space lift left as the hypothesis `TailFitWHConvergent`. -/
theorem dp_tendsto_py_first_order {N : ℕ} {ι : Type*} {l : Filter ι}
    (Qp Qm T0 S0 H1 C1py B1py : Matrix (Fin N) (Fin N) ℂ)
    {B1fam : ι → Matrix (Fin N) (Fin N) ℂ}
    (hoz : H1 * T0 = S0 * C1py) (hTS : T0 * S0 = 1)
    (hfact : T0 = Qp * Qmᵀ) (hT0symm : T0ᵀ = T0)
    (hB1 : B1py = Qpᵀ * H1 * Qp)
    (hconv : TailFitWHConvergent l B1fam B1py) (i j : Fin N) :
    Tendsto (fun n => (starConjLinear Qm (B1fam n)) i j) l (𝓝 (C1py i j)) := by
  have hpy : C1py = Qm * B1py * Qmᵀ :=
    FMSA.MixtureBaxterCore.star_of_first_order_oz Qp Qm T0 S0 H1 C1py B1py hoz hTS hfact hT0symm hB1
  have h := dpDCF_entry_tendsto Qm hconv i j
  rwa [starConjLinear_apply, ← hpy] at h

/-! ## PYE.5 — the `k → r` bridge: from the k-space identity to the real-space inner core

Everything above lives in **k space**: the objects are the matrices `Ĉ₁(k)`.  The physical claim
"the inner-core DCF of the construction is the first-order PY one" is a statement about `c₁(r)` on
`0 < r < R`.  This section closes that gap with the project's own radial Fourier inversion
(`Analysis/RadialFourierInversion.lean`, `radial_inversion` — a **theorem**, not the MA.9 axiom that
was once contemplated for it).

Three steps: transform injectivity (`radial_fourier_injective`), the k-space ⇄ real-space dictionary
for one species pair (`IsRadialEntry`, `radial_fourier_eq_of_entry_eq`), and the core statement
(`inner_core_dcf_eq_of_khat_eq`, and the PYE.4 capstone `inner_core_dcf_eq_of_exact_fit`).

⚠ **Why the statement is on the *open* core `(0,R)` and not on `[0,∞)`.**  The DCF **jumps at
contact** `r = R` (`JumpAsymptotic.lean`), and `radial_inversion` needs continuity at the evaluation
point — the documented trap that `radial_inversion_antideriv` exists for.  Inside the core the
FMSA-DP closed form is `C⁰` (its only breakpoint there is the `λ_ij` kink, IB.9/MRS.4), so the
continuity hypotheses are discharge-able exactly where the theorem is stated.

⚠ **No real-space *error* bound is claimed** (only the exact-fit / equal-transform statement).
Turning PYE.3's k-space bound into a bound on `c₁(r)` would need `k·Ĉ₁(k)` integrable, and
`whOperatorBound` is uniform in `k`: with `δ ~ ‖k‖` at large real `k` the entry bound decays like
`1/k`, so `k·Ĉ₁(k)` is `O(1)` — not integrable.  A real-space error bound needs a *weighted*
k-space estimate, which is not in Group PYE. -/

/-- **PYE.5 (core analysis) — the radial transform is injective on inversion-admissible functions.**
Two real radial functions with the same radial (sine) transform agree at every `r > 0` at which both
satisfy `radial_inversion`'s hypotheses.  Both sides are the *same* inversion integral. -/
theorem radial_fourier_injective (c1 c2 : ℝ → ℝ)
    (hEq : ∀ k, FMSA.HardSphere.radial_fourier c1 k = FMSA.HardSphere.radial_fourier c2 k)
    (hint1 : MeasureTheory.Integrable (fun v => ((v * c1 |v| : ℝ) : ℂ)))
    (hF1 : MeasureTheory.Integrable (𝓕 (fun v => ((v * c1 |v| : ℝ) : ℂ))))
    (hint2 : MeasureTheory.Integrable (fun v => ((v * c2 |v| : ℝ) : ℂ)))
    (hF2 : MeasureTheory.Integrable (𝓕 (fun v => ((v * c2 |v| : ℝ) : ℂ))))
    {r : ℝ} (hr0 : 0 < r)
    (hc1 : ContinuousAt (fun v => ((v * c1 |v| : ℝ) : ℂ)) r)
    (hc2 : ContinuousAt (fun v => ((v * c2 |v| : ℝ) : ℂ)) r) :
    c1 r = c2 r := by
  have h1 := radial_inversion c1 (FMSA.HardSphere.radial_fourier c1) (fun _ => rfl) hint1 hF1 hr0 hc1
  have h2 := radial_inversion c2 (FMSA.HardSphere.radial_fourier c1) (fun k => hEq k) hint2 hF2 hr0 hc2
  rw [h1, h2]

/-- **The k-space ⇄ real-space dictionary for one species pair.**  `IsRadialEntry Chat a i j c` says
the `(i,j)` entry of the k-space DCF matrix is the density-scaled radial transform of the real-space
`c` — the convention `Ĉ_{ij}(k) = a·𝓕_r[c_{ij}](k)` with `a = √(ρ_iρ_j)` ([LN] Eq. 46's prefactor).
Kept as an explicit hypothesis rather than a definition of `Ĉ₁`: the PYE theorems characterize `Ĉ₁`
axiomatically (through the OZ/WH equations), so the convention is the consumer's to supply. -/
def IsRadialEntry {N : ℕ} (Chat : ℝ → Matrix (Fin N) (Fin N) ℂ) (a : ℂ) (i j : Fin N)
    (c : ℝ → ℝ) : Prop :=
  ∀ k : ℝ, Chat k i j = a * ((FMSA.HardSphere.radial_fourier c k : ℝ) : ℂ)

/-- Equal k-space matrices ⇒ equal radial transforms (cancel the nonzero density prefactor). -/
theorem radial_fourier_eq_of_entry_eq {N : ℕ} {Chat1 Chat2 : ℝ → Matrix (Fin N) (Fin N) ℂ}
    {a : ℂ} (ha : a ≠ 0) {i j : Fin N} {c1 c2 : ℝ → ℝ}
    (h1 : IsRadialEntry Chat1 a i j c1) (h2 : IsRadialEntry Chat2 a i j c2)
    (hEq : ∀ k : ℝ, Chat1 k = Chat2 k) (k : ℝ) :
    FMSA.HardSphere.radial_fourier c1 k = FMSA.HardSphere.radial_fourier c2 k := by
  have h : a * ((FMSA.HardSphere.radial_fourier c1 k : ℝ) : ℂ)
      = a * ((FMSA.HardSphere.radial_fourier c2 k : ℝ) : ℂ) := by
    rw [← h1 k, ← h2 k, hEq k]
  exact_mod_cast mul_left_cancel₀ ha h

/-- **PYE.5 ⭐ — the inner-core statement.**  If the two first-order k-space DCFs agree as matrices
at every real `k`, then their real-space pair functions agree **pointwise on the core** `0 < r < R`
— the form in which "the inner-core DCF of the no-pull-back construction is the first-order PY one"
is actually a claim about `c₁(r)`. -/
theorem inner_core_dcf_eq_of_khat_eq {N : ℕ} {Chat1 Chat2 : ℝ → Matrix (Fin N) (Fin N) ℂ}
    {a : ℂ} (ha : a ≠ 0) {i j : Fin N} {c1 c2 : ℝ → ℝ} {Rij : ℝ}
    (h1 : IsRadialEntry Chat1 a i j c1) (h2 : IsRadialEntry Chat2 a i j c2)
    (hEq : ∀ k : ℝ, Chat1 k = Chat2 k)
    (hint1 : MeasureTheory.Integrable (fun v => ((v * c1 |v| : ℝ) : ℂ)))
    (hF1 : MeasureTheory.Integrable (𝓕 (fun v => ((v * c1 |v| : ℝ) : ℂ))))
    (hint2 : MeasureTheory.Integrable (fun v => ((v * c2 |v| : ℝ) : ℂ)))
    (hF2 : MeasureTheory.Integrable (𝓕 (fun v => ((v * c2 |v| : ℝ) : ℂ))))
    (hc1 : ∀ r ∈ Set.Ioo (0 : ℝ) Rij, ContinuousAt (fun v => ((v * c1 |v| : ℝ) : ℂ)) r)
    (hc2 : ∀ r ∈ Set.Ioo (0 : ℝ) Rij, ContinuousAt (fun v => ((v * c2 |v| : ℝ) : ℂ)) r) :
    ∀ r ∈ Set.Ioo (0 : ℝ) Rij, c1 r = c2 r := by
  intro r hr
  exact radial_fourier_injective c1 c2 (radial_fourier_eq_of_entry_eq ha h1 h2 hEq)
    hint1 hF1 hint2 hF2 hr.1 (hc1 r hr) (hc2 r hr)

/-- **PYE.5 capstone — the real-space form of PYE.4's exact-fit statement.**  Under the MRS.2
equations at every real `k` and a fit that is exact in WH data, the construction's inner-core
first-order DCF **equals** the first-order PY one pointwise on `0 < r < R`.

This is the statement the physics question asks for; note what it still carries: the MRS.2 cluster
(`hoz` is the physical first-order OZ equation), the *exact*-fit hypothesis (`hexact` — for a real
finite-tail fit only PYE.3's k-space bound is available), the dictionary, and the
inversion-admissibility hypotheses. -/
theorem inner_core_dcf_eq_of_exact_fit {N : ℕ}
    (Qp Qm T0 S0 H1 C1py B1py B1fit : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hoz : ∀ k : ℝ, H1 k * T0 k = S0 k * C1py k) (hTS : ∀ k : ℝ, T0 k * S0 k = 1)
    (hfact : ∀ k : ℝ, T0 k = Qp k * (Qm k)ᵀ) (hT0symm : ∀ k : ℝ, (T0 k)ᵀ = T0 k)
    (hB1 : ∀ k : ℝ, B1py k = (Qp k)ᵀ * H1 k * Qp k) (hexact : ∀ k : ℝ, B1fit k = B1py k)
    {a : ℂ} (ha : a ≠ 0) {i j : Fin N} {c1fit c1py : ℝ → ℝ} {Rij : ℝ}
    (hdictfit : IsRadialEntry (fun k => starConjLinear (Qm k) (B1fit k)) a i j c1fit)
    (hdictpy : IsRadialEntry C1py a i j c1py)
    (hintfit : MeasureTheory.Integrable (fun v => ((v * c1fit |v| : ℝ) : ℂ)))
    (hFfit : MeasureTheory.Integrable (𝓕 (fun v => ((v * c1fit |v| : ℝ) : ℂ))))
    (hintpy : MeasureTheory.Integrable (fun v => ((v * c1py |v| : ℝ) : ℂ)))
    (hFpy : MeasureTheory.Integrable (𝓕 (fun v => ((v * c1py |v| : ℝ) : ℂ))))
    (hcfit : ∀ r ∈ Set.Ioo (0 : ℝ) Rij, ContinuousAt (fun v => ((v * c1fit |v| : ℝ) : ℂ)) r)
    (hcpy : ∀ r ∈ Set.Ioo (0 : ℝ) Rij, ContinuousAt (fun v => ((v * c1py |v| : ℝ) : ℂ)) r) :
    ∀ r ∈ Set.Ioo (0 : ℝ) Rij, c1fit r = c1py r := by
  have hmat : ∀ k : ℝ, starConjLinear (Qm k) (B1fit k) = C1py k := fun k =>
    dp_eq_py_first_order_of_exact_fit (Qp k) (Qm k) (T0 k) (S0 k) (H1 k) (C1py k) (B1py k)
      (B1fit k) (hoz k) (hTS k) (hfact k) (hT0symm k) (hB1 k) (hexact k)
  exact inner_core_dcf_eq_of_khat_eq ha hdictfit hdictpy hmat hintfit hFfit hintpy hFpy hcfit hcpy

/-- **Non-vacuity of the capstone's structural cluster.**  `inner_core_dcf_eq_of_exact_fit` bundles
the five MRS.2 equations *and* two dictionary hypotheses; the same audit that forced a witness for
the k-space cluster applies here, since a dictionary tying `Ĉ₁` to a radial transform could in
principle contradict them.  It does not: for an **arbitrary** real-space `c` the whole structural
cluster is satisfiable, non-degenerately (`Qm ≠ 1`).  The analytic admissibility hypotheses
(`hint`/`hF`/`ContinuousAt`) are properties of the consumer's `c` alone and compose with this
witness — they are jointly satisfiable already at `c = 0`. -/
example (c : ℝ → ℝ) :
    ∃ Qp Qm T0 S0 H1 C1py B1py B1fit : ℝ → Matrix (Fin 1) (Fin 1) ℂ,
      (∀ k : ℝ, H1 k * T0 k = S0 k * C1py k) ∧ (∀ k : ℝ, T0 k * S0 k = 1) ∧
        (∀ k : ℝ, T0 k = Qp k * (Qm k)ᵀ) ∧ (∀ k : ℝ, (T0 k)ᵀ = T0 k) ∧
        (∀ k : ℝ, B1py k = (Qp k)ᵀ * H1 k * Qp k) ∧ (∀ k : ℝ, B1fit k = B1py k) ∧
        IsRadialEntry (fun k => starConjLinear (Qm k) (B1fit k)) 1 0 0 c ∧
        IsRadialEntry C1py 1 0 0 c ∧ (∀ k : ℝ, Qm k ≠ 1) := by
  classical
  refine ⟨fun _ => !![2], fun _ => !![2], fun _ => !![4], fun _ => !![1/4],
    fun k => !![((FMSA.HardSphere.radial_fourier c k : ℝ) : ℂ) / 16],
    fun k => !![((FMSA.HardSphere.radial_fourier c k : ℝ) : ℂ)],
    fun k => !![((FMSA.HardSphere.radial_fourier c k : ℝ) : ℂ) / 4],
    fun k => !![((FMSA.HardSphere.radial_fourier c k : ℝ) : ℂ) / 4], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; ext i j; fin_cases i; fin_cases j; norm_num [Matrix.mul_apply]; ring
  · intro k; ext i j; fin_cases i; fin_cases j; norm_num [Matrix.mul_apply, Matrix.one_apply]
  · intro k; ext i j; fin_cases i; fin_cases j; norm_num [Matrix.mul_apply]
  · intro k; ext i j; fin_cases i; fin_cases j; norm_num
  · intro k; ext i j; fin_cases i; fin_cases j; norm_num [Matrix.mul_apply]; ring
  · intro k; rfl
  · intro k
    simp only [starConjLinear_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_one,
      Matrix.cons_val_zero, Matrix.of_apply, Matrix.cons_val']
    norm_num
    ring
  · intro k; norm_num
  · intro k hc; have := congrFun (congrFun hc 0) 0; norm_num [Matrix.one_apply] at this

/-! ## The zeroth-order factor of the construction **is** the PY hard-sphere Baxter factor (`N = 1`)

Every physical-form theorem above puts the *same* `Q̂₀` on both sides — the construction's
zeroth-order Baxter factor and PY's.  At `N = 1` that is not an assumption but a **theorem already in
the library**: `Q̂₀ = 1 − q̂₀` is built from `q0_poly`, whose coefficients are the Wertheim-Thiele
`q_prime_py` / `q_doubleprime_py` (`PYDCF.lean`), and BAXTER.3's `baxter_wiener_hopf_complex`
(`BaxterWienerHopfComplex.lean`) proves

    (1 − q̂₀(k))·(1 − q̂₀(−k)) = 1 − ρ·Ĉ_PY(k),

i.e. `T₀ = Q̂₀(k)·Q̂₀ᵀ(−k) = I − Ĉ₀` with `Ĉ₀` the **PY hard-sphere DCF transform** — which is exactly
**MRS.8 at `N = 1`** (for general `N`, MRS.8 is still deferred: `Cmix0_factorization` gives the
factorization by *definition* of `Ĉ₀`, and identifying that `Ĉ₀` with the physical Lebowitz mixture
DCF is the open part).  So at `N = 1` the MRS.2 zeroth-order inputs hold with the genuine PY objects:
`hfact` by construction, `hT0symm` free, `hTS` from `pyhs_no_spinodal` (OZ.20, a theorem).

The mixture-to-scalar reduction that makes this the *same* `Q̂₀` the DP construction uses is also
already proved: `Q0phys_n1` / `Qppphys_n1` / `qhat_complex_eq_mixture_kernel`
(`MixtureNoSpinodalN1.lean`, the MRS.0b chain) show the physical mixture coefficients collapse
exactly to `q_prime_py` / `q_doubleprime_py` at one component. -/

/-- The PY hard-sphere Baxter factor as a `1×1` matrix, `Q̂₀(k) = 1 − q̂₀(k)`. -/
noncomputable def pyBaxterMat (eta sigma rho : ℝ) (k : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.of fun _ _ => 1 - FMSA.HardSphere.Qhat_complex eta sigma rho k

/-- The PY zeroth-order structure matrix `T₀ = Q̂₀(k)·Q̂₀ᵀ(−k)`. -/
noncomputable def pyT0Mat (eta sigma rho : ℝ) (k : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  pyBaxterMat eta sigma rho k * (pyBaxterMat eta sigma rho (-k))ᵀ

/-- At `N = 1` every matrix is symmetric, so MRS.2's `hT0symm` is free. -/
theorem fin1_transpose_eq (A : Matrix (Fin 1) (Fin 1) ℂ) : Aᵀ = A := by
  ext i j; fin_cases i; fin_cases j; rfl

/-- **`T₀ = 1 − ρ·Ĉ_PY(k)` — the construction's zeroth-order factor is the PY one** (`N = 1`).
BAXTER.3 (`baxter_wiener_hopf_complex`) in matrix form; this is MRS.8 at one component. -/
theorem pyT0Mat_entry {eta sigma rho : ℝ} (hsigma : 0 < sigma) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) {k : ℂ} (hk : k ≠ 0) :
    pyT0Mat eta sigma rho k 0 0 = 1 - (rho : ℂ) * FMSA.HardSphere.Chat_complex eta sigma k := by
  have hprod : pyT0Mat eta sigma rho k 0 0
      = (1 - FMSA.HardSphere.Qhat_complex eta sigma rho k) *
        (1 - FMSA.HardSphere.Qhat_complex eta sigma rho (-k)) := by
    simp [pyT0Mat, pyBaxterMat, Matrix.mul_apply, Matrix.transpose_apply]
  rw [hprod]
  exact FMSA.HardSphere.baxter_wiener_hopf_complex hsigma heta heta_def hk

/-- **`hTS` at `N = 1` is a theorem, not a hypothesis.**  `T₀` is invertible at every real `k ≠ 0`
because the PY hard-sphere structure factor `1 − ρĈ_PY(k)` is strictly positive — `pyhs_no_spinodal`
(OZ.20), itself axiom-clean since 2026-07-19. -/
theorem pyT0Mat_isUnit_det {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    {k : ℝ} (hk : k ≠ 0) :
    IsUnit (pyT0Mat eta sigma rho (k : ℂ)).det := by
  have hkc : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  have hpos : 0 < 1 - rho * FMSA.HardSphere.radial_fourier (FMSA.HardSphere.c_HS eta sigma) k :=
    FMSA.HardSphere.pyhs_no_spinodal heta0 heta1 hsigma hrho heta_def k hk
  have hentry : pyT0Mat eta sigma rho (k : ℂ) 0 0
      = ((1 - rho * FMSA.HardSphere.radial_fourier (FMSA.HardSphere.c_HS eta sigma) k : ℝ) : ℂ) := by
    rw [pyT0Mat_entry hsigma heta1 heta_def hkc,
      FMSA.HardSphere.Chat_complex_eq_radial_fourier hsigma]
    push_cast
    ring
  rw [Matrix.det_fin_one, hentry]
  exact (Complex.ofReal_ne_zero.mpr hpos.ne').isUnit

/-- **The MRS.2 zeroth-order inputs, discharged with the physical PY objects (`N = 1`).**
`hfact` (by construction), `hT0symm` (free at `N=1`), `hTS` (from `pyhs_no_spinodal`), and the
identification `T₀ = 1 − ρĈ_PY` (BAXTER.3).  Only the *first-order* OZ equation `hoz` remains a
physical input. -/
theorem dp_zeroth_order_is_py_n1 {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    {k : ℝ} (hk : k ≠ 0) :
    pyT0Mat eta sigma rho (k : ℂ)
        = pyBaxterMat eta sigma rho (k : ℂ) * (pyBaxterMat eta sigma rho (-(k : ℂ)))ᵀ ∧
      (pyT0Mat eta sigma rho (k : ℂ))ᵀ = pyT0Mat eta sigma rho (k : ℂ) ∧
      pyT0Mat eta sigma rho (k : ℂ) * (pyT0Mat eta sigma rho (k : ℂ))⁻¹ = 1 ∧
      pyT0Mat eta sigma rho (k : ℂ) 0 0
        = 1 - (rho : ℂ) * FMSA.HardSphere.Chat_complex eta sigma (k : ℂ) :=
  ⟨rfl, fin1_transpose_eq _,
    Matrix.mul_nonsing_inv _ (pyT0Mat_isUnit_det heta0 heta1 hsigma hrho heta_def hk),
    pyT0Mat_entry hsigma heta1 heta_def (Complex.ofReal_ne_zero.mpr hk)⟩

/-- **PYE.4 at `N = 1` with the physical PY zeroth order.**  With the *actual* PY hard-sphere Baxter
factor as `Q̂₀` (so that `T₀ = 1 − ρĈ_PY`, `hfact`/`hT0symm`/`hTS` all discharged), a fitted WH datum
that equals Y1.6's projection `B₁ = Q̂₀ᵀ(k)·Ĥ₁·Q̂₀(k)` of the first-order PY RDF yields **exactly** the
first-order PY DCF.  The only remaining input is `hoz`, the first-order OZ equation itself. -/
theorem dp_eq_py_first_order_n1 {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    {k : ℝ} (hk : k ≠ 0) (H1 C1py B1fit : Matrix (Fin 1) (Fin 1) ℂ)
    (hoz : H1 * pyT0Mat eta sigma rho (k : ℂ) = (pyT0Mat eta sigma rho (k : ℂ))⁻¹ * C1py)
    (hB1 : B1fit = (pyBaxterMat eta sigma rho (k : ℂ))ᵀ * H1 * pyBaxterMat eta sigma rho (k : ℂ)) :
    starConjLinear (pyBaxterMat eta sigma rho (-(k : ℂ))) B1fit = C1py :=
  dp_eq_py_first_order_of_exact_fit (pyBaxterMat eta sigma rho (k : ℂ))
    (pyBaxterMat eta sigma rho (-(k : ℂ))) (pyT0Mat eta sigma rho (k : ℂ))
    (pyT0Mat eta sigma rho (k : ℂ))⁻¹ H1 C1py B1fit B1fit hoz
    (Matrix.mul_nonsing_inv _ (pyT0Mat_isUnit_det heta0 heta1 hsigma hrho heta_def hk))
    rfl (fin1_transpose_eq _) hB1 rfl

/-- **Non-vacuity of `dp_eq_py_first_order_n1` at the physical PY zeroth order.**  Its two remaining
hypotheses are satisfiable for **every** first-order RDF `H₁`: take `C₁ = T₀·H₁·T₀` (which is
`oz1_C1_eq` read backwards) and `B₁ = Q̂₀ᵀ(k)·H₁·Q̂₀(k)` (Y1.6).  So the theorem is not vacuous, and
in particular not vacuous at the genuine PY Baxter factor — unlike the earlier `Qp = Qm = !![2]`
witness, `Q̂₀(k)` and `Q̂₀(−k)` here are the physically distinct pair. -/
example {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1) (hsigma : 0 < sigma)
    (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) {k : ℝ} (hk : k ≠ 0)
    (H1 : Matrix (Fin 1) (Fin 1) ℂ) :
    ∃ C1py B1fit : Matrix (Fin 1) (Fin 1) ℂ,
      H1 * pyT0Mat eta sigma rho (k : ℂ) = (pyT0Mat eta sigma rho (k : ℂ))⁻¹ * C1py ∧
        B1fit = (pyBaxterMat eta sigma rho (k : ℂ))ᵀ * H1 * pyBaxterMat eta sigma rho (k : ℂ) := by
  refine ⟨pyT0Mat eta sigma rho (k : ℂ) * H1 * pyT0Mat eta sigma rho (k : ℂ),
    (pyBaxterMat eta sigma rho (k : ℂ))ᵀ * H1 * pyBaxterMat eta sigma rho (k : ℂ), ?_, rfl⟩
  rw [show (pyT0Mat eta sigma rho (k : ℂ))⁻¹ *
        (pyT0Mat eta sigma rho (k : ℂ) * H1 * pyT0Mat eta sigma rho (k : ℂ))
      = ((pyT0Mat eta sigma rho (k : ℂ))⁻¹ * pyT0Mat eta sigma rho (k : ℂ)) * H1 *
        pyT0Mat eta sigma rho (k : ℂ) by simp only [Matrix.mul_assoc],
    Matrix.nonsing_inv_mul _ (pyT0Mat_isUnit_det heta0 heta1 hsigma hrho heta_def hk),
    Matrix.one_mul]

/-! ## PYE.7 — finite Yukawa-tail fits are dense: the residual can be made arbitrarily small

PYE.3 bounds the DCF error by the **fit residual**; PYE.7 shows the residual is not bounded away
from zero — on the outer window any continuous closure target is uniformly approximable by finitely
many Yukawa tails with **strictly positive, unit-spaced** rates.

**Route (cheaper than the Stone-Weierstrass sketch in the plan).**  Substituting `t = e^{−r}` maps
the window `[R, R+L]` homeomorphically onto `[e^{−(R+L)}, e^{−R}]` and turns *polynomials in `t`*
into *exponential sums* `Σ_k c_k e^{−k r}`.  So classical Weierstrass
(`exists_polynomial_near_of_continuousOn`) already delivers the density, and the generated rates are
the integers `k` — automatically distinct.  A final `δ`-shift `k ↦ k + δ` makes every rate strictly
positive (the `k = 0` term is the constant, which is not a legal Yukawa tail), at a cost
`≤ (Σ|c_k|)·δ·(R+L)` that is driven below `ε/2` by choosing `δ`.

**Bonus — the rates come out well-separated.**  `z_k = k + δ` has unit spacing, exactly the
`tail_mode='linear'` discipline the numerics were forced into for a *different* reason
(`hncb_first_order.md` §4(b): a free nonlinear fit collapses to near-degenerate rates with cancelling
amplitudes, and the `e^{+z̃R}` inner-core shift factors then overflow).

⚠ **What PYE.7 does NOT do — it does not close PYE.4.**  Two gaps remain, both real:
1. **window, not half-line** — the fit is uniform on the *compact* `[R, R+L]`, while the WH
   projection integrates over `[R,∞)`.  Beyond the window neither the target nor the fitted sum is
   controlled here (the amplitudes may grow as `ε → 0`, so their tail is not uniformly small).
2. **function residual, not WH datum** — PYE.3's bound consumes `‖K^fit − K^exact‖`, a *coupling
   matrix* distance.  Turning a sup-norm function residual into that is exactly the function-space
   WH projection, i.e. PYE.4's lift. -/

/-- `(e^x)^k = e^{k·x}` (elementary induction). -/
private theorem exp_pow_eq (x : ℝ) (k : ℕ) : (Real.exp x) ^ k = Real.exp ((k : ℝ) * x) := by
  induction k with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← Real.exp_add]; push_cast; ring_nf

/-- **PYE.7 ⭐ — density of finite Yukawa-tail sums on the outer window.**  Every function continuous
on `[R, R+L]` is uniformly approximable there, to any accuracy `ε`, by a finite sum of Yukawa tails
`Σ_{t<n} A_t e^{−z_t r}` whose rates are **strictly positive** and **strictly increasing** (unit
spacing). -/
theorem exists_yukawa_tail_fit {R L eps : ℝ} (hR : 0 ≤ R) (hL : 0 < L) (heps : 0 < eps)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc R (R + L))) :
    ∃ (n : ℕ) (A z : ℕ → ℝ), StrictMono z ∧ (∀ t, 0 < z t) ∧
      ∀ r ∈ Set.Icc R (R + L),
        |f r - ∑ t ∈ Finset.range n, A t * Real.exp (-(z t) * r)| ≤ eps := by
  -- the substitution window `t = e^{−r}`
  set a := Real.exp (-(R + L)) with ha
  set b := Real.exp (-R) with hb
  have ha0 : 0 < a := Real.exp_pos _
  have hmaps : Set.MapsTo (fun t : ℝ => -Real.log t) (Set.Icc a b) (Set.Icc R (R + L)) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
    have h1 : Real.log t ≤ -R := by
      have := Real.log_le_log ht0 ht.2
      rwa [hb, Real.log_exp] at this
    have h2 : -(R + L) ≤ Real.log t := by
      have := Real.log_le_log ha0 ht.1
      rwa [ha, Real.log_exp] at this
    constructor <;> linarith
  have hlog : ContinuousOn (fun t : ℝ => -Real.log t) (Set.Icc a b) := by
    refine (Real.continuousOn_log.mono ?_).neg
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le ha0 ht.1)
  have hFcont : ContinuousOn (fun t : ℝ => f (-Real.log t)) (Set.Icc a b) := by
    have := hf.comp hlog hmaps
    simpa [Function.comp_def] using this
  -- Weierstrass on the substituted window
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b (fun t => f (-Real.log t)) hFcont
    (eps / 2) (by linarith)
  have hkey : ∀ r ∈ Set.Icc R (R + L), |p.eval (Real.exp (-r)) - f r| < eps / 2 := by
    intro r hr
    have ht : Real.exp (-r) ∈ Set.Icc a b :=
      ⟨Real.exp_le_exp.mpr (by linarith [hr.2]), Real.exp_le_exp.mpr (by linarith [hr.1])⟩
    have h := hp _ ht
    rwa [Real.log_exp, neg_neg] at h
  -- a polynomial in `e^{−r}` *is* an exponential sum with integer rates
  set N := p.natDegree with hN
  have hexpand : ∀ r : ℝ, p.eval (Real.exp (-r))
      = ∑ k ∈ Finset.range (N + 1), p.coeff k * Real.exp (-(k : ℝ) * r) := by
    intro r
    rw [Polynomial.eval_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [exp_pow_eq]
    congr 2
    ring
  -- the `δ`-shift that makes every rate strictly positive
  set S := ∑ k ∈ Finset.range (N + 1), |p.coeff k| with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hRL : 0 < R + L + 1 := by linarith
  set delta := min 1 (eps / (2 * (S + 1) * (R + L + 1))) with hdeltadef
  have hd0 : 0 < delta := lt_min one_pos (by positivity)
  have hdshift : S * (delta * (R + L)) ≤ eps / 2 := by
    have hdle : delta ≤ eps / (2 * (S + 1) * (R + L + 1)) := min_le_right _ _
    have hpos : (0 : ℝ) < 2 * (S + 1) * (R + L + 1) := by positivity
    have hchain : S * (delta * (R + L)) ≤ (S + 1) * (delta * (R + L + 1)) := by
      have h1 : delta * (R + L) ≤ delta * (R + L + 1) := by nlinarith [hd0.le]
      nlinarith [hd0.le, hS0]
    have : (S + 1) * (delta * (R + L + 1)) ≤ eps / 2 := by
      have := mul_le_mul_of_nonneg_left hdle (by positivity : (0:ℝ) ≤ (S + 1) * (R + L + 1))
      calc (S + 1) * (delta * (R + L + 1)) = ((S + 1) * (R + L + 1)) * delta := by ring
        _ ≤ ((S + 1) * (R + L + 1)) * (eps / (2 * (S + 1) * (R + L + 1))) := by
            exact mul_le_mul_of_nonneg_left hdle (by positivity)
        _ = eps / 2 := by field_simp
    linarith
  refine ⟨N + 1, fun k => p.coeff k, fun k => (k : ℝ) + delta, ?_, ?_, ?_⟩
  · intro i j hij
    have : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    linarith
  · intro t; positivity
  · intro r hr
    have hr0 : 0 ≤ r := le_trans hR hr.1
    -- the shift costs at most `S·δ·(R+L)`
    have hterm : ∀ k ∈ Finset.range (N + 1),
        |p.coeff k * Real.exp (-(k : ℝ) * r) - p.coeff k * Real.exp (-((k : ℝ) + delta) * r)|
          ≤ |p.coeff k| * (delta * (R + L)) := by
      intro k _
      have hsplit : p.coeff k * Real.exp (-(k : ℝ) * r) - p.coeff k * Real.exp (-((k : ℝ) + delta) * r)
          = p.coeff k * (Real.exp (-(k : ℝ) * r) * (1 - Real.exp (-delta * r))) := by
        rw [show -((k : ℝ) + delta) * r = -(k : ℝ) * r + -delta * r by ring, Real.exp_add]
        ring
      have hexp_le : Real.exp (-(k : ℝ) * r) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : (0 : ℝ) ≤ (k : ℝ) * r := by positivity
        linarith
      have hexp_pos : 0 < Real.exp (-(k : ℝ) * r) := Real.exp_pos _
      have hone_sub : 0 ≤ 1 - Real.exp (-delta * r) := by
        have : Real.exp (-delta * r) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : (0 : ℝ) ≤ delta * r := by positivity
          linarith
        linarith
      have hone_sub_le : 1 - Real.exp (-delta * r) ≤ delta * (R + L) := by
        have h1 : -delta * r + 1 ≤ Real.exp (-delta * r) := Real.add_one_le_exp _
        have h2 : r ≤ R + L := hr.2
        nlinarith [hd0.le]
      rw [hsplit, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.exp (-(k : ℝ) * r) * (1 - Real.exp (-delta * r)))]
      calc Real.exp (-(k : ℝ) * r) * (1 - Real.exp (-delta * r))
          ≤ 1 * (delta * (R + L)) := by
            exact mul_le_mul hexp_le hone_sub_le hone_sub (by norm_num)
        _ = delta * (R + L) := by ring
    have hsum : |∑ k ∈ Finset.range (N + 1), p.coeff k * Real.exp (-(k : ℝ) * r)
          - ∑ k ∈ Finset.range (N + 1), p.coeff k * Real.exp (-((k : ℝ) + delta) * r)|
        ≤ eps / 2 := by
      rw [← Finset.sum_sub_distrib]
      calc |∑ k ∈ Finset.range (N + 1), (p.coeff k * Real.exp (-(k : ℝ) * r)
              - p.coeff k * Real.exp (-((k : ℝ) + delta) * r))|
          ≤ ∑ k ∈ Finset.range (N + 1), |p.coeff k * Real.exp (-(k : ℝ) * r)
              - p.coeff k * Real.exp (-((k : ℝ) + delta) * r)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range (N + 1), |p.coeff k| * (delta * (R + L)) :=
            Finset.sum_le_sum hterm
        _ = S * (delta * (R + L)) := by rw [hSdef, Finset.sum_mul]
        _ ≤ eps / 2 := hdshift
    have h1 : |f r - p.eval (Real.exp (-r))| ≤ eps / 2 := by
      rw [abs_sub_comm]; exact (hkey r hr).le
    calc |f r - ∑ t ∈ Finset.range (N + 1), p.coeff t * Real.exp (-((t : ℝ) + delta) * r)|
        ≤ |f r - p.eval (Real.exp (-r))|
          + |p.eval (Real.exp (-r))
              - ∑ t ∈ Finset.range (N + 1), p.coeff t * Real.exp (-((t : ℝ) + delta) * r)| :=
          abs_sub_le _ _ _
      _ ≤ eps / 2 + eps / 2 := by
          refine add_le_add h1 ?_
          rw [hexpand r]
          exact hsum
      _ = eps := by ring

/-- **PYE.7 for the PY-level outer closure.**  The target the `pullback_passes = 0` construction
actually fits is `r·c₁(r) = r·g_HS(r)·(−βu(r))` (PYE.1; the `r·` factor is [LN] Eq. 46's, the one the
transform cancels against the tail's `1/r`).  Being continuous on the window, it admits finite
Yukawa-tail fits of arbitrary accuracy — so PYE.3's residual really can be driven to zero *on the
window*. -/
theorem exists_yukawa_tail_fit_pyOuter {R L beta eps : ℝ} (hR : 0 ≤ R) (hL : 0 < L)
    (heps : 0 < eps) (gHS u : ℝ → ℝ) (hg : ContinuousOn gHS (Set.Icc R (R + L)))
    (hu : ContinuousOn u (Set.Icc R (R + L))) :
    ∃ (n : ℕ) (A z : ℕ → ℝ), StrictMono z ∧ (∀ t, 0 < z t) ∧
      ∀ r ∈ Set.Icc R (R + L),
        |r * (gHS r * -(beta * u r))
          - ∑ t ∈ Finset.range n, A t * Real.exp (-(z t) * r)| ≤ eps := by
  refine exists_yukawa_tail_fit hR hL heps (fun r => r * (gHS r * -(beta * u r))) ?_
  exact continuousOn_id.mul (hg.mul (((continuousOn_const.mul hu)).neg))

/-! ## PYE.4 — the function-space lift

PYE.4 asks for the WH solution map on a *function-space* closure, and for the finite-pole maps to
converge to it.  This section removes the two structural obstacles and reduces what is left to a
single **named, classical** operator bound.

**⚠ First, a dead end that must be recorded: the amplitude route cannot work.**  PYE.3 bounds the
DCF error by `whOperatorBound · ‖K^fit − K^exact‖` — a distance between *coupling amplitudes*.  One
cannot lift that to a function-space statement, because the map `closure ↦ amplitudes` is
**unbounded**: near-degenerate rates represent a small function with huge cancelling amplitudes
(`hncb_first_order.md` §4(b) measured exactly this: `z̃ = [18.23, 18.35]`, `K̃ = [−441, +435]`).  So
the lift must bound the WH data **directly in terms of the closure function**, in `L¹` — which is
what the transform stage below does (`‖Û₁‖_∞ ≤ ‖Ψ‖₁`, no amplitudes anywhere).

**What is proved here.**

* `exists_yukawa_tail_fit_halfLine` — **PYE.7's window gap closed**: a closure that *decays* is
  uniformly approximable by Yukawa tails on the whole half-line `[R,∞)`, not merely on a compact
  window.  Same substitution `t = e^{−r}`, but now the interval is `[0, e^{−R}]` — the **closed**
  interval including `t = 0`, into which the half-line maps.  Killing the polynomial's constant term
  (legal because the decay forces `G 0 = 0`) leaves only rates `k ≥ 1`, all strictly positive.
* `exists_yukawa_tail_fit_L1` — the `L¹` version, by fitting the *weighted* closure
  `e^{a(r−R)}·Ψ(r)` and absorbing the weight into the rates.
* `norm_transform_le_L1` — the transform stage: `‖Û₁(k)‖ ≤ ‖Ψ‖_{L¹}` **uniformly in `k`**.
* `WHProjectionL1` / `tailFitWHConvergent_of_L1_tendsto` / `exists_tailFit_whConvergent` — the
  reduction: `TailFitWHConvergent`, previously an opaque hypothesis of `dp_tendsto_py_first_order`,
  is **derived** from `L¹` convergence of the closures plus one operator bound.

**What remains open (honestly).**  The single hypothesis `WHProjectionL1`: that the composite
`Ψ ↦ B₁` (conjugate by `Q̂₀(−k)⁻¹`, restrict to `[R,∞)`, transform) is `L¹`-bounded.  In real space
each stage is `L¹`-bounded — the restriction is multiplication by an indicator (norm ≤ 1) and the
conjugation is convolution with the kernel of `Q̂₀⁻¹` — but *that kernel being `L¹`* is **Wiener's
`1/f` theorem for the causal convolution algebra**, i.e. exactly the MA.13 (`wiener_causal_resolvent`)
/ MA.15 (`radialShell_bounded_injective`) family: kept axioms in this project precisely because
Mathlib has no Wiener algebra.  It is therefore left as a **hypothesis**, not axiomatized here —
adding a second copy of an MA-class axiom in a physics file would be exactly the wrong move.
⚠ Note also the norm matters: the causal projection is **not** bounded in the sup-norm on the Fourier
side (it is a Riesz-projection-type operator), so a "uniformly in `k`" version of the hypothesis
would be the *wrong* statement; `L¹` in real space is the norm in which every stage is bounded. -/

/-- **PYE.4a — half-line uniform density.**  A closure continuous on `[R,∞)` and vanishing at
infinity is uniformly approximable there, to any accuracy, by a finite Yukawa-tail sum with
**integer rates `≥ 1`** (in particular strictly positive).  This is PYE.7 with the substituted
interval taken **closed at `t = 0`**: the half-line `[R,∞)` maps into `[0, e^{−R}]`, so Weierstrass
控制 the whole half-line at once, and the decay hypothesis is what makes the substituted function
continuous at `t = 0` (with value `0`, which is what lets the constant term be dropped). -/
theorem exists_yukawa_tail_fit_halfLine {R eps : ℝ} (heps : 0 < eps) (Phi : ℝ → ℝ)
    (hcont : ContinuousOn Phi (Set.Ici R)) (hdecay : Tendsto Phi atTop (𝓝 0)) :
    ∃ (n : ℕ) (A : ℕ → ℝ), ∀ r ∈ Set.Ici R,
      |Phi r - ∑ k ∈ Finset.range n, A k * Real.exp (-((k : ℝ) + 1) * r)| ≤ eps := by
  set b := Real.exp (-R) with hbdef
  have hb0 : 0 < b := Real.exp_pos _
  set G : ℝ → ℝ := fun t => if 0 < t then Phi (-Real.log t) else 0 with hGdef
  have hG0 : G 0 = 0 := by simp [hGdef]
  have hmem : ∀ t : ℝ, 0 < t → t ≤ b → -Real.log t ∈ Set.Ici R := by
    intro t ht0 htb
    have h := Real.log_le_log ht0 htb
    rw [hbdef, Real.log_exp] at h
    simpa using (by linarith : R ≤ -Real.log t)
  -- `G` is continuous on the closed interval `[0, b]`
  have hGcont : ContinuousOn G (Set.Icc 0 b) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · -- at `t = 0` continuity is exactly the decay hypothesis
      have htz : t = 0 := h0.symm
      subst htz
      rw [← continuousWithinAt_sdiff_self]
      have hsub : (Set.Icc (0:ℝ) b \ {0}) ⊆ Set.Ioi 0 := by
        intro s hs
        rcases lt_or_eq_of_le hs.1.1 with h | h
        · exact h
        · exact absurd h.symm hs.2
      have hlim : Tendsto (fun s : ℝ => Phi (-Real.log s)) (𝓝[>] 0) (𝓝 0) := by
        have h1 : Tendsto (fun s : ℝ => -Real.log s) (𝓝[>] 0) atTop :=
          tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
        exact hdecay.comp h1
      have heq : ∀ s ∈ Set.Ioi (0:ℝ), G s = Phi (-Real.log s) := by
        intro s hs
        have hs' : (0:ℝ) < s := hs
        simp [hGdef, hs']
      have hlimG : Tendsto G (𝓝[>] 0) (𝓝 0) :=
        hlim.congr' (by filter_upwards [self_mem_nhdsWithin] with s hs using (heq s hs).symm)
      have hcw : ContinuousWithinAt G (Set.Ioi 0) 0 := by
        rw [ContinuousWithinAt, hG0]
        exact hlimG
      exact hcw.mono hsub
    · -- at `t > 0` it is the composition `Phi ∘ (−log)`
      have hIoi : Set.Ioi (0:ℝ) ∈ 𝓝 t := Ioi_mem_nhds h0
      have hcomp : ContinuousWithinAt (fun s : ℝ => Phi (-Real.log s)) (Set.Icc 0 b ∩ Set.Ioi 0) t := by
        have hlog : ContinuousWithinAt (fun s : ℝ => -Real.log s) (Set.Icc 0 b ∩ Set.Ioi 0) t :=
          ((Real.continuousAt_log (ne_of_gt h0)).neg).continuousWithinAt
        have hmaps : Set.MapsTo (fun s : ℝ => -Real.log s) (Set.Icc 0 b ∩ Set.Ioi 0) (Set.Ici R) := by
          intro s hs; exact hmem s hs.2 hs.1.2
        have hc := ContinuousWithinAt.comp (g := Phi) (f := fun s : ℝ => -Real.log s)
          (hcont _ (hmem t h0 ht.2)) hlog hmaps
        simpa [Function.comp_def] using hc
      have heqf : ∀ s ∈ Set.Icc (0:ℝ) b ∩ Set.Ioi 0, G s = Phi (-Real.log s) := by
        intro s hs
        have hs' : (0:ℝ) < s := hs.2
        simp [hGdef, hs']
      have hGwithin : ContinuousWithinAt G (Set.Icc 0 b ∩ Set.Ioi 0) t := by
        refine hcomp.congr heqf ?_
        simp [hGdef, h0]
      rw [ContinuousWithinAt, nhdsWithin_restrict' _ hIoi]
      exact hGwithin
  -- Weierstrass on `[0, b]`, then drop the constant term
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 b G hGcont (eps / 2) (by linarith)
  have hconst : |p.coeff 0| ≤ eps / 2 := by
    have h := hp 0 ⟨le_refl 0, hb0.le⟩
    rw [hG0, sub_zero] at h
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact h.le
  refine ⟨p.natDegree, fun j => p.coeff (j + 1), ?_⟩
  intro r hr
  have hrR : R ≤ r := hr
  have ht : Real.exp (-r) ∈ Set.Icc 0 b :=
    ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (by linarith)⟩
  have hGt : G (Real.exp (-r)) = Phi r := by
    have : (0:ℝ) < Real.exp (-r) := Real.exp_pos _
    simp only [hGdef, if_pos this, Real.log_exp, neg_neg]
  -- expand the polynomial in `t = e^{−r}`, splitting off the constant term
  have hexpand : p.eval (Real.exp (-r))
      = (∑ j ∈ Finset.range p.natDegree, p.coeff (j + 1) * Real.exp (-((j : ℝ) + 1) * r))
        + p.coeff 0 := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ']
    simp only [pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [exp_pow_eq]
    have hcast : ((j + 1 : ℕ) : ℝ) * (-r) = -((j : ℝ) + 1) * r := by push_cast; ring
    rw [hcast]
  have hnear : |p.eval (Real.exp (-r)) - Phi r| ≤ eps / 2 := by
    have := hp _ ht
    rw [hGt] at this
    exact this.le
  calc |Phi r - ∑ j ∈ Finset.range p.natDegree, p.coeff (j + 1) * Real.exp (-((j : ℝ) + 1) * r)|
      = |(Phi r - p.eval (Real.exp (-r))) + p.coeff 0| := by rw [hexpand]; congr 1; ring
    _ ≤ |Phi r - p.eval (Real.exp (-r))| + |p.coeff 0| := abs_add_le _ _
    _ ≤ eps / 2 + eps / 2 := by
        refine add_le_add ?_ hconst
        rw [abs_sub_comm]; exact hnear
    _ = eps := by ring

/-- `∫_R^∞ e^{−a(r−R)} dr = 1/a` (`a > 0`) — the weight's total mass, which converts the weighted
uniform bound of `exists_yukawa_tail_fit_L1` into an `L¹` bound. -/
theorem integral_exp_neg_shift {a R : ℝ} (ha : 0 < a) :
    ∫ r in Set.Ioi R, Real.exp (-a * (r - R)) = 1 / a := by
  have hcongr : ∀ r : ℝ, Real.exp (-a * (r - R)) = Real.exp (a * R) * Real.exp (-a * r) := by
    intro r; rw [← Real.exp_add]; congr 1; ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r _ => hcongr r),
    MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (show -a < 0 by linarith) R]
  have hexp : Real.exp (a * R) * Real.exp (-a * R) = 1 := by
    rw [← Real.exp_add, show a * R + -a * R = 0 by ring, Real.exp_zero]
  rw [show (-Real.exp (-a * R) / -a) = Real.exp (-a * R) / a by field_simp, ← mul_div_assoc, hexp]

/-- The `L¹`-integrability of the weight. -/
theorem integrableOn_exp_neg_shift {a R : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun r => Real.exp (-a * (r - R))) (Set.Ioi R) := by
  have hcongr : ∀ r : ℝ, Real.exp (-a * (r - R)) = Real.exp (a * R) * Real.exp (-a * r) := by
    intro r; rw [← Real.exp_add]; congr 1; ring
  have h := (integrableOn_exp_mul_Ioi (show -a < 0 by linarith) R).const_mul (Real.exp (a * R))
  exact h.congr (Filter.Eventually.of_forall (fun r => (hcongr r).symm))

/-- **PYE.4b — `L¹` density on the half-line.**  An *exponentially decaying* closure (the physical
case: the outer closure carries the Yukawa tail `e^{−z(r−R)}`) is approximable in `L¹([R,∞))`, to any
accuracy, by a finite Yukawa-tail sum with strictly positive, strictly increasing rates.

Route: fit the **weighted** closure `e^{a(r−R)}·Ψ(r)` uniformly on the half-line (PYE.4a — the weight
is exactly what makes it vanish at infinity), then absorb the weight back into the rates
(`e^{−a(r−R)}·e^{−k r}` is again a Yukawa tail, of rate `k + a`).  The weighted uniform error
integrates to `‖·‖₁ ≤ (εa)·(1/a) = ε`. -/
theorem exists_yukawa_tail_fit_L1 {R a eps : ℝ} (ha : 0 < a) (heps : 0 < eps) (Psi : ℝ → ℝ)
    (hcont : ContinuousOn Psi (Set.Ici R))
    (hdecay : Tendsto (fun r => Real.exp (a * (r - R)) * Psi r) atTop (𝓝 0)) :
    ∃ (n : ℕ) (A z : ℕ → ℝ), StrictMono z ∧ (∀ t, 0 < z t) ∧
      (∀ r ∈ Set.Ici R, |Psi r - ∑ t ∈ Finset.range n, A t * Real.exp (-(z t) * r)|
        ≤ (eps * a) * Real.exp (-a * (r - R))) ∧
      ∫ r in Set.Ioi R, |Psi r - ∑ t ∈ Finset.range n, A t * Real.exp (-(z t) * r)| ≤ eps ∧
      MeasureTheory.IntegrableOn Psi (Set.Ioi R) := by
  -- fit the weighted closure uniformly on the half-line
  have hPhicont : ContinuousOn (fun r => Real.exp (a * (r - R)) * Psi r) (Set.Ici R) :=
    (Real.continuous_exp.comp (by fun_prop)).continuousOn.mul hcont
  obtain ⟨n, A, hA⟩ := exists_yukawa_tail_fit_halfLine (R := R) (eps := eps * a) (by positivity)
    (fun r => Real.exp (a * (r - R)) * Psi r) hPhicont hdecay
  refine ⟨n, fun j => A j * Real.exp (a * R), fun j => ((j : ℝ) + 1) + a, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    linarith
  · intro t; positivity
  · -- the weighted uniform bound, un-weighted
    intro r hr
    have hkey := hA r hr
    have hrw : ∀ j : ℕ, A j * Real.exp (a * R) * Real.exp (-(((j : ℝ) + 1) + a) * r)
        = Real.exp (-a * (r - R)) * (A j * Real.exp (-((j : ℝ) + 1) * r)) := by
      intro j
      rw [show A j * Real.exp (a * R) * Real.exp (-(((j : ℝ) + 1) + a) * r)
          = A j * (Real.exp (a * R) * Real.exp (-(((j : ℝ) + 1) + a) * r)) by ring,
        ← Real.exp_add,
        show Real.exp (-a * (r - R)) * (A j * Real.exp (-((j : ℝ) + 1) * r))
          = A j * (Real.exp (-a * (r - R)) * Real.exp (-((j : ℝ) + 1) * r)) by ring,
        ← Real.exp_add]
      congr 2
      ring
    rw [Finset.sum_congr rfl (fun j _ => hrw j), ← Finset.mul_sum]
    have hfactor : Psi r - Real.exp (-a * (r - R))
          * ∑ j ∈ Finset.range n, A j * Real.exp (-((j : ℝ) + 1) * r)
        = Real.exp (-a * (r - R))
          * (Real.exp (a * (r - R)) * Psi r
            - ∑ j ∈ Finset.range n, A j * Real.exp (-((j : ℝ) + 1) * r)) := by
      have hmul : Real.exp (-a * (r - R)) * Real.exp (a * (r - R)) = 1 := by
        rw [← Real.exp_add, show -a * (r - R) + a * (r - R) = 0 by ring, Real.exp_zero]
      linear_combination (-Psi r) * hmul
    rw [hfactor, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-a * (r - R))
          * |Real.exp (a * (r - R)) * Psi r - ∑ j ∈ Finset.range n, A j * Real.exp (-((j:ℝ)+1) * r)|
        ≤ Real.exp (-a * (r - R)) * (eps * a) :=
          mul_le_mul_of_nonneg_left hkey (Real.exp_pos _).le
      _ = eps * a * Real.exp (-a * (r - R)) := by ring
  · -- integrate the weighted bound
    set fit : ℝ → ℝ := fun r => ∑ t ∈ Finset.range n,
      (A t * Real.exp (a * R)) * Real.exp (-(((t : ℝ) + 1) + a) * r) with hfitdef
    have hptw : ∀ r ∈ Set.Ioi R, |Psi r - fit r| ≤ (eps * a) * Real.exp (-a * (r - R)) := by
      intro r hr
      have hr' : r ∈ Set.Ici R := Set.mem_Ici.mpr (le_of_lt hr)
      -- same computation as the previous bullet
      have hkey := hA r hr'
      have hrw : ∀ j : ℕ, A j * Real.exp (a * R) * Real.exp (-(((j : ℝ) + 1) + a) * r)
          = Real.exp (-a * (r - R)) * (A j * Real.exp (-((j : ℝ) + 1) * r)) := by
        intro j
        rw [show A j * Real.exp (a * R) * Real.exp (-(((j : ℝ) + 1) + a) * r)
            = A j * (Real.exp (a * R) * Real.exp (-(((j : ℝ) + 1) + a) * r)) by ring,
          ← Real.exp_add,
          show Real.exp (-a * (r - R)) * (A j * Real.exp (-((j : ℝ) + 1) * r))
            = A j * (Real.exp (-a * (r - R)) * Real.exp (-((j : ℝ) + 1) * r)) by ring,
          ← Real.exp_add]
        congr 2
        ring
      rw [hfitdef]
      simp only
      rw [Finset.sum_congr rfl (fun j _ => hrw j), ← Finset.mul_sum]
      have hfactor : Psi r - Real.exp (-a * (r - R))
            * ∑ j ∈ Finset.range n, A j * Real.exp (-((j : ℝ) + 1) * r)
          = Real.exp (-a * (r - R))
            * (Real.exp (a * (r - R)) * Psi r
              - ∑ j ∈ Finset.range n, A j * Real.exp (-((j : ℝ) + 1) * r)) := by
        have hmul : Real.exp (-a * (r - R)) * Real.exp (a * (r - R)) = 1 := by
          rw [← Real.exp_add, show -a * (r - R) + a * (r - R) = 0 by ring, Real.exp_zero]
        linear_combination (-Psi r) * hmul
      rw [hfactor, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-a * (r - R))
            * |Real.exp (a * (r-R)) * Psi r - ∑ j ∈ Finset.range n, A j * Real.exp (-((j:ℝ)+1) * r)|
          ≤ Real.exp (-a * (r - R)) * (eps * a) :=
            mul_le_mul_of_nonneg_left hkey (Real.exp_pos _).le
        _ = eps * a * Real.exp (-a * (r - R)) := by ring
    have hdom : MeasureTheory.IntegrableOn (fun r => (eps * a) * Real.exp (-a * (r - R)))
        (Set.Ioi R) := (integrableOn_exp_neg_shift ha).const_mul _
    have hmeas : MeasureTheory.AEStronglyMeasurable (fun r => Psi r - fit r)
        (MeasureTheory.volume.restrict (Set.Ioi R)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      exact (hcont.mono Set.Ioi_subset_Ici_self).sub (by fun_prop)
    have hint : MeasureTheory.IntegrableOn (fun r => Psi r - fit r) (Set.Ioi R) := by
      refine MeasureTheory.Integrable.mono' hdom hmeas ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      simpa [Real.norm_eq_abs] using hptw r hr
    have hfitint : MeasureTheory.IntegrableOn fit (Set.Ioi R) := by
      rw [hfitdef]
      refine MeasureTheory.integrable_finsetSum _ fun t _ => ?_
      have hz : -(((t : ℝ) + 1) + a) < 0 := by
        have : (0:ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
        linarith
      exact (integrableOn_exp_mul_Ioi hz R).const_mul _
    refine ⟨?_, ?_⟩
    · calc ∫ r in Set.Ioi R, |Psi r - fit r|
          ≤ ∫ r in Set.Ioi R, (eps * a) * Real.exp (-a * (r - R)) :=
            MeasureTheory.setIntegral_mono_on hint.abs hdom measurableSet_Ioi hptw
        _ = (eps * a) * (1 / a) := by
            rw [MeasureTheory.integral_const_mul, integral_exp_neg_shift ha]
        _ = eps := by field_simp
    · have : (fun r => (Psi r - fit r) + fit r) = Psi := by funext r; ring
      rw [← this]
      exact hint.add hfitint

/-! ### The transform stage, and the reduction of `TailFitWHConvergent` -/

/-- **The transform stage is `L¹`-bounded, uniformly in `k`.**  `‖Û₁(k)‖ ≤ ‖Ψ‖_{L¹}` — the estimate
that replaces PYE.3's amplitude bound in the function-space route (no amplitudes appear, so the
unbounded `closure ↦ amplitudes` map is bypassed). -/
theorem norm_transform_le_L1 {R : ℝ} (D : ℝ → ℝ) (k : ℝ) :
    ‖∫ r in Set.Ioi R, (D r : ℂ) * Complex.exp (-Complex.I * (k : ℂ) * (r : ℂ))‖
      ≤ ∫ r in Set.Ioi R, |D r| := by
  have hexpnorm : ∀ r : ℝ, ‖Complex.exp (-Complex.I * (k : ℂ) * (r : ℂ))‖ = 1 := by
    intro r
    rw [Complex.norm_exp]
    norm_num [Complex.mul_re, Complex.mul_im]
  calc ‖∫ r in Set.Ioi R, (D r : ℂ) * Complex.exp (-Complex.I * (k : ℂ) * (r : ℂ))‖
      ≤ ∫ r in Set.Ioi R, ‖(D r : ℂ) * Complex.exp (-Complex.I * (k : ℂ) * (r : ℂ))‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ r in Set.Ioi R, |D r| := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
        rw [norm_mul, hexpnorm r, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- A finite Yukawa-tail sum with strictly positive rates is `L¹` on `[R,∞)`. -/
theorem integrableOn_tailSum {R : ℝ} (n : ℕ) (A z : ℕ → ℝ) (hz : ∀ t, 0 < z t) :
    MeasureTheory.IntegrableOn (fun r => ∑ t ∈ Finset.range n, A t * Real.exp (-(z t) * r))
      (Set.Ioi R) := by
  refine MeasureTheory.integrable_finsetSum _ fun t _ => ?_
  exact (integrableOn_exp_mul_Ioi (show -(z t) < 0 by linarith [hz t]) R).const_mul _

/-- **PYE.4 — the one remaining analytic input, isolated as a hypothesis (never an axiom).**
`WHProjectionL1 R C B1of` says the WH projection `Ψ ↦ B₁` (at the evaluation point) is
difference-additive and **`L¹`-bounded**: `‖B₁(Ψ)‖ ≤ C·‖Ψ‖_{L¹([R,∞))}`.

**Why `L¹` and not a sup-norm on the `k`-axis.**  In real space every stage of the projection is
`L¹`-bounded — the causal restriction is multiplication by an indicator (norm ≤ 1) and the
conjugation by `Q̂₀(−k)⁻¹` is convolution with that operator's real-space kernel.  On the Fourier
side the causal projection is a Riesz-projection-type operator and is **not** sup-norm bounded, so
the naive "uniformly in `k`" hypothesis would be the wrong (indeed false) statement.

**Why it is not proved here.**  `Q̂₀⁻¹`'s kernel being `L¹` is **Wiener's `1/f` theorem for the causal
convolution algebra** — the MA.13 (`wiener_causal_resolvent`) / MA.15 (`radialShell_bounded_injective`)
family, which this project keeps as axioms precisely because Mathlib has no Wiener algebra. Adding a
second copy of an MA-class axiom inside a physics file would be exactly the wrong move; it stays a
hypothesis. -/
structure WHProjectionL1 {N : ℕ} (R C : ℝ) (B1of : (ℝ → ℝ) → Matrix (Fin N) (Fin N) ℂ) : Prop where
  /-- the projection is additive on differences (it is linear; only this instance is used) -/
  map_sub : ∀ Psi1 Psi2, MeasureTheory.IntegrableOn Psi1 (Set.Ioi R) →
    MeasureTheory.IntegrableOn Psi2 (Set.Ioi R) → B1of Psi1 - B1of Psi2 = B1of (Psi1 - Psi2)
  /-- `L¹` boundedness, uniform over entries -/
  bound : ∀ Psi, MeasureTheory.IntegrableOn Psi (Set.Ioi R) →
    ∀ p q, ‖B1of Psi p q‖ ≤ C * ∫ r in Set.Ioi R, |Psi r|

/-- **Non-vacuity of `WHProjectionL1`** — and a trap that was live for one iteration.  Quantifying
`map_sub`/`bound` over **all** `Ψ : ℝ → ℝ` (rather than the integrable ones) silently forces
`B1of ≡ 0`: for a non-integrable `Ψ` the junk value `∫|Ψ| = 0` makes `bound` read `B1of Ψ = 0`, and
then `map_sub` on two non-integrable functions with integrable difference kills `B1of` on *every*
integrable function too.  The theorems above would have been true only of the zero projection.

With the hypotheses restricted to integrable inputs the class is inhabited **non-degenerately**:
`B1of Ψ := (∫_R^∞ Ψ)·I` satisfies both fields with `C = 1` (`map_sub` = additivity of the integral on
integrable functions, `bound` = `|∫Ψ| ≤ ∫|Ψ|`) and is nonzero, e.g. on `Ψ = e^{−(r−R)}`. -/
example {R : ℝ} : ∃ (B1of : (ℝ → ℝ) → Matrix (Fin 1) (Fin 1) ℂ) (C : ℝ),
    WHProjectionL1 R C B1of ∧
      ∃ Psi : ℝ → ℝ, MeasureTheory.IntegrableOn Psi (Set.Ioi R) ∧ B1of Psi ≠ 0 := by
  refine ⟨fun Psi => Matrix.of fun _ _ => ((∫ r in Set.Ioi R, Psi r : ℝ) : ℂ), 1, ⟨?_, ?_⟩, ?_⟩
  · intro Psi1 Psi2 h1 h2
    ext i j
    have hsub : ∫ r in Set.Ioi R, (Psi1 r - Psi2 r)
        = (∫ r in Set.Ioi R, Psi1 r) - ∫ r in Set.Ioi R, Psi2 r :=
      MeasureTheory.integral_sub h1 h2
    simp only [Matrix.sub_apply, Matrix.of_apply, Pi.sub_apply]
    rw [hsub]
    push_cast
    ring
  · intro Psi _ p q
    simp only [Matrix.of_apply, Complex.norm_real, Real.norm_eq_abs, one_mul]
    exact MeasureTheory.abs_integral_le_integral_abs
  · refine ⟨fun r => Real.exp (-(1 : ℝ) * (r - R)), integrableOn_exp_neg_shift one_pos, ?_⟩
    intro hzero
    have h := congrFun (congrFun hzero 0) 0
    simp only [Matrix.of_apply, Matrix.zero_apply] at h
    rw [integral_exp_neg_shift (a := 1) one_pos] at h
    norm_num at h

/-- **PYE.4 ⭐ — `TailFitWHConvergent` is no longer opaque.**  Under the `L¹`-bounded projection,
`L¹` convergence of the *closures* gives convergence of the **WH data** — which is exactly the
hypothesis `dp_tendsto_py_first_order` consumes.  So the abstract equivalence
`DP-map[g_HS·(−βu)] = (OZ+PY)₁` now rests on one standard operator bound instead of an unexplained
convergence assumption. -/
theorem tailFitWHConvergent_of_L1_tendsto {N : ℕ} {R C : ℝ} {ι : Type*} {l : Filter ι}
    {B1of : (ℝ → ℝ) → Matrix (Fin N) (Fin N) ℂ} (hP : WHProjectionL1 R C B1of)
    {Psifam : ι → ℝ → ℝ} {Psi : ℝ → ℝ}
    (hIfam : ∀ m, MeasureTheory.IntegrableOn (Psifam m) (Set.Ioi R))
    (hI : MeasureTheory.IntegrableOn Psi (Set.Ioi R))
    (hL1 : Tendsto (fun m => ∫ r in Set.Ioi R, |Psifam m r - Psi r|) l (𝓝 0)) :
    TailFitWHConvergent l (fun m => B1of (Psifam m)) (B1of Psi) := by
  intro p q
  refine tendsto_sub_nhds_zero_iff.mp ?_
  have hdiff : ∀ m, ‖B1of (Psifam m) p q - B1of Psi p q‖
      ≤ C * ∫ r in Set.Ioi R, |Psifam m r - Psi r| := by
    intro m
    have h1 : B1of (Psifam m) p q - B1of Psi p q = B1of (Psifam m - Psi) p q := by
      have h := hP.map_sub (Psifam m) Psi (hIfam m) hI
      calc B1of (Psifam m) p q - B1of Psi p q = (B1of (Psifam m) - B1of Psi) p q := rfl
        _ = B1of (Psifam m - Psi) p q := by rw [h]
    rw [h1]
    simpa using hP.bound (Psifam m - Psi) ((hIfam m).sub hI) p q
  exact squeeze_zero_norm hdiff (by simpa using hL1.const_mul C)

/-- **PYE.4 capstone — such a sequence exists.**  For an exponentially decaying closure `Ψ` there
*is* a sequence of finite Yukawa-tail closures whose WH data converge to `Ψ`'s: PYE.4b supplies the
`L¹` approximants, `tailFitWHConvergent_of_L1_tendsto` transports them.  Feeding the result into
`dp_tendsto_py_first_order` gives the DP DCFs converging to the exact first-order PY DCF.

So PYE.4's remaining content is **exactly** `WHProjectionL1` (an MA-class `L¹` operator bound) —
everything else in the lift is proved. -/
theorem exists_tailFit_whConvergent {N : ℕ} {R a C : ℝ} (ha : 0 < a)
    {B1of : (ℝ → ℝ) → Matrix (Fin N) (Fin N) ℂ} (hP : WHProjectionL1 R C B1of)
    (Psi : ℝ → ℝ) (hcont : ContinuousOn Psi (Set.Ici R))
    (hdecay : Tendsto (fun r => Real.exp (a * (r - R)) * Psi r) atTop (𝓝 0)) :
    ∃ fitfam : ℕ → ℝ → ℝ,
      (∀ m, ∃ (n : ℕ) (A z : ℕ → ℝ), StrictMono z ∧ (∀ t, 0 < z t) ∧
        fitfam m = fun r => ∑ t ∈ Finset.range n, A t * Real.exp (-(z t) * r)) ∧
      TailFitWHConvergent atTop (fun m => B1of (fitfam m)) (B1of Psi) := by
  obtain ⟨-, -, -, -, -, -, -, hPsiInt⟩ :=
    exists_yukawa_tail_fit_L1 (R := R) (a := a) (eps := 1) ha one_pos Psi hcont hdecay
  have hfit : ∀ m : ℕ, ∃ f : ℝ → ℝ,
      (∃ (n : ℕ) (A z : ℕ → ℝ), StrictMono z ∧ (∀ t, 0 < z t) ∧
        f = fun r => ∑ t ∈ Finset.range n, A t * Real.exp (-(z t) * r)) ∧
      MeasureTheory.IntegrableOn f (Set.Ioi R) ∧
      ∫ r in Set.Ioi R, |Psi r - f r| ≤ 1 / ((m : ℝ) + 1) := by
    intro m
    obtain ⟨n, A, z, hmono, hpos, -, hint, -⟩ :=
      exists_yukawa_tail_fit_L1 (R := R) (a := a) (eps := 1 / ((m : ℝ) + 1)) ha (by positivity)
        Psi hcont hdecay
    exact ⟨_, ⟨n, A, z, hmono, hpos, rfl⟩, integrableOn_tailSum n A z hpos, hint⟩
  choose fitfam hstruct hfitint hbound using hfit
  refine ⟨fitfam, hstruct, ?_⟩
  refine tailFitWHConvergent_of_L1_tendsto hP hfitint hPsiInt ?_
  refine squeeze_zero (fun m => MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    (fun r _ => abs_nonneg _)) (fun m => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  have hcomm : ∫ r in Set.Ioi R, |fitfam m r - Psi r| = ∫ r in Set.Ioi R, |Psi r - fitfam m r| :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun r _ => abs_sub_comm _ _
  rw [hcomm]
  exact hbound m

/-- **PYE.4 capstone ⭐⭐ — the abstract equivalence `DP-map[g_HS·(−βu)] = (OZ+PY)₁`, assembled into one
conditional theorem.**  Given the single remaining analytic input `WHProjectionL1` (the `L¹`-bounded WH
projection — the matrix Wiener-`1/f` boundary, deliberately a hypothesis rather than a duplicated MA-class
axiom), an exponentially decaying exact outer closure `Ψ`, the first-order OZ/factorization data, and the
identification `hB1of : B1of Ψ = Q̂₀ᵀ·Ĥ₁·Q̂₀` of the projection at the exact closure with the WH datum,
there **is** a family of finite Yukawa-tail closures whose DP direct correlation functions converge
entrywise to the exact first-order PY DCF `C1py`.  It chains `exists_tailFit_whConvergent` (the `L¹`
approximants + their WH convergence) into `dp_tendsto_py_first_order` (the (★) assembly's continuity), so
PYE.4 is now a **complete conditional theorem**: its only hypothesis beyond the physical set-up is
`WHProjectionL1`, and it introduces no axiom (`#print axioms` = std-3). -/
theorem dp_converges_to_py_first_order_of_whProjectionL1
    {N : ℕ} {R a C : ℝ} (ha : 0 < a)
    (Qp Qm T0 S0 H1 C1py : Matrix (Fin N) (Fin N) ℂ)
    {B1of : (ℝ → ℝ) → Matrix (Fin N) (Fin N) ℂ}
    (hP : WHProjectionL1 R C B1of)
    (Psi : ℝ → ℝ) (hcont : ContinuousOn Psi (Set.Ici R))
    (hdecay : Tendsto (fun r => Real.exp (a * (r - R)) * Psi r) atTop (𝓝 0))
    (hoz : H1 * T0 = S0 * C1py) (hTS : T0 * S0 = 1)
    (hfact : T0 = Qp * Qmᵀ) (hT0symm : T0ᵀ = T0)
    (hB1of : B1of Psi = Qpᵀ * H1 * Qp) (i j : Fin N) :
    ∃ fitfam : ℕ → ℝ → ℝ,
      (∀ m, ∃ (n : ℕ) (A z : ℕ → ℝ), StrictMono z ∧ (∀ t, 0 < z t) ∧
        fitfam m = fun r => ∑ t ∈ Finset.range n, A t * Real.exp (-(z t) * r)) ∧
      Tendsto (fun m => (starConjLinear Qm (B1of (fitfam m))) i j) atTop (𝓝 (C1py i j)) := by
  obtain ⟨fitfam, hform, hconv⟩ := exists_tailFit_whConvergent ha hP Psi hcont hdecay
  refine ⟨fitfam, hform, ?_⟩
  rw [hB1of] at hconv
  exact dp_tendsto_py_first_order Qp Qm T0 S0 H1 C1py (Qpᵀ * H1 * Qp)
    hoz hTS hfact hT0symm rfl hconv i j


/-! ## PYE.6 at general `N` — the zeroth-order factor is the physical mixture PY Baxter

The `N = 1` wiring above (`pyBaxterMat`/`pyT0Mat`/`dp_zeroth_order_is_py_n1`) is here lifted to a
general `N`-component mixture, discharging MRS.2's `hfact`/`hT0symm`/`hTS` with the **physical**
mixture Baxter matrix `Q̂₀(ik) = Q0_mat_c_phys (i·k)`:

* `hfact` — `T₀ = Q̂₀(ik)·Q̂₀ᵀ(−ik)` — is `Cmix0_factorization` (MRS.6, by definition of `Ĉ₀`);
* `hT0symm` — `T₀ᵀ = T₀` — is the momentum-space DCF symmetry `Ĉ₀ᵀ = Ĉ₀`, from MRS.7's swap
  identity `Cmix0_phys_swap` (the rank-2 KEY relations of `Q0phys`/`Qppphys`);
* `hTS` — `T₀` invertible — is the physical no-spinodal axiom `pyhs_mixture_no_spinodal`
  (`det Q̂₀(ik) ≠ 0` for real `k ≠ 0`).

⚠ Unlike the `N = 1` case (which uses the PROVEN scalar `pyhs_no_spinodal`), this carries the
project's single physics axiom `pyhs_mixture_no_spinodal` through `hTS`.  The identification of the
zeroth-order symbol `Ĉ₀ = Cmix0(Q̂₀)` with the physical Lebowitz mixture PY DCF is the value route
MRS.8 (`shellForcing_eq_cMixDCFN`, general `N`) together with `Cmix0 = 𝓕(matDCFfull)`
(`MixtureDCFAEInjective`). -/

section PYE6GeneralN

open FMSA.MixtureNoSpinodal FMSA.MixtureBaxterCore FMSA.MatrixQ0 FMSA.MixtureBaxter

variable {N : ℕ} (sigma rho : Fin N → ℝ)

/-- The physical mixture Baxter factor at the Fourier argument `s = i·k`, `Q̂₀(ik)` (`N` species). -/
noncomputable def mixBaxterMat (k : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Q0_mat_c_phys (Complex.I * (k : ℂ)) sigma rho

/-- The physical mixture zeroth-order structure matrix `T₀ = I − Ĉ₀`. -/
noncomputable def mixT0Mat (k : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  1 - Cmix0 (fun s => Q0_mat_c_phys s sigma rho) (Complex.I * (k : ℂ))

/-- **`hfact` (general `N`)** — `T₀ = Q̂₀(ik)·Q̂₀ᵀ(−ik)` (MRS.6 `Cmix0_factorization`). -/
theorem mixT0Mat_factorization (k : ℝ) :
    mixT0Mat sigma rho k
      = mixBaxterMat sigma rho k * (Q0_mat_c_phys (-(Complex.I * (k : ℂ))) sigma rho)ᵀ := by
  rw [mixT0Mat, mixBaxterMat, ← Cmix0_factorization]

/-- **`hT0symm` (general `N`)** — the physical momentum-space DCF symmetry `T₀ᵀ = T₀`
(MRS.7 `Cmix0_phys_swap`, the rank-2 KEY relations). -/
theorem mixT0Mat_isSymm (hrho : ∀ i, 0 ≤ rho i) (hvac : vacMix rho sigma ≠ 0)
    {k : ℝ} (hk : k ≠ 0) :
    (mixT0Mat sigma rho k)ᵀ = mixT0Mat sigma rho k := by
  have hkc : Complex.I * (k : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)
  rw [mixT0Mat, Matrix.transpose_sub, Matrix.transpose_one]
  congr 1
  ext i j
  rw [Matrix.transpose_apply]
  refine Cmix0_phys_swap (fun a => (sigma a : ℂ)) (fun a => (rho a : ℂ))
    (fun b => (Qppphys rho sigma b b : ℂ)) (fun a b => (Q0phys rho sigma a b : ℂ))
    (fun a b => (Qppphys rho sigma a b : ℂ)) (fun a b => (rhoGeoPhys rho a b : ℂ))
    (Real.pi / vacMix rho sigma : ℂ) (xi2 rho sigma : ℂ) (Complex.I * (k : ℂ)) hkc
    ?_ ?_ ?_ ?_ ?_ ?_ j i
  · intro a b
    have h := Q0phys_key_relation rho sigma a b hvac
    have hc : ((Q0phys rho sigma a b : ℝ) : ℂ)
        = ((sigma a / 2 * Qppphys rho sigma a b
            + Real.pi / vacMix rho sigma * sigma b : ℝ) : ℂ) := congrArg _ h
    push_cast at hc ⊢; linear_combination hc
  · intro a b; rfl
  · intro b
    have h := Qppphys_key_relation rho sigma b b hvac
    have hc : ((Qppphys rho sigma b b : ℝ) : ℂ)
        = ((2 * (Real.pi / vacMix rho sigma)
            + (Real.pi / vacMix rho sigma) ^ 2 * xi2 rho sigma * sigma b : ℝ) : ℂ) := congrArg _ h
    push_cast at hc ⊢; linear_combination hc
  · simp only [xi2]; push_cast; ring
  · intro a b; simp only [rhoGeoPhys]; rw [mul_comm (rho a) (rho b)]
  · intro a b l
    have h := rhoGeoPhys_mul_eq rho hrho a b l
    have hc : ((rhoGeoPhys rho a l * rhoGeoPhys rho b l : ℝ) : ℂ)
        = ((rho l * rhoGeoPhys rho a b : ℝ) : ℂ) := congrArg _ h
    push_cast at hc ⊢; rw [hc]

/-- **`hTS` (general `N`)** — `T₀` invertible at every real `k ≠ 0`, from the physical no-spinodal
axiom `pyhs_mixture_no_spinodal` (`det Q̂₀(ik) ≠ 0`).  ⚠ carries `pyhs_mixture_no_spinodal`. -/
theorem mixT0Mat_isUnit_det (hsig : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i)
    (heta : etaMix rho sigma < 1) {k : ℝ} (hk : k ≠ 0) :
    IsUnit (mixT0Mat sigma rho k).det := by
  rw [mixT0Mat_factorization, Matrix.det_mul, Matrix.det_transpose]
  refine isUnit_iff_ne_zero.mpr (mul_ne_zero ?_ ?_)
  · rw [mixBaxterMat]; exact pyhs_mixture_no_spinodal hsig hrho heta hk
  · have h2 := pyhs_mixture_no_spinodal hsig hrho heta (neg_ne_zero.mpr hk)
    have harg : Complex.I * ((-k : ℝ) : ℂ) = -(Complex.I * (k : ℂ)) := by push_cast; ring
    rwa [harg] at h2

/-- **PYE.6 at general `N` — the zeroth-order MRS.2 inputs, discharged with the physical mixture
`Q̂₀`.**  `hfact`/`hT0symm`/`hTS`, so MRS.2 needs only `hoz`. -/
theorem dp_zeroth_order_is_py_N (hsig : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i)
    (heta : etaMix rho sigma < 1) (hvac : vacMix rho sigma ≠ 0) {k : ℝ} (hk : k ≠ 0) :
    mixT0Mat sigma rho k
        = mixBaxterMat sigma rho k * (Q0_mat_c_phys (-(Complex.I * (k : ℂ))) sigma rho)ᵀ ∧
      (mixT0Mat sigma rho k)ᵀ = mixT0Mat sigma rho k ∧
      mixT0Mat sigma rho k * (mixT0Mat sigma rho k)⁻¹ = 1 :=
  ⟨mixT0Mat_factorization sigma rho k,
    mixT0Mat_isSymm sigma rho (fun i => (hrho i).le) hvac hk,
    Matrix.mul_nonsing_inv _ (mixT0Mat_isUnit_det sigma rho hsig hrho heta hk)⟩

/-- **PYE.4 at general `N` with the physical mixture PY zeroth order.**  With the physical mixture
Baxter matrix as `Q̂₀` (so `hfact`/`hT0symm`/`hTS` are discharged), a fitted WH datum equal to Y1.6's
projection `B₁ = Q̂₀ᵀ·Ĥ₁·Q̂₀` yields exactly the first-order DCF.  Only `hoz` remains a physical
input.  ⚠ carries `pyhs_mixture_no_spinodal` via `hTS`. -/
theorem dp_eq_py_first_order_N (hsig : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i)
    (heta : etaMix rho sigma < 1) (hvac : vacMix rho sigma ≠ 0) {k : ℝ} (hk : k ≠ 0)
    (H1 C1py B1fit : Matrix (Fin N) (Fin N) ℂ)
    (hoz : H1 * mixT0Mat sigma rho k = (mixT0Mat sigma rho k)⁻¹ * C1py)
    (hB1 : B1fit = (mixBaxterMat sigma rho k)ᵀ * H1 * mixBaxterMat sigma rho k) :
    starConjLinear (Q0_mat_c_phys (-(Complex.I * (k : ℂ))) sigma rho) B1fit = C1py :=
  dp_eq_py_first_order_of_exact_fit (mixBaxterMat sigma rho k)
    (Q0_mat_c_phys (-(Complex.I * (k : ℂ))) sigma rho) (mixT0Mat sigma rho k)
    (mixT0Mat sigma rho k)⁻¹ H1 C1py B1fit B1fit hoz
    (Matrix.mul_nonsing_inv _ (mixT0Mat_isUnit_det sigma rho hsig hrho heta hk))
    (mixT0Mat_factorization sigma rho k)
    (mixT0Mat_isSymm sigma rho (fun i => (hrho i).le) hvac hk) hB1 rfl

end PYE6GeneralN


/-! ## HNCB.2 — the fixed-rate predictor–corrector pull-back rung is affine

With the tail **rates frozen**, one predictor–corrector rung maps the finite amplitude vector `K̃` to
`K̃' = refit(−βu + B·h₁[K̃])`, where every sub-step is `ℂ`-linear: `C̃₁ = dpDCF[K̃]` (the PYE.2 fixed-rate
DP map `dpDCFLinear`), `h₁ = F⁻¹·C̃₁·F⁻¹` (the OZ apply `starConjLinear F⁻¹`), the bridge scaling `B·`,
the amplitude embedding `embed`, and the fixed-rate least-squares `refit`.  So the rung is **affine**:
`K̃' = a + L·K̃` with `a = refit(−βu)` and `L` the bundled composite.  (With free rates the DP map is
*not* linear — the rates enter the denominators `s + z` — so the frozen-rate discipline is exactly what
makes this hold; cf. `dpTailsLinear`'s warning.)  This is the map whose unique fixed point
`K̃* = (I−L)⁻¹a` closes HNCB.3. -/

section HNCB2
variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The fixed-rate predictor–corrector pull-back rung `K̃ ↦ refit(−βu + B·(F⁻¹·C̃₁·F⁻¹))` with
`C̃₁ = dpDCF[embed K̃]` (rates frozen inside `dpDCFLinear`). -/
noncomputable def pullbackRung
    (embed : V →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ) (refit : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] V)
    (Qm Amat : Matrix (Fin N) (Fin N) ℂ) (zmat : Fin N → Fin N → ℂ) (s : ℂ)
    (Finv : Matrix (Fin N) (Fin N) ℂ) (bridgeB : ℂ) (minusBetaU : Matrix (Fin N) (Fin N) ℂ)
    (Ktilde : V) : V :=
  refit (minusBetaU + bridgeB •
    starConjLinear Finv (dpDCFLinear Qm Amat zmat s (embed Ktilde)))

/-- The linear part `L` of the pull-back rung, as a bundled `ℂ`-linear map
`L = B · (refit ∘ starConj(F⁻¹) ∘ dpDCFLinear ∘ embed)`. -/
noncomputable def pullbackLinearPart
    (embed : V →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ) (refit : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] V)
    (Qm Amat : Matrix (Fin N) (Fin N) ℂ) (zmat : Fin N → Fin N → ℂ) (s : ℂ)
    (Finv : Matrix (Fin N) (Fin N) ℂ) (bridgeB : ℂ) : V →ₗ[ℂ] V :=
  bridgeB • (refit ∘ₗ (starConjLinear Finv) ∘ₗ dpDCFLinear Qm Amat zmat s ∘ₗ embed)

/-- **HNCB.2 ⭐ — the fixed-rate pull-back rung is affine:** `K̃' = a + L·K̃`, with constant term
`a = refit(−βu)` and linear part `L = pullbackLinearPart`.  Because every sub-step (`dpDCFLinear`,
`starConjLinear`, the bridge scaling, `refit`, `embed`) is `ℂ`-linear, the rung splits as a constant
plus a bundled linear map.  This is precisely the affineness the free-rate corrector lacks. -/
theorem pullbackRung_affine
    (embed : V →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ) (refit : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] V)
    (Qm Amat : Matrix (Fin N) (Fin N) ℂ) (zmat : Fin N → Fin N → ℂ) (s : ℂ)
    (Finv : Matrix (Fin N) (Fin N) ℂ) (bridgeB : ℂ) (minusBetaU : Matrix (Fin N) (Fin N) ℂ)
    (Ktilde : V) :
    pullbackRung embed refit Qm Amat zmat s Finv bridgeB minusBetaU Ktilde
      = refit minusBetaU
        + pullbackLinearPart embed refit Qm Amat zmat s Finv bridgeB Ktilde := by
  simp only [pullbackRung, pullbackLinearPart, map_add, map_smul, LinearMap.smul_apply,
    LinearMap.comp_apply]

/-- The affine rung's constant term is `refit(−βu)` — its value at `K̃ = 0`. -/
theorem pullbackRung_zero
    (embed : V →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ) (refit : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] V)
    (Qm Amat : Matrix (Fin N) (Fin N) ℂ) (zmat : Fin N → Fin N → ℂ) (s : ℂ)
    (Finv : Matrix (Fin N) (Fin N) ℂ) (bridgeB : ℂ) (minusBetaU : Matrix (Fin N) (Fin N) ℂ) :
    pullbackRung embed refit Qm Amat zmat s Finv bridgeB minusBetaU 0 = refit minusBetaU := by
  rw [pullbackRung_affine]; simp

end HNCB2


end FMSA.FirstOrderClosure
