/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAMixtureBHRootSmooth
import LeanCode.YukawaOZMix.MSAMixtureBHRootUneq
import LeanCode.YukawaOZMix.MixtureBlumHoyeDerivation

/-!
# MSAEMIX.6 at **unequal** σ — the matrix Blum–Høye root is `C^∞` at `K = 0` (general `N`)

The unequal-diameter analogue of `MSAMixtureBHRootSmooth`.  The physical **unequal**-σ mixture MSA
amplitudes `(Dt, Gt)` are a `C^∞` family of the coupling near `K = 0`, seeded from a `MixBHRootUneq`
hard-sphere root.  The scaffolding transfers **unchanged** from the equal-σ file, because the only
difference — the σ-edge recentering factor `e^{z·edgeLo σ · ·}` on the Baxter transform — is a
`σ`-**constant** (it carries no `(Dt, Gt)` dependence), so every amplitude is still a *polynomial in the
entries of `(Dt, Gt)`* and the residual is `C^∞` by the same recipe.  (Structurally,
`FMSA.ExactMSA.MixLeg3.qhatMixRuneq_recentered_eq_qhatMixR` shows the recentered transform is the equal-σ
`qhatMixR` at the row diameter, so the two residuals differ only by `σ`-constant factors.)

Items landed here (all std-3):
* **item 2** — `matBhResidualUneq` + `matBhResidualUneq_eq_zero_iff` (zero set = `MixBHRootUneq`);
* **item 3** — `contDiff_matBhResidualUneq` (`ContDiff ℝ ⊤`);
* **item 4** — `matBhResidualUneq_base_eq` (base point is a root iff `Gt₀` is a zero-coupling root);
* **capstone** — `exists_contDiffAt_matBhRootUneq`, the smooth family, taking the raw Fréchet-derivative
  invertibility `hjac` as input;
* **item 5** — `exists_contDiffAt_matBhRootUneq_physical` discharges `hjac` down to the two asymmetric
  row-diameter HS-block determinants, and `exists_contDiffAt_matBhRootUneq_of_physical` closes them
  **unconditionally**: the recentering + a diagonal-conjugation Sylvester argument reduce both to the
  *same* physical `Q0_mat_phys` the equal-σ file uses, so M.4's `Q0_mat_phys_isUnit_det` (general σ,
  std-3) discharges them with no equal-σ hypothesis and no physics axiom.  So the unequal-σ family now
  matches the equal-σ grade exactly — the sole remaining grade is Blum–Høye transcription faithfulness,
  as at `N = 1`.
-/

open scoped BigOperators

namespace MSAMixture

variable {N : ℕ}

/-! ### Item 2 — the unequal-σ matrix Blum–Høye residual map -/

/-- **The unequal-σ matrix Blum–Høye residual** whose zero set is `MixBHRootUneq`.  Identical in shape to
the equal-σ `matBhResidual`, but with the unequal-σ Baxter transform `qhatMixRuneq` and the σ-edge
recentering factors `e^{z·edgeLo σ j l}` (c-side) / `e^{z·edgeLo σ l j}` (g-side).  The coupling enters
as a scalar scale `τ` on `Kdir`, so the domain is `ℝ × (Dt, Gt)`. -/
noncomputable def matBhResidualUneq (z : ℝ) (rho σ : Fin N → ℝ)
    (Kdir : Matrix (Fin N) (Fin N) ℝ)
    (q : ℝ × (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ)) :
    Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ :=
  let Dt := q.2.1
  let Gt := q.2.2
  let QRu := qhatMixRuneq z σ (qpMat z rho σ Gt Dt) (Wt z rho Gt Dt)
    (Ct z rho σ Gt Dt) (AVec z rho σ Gt Dt) z
  (Matrix.of fun i j => (∑ l, Dt i l * ((if l = j then (1 : ℝ) else 0)
        - rho l * (Real.exp (z * edgeLo σ j l) * QRu j l)))
      - 2 * Real.pi * (q.1 • Kdir) i j / z,
   Matrix.of fun i j =>
      2 * Real.pi * (∑ l, Gt i l * ((if l = j then (1 : ℝ) else 0)
        - rho l * (Real.exp (z * edgeLo σ l j) * QRu l j)))
      - (AVec z rho σ Gt Dt j + z * qpMat z rho σ Gt Dt i j
          + z ^ 2 * Ct z rho σ Gt Dt i j / 2) / z ^ 2)

/-- **Item 2 correctness: the residual's zero set is exactly `MixBHRootUneq`.** -/
theorem matBhResidualUneq_eq_zero_iff (z : ℝ) (rho σ : Fin N → ℝ)
    (Kdir : Matrix (Fin N) (Fin N) ℝ) (τ : ℝ) (Dt Gt : Matrix (Fin N) (Fin N) ℝ) :
    matBhResidualUneq z rho σ Kdir (τ, (Dt, Gt)) = 0
      ↔ MixBHRootUneq z rho σ Gt Dt (τ • Kdir) := by
  rw [matBhResidualUneq, MixBHRootUneq, Prod.mk_eq_zero, ← Matrix.ext_iff, ← Matrix.ext_iff]
  simp only [Matrix.of_apply, Matrix.zero_apply, sub_eq_zero, Matrix.smul_apply, smul_eq_mul]

/-- **Item 4 — the base equation.**  The HS point `(0, Gt₀)` at coupling `τ = 0` is a root of the
residual iff `Gt₀` is a zero-coupling `MixBHRootUneq`. -/
theorem matBhResidualUneq_base_eq (z : ℝ) (rho σ : Fin N → ℝ)
    (Kdir Gt₀ : Matrix (Fin N) (Fin N) ℝ) (hroot0 : MixBHRootUneq z rho σ Gt₀ 0 0) :
    matBhResidualUneq z rho σ Kdir (0, (0, Gt₀)) = 0 :=
  (matBhResidualUneq_eq_zero_iff z rho σ Kdir 0 0 Gt₀).mpr (by simpa using hroot0)

section Smooth
open scoped Matrix.Norms.Frobenius

/-- ⭐⭐ **MSAEMIX.6 item 3 at unequal σ.**  The unequal-σ Blum–Høye residual map is `C^∞`.  Every
amplitude is a polynomial in the entries of `(Dt, Gt)` with constant coefficients (the σ-edge
recentering `e^{z·edgeLo}` and the `qhatMixRuneq` exponentials are `σ`-constants), so `fun_prop`
discharges each entry after `simp` unfolds the definitions, and `contDiff_matrix_of` assembles. -/
theorem contDiff_matBhResidualUneq (z : ℝ) (rho σ : Fin N → ℝ)
    (Kdir : Matrix (Fin N) (Fin N) ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (matBhResidualUneq z rho σ Kdir) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun q => (matBhResidualUneq z rho σ Kdir q).1) := by
    simp only [matBhResidualUneq]; apply contDiff_matrix_of; intro i j
    simp only [qhatMixRuneq, qpMat, AVec, qpMSA, AMSA, mixDqp, mixDA, mixM, mixN, Wt, Ct, gam,
      Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun q => (matBhResidualUneq z rho σ Kdir q).2) := by
    simp only [matBhResidualUneq]; apply contDiff_matrix_of; intro i j
    simp only [qhatMixRuneq, qpMat, AVec, qpMSA, AMSA, mixDqp, mixDA, mixM, mixN, Wt, Ct, gam,
      Matrix.smul_apply, smul_eq_mul]
    fun_prop
  exact h1.prodMk h2

/-- ⭐⭐⭐ **MSAEMIX.6 capstone at unequal σ (assembly).**  Given the HS seed `Gt₀`
(`MixBHRootUneq … Gt₀ 0 0`) and the partial-Jacobian invertibility `hjac`, the unequal-σ mixture MSA
amplitudes form a `C^∞` family of the coupling near `K = 0`.  Items 1–4 are discharged (the same IFT
engine `exists_contDiffAt_root_of_prodDomain_ift`, `contDiff_matBhResidualUneq`,
`matBhResidualUneq_base_eq`); only `hjac` remains — the unequal-σ item-5 obligation. -/
theorem exists_contDiffAt_matBhRootUneq (z : ℝ) (rho σ : Fin N → ℝ)
    (Kdir Gt₀ : Matrix (Fin N) (Fin N) ℝ) (hroot0 : MixBHRootUneq z rho σ Gt₀ 0 0)
    (hjac : (fderiv ℝ (matBhResidualUneq z rho σ Kdir) (0, (0, Gt₀)) ∘L
        ContinuousLinearMap.inr ℝ ℝ
          (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ)).IsInvertible) :
    ∃ ψ : ℝ → Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ,
      ψ 0 = (0, Gt₀) ∧
      (∀ᶠ τ in nhds (0 : ℝ), MixBHRootUneq z rho σ (ψ τ).2 (ψ τ).1 (τ • Kdir)) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) ψ 0 := by
  obtain ⟨ψ, h0, hroot, hcd⟩ :=
    FMSA.MSASolutionFamily.exists_contDiffAt_root_of_prodDomain_ift (by simp)
    (contDiff_matBhResidualUneq z rho σ Kdir).contDiffAt
    (matBhResidualUneq_base_eq z rho σ Kdir Gt₀ hroot0) hjac
  refine ⟨ψ, h0, ?_, hcd⟩
  filter_upwards [hroot] with τ hτ
  exact (matBhResidualUneq_eq_zero_iff z rho σ Kdir τ (ψ τ).1 (ψ τ).2).mp hτ

/-! ### Item 5 — the fderiv shape, discharging `hjac` down to the two physical HS-block dets

The generic block-triangular derivative lemma `matBhResidualShape_hasFDerivAt` and the amplitude
`Dt = 0` lemmas (`qpMat_zero_Dt`, …) are shared with the equal-σ file; only the dressing matrices carry
the σ-edge recentering.  `resGuneq`/`resHuneq` are the unequal-σ diagonal blocks (`resD` — the g-source,
carrying no recentering — is reused as `resD z 0 rho σ`, its `sig` argument being unused). -/

/-- The unequal-σ c-side dressing block (recentered). -/
noncomputable def resGuneq (z : ℝ) (rho σ : Fin N → ℝ)
    (p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun l j => (if l = j then (1 : ℝ) else 0) - rho l *
    (Real.exp (z * edgeLo σ j l) * qhatMixRuneq z σ (qpMat z rho σ p.2 p.1) (Wt z rho p.2 p.1)
      (Ct z rho σ p.2 p.1) (AVec z rho σ p.2 p.1) z j l)

/-- The unequal-σ g-side dressing block (recentered). -/
noncomputable def resHuneq (z : ℝ) (rho σ : Fin N → ℝ)
    (p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun l j => (if l = j then (1 : ℝ) else 0) - rho l *
    (Real.exp (z * edgeLo σ l j) * qhatMixRuneq z σ (qpMat z rho σ p.2 p.1) (Wt z rho p.2 p.1)
      (Ct z rho σ p.2 p.1) (AVec z rho σ p.2 p.1) z l j)

/-- The unequal-σ residual at `Dt = 0` in dressing-matrix (`p.1·resG, 2π·(p.2·resH) − resD`) form. -/
theorem matBhResidualUneq_zero_eq (z : ℝ) (rho σ : Fin N → ℝ)
    (Kdir : Matrix (Fin N) (Fin N) ℝ) (p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) :
    matBhResidualUneq z rho σ Kdir (0, p)
      = (p.1 * resGuneq z rho σ p,
         (2 * Real.pi) • (p.2 * resHuneq z rho σ p) - resD z 0 rho σ p) := by
  rw [matBhResidualUneq]
  refine Prod.ext ?_ ?_
  · ext i j
    simp only [Matrix.of_apply, zero_smul, Matrix.zero_apply, mul_zero, zero_div, sub_zero,
      Matrix.mul_apply, resGuneq]
  · ext i j
    simp only [Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      resHuneq, resD, Finset.mul_sum]

theorem contDiff_resGuneq (z : ℝ) (rho σ : Fin N → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (resGuneq z rho σ) := by
  unfold resGuneq; apply contDiff_matrix_of; intro i j
  simp only [qhatMixRuneq, qpMat, AVec, qpMSA, AMSA, mixDqp, mixDA, mixM, mixN, Wt, Ct, gam,
    Matrix.smul_apply, smul_eq_mul]
  fun_prop

theorem contDiff_resHuneq (z : ℝ) (rho σ : Fin N → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (resHuneq z rho σ) := by
  unfold resHuneq; apply contDiff_matrix_of; intro i j
  simp only [qhatMixRuneq, qpMat, AVec, qpMSA, AMSA, mixDqp, mixDA, mixM, mixN, Wt, Ct, gam,
    Matrix.smul_apply, smul_eq_mul]
  fun_prop

theorem resHuneq_zero_const (z : ℝ) (rho σ : Fin N → ℝ) (Gt Gt' : Matrix (Fin N) (Fin N) ℝ) :
    resHuneq z rho σ (0, Gt) = resHuneq z rho σ (0, Gt') := by
  simp only [resHuneq, qpMat_zero_Dt, Wt_zero_Dt, Ct_zero_Dt, AVec_zero_Dt]

theorem resHuneq_fderiv_inr (z : ℝ) (rho σ : Fin N → ℝ) (Gt₀ : Matrix (Fin N) (Fin N) ℝ) :
    fderiv ℝ (resHuneq z rho σ) (0, Gt₀) ∘L
      ContinuousLinearMap.inr ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ) = 0 := by
  have hcd : HasFDerivAt (resHuneq z rho σ) (fderiv ℝ (resHuneq z rho σ) (0, Gt₀)) (0, Gt₀) :=
    ((contDiff_resHuneq z rho σ).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp : HasFDerivAt (fun Gt => resHuneq z rho σ (0, Gt))
      (fderiv ℝ (resHuneq z rho σ) (0, Gt₀) ∘L
        ContinuousLinearMap.inr ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ)) Gt₀ :=
    hcd.comp Gt₀ (ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.inr ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ)))
  have hconst : HasFDerivAt (fun Gt => resHuneq z rho σ (0, Gt))
      (0 : Matrix (Fin N) (Fin N) ℝ →L[ℝ] Matrix (Fin N) (Fin N) ℝ) Gt₀ := by
    have he : (fun Gt => resHuneq z rho σ (0, Gt)) = fun _ => resHuneq z rho σ (0, Gt₀) := by
      funext Gt; exact resHuneq_zero_const z rho σ Gt Gt₀
    rw [he]; exact hasFDerivAt_const _ _
  exact hcomp.unique hconst

/-- ⭐⭐⭐ **MSAEMIX.6 at unequal σ, item 5 discharged modulo the two physical HS-block dets.**  The
unequal-σ mixture MSA amplitudes are a `C^∞` family of the coupling near `K = 0`, from a `MixBHRootUneq`
seed and the two hard-sphere OZ blocks `resGuneq/resHuneq (0,Gt₀)` nonsingular.  The block-triangular
fderiv transcription is proved internally (reusing the shared `matBhResidualShape_hasFDerivAt`); the
`e^{z·edgeLo}` recentering only changes the diagonal blocks, not the derivative structure.  The exact
unequal-σ analogue of `exists_contDiffAt_matBhRoot_physical` — same "two of three parts" grade, now with
the two dets the *asymmetric row-diameter* HS-OZ matrices. -/
theorem exists_contDiffAt_matBhRootUneq_physical (z : ℝ) (rho σ : Fin N → ℝ)
    (Kdir Gt₀ : Matrix (Fin N) (Fin N) ℝ) (hroot0 : MixBHRootUneq z rho σ Gt₀ 0 0)
    (h₁ : IsUnit (resGuneq z rho σ (0, Gt₀)).det)
    (h₂ : IsUnit (resHuneq z rho σ (0, Gt₀)).det) :
    ∃ ψ : ℝ → Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ,
      ψ 0 = (0, Gt₀) ∧
      (∀ᶠ τ in nhds (0 : ℝ), MixBHRootUneq z rho σ (ψ τ).2 (ψ τ).1 (τ • Kdir)) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) ψ 0 := by
  have hstruct := matBhResidualShape_hasFDerivAt
    (Gmat := resGuneq z rho σ) (Hmat := resHuneq z rho σ) (Dmat := resD z 0 rho σ)
    (N₁ := resGuneq z rho σ (0, Gt₀)) (N₂ := resHuneq z rho σ (0, Gt₀))
    (((contDiff_resGuneq z rho σ).differentiable (by simp)).differentiableAt.hasFDerivAt)
    (((contDiff_resHuneq z rho σ).differentiable (by simp)).differentiableAt.hasFDerivAt)
    (((contDiff_resD z 0 rho σ).differentiable (by simp)).differentiableAt.hasFDerivAt)
    rfl rfl (resHuneq_fderiv_inr z rho σ Gt₀) (resD_fderiv_inr z 0 rho σ Gt₀)
  have hpart := hstruct.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun p => matBhResidualUneq_zero_eq z rho σ Kdir p))
  have hmatcd : HasFDerivAt (matBhResidualUneq z rho σ Kdir)
      (fderiv ℝ (matBhResidualUneq z rho σ Kdir) (0, (0, Gt₀))) (0, (0, Gt₀)) :=
    ((contDiff_matBhResidualUneq z rho σ Kdir).differentiable
      (by simp)).differentiableAt.hasFDerivAt
  have hcomp : HasFDerivAt (fun p => matBhResidualUneq z rho σ Kdir (0, p))
      (fderiv ℝ (matBhResidualUneq z rho σ Kdir) (0, (0, Gt₀)) ∘L
        ContinuousLinearMap.inr ℝ ℝ
          (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ)) (0, Gt₀) :=
    hmatcd.comp (0, Gt₀) (ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.inr ℝ ℝ (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ)))
  have hshape := hcomp.unique hpart
  exact exists_contDiffAt_matBhRootUneq z rho σ Kdir Gt₀ hroot0
    (hshape ▸ matBhJacobianCLM_isInvertible _ h₁ h₂)

/-- ⭐⭐⭐ **MSAEMIX.6 at unequal σ — the two dets discharged from strict row diagonal dominance.**  When
the asymmetric row-diameter HS-OZ blocks `resGuneq/resHuneq (0,Gt₀)` are strictly diagonally dominant,
their determinants are units (Mathlib's Gershgorin `det_ne_zero_of_sum_row_lt_diag`), so the unequal-σ
mixture MSA amplitudes are a `C^∞` family near `K = 0` from only the seed and the two checkable
inequalities — the unequal-σ analogue of `exists_contDiffAt_matBhRoot_of_diag_dom`.  (This is now
subsumed by the fully *unconditional* `exists_contDiffAt_matBhRootUneq_of_physical` below, which reduces
both dets to `Q0_mat_phys` and closes them via M.4's `Q0_mat_phys_isUnit_det`; kept for the checkable
diagonal-dominance route.) -/
theorem exists_contDiffAt_matBhRootUneq_of_diag_dom (z : ℝ) (rho σ : Fin N → ℝ)
    (Kdir Gt₀ : Matrix (Fin N) (Fin N) ℝ) (hroot0 : MixBHRootUneq z rho σ Gt₀ 0 0)
    (hdomG : ∀ k, ∑ j ∈ Finset.univ.erase k, |resGuneq z rho σ (0, Gt₀) k j|
      < |resGuneq z rho σ (0, Gt₀) k k|)
    (hdomH : ∀ k, ∑ j ∈ Finset.univ.erase k, |resHuneq z rho σ (0, Gt₀) k j|
      < |resHuneq z rho σ (0, Gt₀) k k|) :
    ∃ ψ : ℝ → Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ,
      ψ 0 = (0, Gt₀) ∧
      (∀ᶠ τ in nhds (0 : ℝ), MixBHRootUneq z rho σ (ψ τ).2 (ψ τ).1 (τ • Kdir)) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) ψ 0 :=
  exists_contDiffAt_matBhRootUneq_physical z rho σ Kdir Gt₀ hroot0
    (isUnit_iff_ne_zero.mpr
      (det_ne_zero_of_sum_row_lt_diag (by simpa only [Real.norm_eq_abs] using hdomG)))
    (isUnit_iff_ne_zero.mpr
      (det_ne_zero_of_sum_row_lt_diag (by simpa only [Real.norm_eq_abs] using hdomH)))

/-! #### Item 5 **unconditional** discharge — reduce the two asymmetric dets to `Q0_mat_phys` (M.4)

The asymmetric row-diameter blocks reduce to the **same** physical Baxter matrix `Q0_mat_phys` that
the equal-σ file uses, so M.4's unconditional positivity `Q0_mat_phys_isUnit_det` discharges both dets
with **no** equal-σ hypothesis and **no** physics axiom.  Two structural facts make this work:

* the recentering `qhatMixRuneq_recentered_eq_qhatMixR` (`e^{z·edgeLo}·qhatMixRuneq = qhatMixR` at the
  *row* diameter) puts the per-row `σ_l` inside, so `resHuneq(0,Gt₀) = 1 − D_ρ·hsCoreUneq` and
  `resGuneq(0,Gt₀) = 1 − D_ρ·hsCoreUneqᵀ`, with `hsCoreUneq_lj = p₁(σ_l)·Q0phys_lj + p₂(σ_l)·Qppphys_lj`;
* the physical Baxter matrix is `Q0_mat_phys z σ ρ = 1 − D_{√ρ·e^{zσ/2}}·hsCoreUneq·D_{√ρ·e^{-zσ/2}}` —
  the Baxter shift `e^{-(σ_j-σ_l)z/2} = e^{zσ_l/2}·e^{-zσ_j/2}` factors into a *diagonal conjugation*,
  and under Sylvester `det(1-AB)=det(1-BA)` the two diagonals recombine to `D_ρ` (the exponentials cancel
  — exactly the role `hσ` played at equal σ, now automatic).

Hence `det resGuneq = det resHuneq = det Q0_mat_phys` unconditionally, so the equal-σ rank-2
Weinstein–Aronszajn positivity `Q0_moment_det_pos` (general σ, no diameter equality) closes the unequal-σ
case verbatim.  This retires the last open crux: the "asymmetric block breaks the rank-2 argument" worry
was unfounded — the asymmetry is a pure diagonal conjugation invisible to the determinant. -/
open FMSA.MatrixQ0

/-- The unequal-σ **row-diameter** hard-sphere Baxter core:
`hsCoreUneq_lj = p₁(σ_l)·Q0phys_lj + p₂(σ_l)·Qppphys_lj`, the per-row analogue of the equal-σ `hsCore`
(there `p₁,p₂` used the single `sig`; here the recentering supplies the row diameter `σ_l`). -/
noncomputable def hsCoreUneq (z : ℝ) (rho σ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun l j =>
    (1 - z * σ l - Real.exp (-(z * σ l))) / z ^ 2 * Q0phys rho σ l j
    + (1 - z * σ l + (z * σ l) ^ 2 / 2 - Real.exp (-(z * σ l))) / z ^ 3 * Qppphys rho σ l j

theorem resHuneq_eq_baxter (z : ℝ) (rho σ : Fin N → ℝ) (Gt₀ : Matrix (Fin N) (Fin N) ℝ) :
    resHuneq z rho σ (0, Gt₀) = 1 - Matrix.diagonal rho * hsCoreUneq z rho σ := by
  ext l j
  simp only [resHuneq, Matrix.of_apply]
  rw [FMSA.ExactMSA.MixLeg3.qhatMixRuneq_recentered_eq_qhatMixR z σ _ _ _ _ l j]
  simp only [qpMat_zero_Dt, Wt_zero_Dt, Ct_zero_Dt, AVec_zero_Dt, qhatMixR, qp0Mat, A0Vec,
    hsCoreUneq, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_mul,
    Matrix.zero_apply, Pi.zero_apply, Qppphys, zero_div, zero_mul, add_zero]

theorem resGuneq_eq_baxter (z : ℝ) (rho σ : Fin N → ℝ) (Gt₀ : Matrix (Fin N) (Fin N) ℝ) :
    resGuneq z rho σ (0, Gt₀) = 1 - Matrix.diagonal rho * (hsCoreUneq z rho σ).transpose := by
  ext l j
  simp only [resGuneq, Matrix.of_apply]
  rw [FMSA.ExactMSA.MixLeg3.qhatMixRuneq_recentered_eq_qhatMixR z σ _ _ _ _ j l]
  simp only [qpMat_zero_Dt, Wt_zero_Dt, Ct_zero_Dt, AVec_zero_Dt, qhatMixR, qp0Mat, A0Vec,
    hsCoreUneq, Matrix.transpose_apply, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_mul, Matrix.zero_apply, Pi.zero_apply, Qppphys, zero_div, zero_mul, add_zero]

/-- The physical Baxter matrix as a **diagonal conjugation** of the row-diameter core: the Baxter shift
`e^{-(σ_j-σ_l)z/2}` splits as `e^{zσ_l/2}·e^{-zσ_j/2}`, absorbed into the two diagonals.  No `hσ`. -/
theorem Q0phys_eq_baxter_uneq (z : ℝ) (rho σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ rho i) :
    Q0_mat_phys z σ rho
      = 1 - Matrix.diagonal (fun i => Real.sqrt (rho i) * Real.exp (z * σ i / 2))
          * hsCoreUneq z rho σ
          * Matrix.diagonal (fun i => Real.sqrt (rho i) * Real.exp (-(z * σ i / 2))) := by
  ext l j
  simp only [Q0_mat_phys, Q0_mat, q0_entry, rhoGeoPhys, hsCoreUneq, Matrix.of_apply,
    Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hexp : Real.exp (z * σ l / 2) * Real.exp (-(z * σ j / 2))
      = Real.exp (-((σ j - σ l) / 2 * z)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [Real.sqrt_mul (hρ l), ← hexp]; ring

/-- ⭐ Both asymmetric HS-OZ blocks and the physical Baxter matrix share the determinant, **no `hσ`**:
plain-ρ vs the `√ρ·e^{±zσ/2}` diagonal conjugation drops out under Sylvester `det(1-AB)=det(1-BA)`. -/
theorem detHuneq_eq_Q0 (z : ℝ) (rho σ : Fin N → ℝ) (Gt₀ : Matrix (Fin N) (Fin N) ℝ)
    (hρ : ∀ i, 0 ≤ rho i) :
    (resHuneq z rho σ (0, Gt₀)).det = (Q0_mat_phys z σ rho).det := by
  have hd : Matrix.diagonal (fun i => (Real.sqrt (rho i) * Real.exp (-(z * σ i / 2)))
        * (Real.sqrt (rho i) * Real.exp (z * σ i / 2)))
      = (Matrix.diagonal rho : Matrix (Fin N) (Fin N) ℝ) := by
    congr 1; ext i
    have he : Real.exp (-(z * σ i / 2)) * Real.exp (z * σ i / 2) = 1 := by
      rw [← Real.exp_add]; norm_num
    calc (Real.sqrt (rho i) * Real.exp (-(z * σ i / 2)))
            * (Real.sqrt (rho i) * Real.exp (z * σ i / 2))
        = (Real.sqrt (rho i) * Real.sqrt (rho i))
            * (Real.exp (-(z * σ i / 2)) * Real.exp (z * σ i / 2)) := by ring
      _ = rho i := by rw [Real.mul_self_sqrt (hρ i), he, mul_one]
  rw [resHuneq_eq_baxter, Q0phys_eq_baxter_uneq z rho σ hρ,
    Matrix.det_one_sub_mul_comm (Matrix.diagonal rho) (hsCoreUneq z rho σ),
    mul_assoc (Matrix.diagonal (fun i => Real.sqrt (rho i) * Real.exp (z * σ i / 2)))
      (hsCoreUneq z rho σ),
    Matrix.det_one_sub_mul_comm
      (Matrix.diagonal (fun i => Real.sqrt (rho i) * Real.exp (z * σ i / 2)))
      (hsCoreUneq z rho σ
        * Matrix.diagonal (fun i => Real.sqrt (rho i) * Real.exp (-(z * σ i / 2)))),
    mul_assoc, Matrix.diagonal_mul_diagonal, hd]

theorem detGuneq_eq_Q0 (z : ℝ) (rho σ : Fin N → ℝ) (Gt₀ : Matrix (Fin N) (Fin N) ℝ)
    (hρ : ∀ i, 0 ≤ rho i) :
    (resGuneq z rho σ (0, Gt₀)).det = (Q0_mat_phys z σ rho).det := by
  rw [resGuneq_eq_baxter,
    ← Matrix.det_transpose (1 - Matrix.diagonal rho * (hsCoreUneq z rho σ).transpose),
    Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose,
    Matrix.det_one_sub_mul_comm (hsCoreUneq z rho σ) (Matrix.diagonal rho),
    ← resHuneq_eq_baxter z rho σ Gt₀, detHuneq_eq_Q0 z rho σ Gt₀ hρ]

/-- ⭐⭐⭐ MSAEMIX.6 at unequal σ with the dets reduced to `Q0_mat_phys` nonsingular. -/
theorem exists_contDiffAt_matBhRootUneq_of_Q0 (z : ℝ) (rho σ : Fin N → ℝ)
    (Kdir Gt₀ : Matrix (Fin N) (Fin N) ℝ) (hρ : ∀ i, 0 ≤ rho i)
    (hroot0 : MixBHRootUneq z rho σ Gt₀ 0 0) (hQ0 : IsUnit (Q0_mat_phys z σ rho).det) :
    ∃ ψ : ℝ → Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ,
      ψ 0 = (0, Gt₀) ∧
      (∀ᶠ τ in nhds (0 : ℝ), MixBHRootUneq z rho σ (ψ τ).2 (ψ τ).1 (τ • Kdir)) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) ψ 0 :=
  exists_contDiffAt_matBhRootUneq_physical z rho σ Kdir Gt₀ hroot0
    (by rw [detGuneq_eq_Q0 z rho σ Gt₀ hρ]; exact hQ0)
    (by rw [detHuneq_eq_Q0 z rho σ Gt₀ hρ]; exact hQ0)

/-- ⭐⭐⭐ **MSAEMIX.6 at unequal σ — fully discharged, no det hypothesis at all (std-3).**  At any
physical unequal-σ mixture (`z > 0`, `vacMix > 0`, `ρ ≥ 0`, `σ > 0`) with a hard-sphere seed
`MixBHRootUneq … Gt₀ 0 0`, the unequal-σ mixture MSA amplitudes `(Dt, Gt)` are a `C^∞` family of the
coupling near `K = 0`.  The two asymmetric HS-block determinants reduce (unconditionally) to
`Q0_mat_phys`, discharged by M.4 `FMSA.MatrixQ0.Q0_mat_phys_isUnit_det` (general `N`, general σ, std-3 —
the rank-two Weinstein–Aronszajn positivity `Q0_moment_det_pos`).  This is the exact unequal-σ analogue
of the equal-σ `exists_contDiffAt_matBhRoot_of_physical`; the sole remaining grade is the transcription
faithfulness of the Blum–Høye system, as at `N = 1`. -/
theorem exists_contDiffAt_matBhRootUneq_of_physical (z : ℝ) (rho σ : Fin N → ℝ)
    (Kdir Gt₀ : Matrix (Fin N) (Fin N) ℝ)
    (hz : 0 < z) (hvac : 0 < vacMix rho σ) (hrho : ∀ i, 0 ≤ rho i) (hsigma : ∀ i, 0 < σ i)
    (hroot0 : MixBHRootUneq z rho σ Gt₀ 0 0) :
    ∃ ψ : ℝ → Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ,
      ψ 0 = (0, Gt₀) ∧
      (∀ᶠ τ in nhds (0 : ℝ), MixBHRootUneq z rho σ (ψ τ).2 (ψ τ).1 (τ • Kdir)) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) ψ 0 :=
  exists_contDiffAt_matBhRootUneq_of_Q0 z rho σ Kdir Gt₀ hrho hroot0
    (Q0_mat_phys_isUnit_det hz hvac hrho hsigma)

end Smooth

end MSAMixture
