/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAMixtureBHRootSmooth
import LeanCode.YukawaOZMix.MSAMixtureBHRootUneq

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
  invertibility `hjac` as input (the general-`N` item-5 obligation — the *only* thing not transferred, as
  the recentering makes the block-triangular Jacobian's diagonal blocks the asymmetric row-diameter
  hard-sphere OZ matrices, whose determinant condition is the unequal-σ analogue of
  `Q0_mat_phys_isUnit_det`; see the file docstring's discussion).
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

end Smooth

end MSAMixture
