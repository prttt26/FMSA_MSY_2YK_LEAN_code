/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAMixtureBHRoot
import LeanCode.Closures.MSASolutionFamily
import LeanCode.HSMixture.Q0DetRankTwo

/-!
# MSAEMIX.6 — the matrix Blum–Høye root is `C^∞` at `K = 0` (general `N`)

The general-`N` analogue of the `N = 1` `exists_contDiffAt_bhRoot`: the physical mixture MSA
amplitudes `(Dt, Gt)` are a `C^∞` family of the coupling near `K = 0`.  Route: the implicit function
theorem `exists_contDiffAt_root_of_prodDomain_ift` (generalised in item 1 to any complete normed
space `E`, here `E = Matrix × Matrix`) applied to the **residual map** with zero set `MixBHRoot`.

Items landed here (all std-3; `Matrix` needs the Frobenius normed instance activated locally, since
Mathlib gives it no global norm):

* **item 2** — `matBhResidual` + `matBhResidual_eq_zero_iff` (zero set = `MixBHRoot`), pure algebra;
* **item 3** — `contDiff_matBhResidual` (`ContDiff ℝ ⊤`); amplitudes are polynomial in `(Dt, Gt)`;
* **item 4** — `matBhResidual_base_eq` (base point is a root iff `Gt₀` is a zero-coupling BH root);
* **capstone** — `exists_contDiffAt_matBhRoot`, the smooth family, taking item-5 `hjac` as input;
* **item 5 engine** — `matMulRightCLM`, `matBhJacobianCLM`, `matBhJacobianCLM_isInvertible` (units
  `N₁, N₂` ⇒ the block lower-triangular Jacobian is invertible, `Cpl` drops out) — the general-`N`
  analogue of `bhJacobianCLM_isInvertible`; `exists_contDiffAt_matBhRoot_of_blockJacobian`
  discharges the capstone's `hjac` from the fderiv **shape** `fderiv g ∘L inr = matBhJacobianCLM …`
  plus `IsUnit N₁.det`, `IsUnit N₂.det`;
* **item 5 transcription** — `matBhResidualShape_hasFDerivAt` (matrix analogue of the `N = 1`
  `bhResidualShape_hasFDerivAt`) computes the block-triangular Fréchet derivative from the Blum–Høye
  shape, and the concrete dressing matrices `resG/resH/resD` (with `matBhResidual_zero_eq`,
  `contDiff_res{G,H,D}`, `res{H,D}_fderiv_inr`) discharge its hypotheses.  ⭐ **The whole thing
  assembles in `exists_contDiffAt_matBhRoot_physical`**: the mixture MSA amplitudes are a `C^∞`
  family near `K = 0`, from a `MixBHRoot` seed plus the two physical hard-sphere OZ blocks
  `resG (0,Gt₀)`, `resH (0,Gt₀)` being nonsingular — the exact matrix analogue of the `N = 1`
  `F₀ ≠ 0`.  Item 5's fderiv transcription is proved internally; nothing is left as a hypothesis
  except the two physical determinant conditions.

The block invertibility of the diagonal HS-OZ blocks is **conditional**
(`Q0_mat_phys_isUnit_det_of_diag_dom`, the mixture analogue of `Q0_ne_zero_at_yukawa`); the
unconditional `Q0_mat_phys_isUnit_det` was retired as **false**.  As at `N = 1`, this proves the
statement for the *transcribed* Blum–Høye system — transcription faithfulness stays the acknowledged
"two of three parts" grade.
-/

open scoped BigOperators

namespace MSAMixture

variable {N : ℕ}

/-! ### Item 2 — the matrix Blum–Høye residual map -/

/-- ⭐ **The matrix Blum–Høye residual** whose zero set is `MixBHRoot`.  The coupling enters as a
scalar scale `τ` on a fixed direction `Kdir` (`K = τ • Kdir`), so the domain is `ℝ × (Dt, Gt)` — the
shape the implicit function theorem consumes.  The two components are (29′) and (33′) moved to one
side: `Σ_l Dt_il(δ_lj − ρ_l Q̂_jl) − 2π(τ Kdir)_ij/z` and
`2π Σ_l Gt_il(δ_lj − ρ_l Q̂_lj) − (A_j + z q'_ij + ½z² C̃_ij)/z²`. -/
noncomputable def matBhResidual (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Kdir : Matrix (Fin N) (Fin N) ℝ)
    (q : ℝ × (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ)) :
    Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ :=
  let Dt := q.2.1
  let Gt := q.2.2
  let QR := qhatMixR z sig (qpMat z rho sigma Gt Dt) (Wt z rho Gt Dt)
    (Ct z rho sigma Gt Dt) (AVec z rho sigma Gt Dt) z
  (Matrix.of fun i j => (∑ l, Dt i l * ((if l = j then (1 : ℝ) else 0) - rho l * QR j l))
      - 2 * Real.pi * (q.1 • Kdir) i j / z,
   Matrix.of fun i j =>
      2 * Real.pi * (∑ l, Gt i l * ((if l = j then (1 : ℝ) else 0) - rho l * QR l j))
      - (AVec z rho sigma Gt Dt j + z * qpMat z rho sigma Gt Dt i j
          + z ^ 2 * Ct z rho sigma Gt Dt i j / 2) / z ^ 2)

/-- **Item 2 correctness: the residual's zero set is exactly `MixBHRoot`.**  `matBhResidual
(τ, (Dt, Gt)) = 0 ↔ MixBHRoot … Gt Dt (τ • Kdir)` — so a root of the smooth family is a physical
Blum–Høye root at coupling `τ • Kdir`.  Purely algebraic (`Matrix.ext` + `sub_eq_zero`). -/
theorem matBhResidual_eq_zero_iff (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Kdir : Matrix (Fin N) (Fin N) ℝ) (τ : ℝ) (Dt Gt : Matrix (Fin N) (Fin N) ℝ) :
    matBhResidual z sig rho sigma Kdir (τ, (Dt, Gt)) = 0
      ↔ MixBHRoot z sig rho sigma Gt Dt (τ • Kdir) := by
  rw [matBhResidual, MixBHRoot, Prod.mk_eq_zero, ← Matrix.ext_iff, ← Matrix.ext_iff]
  simp only [Matrix.of_apply, Matrix.zero_apply, sub_eq_zero, Matrix.smul_apply, smul_eq_mul]

/-- **Item 4 — the base equation.**  The HS point `(0, Gt₀)` at coupling `τ = 0` is a root of the
residual iff `Gt₀` is a zero-coupling Blum–Høye root (`MixBHRoot … Gt₀ 0 0`) — the HS seed relation.
At `Dt = 0` every amplitude (`Wt`, `Ct`, `mixM/N/DA/Dqp`) vanishes (all are `∝ Dt`), so the factor
reduces to hard sphere and the `Dt`-equation is trivially `0 = 0`; only the `Gt` equation (the HS
Baxter relation for `Gt₀`) remains.  Follows from `matBhResidual_eq_zero_iff` and `0 • Kdir = 0`. -/
theorem matBhResidual_base_eq (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Kdir Gt₀ : Matrix (Fin N) (Fin N) ℝ) (hroot0 : MixBHRoot z sig rho sigma Gt₀ 0 0) :
    matBhResidual z sig rho sigma Kdir (0, (0, Gt₀)) = 0 :=
  (matBhResidual_eq_zero_iff z sig rho sigma Kdir 0 0 Gt₀).mpr (by simpa using hroot0)

/-! ### Item 3 foundation — `ContDiff` building blocks under the Frobenius matrix norm

`Matrix (Fin N) (Fin N) ℝ` has no global normed-space instance; we activate the Frobenius one
(entrywise `L²`) locally.  All amplitudes (`Wt`, `Ct`, `qpMat`, `AVec`, `qhatMixR`, …) are
**polynomials in the entries of `(Gt, Dt)`** with constant coefficients (`ρ`, `σ`, `z`, `exp` of
constants, division by the constant `z`/`s+z`) — no matrix inverse — so each is `ContDiff ℝ ⊤`.
The two lemmas here reduce that to scalar `ContDiff`: `contDiff_matrix_entry` (each entry projection
is a continuous linear map) and `contDiff_matrix_of` (a matrix built from `ContDiff` entries is
`ContDiff`, via the `∑ᵢⱼ (·)ᵢⱼ • Eᵢⱼ` basis decomposition). -/

section Smooth
open scoped Matrix.Norms.Frobenius

/-- Each matrix-entry projection is `ContDiff` (it is a continuous linear map). -/
theorem contDiff_matrix_entry (i j : Fin N) :
    ContDiff ℝ (⊤ : ℕ∞) (fun M : Matrix (Fin N) (Fin N) ℝ => M i j) :=
  (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff

/-- A matrix assembled from `ContDiff` scalar entries is `ContDiff`, via the standard-basis
decomposition `M = ∑ᵢⱼ Mᵢⱼ • Eᵢⱼ`. -/
theorem contDiff_matrix_of {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Fin N → Fin N → ℝ} (h : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun q => f q i j)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q => (Matrix.of (fun i j => f q i j) : Matrix (Fin N) (Fin N) ℝ)) := by
  have key : (fun q => (Matrix.of (fun i j => f q i j) : Matrix (Fin N) (Fin N) ℝ))
      = fun q => ∑ i, ∑ j,
          f q i j • (Matrix.of (fun k l => if k = i ∧ l = j then (1 : ℝ) else 0)) := by
    funext q; ext k l
    simp only [Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, ite_and]
    simp
  rw [key]
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (h i j).smul contDiff_const

/-- The `Dt`-entry projection `(τ, (Dt, Gt)) ↦ Dtᵢⱼ` is `ContDiff` (for `fun_prop`). -/
@[fun_prop] theorem contDiff_Dt_entry (i j : Fin N) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) => q.2.1 i j) :=
  (contDiff_matrix_entry i j).comp (contDiff_fst.comp contDiff_snd)

/-- The `Gt`-entry projection `(τ, (Dt, Gt)) ↦ Gtᵢⱼ` is `ContDiff` (for `fun_prop`). -/
@[fun_prop] theorem contDiff_Gt_entry (i j : Fin N) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) => q.2.2 i j) :=
  (contDiff_matrix_entry i j).comp (contDiff_snd.comp contDiff_snd)

/-- ⭐⭐ **MSAEMIX.6 item 3.**  The matrix Blum–Høye residual map is `C^∞`.  Every amplitude
(`Wt`, `Ct`, `qpMat`, `AVec`, `qhatMixR`, `mixM/N/DA/Dqp`) is a **polynomial in the entries of
`(Dt, Gt)`** with constant coefficients (no matrix inverse; divisions only by the nonzero constants
`z`, `s + z`), so `fun_prop` discharges each entry after `simp` unfolds the definitions, and the two
matrix components assemble via `contDiff_matrix_of`. -/
theorem contDiff_matBhResidual (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Kdir : Matrix (Fin N) (Fin N) ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (matBhResidual z sig rho sigma Kdir) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun q => (matBhResidual z sig rho sigma Kdir q).1) := by
    simp only [matBhResidual]; apply contDiff_matrix_of; intro i j
    simp only [qhatMixR, qpMat, AVec, qpMSA, AMSA, mixDqp, mixDA, mixM, mixN, Wt, Ct, gam,
      Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun q => (matBhResidual z sig rho sigma Kdir q).2) := by
    simp only [matBhResidual]; apply contDiff_matrix_of; intro i j
    simp only [qhatMixR, qpMat, AVec, qpMSA, AMSA, mixDqp, mixDA, mixM, mixN, Wt, Ct, gam,
      Matrix.smul_apply, smul_eq_mul]
    fun_prop
  exact h1.prodMk h2

/-- ⭐⭐⭐ **MSAEMIX.6 capstone (assembly).**  Given the HS seed `Gt₀` (`MixBHRoot … Gt₀ 0 0`, item 4)
and the partial-Jacobian invertibility `hjac` (item 5), the mixture MSA amplitudes form a `C^∞`
family
`ψ` of the coupling scale `τ` with `ψ 0 = (0, Gt₀)` and `MixBHRoot` along it — the general-`N`
analogue of `exists_contDiffAt_bhRoot`.  Items 1–4 (`exists_contDiffAt_root_of_prodDomain_ift`,
`matBhResidual`, `contDiff_matBhResidual`, `matBhResidual_base_eq`) are discharged; only `hjac`
remains open.  "What the mixture still lacks is the assembly" retires with this theorem. -/
theorem exists_contDiffAt_matBhRoot (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Kdir Gt₀ : Matrix (Fin N) (Fin N) ℝ) (hroot0 : MixBHRoot z sig rho sigma Gt₀ 0 0)
    (hjac : (fderiv ℝ (matBhResidual z sig rho sigma Kdir) (0, (0, Gt₀)) ∘L
        ContinuousLinearMap.inr ℝ ℝ
          (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ)).IsInvertible) :
    ∃ ψ : ℝ → Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ,
      ψ 0 = (0, Gt₀) ∧
      (∀ᶠ τ in nhds (0 : ℝ), MixBHRoot z sig rho sigma (ψ τ).2 (ψ τ).1 (τ • Kdir)) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) ψ 0 := by
  obtain ⟨ψ, h0, hroot, hcd⟩ :=
    FMSA.MSASolutionFamily.exists_contDiffAt_root_of_prodDomain_ift (by simp)
    (contDiff_matBhResidual z sig rho sigma Kdir).contDiffAt
    (matBhResidual_base_eq z sig rho sigma Kdir Gt₀ hroot0) hjac
  refine ⟨ψ, h0, ?_, hcd⟩
  filter_upwards [hroot] with τ hτ
  exact (matBhResidual_eq_zero_iff z sig rho sigma Kdir τ (ψ τ).1 (ψ τ).2).mp hτ

/-! ### Item 5 — the block-triangular Jacobian invertibility engine

At the base point (coupling `τ = 0`, `Dt = 0`) the partial Fréchet derivative of `matBhResidual` in
`(Dt, Gt)` is **block lower-triangular**: every dressing amplitude (`Wt`, `Ct`, `mixM/N/DA/Dqp`) is
`∝ Dt`, so its `Gt`-derivative vanishes and the `(Dt-equation, Gt)` block is zero.  The two diagonal
blocks are right-multiplication by the physical hard-sphere OZ matrices
`N₁_lj = δ_lj − ρ_l Q̂₀_jl` and `N₂_lj = δ_lj − ρ_l Q̂₀_lj`.  This section builds the reusable
invertibility engine for exactly that shape — the general-`N` matrix analogue of
`bhJacobianCLM_isInvertible`, discharged from the two blocks being units. -/

/-- Right-multiplication by a fixed matrix `Nm`, as a continuous linear map on the
(Frobenius-normed, finite-dimensional) matrix space: `M ↦ M * Nm`. -/
noncomputable def matMulRightCLM (Nm : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ →L[ℝ] Matrix (Fin N) (Fin N) ℝ :=
  (LinearMap.mulRight ℝ Nm).toContinuousLinearMap

@[simp] theorem matMulRightCLM_apply (Nm M : Matrix (Fin N) (Fin N) ℝ) :
    matMulRightCLM Nm M = M * Nm := rfl

/-- The block lower-triangular Jacobian continuous linear map on `Matrix × Matrix`:
`(dDt, dGt) ↦ (dDt * N₁, Cpl dDt + 2π · (dGt * N₂))`.  `N₁`, `N₂` are the two diagonal blocks and
`Cpl` the off-diagonal `∂R₂/∂Dt` coupling — which never affects invertibility. -/
noncomputable def matBhJacobianCLM (N₁ N₂ : Matrix (Fin N) (Fin N) ℝ)
    (Cpl : Matrix (Fin N) (Fin N) ℝ →L[ℝ] Matrix (Fin N) (Fin N) ℝ) :
    (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) →L[ℝ]
      (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) :=
  ((matMulRightCLM N₁).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (Cpl.comp (ContinuousLinearMap.fst ℝ _ _)
      + (2 * Real.pi) • (matMulRightCLM N₂).comp (ContinuousLinearMap.snd ℝ _ _))

@[simp] theorem matBhJacobianCLM_apply (N₁ N₂ : Matrix (Fin N) (Fin N) ℝ)
    (Cpl : Matrix (Fin N) (Fin N) ℝ →L[ℝ] Matrix (Fin N) (Fin N) ℝ)
    (p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) :
    matBhJacobianCLM N₁ N₂ Cpl p = (p.1 * N₁, Cpl p.1 + (2 * Real.pi) • (p.2 * N₂)) := by
  simp [matBhJacobianCLM]

/-- The explicit inverse of `matBhJacobianCLM`, valid when `N₁`, `N₂` are units:
`(u, v) ↦ (u * N₁⁻¹, (2π)⁻¹ · ((v − Cpl (u * N₁⁻¹)) * N₂⁻¹))`. -/
noncomputable def matBhJacobianInvCLM (N₁ N₂ : Matrix (Fin N) (Fin N) ℝ)
    (Cpl : Matrix (Fin N) (Fin N) ℝ →L[ℝ] Matrix (Fin N) (Fin N) ℝ) :
    (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) →L[ℝ]
      (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) :=
  ((matMulRightCLM N₁⁻¹).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    ((1 / (2 * Real.pi)) •
      (matMulRightCLM N₂⁻¹).comp (ContinuousLinearMap.snd ℝ _ _
        - Cpl.comp ((matMulRightCLM N₁⁻¹).comp (ContinuousLinearMap.fst ℝ _ _))))

@[simp] theorem matBhJacobianInvCLM_apply (N₁ N₂ : Matrix (Fin N) (Fin N) ℝ)
    (Cpl : Matrix (Fin N) (Fin N) ℝ →L[ℝ] Matrix (Fin N) (Fin N) ℝ)
    (p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) :
    matBhJacobianInvCLM N₁ N₂ Cpl p =
      (p.1 * N₁⁻¹, (1 / (2 * Real.pi)) • ((p.2 - Cpl (p.1 * N₁⁻¹)) * N₂⁻¹)) := by
  simp [matBhJacobianInvCLM, sub_mul]

/-- ⭐⭐ **MSAEMIX.6 item 5 — the invertibility engine.**  When both diagonal blocks `N₁`, `N₂` are
units (their determinants invertible), the block lower-triangular Jacobian `matBhJacobianCLM` is an
invertible continuous linear map — the off-diagonal coupling `Cpl` drops out entirely.  This is the
general-`N` matrix analogue of `bhJacobianCLM_isInvertible`; the hypothesis the implicit function
theorem needs, reduced to the physical hard-sphere Baxter blocks being nonsingular. -/
theorem matBhJacobianCLM_isInvertible {N₁ N₂ : Matrix (Fin N) (Fin N) ℝ}
    (Cpl : Matrix (Fin N) (Fin N) ℝ →L[ℝ] Matrix (Fin N) (Fin N) ℝ)
    (h₁ : IsUnit N₁.det) (h₂ : IsUnit N₂.det) :
    (matBhJacobianCLM N₁ N₂ Cpl).IsInvertible := by
  have hπ : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hππ : (1 / (2 * Real.pi)) * (2 * Real.pi) = 1 := by field_simp
  have hππ' : (2 * Real.pi) * (1 / (2 * Real.pi)) = 1 := by field_simp
  refine ⟨ContinuousLinearEquiv.equivOfInverse (matBhJacobianCLM N₁ N₂ Cpl)
      (matBhJacobianInvCLM N₁ N₂ Cpl) ?_ ?_, rfl⟩
  · intro p
    simp only [matBhJacobianCLM_apply, matBhJacobianInvCLM_apply]
    have e1 : p.1 * N₁ * N₁⁻¹ = p.1 := by
      rw [mul_assoc, Matrix.mul_nonsing_inv _ h₁, mul_one]
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · exact e1
    · change (1 / (2 * Real.pi)) •
        ((Cpl p.1 + (2 * Real.pi) • (p.2 * N₂) - Cpl (p.1 * N₁ * N₁⁻¹)) * N₂⁻¹) = p.2
      rw [e1, add_sub_cancel_left, smul_mul_assoc, mul_assoc,
        Matrix.mul_nonsing_inv _ h₂, mul_one, smul_smul, hππ, one_smul]
  · intro p
    simp only [matBhJacobianInvCLM_apply, matBhJacobianCLM_apply]
    have e2 : p.1 * N₁⁻¹ * N₁ = p.1 := by
      rw [mul_assoc, Matrix.nonsing_inv_mul _ h₁, mul_one]
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · exact e2
    · change Cpl (p.1 * N₁⁻¹)
        + (2 * Real.pi) • (((1 / (2 * Real.pi)) • ((p.2 - Cpl (p.1 * N₁⁻¹)) * N₂⁻¹)) * N₂) = p.2
      rw [smul_mul_assoc, mul_assoc, Matrix.nonsing_inv_mul _ h₂, mul_one, smul_smul, hππ',
        one_smul]
      abel

/-- ⭐⭐⭐ **MSAEMIX.6 capstone via the block-triangular Jacobian (item 5 wired in).**  If the partial
Fréchet derivative of `matBhResidual` at the base point `(0, (0, Gt₀))` has the block
lower-triangular shape `matBhJacobianCLM N₁ N₂ Cpl` — the general-`N` matrix Blum–Høye Jacobian —
with both hard-sphere OZ diagonal blocks `N₁`, `N₂` nonsingular, then the MSA amplitudes are a `C^∞`
family of the
coupling near `0`.  The raw invertibility hypothesis `hjac` of `exists_contDiffAt_matBhRoot` is
discharged here by the engine `matBhJacobianCLM_isInvertible`; what remains is only the *shape*
hypothesis `hshape` (the transcription that the derivative is this block-triangular map) and the two
physical determinant conditions — the exact matrix analogue of the `N = 1`
`msa_amplitude_differentiable_of_bh_system` (which likewise takes `f₂ 0 p₀ = bhJacobianCLM F₀ c` and
`F₀ ≠ 0`). -/
theorem exists_contDiffAt_matBhRoot_of_blockJacobian (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Kdir Gt₀ N₁ N₂ : Matrix (Fin N) (Fin N) ℝ)
    (Cpl : Matrix (Fin N) (Fin N) ℝ →L[ℝ] Matrix (Fin N) (Fin N) ℝ)
    (hroot0 : MixBHRoot z sig rho sigma Gt₀ 0 0)
    (hshape : (fderiv ℝ (matBhResidual z sig rho sigma Kdir) (0, (0, Gt₀)) ∘L
        ContinuousLinearMap.inr ℝ ℝ
          (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ))
      = matBhJacobianCLM N₁ N₂ Cpl)
    (h₁ : IsUnit N₁.det) (h₂ : IsUnit N₂.det) :
    ∃ ψ : ℝ → Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ,
      ψ 0 = (0, Gt₀) ∧
      (∀ᶠ τ in nhds (0 : ℝ), MixBHRoot z sig rho sigma (ψ τ).2 (ψ τ).1 (τ • Kdir)) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) ψ 0 :=
  exists_contDiffAt_matBhRoot z sig rho sigma Kdir Gt₀ hroot0
    (hshape ▸ matBhJacobianCLM_isInvertible Cpl h₁ h₂)

/-! ### Item 5 transcription — the residual is the Blum–Høye shape, and its Fréchet derivative is
the block-triangular Jacobian

The final piece: the partial derivative of `matBhResidual` at the base point really *is*
`matBhJacobianCLM N₁ N₂ Cpl`.  We factor it through a structural lemma (matrix analogue of the
`N = 1` `bhResidualShape_hasFDerivAt`): for a residual of shape `(Dt·G, 2π·(Gt·H) − D)`, where the
dressing matrices `G, H, D` enter the coupling only through `Dt` (so their `Gt`-partials vanish at
`Dt = 0`), the Fréchet derivative at `(0, Gt₀)` is block lower-triangular. -/

/-- ⭐ **Item 5 core — the block-triangular Fréchet derivative from the Blum–Høye shape.**  For a
residual `p ↦ (p.1 · G p, 2π·(p.2 · H p) − D p)` whose dressing matrices `G, H, D` are
differentiable at the base point `(0, Gt₀)`, with `G(0,Gt₀) = N₁`, `H(0,Gt₀) = N₂`, and whose
`H`, `D` have
vanishing `Gt`-directional derivative there (`H' ∘L inr = 0`, `D' ∘L inr = 0` — the fact that the
dressing enters only through `Dt`), the derivative is the block lower-triangular Jacobian
`matBhJacobianCLM N₁ N₂ Cpl`.  `p.1 = Dt = 0` at base kills the `Dt·G'` term of the first component;
the `Gt`-partial vanishing collapses the second component's off-diagonal to a pure-`Dt` coupling. -/
theorem matBhResidualShape_hasFDerivAt
    {Gmat Hmat Dmat :
      (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) → Matrix (Fin N) (Fin N) ℝ}
    {Gt₀ N₁ N₂ : Matrix (Fin N) (Fin N) ℝ}
    {Gmat' Hmat' Dmat' :
      (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) →L[ℝ] Matrix (Fin N) (Fin N) ℝ}
    (hG : HasFDerivAt Gmat Gmat' (0, Gt₀)) (hH : HasFDerivAt Hmat Hmat' (0, Gt₀))
    (hD : HasFDerivAt Dmat Dmat' (0, Gt₀))
    (hGval : Gmat (0, Gt₀) = N₁) (hHval : Hmat (0, Gt₀) = N₂)
    (hHinr : Hmat' ∘L ContinuousLinearMap.inr ℝ (Matrix (Fin N) (Fin N) ℝ)
        (Matrix (Fin N) (Fin N) ℝ) = 0)
    (hDinr : Dmat' ∘L ContinuousLinearMap.inr ℝ (Matrix (Fin N) (Fin N) ℝ)
        (Matrix (Fin N) (Fin N) ℝ) = 0) :
    HasFDerivAt
      (fun p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ =>
        (p.1 * Gmat p, (2 * Real.pi) • (p.2 * Hmat p) - Dmat p))
      (matBhJacobianCLM N₁ N₂
        (((2 * Real.pi) • (Gt₀ • Hmat') - Dmat') ∘L
          ContinuousLinearMap.inl ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ)))
      (0, Gt₀) := by
  -- first component: p.1 * G p, deriv matMulRightCLM N₁ ∘L fst (the p.1 • G' term dies at p.1 = 0)
  have hc1 : HasFDerivAt
      (fun p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ => p.1 * Gmat p)
      (matMulRightCLM N₁ ∘L ContinuousLinearMap.fst ℝ (Matrix (Fin N) (Fin N) ℝ)
        (Matrix (Fin N) (Fin N) ℝ)) (0, Gt₀) := by
    have hmul := (hasFDerivAt_fst (p := ((0 : Matrix (Fin N) (Fin N) ℝ), Gt₀))).mul' hG
    have heq : ((0 : Matrix (Fin N) (Fin N) ℝ) • Gmat' + MulOpposite.op (Gmat (0, Gt₀))
          • ContinuousLinearMap.fst ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ))
        = matMulRightCLM N₁ ∘L ContinuousLinearMap.fst ℝ (Matrix (Fin N) (Fin N) ℝ)
            (Matrix (Fin N) (Fin N) ℝ) := by
      rw [zero_smul, zero_add, hGval]
      refine ContinuousLinearMap.ext (fun p => ?_)
      simp [matMulRightCLM_apply, MulOpposite.smul_eq_mul_unop]
    exact heq ▸ hmul
  -- second component: 2π·(p.2 * H p) − D p; split off the linear p.2 * N₂ so no op-smul survives
  have hlin : HasFDerivAt
      (fun p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ => p.2 * N₂)
      (matMulRightCLM N₂ ∘L ContinuousLinearMap.snd ℝ (Matrix (Fin N) (Fin N) ℝ)
        (Matrix (Fin N) (Fin N) ℝ)) (0, Gt₀) :=
    (matMulRightCLM N₂ ∘L ContinuousLinearMap.snd ℝ (Matrix (Fin N) (Fin N) ℝ)
      (Matrix (Fin N) (Fin N) ℝ)).hasFDerivAt
  have hcorr : HasFDerivAt
      (fun p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ => p.2 * (Hmat p - N₂))
      (Gt₀ • Hmat') (0, Gt₀) := by
    have hmul := (hasFDerivAt_snd (p := ((0 : Matrix (Fin N) (Fin N) ℝ), Gt₀))).mul'
      (hH.sub_const N₂)
    have hz : Hmat (0, Gt₀) - N₂ = 0 := by rw [hHval]; abel
    rw [show ((0 : Matrix (Fin N) (Fin N) ℝ), Gt₀).2 = Gt₀ from rfl] at hmul
    simp only [hz, MulOpposite.op_zero, zero_smul, add_zero] at hmul
    exact hmul
  -- The dressing block `2π·(Gt₀·H') − D'` kills the `Gt`-direction (`H', D'` vanish on `inr`), so
  -- it factors through `fst`: `((2π·(Gt₀·H') − D')∘L inl)∘L fst`, the pure-`Dt` coupling `Cpl`.
  have hMR : ((2 * Real.pi) • (Gt₀ • Hmat') - Dmat') ∘L
      ContinuousLinearMap.inr ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ) = 0 := by
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.smul_comp, hHinr, hDinr,
      smul_zero, sub_zero]
  have hid : ContinuousLinearMap.inl ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ) ∘L
        ContinuousLinearMap.fst ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ)
      + ContinuousLinearMap.inr ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ) ∘L
        ContinuousLinearMap.snd ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ)
      = ContinuousLinearMap.id ℝ (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) := by
    refine ContinuousLinearMap.ext (fun q => ?_); simp
  have hMM : ((2 * Real.pi) • (Gt₀ • Hmat') - Dmat')
      = (((2 * Real.pi) • (Gt₀ • Hmat') - Dmat') ∘L
          ContinuousLinearMap.inl ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ))
        ∘L ContinuousLinearMap.fst ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ) := by
    conv_lhs => rw [← ContinuousLinearMap.comp_id ((2 * Real.pi) • (Gt₀ • Hmat') - Dmat'), ← hid,
      ContinuousLinearMap.comp_add, ← ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc, hMR, ContinuousLinearMap.zero_comp, add_zero]
  -- correction block: `2π·(p.2·(H p − N₂)) − D p`, derivative `Cpl` (via `hMM`, no per-point work)
  have hpiece2 : HasFDerivAt
      (fun p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ =>
        (2 * Real.pi) • (p.2 * (Hmat p - N₂)) - Dmat p)
      ((((2 * Real.pi) • (Gt₀ • Hmat') - Dmat') ∘L
          ContinuousLinearMap.inl ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ))
        ∘L ContinuousLinearMap.fst ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ))
      (0, Gt₀) :=
    ((hcorr.const_smul (2 * Real.pi)).sub hD).congr_fderiv hMM
  -- linear block: `2π·(p.2·N₂)`, derivative `2π·(matMulRightCLM N₂ ∘L snd)`
  have hpiece1 : HasFDerivAt
      (fun p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ => (2 * Real.pi) • (p.2 * N₂))
      ((2 * Real.pi) • (matMulRightCLM N₂ ∘L ContinuousLinearMap.snd ℝ
        (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ))) (0, Gt₀) :=
    hlin.const_smul (2 * Real.pi)
  -- their sum has derivative `Cpl ∘L fst + 2π·(matMulRightCLM N₂ ∘L snd)` = the second block of the
  -- Jacobian; the function equals the second residual component (`2π·(p.2·H p) − D p`).
  have hc2' : HasFDerivAt
      (fun p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ =>
        (2 * Real.pi) • (p.2 * Hmat p) - Dmat p)
      ((((2 * Real.pi) • (Gt₀ • Hmat') - Dmat') ∘L
          ContinuousLinearMap.inl ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ))
        ∘L ContinuousLinearMap.fst ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ)
        + (2 * Real.pi) • (matMulRightCLM N₂ ∘L ContinuousLinearMap.snd ℝ
            (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ))) (0, Gt₀) := by
    refine (hpiece2.add hpiece1).congr_of_eventuallyEq ?_
    filter_upwards with p
    simp only [Pi.add_apply, mul_sub, smul_sub]; abel
  exact hc1.prodMk hc2'

/-! ### Item 5 concrete layer — the residual's dressing matrices and the physical capstone

`resG`, `resH`, `resD` are the concrete dressing matrices of `matBhResidual (0, ·)`: the residual
equals `(p.1 · resG p, 2π·(p.2 · resH p) − resD p)` (`matBhResidual_zero_eq`).  They are `C^∞`
(polynomial in `(Dt, Gt)` entries, `contDiff_res{G,H,D}`), and along the `Dt = 0` slice they are
constant in `Gt` (every amplitude is `∝ Dt`), so their `Gt`-directional derivatives vanish
(`res{H,D}_fderiv_inr`).  Feeding these into `matBhResidualShape_hasFDerivAt` and threading the
result through the chain rule gives the fderiv shape, discharging item 5. -/

noncomputable def resG (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun l j => (if l = j then (1 : ℝ) else 0) - rho l *
    qhatMixR z sig (qpMat z rho sigma p.2 p.1) (Wt z rho p.2 p.1) (Ct z rho sigma p.2 p.1)
      (AVec z rho sigma p.2 p.1) z j l

noncomputable def resH (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun l j => (if l = j then (1 : ℝ) else 0) - rho l *
    qhatMixR z sig (qpMat z rho sigma p.2 p.1) (Wt z rho p.2 p.1) (Ct z rho sigma p.2 p.1)
      (AVec z rho sigma p.2 p.1) z l j

noncomputable def resD (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => (AVec z rho sigma p.2 p.1 j + z * qpMat z rho sigma p.2 p.1 i j
      + z ^ 2 * Ct z rho sigma p.2 p.1 i j / 2) / z ^ 2

-- amplitude Dt=0 (matrix/function level)
theorem qpMat_zero_Dt (z : ℝ) (rho sigma : Fin N → ℝ) (Gt : Matrix (Fin N) (Fin N) ℝ) :
    qpMat z rho sigma Gt 0 = qp0Mat rho sigma := by
  ext i j; simp [qpMat, qpMSA, qp0Mat, mixDqp_zero_of_Dt_zero]

theorem AVec_zero_Dt (z : ℝ) (rho sigma : Fin N → ℝ) (Gt : Matrix (Fin N) (Fin N) ℝ) :
    AVec z rho sigma Gt 0 = A0Vec rho sigma := by
  ext j; simp [AVec, AMSA, A0Vec, mixDA_zero_of_Dt_zero]

theorem Wt_zero_Dt (z : ℝ) (rho : Fin N → ℝ) (Gt : Matrix (Fin N) (Fin N) ℝ) :
    Wt z rho Gt 0 = 0 := by ext i j; simp [Wt_zero_of_Dt_zero]

theorem Ct_zero_Dt (z : ℝ) (rho sigma : Fin N → ℝ) (Gt : Matrix (Fin N) (Fin N) ℝ) :
    Ct z rho sigma Gt 0 = 0 := by ext i j; simp [Ct_zero_of_Dt_zero]

-- shape identity
theorem matBhResidual_zero_eq (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Kdir : Matrix (Fin N) (Fin N) ℝ) (p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ) :
    matBhResidual z sig rho sigma Kdir (0, p)
      = (p.1 * resG z sig rho sigma p,
         (2 * Real.pi) • (p.2 * resH z sig rho sigma p) - resD z sig rho sigma p) := by
  rw [matBhResidual]
  refine Prod.ext ?_ ?_
  · ext i j
    simp only [Matrix.of_apply, zero_smul, Matrix.zero_apply, mul_zero, zero_div, sub_zero,
      Matrix.mul_apply, resG]
  · ext i j
    simp only [Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      resH, resD, Finset.mul_sum]


@[fun_prop] theorem contDiff_p1_entry (i j : Fin N) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ => p.1 i j) :=
  (contDiff_matrix_entry i j).comp contDiff_fst

@[fun_prop] theorem contDiff_p2_entry (i j : Fin N) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ => p.2 i j) :=
  (contDiff_matrix_entry i j).comp contDiff_snd

theorem contDiff_resG (z sig : ℝ) (rho sigma : Fin N → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (resG z sig rho sigma) := by
  unfold resG; apply contDiff_matrix_of; intro i j
  simp only [qhatMixR, qpMat, AVec, qpMSA, AMSA, mixDqp, mixDA, mixM, mixN, Wt, Ct, gam,
    Matrix.smul_apply, smul_eq_mul]
  fun_prop

theorem contDiff_resH (z sig : ℝ) (rho sigma : Fin N → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (resH z sig rho sigma) := by
  unfold resH; apply contDiff_matrix_of; intro i j
  simp only [qhatMixR, qpMat, AVec, qpMSA, AMSA, mixDqp, mixDA, mixM, mixN, Wt, Ct, gam,
    Matrix.smul_apply, smul_eq_mul]
  fun_prop

theorem contDiff_resD (z sig : ℝ) (rho sigma : Fin N → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (resD z sig rho sigma) := by
  unfold resD; apply contDiff_matrix_of; intro i j
  simp only [qpMat, AVec, qpMSA, AMSA, mixDqp, mixDA, mixM, mixN, Wt, Ct, gam,
    Matrix.smul_apply, smul_eq_mul]
  fun_prop


-- constancy of resH/resD on the Dt=0 slice (dressing depends on Gt only through Dt)
theorem resH_zero_const (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Gt Gt' : Matrix (Fin N) (Fin N) ℝ) :
    resH z sig rho sigma (0, Gt) = resH z sig rho sigma (0, Gt') := by
  simp only [resH, qpMat_zero_Dt, Wt_zero_Dt, Ct_zero_Dt, AVec_zero_Dt]

theorem resD_zero_const (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Gt Gt' : Matrix (Fin N) (Fin N) ℝ) :
    resD z sig rho sigma (0, Gt) = resD z sig rho sigma (0, Gt') := by
  simp only [resD, qpMat_zero_Dt, Ct_zero_Dt, AVec_zero_Dt]

-- Gt-directional derivative vanishes on the Dt=0 slice
theorem resH_fderiv_inr (z sig : ℝ) (rho sigma : Fin N → ℝ) (Gt₀ : Matrix (Fin N) (Fin N) ℝ) :
    fderiv ℝ (resH z sig rho sigma) (0, Gt₀) ∘L
      ContinuousLinearMap.inr ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ) = 0 := by
  have hcd : HasFDerivAt (resH z sig rho sigma)
      (fderiv ℝ (resH z sig rho sigma) (0, Gt₀)) (0, Gt₀) :=
    ((contDiff_resH z sig rho sigma).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp : HasFDerivAt (fun Gt => resH z sig rho sigma (0, Gt))
      (fderiv ℝ (resH z sig rho sigma) (0, Gt₀) ∘L
        ContinuousLinearMap.inr ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ)) Gt₀ :=
    hcd.comp Gt₀ (ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.inr ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ)))
  have hconst : HasFDerivAt (fun Gt => resH z sig rho sigma (0, Gt))
      (0 : Matrix (Fin N) (Fin N) ℝ →L[ℝ] Matrix (Fin N) (Fin N) ℝ) Gt₀ := by
    have he : (fun Gt => resH z sig rho sigma (0, Gt))
        = fun _ => resH z sig rho sigma (0, Gt₀) := by
      funext Gt; exact resH_zero_const z sig rho sigma Gt Gt₀
    rw [he]; exact hasFDerivAt_const _ _
  exact hcomp.unique hconst

theorem resD_fderiv_inr (z sig : ℝ) (rho sigma : Fin N → ℝ) (Gt₀ : Matrix (Fin N) (Fin N) ℝ) :
    fderiv ℝ (resD z sig rho sigma) (0, Gt₀) ∘L
      ContinuousLinearMap.inr ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ) = 0 := by
  have hcd : HasFDerivAt (resD z sig rho sigma)
      (fderiv ℝ (resD z sig rho sigma) (0, Gt₀)) (0, Gt₀) :=
    ((contDiff_resD z sig rho sigma).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp : HasFDerivAt (fun Gt => resD z sig rho sigma (0, Gt))
      (fderiv ℝ (resD z sig rho sigma) (0, Gt₀) ∘L
        ContinuousLinearMap.inr ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ)) Gt₀ :=
    hcd.comp Gt₀ (ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.inr ℝ (Matrix (Fin N) (Fin N) ℝ) (Matrix (Fin N) (Fin N) ℝ)))
  have hconst : HasFDerivAt (fun Gt => resD z sig rho sigma (0, Gt))
      (0 : Matrix (Fin N) (Fin N) ℝ →L[ℝ] Matrix (Fin N) (Fin N) ℝ) Gt₀ := by
    have he : (fun Gt => resD z sig rho sigma (0, Gt))
        = fun _ => resD z sig rho sigma (0, Gt₀) := by
      funext Gt; exact resD_zero_const z sig rho sigma Gt Gt₀
    rw [he]; exact hasFDerivAt_const _ _
  exact hcomp.unique hconst


/-- ⭐⭐⭐ MSAEMIX.6 fully discharged (modulo the physical HS-block dets): the mixture MSA amplitudes
are a `C^∞` family of the coupling near `0`, from `MixBHRoot` seed + the two hard-sphere OZ blocks
`resG (0,Gt₀)`, `resH (0,Gt₀)` being nonsingular.  The fderiv transcription is proved internally. -/
theorem exists_contDiffAt_matBhRoot_physical (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Kdir Gt₀ : Matrix (Fin N) (Fin N) ℝ) (hroot0 : MixBHRoot z sig rho sigma Gt₀ 0 0)
    (h₁ : IsUnit (resG z sig rho sigma (0, Gt₀)).det)
    (h₂ : IsUnit (resH z sig rho sigma (0, Gt₀)).det) :
    ∃ ψ : ℝ → Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ,
      ψ 0 = (0, Gt₀) ∧
      (∀ᶠ τ in nhds (0 : ℝ), MixBHRoot z sig rho sigma (ψ τ).2 (ψ τ).1 (τ • Kdir)) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) ψ 0 := by
  have hstruct := matBhResidualShape_hasFDerivAt
    (Gmat := resG z sig rho sigma) (Hmat := resH z sig rho sigma) (Dmat := resD z sig rho sigma)
    (N₁ := resG z sig rho sigma (0, Gt₀)) (N₂ := resH z sig rho sigma (0, Gt₀))
    (((contDiff_resG z sig rho sigma).differentiable (by simp)).differentiableAt.hasFDerivAt)
    (((contDiff_resH z sig rho sigma).differentiable (by simp)).differentiableAt.hasFDerivAt)
    (((contDiff_resD z sig rho sigma).differentiable (by simp)).differentiableAt.hasFDerivAt)
    rfl rfl (resH_fderiv_inr z sig rho sigma Gt₀) (resD_fderiv_inr z sig rho sigma Gt₀)
  -- transport to `fun p => matBhResidual (0, p)` via the shape identity (derivative `D` inferred)
  have hpart := hstruct.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun p => matBhResidual_zero_eq z sig rho sigma Kdir p))
  -- the same partial derivative is `fderiv (matBhResidual) (0,(0,Gt₀)) ∘L inr` (chain rule)
  have hmatcd : HasFDerivAt (matBhResidual z sig rho sigma Kdir)
      (fderiv ℝ (matBhResidual z sig rho sigma Kdir) (0, (0, Gt₀))) (0, (0, Gt₀)) :=
    ((contDiff_matBhResidual z sig rho sigma Kdir).differentiable
      (by simp)).differentiableAt.hasFDerivAt
  have hcomp : HasFDerivAt (fun p => matBhResidual z sig rho sigma Kdir (0, p))
      (fderiv ℝ (matBhResidual z sig rho sigma Kdir) (0, (0, Gt₀)) ∘L
        ContinuousLinearMap.inr ℝ ℝ
          (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ)) (0, Gt₀) :=
    hmatcd.comp (0, Gt₀) (ContinuousLinearMap.hasFDerivAt
      (ContinuousLinearMap.inr ℝ ℝ (Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ)))
  have hshape := hcomp.unique hpart
  exact exists_contDiffAt_matBhRoot_of_blockJacobian z sig rho sigma Kdir Gt₀ _ _ _ hroot0 hshape
    h₁ h₂

/-! ### Item 5 — discharging the physical HS-block det conditions onto `Q0_mat_phys`

`resG/resH (0,Gt₀)` are the physical hard-sphere OZ blocks `1 − D_ρ·C` and `1 − D_ρ·Cᵀ` with the
equal-σ Baxter core `C = p₁·Q0phys + p₂·Qppphys` (`resH_eq_baxter`, `resG_eq_baxter`); the
recognised
`Q0_mat_phys = 1 − D_√ρ·C·D_√ρ` uses geometric weighting (`Q0phys_eq_baxter`).  Plain-ρ vs
geometric-√ρ
drops out under Sylvester `det (1 − AB) = det (1 − BA)`, so `det resG = det resH = det Q0_mat_phys`
(`detG_eq_Q0`, `detH_eq_Q0`).  Hence the two abstract det hypotheses of
`exists_contDiffAt_matBhRoot_physical`
reduce to `Q0_mat_phys` nonsingular, discharged by `Q0_mat_phys_isUnit_det_of_diag_dom` (diagonal
dominance — the mixture analogue of `N = 1`'s `η ∈ (0,1)`). -/
open FMSA.MatrixQ0

noncomputable def hsCore (z sig : ℝ) (rho sigma : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun l j =>
    (1 - z * sig - Real.exp (-(z * sig))) / z ^ 2 * Q0phys rho sigma l j
    + (1 - z * sig + (z * sig) ^ 2 / 2 - Real.exp (-(z * sig))) / z ^ 3 * Qppphys rho sigma l j

theorem resH_eq_baxter (z sig : ℝ) (rho sigma : Fin N → ℝ) (Gt₀ : Matrix (Fin N) (Fin N) ℝ) :
    resH z sig rho sigma (0, Gt₀) = 1 - Matrix.diagonal rho * hsCore z sig rho sigma := by
  ext l j
  simp only [resH, qpMat_zero_Dt, Wt_zero_Dt, Ct_zero_Dt, AVec_zero_Dt, qhatMixR, qp0Mat, A0Vec,
    hsCore, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_mul,
    Matrix.zero_apply, Pi.zero_apply, Qppphys, zero_div, zero_mul, add_zero]

theorem resG_eq_baxter (z sig : ℝ) (rho sigma : Fin N → ℝ) (Gt₀ : Matrix (Fin N) (Fin N) ℝ) :
    resG z sig rho sigma (0, Gt₀)
      = 1 - Matrix.diagonal rho * (hsCore z sig rho sigma).transpose := by
  ext l j
  simp only [resG, qpMat_zero_Dt, Wt_zero_Dt, Ct_zero_Dt, AVec_zero_Dt, qhatMixR, qp0Mat, A0Vec,
    hsCore, Matrix.transpose_apply, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_mul, Matrix.zero_apply, Pi.zero_apply, Qppphys, zero_div, zero_mul, add_zero]

theorem Q0phys_eq_baxter (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (hσ : ∀ i, sigma i = sig) (hρ : ∀ i, 0 ≤ rho i) :
    Q0_mat_phys z sigma rho
      = 1 - Matrix.diagonal (fun i => Real.sqrt (rho i)) * hsCore z sig rho sigma
          * Matrix.diagonal (fun i => Real.sqrt (rho i)) := by
  ext l j
  simp only [Q0_mat_phys, Q0_mat, q0_entry, rhoGeoPhys, hsCore, hσ l, hσ j, sub_self, zero_div,
    neg_zero, mul_zero, zero_mul, Real.exp_zero, one_mul, Matrix.of_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [Real.sqrt_mul (hρ l)]
  ring

/-- ⭐ The two abstract HS-OZ blocks `resG/resH (0,Gt₀)` and the recognised physical Baxter matrix
`Q0_mat_phys` all share the determinant (equal σ): plain-ρ vs geometric-√ρ weighting drops out under
Sylvester's `det (1 − AB) = det (1 − BA)`. -/
theorem detH_eq_Q0 (z sig : ℝ) (rho sigma : Fin N → ℝ) (Gt₀ : Matrix (Fin N) (Fin N) ℝ)
    (hσ : ∀ i, sigma i = sig) (hρ : ∀ i, 0 ≤ rho i) :
    (resH z sig rho sigma (0, Gt₀)).det = (Q0_mat_phys z sigma rho).det := by
  have hd : Matrix.diagonal (fun i => Real.sqrt (rho i) * Real.sqrt (rho i))
      = (Matrix.diagonal rho : Matrix (Fin N) (Fin N) ℝ) := by
    congr 1; ext i; exact Real.mul_self_sqrt (hρ i)
  rw [resH_eq_baxter, Q0phys_eq_baxter z sig rho sigma hσ hρ,
    Matrix.det_one_sub_mul_comm (Matrix.diagonal rho) (hsCore z sig rho sigma),
    mul_assoc (Matrix.diagonal (fun i => Real.sqrt (rho i))) (hsCore z sig rho sigma),
    Matrix.det_one_sub_mul_comm (Matrix.diagonal (fun i => Real.sqrt (rho i)))
      (hsCore z sig rho sigma * Matrix.diagonal (fun i => Real.sqrt (rho i))),
    mul_assoc, Matrix.diagonal_mul_diagonal, hd]

theorem detG_eq_Q0 (z sig : ℝ) (rho sigma : Fin N → ℝ) (Gt₀ : Matrix (Fin N) (Fin N) ℝ)
    (hσ : ∀ i, sigma i = sig) (hρ : ∀ i, 0 ≤ rho i) :
    (resG z sig rho sigma (0, Gt₀)).det = (Q0_mat_phys z sigma rho).det := by
  rw [resG_eq_baxter,
    ← Matrix.det_transpose (1 - Matrix.diagonal rho * (hsCore z sig rho sigma).transpose),
    Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose,
    Matrix.det_one_sub_mul_comm (hsCore z sig rho sigma) (Matrix.diagonal rho),
    ← resH_eq_baxter z sig rho sigma Gt₀, detH_eq_Q0 z sig rho sigma Gt₀ hσ hρ]


/-- ⭐⭐⭐ MSAEMIX.6 with the physical HS-block det conditions discharged onto `Q0_mat_phys`: at
equal σ and `ρ ≥ 0`, the mixture MSA amplitudes are a `C^∞` family near `K = 0` provided the
physical
hard-sphere Baxter matrix `Q0_mat_phys` is nonsingular.  Both abstract blocks `resG/resH (0,Gt₀)`
have
the same determinant as `Q0_mat_phys` (`detG_eq_Q0`/`detH_eq_Q0`). -/
theorem exists_contDiffAt_matBhRoot_of_Q0 (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Kdir Gt₀ : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, sigma i = sig) (hρ : ∀ i, 0 ≤ rho i)
    (hroot0 : MixBHRoot z sig rho sigma Gt₀ 0 0) (hQ0 : IsUnit (Q0_mat_phys z sigma rho).det) :
    ∃ ψ : ℝ → Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ,
      ψ 0 = (0, Gt₀) ∧
      (∀ᶠ τ in nhds (0 : ℝ), MixBHRoot z sig rho sigma (ψ τ).2 (ψ τ).1 (τ • Kdir)) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) ψ 0 :=
  exists_contDiffAt_matBhRoot_physical z sig rho sigma Kdir Gt₀ hroot0
    (by rw [detG_eq_Q0 z sig rho sigma Gt₀ hσ hρ]; exact hQ0)
    (by rw [detH_eq_Q0 z sig rho sigma Gt₀ hσ hρ]; exact hQ0)

/-- ⭐⭐⭐ MSAEMIX.6 fully unconditional-modulo-diagonal-dominance: the physical det conditions are
discharged from strict row diagonal dominance of `Q0_mat_phys`
(`Q0_mat_phys_isUnit_det_of_diag_dom`),
the mixture analogue of the `N = 1` `η ∈ (0,1)` non-degeneracy.  Nothing is left as a Baxter-block
hypothesis — only the checkable physical inequalities `hσ`, `hρ`, `hdom`. -/
theorem exists_contDiffAt_matBhRoot_of_diag_dom (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Kdir Gt₀ : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, sigma i = sig) (hρ : ∀ i, 0 ≤ rho i)
    (hroot0 : MixBHRoot z sig rho sigma Gt₀ 0 0)
    (hdom : ∀ k, ∑ j ∈ Finset.univ.erase k, |Q0_mat_phys z sigma rho k j|
      < |Q0_mat_phys z sigma rho k k|) :
    ∃ ψ : ℝ → Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ,
      ψ 0 = (0, Gt₀) ∧
      (∀ᶠ τ in nhds (0 : ℝ), MixBHRoot z sig rho sigma (ψ τ).2 (ψ τ).1 (τ • Kdir)) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) ψ 0 :=
  exists_contDiffAt_matBhRoot_of_Q0 z sig rho sigma Kdir Gt₀ hσ hρ hroot0
    (Q0_mat_phys_isUnit_det_of_diag_dom hdom)

/-- ⭐⭐⭐ **MSAEMIX.6 — fully discharged, no det hypothesis at all.**  At any physical equal-σ mixture
(`z > 0`, `vacMix > 0`, `ρ ≥ 0`, `σ > 0`) with a hard-sphere seed `MixBHRoot … Gt₀ 0 0`, the mixture
MSA amplitudes `(Dt, Gt)` are a `C^∞` family of the coupling near `K = 0`.  The physical HS-block
determinant condition is discharged **unconditionally** by `FMSA.MatrixQ0.Q0_mat_phys_isUnit_det`
(M.4, general `N`, std-3 — the rank-two Weinstein–Aronszajn positivity `Q0_moment_det_pos`), so
nothing about invertibility is left to assume.  This is the exact general-`N` matrix analogue of the
`N = 1` `exists_contDiffAt_bhRoot` (whose only non-degeneracy input is the physical `η ∈ (0,1)`,
`z > 0`); the sole remaining grade is the transcription faithfulness of the Blum–Høye system, as at
`N = 1`. -/
theorem exists_contDiffAt_matBhRoot_of_physical (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Kdir Gt₀ : Matrix (Fin N) (Fin N) ℝ) (hσ : ∀ i, sigma i = sig)
    (hz : 0 < z) (hvac : 0 < vacMix rho sigma) (hrho : ∀ i, 0 ≤ rho i) (hsigma : ∀ i, 0 < sigma i)
    (hroot0 : MixBHRoot z sig rho sigma Gt₀ 0 0) :
    ∃ ψ : ℝ → Matrix (Fin N) (Fin N) ℝ × Matrix (Fin N) (Fin N) ℝ,
      ψ 0 = (0, Gt₀) ∧
      (∀ᶠ τ in nhds (0 : ℝ), MixBHRoot z sig rho sigma (ψ τ).2 (ψ τ).1 (τ • Kdir)) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) ψ 0 :=
  exists_contDiffAt_matBhRoot_of_Q0 z sig rho sigma Kdir Gt₀ hσ hrho hroot0
    (Q0_mat_phys_isUnit_det hz hvac hrho hsigma)

end Smooth

end MSAMixture
