/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.MixtureQ0Inverse

/-!
# Tang & Lu eq (21)/(22) assembly — the first-order RDF as a four-term expansion

Item (c) of the eq (20) residue programme: the *algebraic bookkeeping* that turns
`Ĥ₁ = [Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹` (eq 15) into the explicit eq (21)/(22) form.

The closed-form inverse (`Q0_mat_phys_inv_eq`) is `[Q̂₀]⁻¹ = 1 + A` with `A := Amat` the Woodbury
off-identity part `U(1−VU)⁻¹V`; hence `[Q̂₀ᵀ]⁻¹ = ([Q̂₀]⁻¹)ᵀ = 1 + Aᵀ`.  Substituting into `Ĥ₁`
and multiplying out gives the **four terms**

`Ĥ₁ = B₁ + Aᵀ·B₁ + B₁·A + Aᵀ·B₁·A`

(`H1_assembly_phys`), whose entries are exactly the four sums of Tang & Lu eq (21):

`{H₁}ᵢⱼ = bᵢⱼ + ∑ₙ bᵢₙAₙⱼ + ∑ₘ bₘⱼAₘᵢ + ∑ₘₙ AₘᵢAₙⱼbₘₙ`

(`H1_assembly_phys_apply`; here `{B₁}ᵢⱼ = bᵢⱼ·e^{−ikRᵢⱼ}` carries the residue `bᵢⱼ` of eq (23),
built from the per-pole residue values of `YukawaDCF/MixtureYukawaResidue`).  This is pure matrix
algebra — axiom-clean — on `H1_eq_phys` + `Q0_mat_phys_inv_eq` + the generic expansion `H1_expand`.
-/

open Matrix

namespace FMSA.MatrixQ0

/-- **Tang & Lu eq (21)/(22) — the generic four-term expansion.**  With `[Q̂₀]⁻¹ = 1 + A` (so
`[Q̂₀ᵀ]⁻¹ = 1 + Aᵀ`), `Ĥ₁ = [Q̂₀ᵀ]⁻¹B₁[Q̂₀]⁻¹` multiplies out to `B₁ + Aᵀ·B₁ + B₁·A + Aᵀ·B₁·A`. -/
theorem H1_expand {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) :
    (1 + Aᵀ) * B * (1 + A) = B + Aᵀ * B + B * A + Aᵀ * B * A := by
  noncomm_ring

/-- The Woodbury off-identity part of `[Q̂₀]⁻¹` (`[Q̂₀]⁻¹ = 1 + Amat`, `Q0_mat_phys_inv_eq`). -/
noncomputable def Amat {N : ℕ} (z : ℝ) (sigma rho : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Umat z sigma rho * (1 - Vmat z sigma rho * Umat z sigma rho)⁻¹ * Vmat z sigma rho

/-- **Tang & Lu eq (21)/(22) assembly for the physical Baxter factor.**  From the transformed
first-order OZ equation `Q̂₀ᵀ·Ĥ₁·Q̂₀ = B₁` (real `z > 0`, `det ≥ 1 > 0`), the first-order RDF is
`Ĥ₁ = B₁ + Aᵀ·B₁ + B₁·A + Aᵀ·B₁·A` with `A = Amat` the closed-form Woodbury off-identity part of
`[Q̂₀]⁻¹`.  Pure algebra on `H1_eq_phys` + `Q0_mat_phys_inv_eq` + `H1_expand`. -/
theorem H1_assembly_phys {N : ℕ} {z : ℝ} {sigma rho : Fin N → ℝ}
    (hz : 0 < z) (hvac : 0 < vacMix rho sigma) (hrho : ∀ i, 0 ≤ rho i) (hsigma : ∀ i, 0 < sigma i)
    (H1 B1 : Matrix (Fin N) (Fin N) ℝ)
    (heq : (Q0_mat_phys z sigma rho)ᵀ * H1 * (Q0_mat_phys z sigma rho) = B1) :
    H1 = B1 + (Amat z sigma rho)ᵀ * B1 + B1 * (Amat z sigma rho)
      + (Amat z sigma rho)ᵀ * B1 * (Amat z sigma rho) := by
  have hinv : (Q0_mat_phys z sigma rho)⁻¹ = 1 + Amat z sigma rho :=
    Q0_mat_phys_inv_eq hz hvac hrho hsigma
  have hH1 : H1 = ((Q0_mat_phys z sigma rho)ᵀ)⁻¹ * B1 * (Q0_mat_phys z sigma rho)⁻¹ :=
    H1_eq_phys hz hvac hrho hsigma H1 B1 heq
  have hT : ((Q0_mat_phys z sigma rho)ᵀ)⁻¹ = 1 + (Amat z sigma rho)ᵀ := by
    rw [← transpose_nonsing_inv, hinv, transpose_add, transpose_one]
  rw [hH1, hT, hinv]
  exact H1_expand (Amat z sigma rho) B1

/-- **Tang & Lu eq (21), entrywise.**  The four terms of `H1_assembly_phys` read off as the sums
`{H₁}ᵢⱼ = {B₁}ᵢⱼ + ∑ₘ Aₘᵢ{B₁}ₘⱼ + ∑ₙ {B₁}ᵢₙAₙⱼ + ∑ₙ∑ₘ Aₘᵢ{B₁}ₘₙAₙⱼ` (eq 21 with
`{B₁}ᵢⱼ = bᵢⱼ·e^{−ikRᵢⱼ}`). -/
theorem H1_assembly_phys_apply {N : ℕ} {z : ℝ} {sigma rho : Fin N → ℝ}
    (hz : 0 < z) (hvac : 0 < vacMix rho sigma) (hrho : ∀ i, 0 ≤ rho i) (hsigma : ∀ i, 0 < sigma i)
    (H1 B1 : Matrix (Fin N) (Fin N) ℝ)
    (heq : (Q0_mat_phys z sigma rho)ᵀ * H1 * (Q0_mat_phys z sigma rho) = B1) (i j : Fin N) :
    H1 i j = B1 i j + (∑ m, Amat z sigma rho m i * B1 m j)
      + (∑ n, B1 i n * Amat z sigma rho n j)
      + ∑ n, ∑ m, Amat z sigma rho m i * B1 m n * Amat z sigma rho n j := by
  rw [H1_assembly_phys hz hvac hrho hsigma H1 B1 heq]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]

end FMSA.MatrixQ0
