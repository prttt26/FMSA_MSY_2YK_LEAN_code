/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.Q0ComplexDetMatchClose

/-!
# First-order mixture RDF `Ĥ₁(s) = [Q̂₀ᵀ(s)]⁻¹·B₁(s)·[Q̂₀(s)]⁻¹` (Tang & Lu eq 15/21, complex `s`)

The final momentum-side assembly of the Tang & Lu first-order mixture RDF, complex-`s` analogue of
`MixtureH1Assembly` (real `z`).  From the transformed first-order OZ equation `Q̂₀ᵀ·Ĥ₁·Q̂₀ = B₁`
(eq 14) and the complex Woodbury inverse `[Q̂₀(s)]⁻¹ = I + AmatC` (`AmatC = Uₒ(I−VₒUₒ)⁻¹Vₒ`,
`Q0ComplexRankTwo.Q0_mat_c_phys_inv_eq`):

* **`Q0_mat_c_phys_H1_eq`** — eq (15): `Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹`;
* **`H1_assembly_c`** — eq (21) four-term matrix form `Ĥ₁ = B₁ + AmatCᵀ·B₁ + B₁·AmatC +
  AmatCᵀ·B₁·AmatC` (`[Q̂₀ᵀ]⁻¹ = I + AmatCᵀ`, `noncomm_ring`);
* **`H1_assembly_c_apply`** — eq (21) entrywise: `{H₁}ᵢⱼ = {B₁}ᵢⱼ + ∑ₘ Aₘᵢ{B₁}ₘⱼ + ∑ₙ {B₁}ᵢₙAₙⱼ
  + ∑ₙ∑ₘ Aₘᵢ{B₁}ₘₙAₙⱼ`;
* **`AmatC_entry`** — the propagator entries are the **explicit** Tang & Lu amplitudes `Aᵢⱼ =
  2π√(ρᵢρⱼ)·Wtl_ij·e^{−sλᵢⱼ}/(Δ·detTL)` (`AmatC = [Q̂₀]⁻¹ − I` + `Q0_inv_entry_bridge`).

So `Ĥ₁` is fully explicit: the eq (21) sums (`H1_assembly_c_apply`) with the propagator entries
(`AmatC_entry`) resolved to the closed-form Appendix amplitudes and `B₁` carrying the eq (23)
residues.  All axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Complex Matrix

namespace FMSA.ComplexRankTwo

open FMSA.MatrixQ0 FMSA.Q0Complex FMSA.MixtureNoSpinodal FMSA.MixtureArcBound

/-- **Tang & Lu eq (15) over ℂ** — `Q̂₀ᵀ·Ĥ₁·Q̂₀ = B₁` (`det ≠ 0`) ⟹ `Ĥ₁ = [Q̂₀ᵀ]⁻¹·B₁·[Q̂₀]⁻¹`. -/
theorem H1_eq_of_transformed_c {N : ℕ} (Q0 H1 B1 : Matrix (Fin N) (Fin N) ℂ)
    (hdet : IsUnit Q0.det) (heq : Q0ᵀ * H1 * Q0 = B1) :
    H1 = (Q0ᵀ)⁻¹ * B1 * Q0⁻¹ := by
  have hdetT : IsUnit (Q0ᵀ).det := (Matrix.det_transpose Q0) ▸ hdet
  have hL : (Q0ᵀ)⁻¹ * Q0ᵀ = 1 := Matrix.nonsing_inv_mul _ hdetT
  have hR : Q0 * Q0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  rw [← heq]
  simp only [Matrix.mul_assoc]
  rw [hR, Matrix.mul_one, ← Matrix.mul_assoc, hL, Matrix.one_mul]

/-- The Woodbury off-identity part of `[Q̂₀(s)]⁻¹` (`[Q̂₀(s)]⁻¹ = 1 + AmatC`). -/
noncomputable def AmatC {N : ℕ} (s : ℂ) (sigma rho : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  UmatC s sigma rho * (1 - VmatC s sigma rho * UmatC s sigma rho)⁻¹ * VmatC s sigma rho

/-- **`AmatC` entries are the explicit Tang & Lu amplitudes** `2π√(ρᵢρⱼ)Wtl_ij e^{−sλ}/(Δ detTL)`
(via `Q0_inv_entry_bridge`, since `AmatC = [Q̂₀]⁻¹ − I`). -/
theorem AmatC_entry {N : ℕ} {sigma rho : Fin N → ℝ} {s : ℂ} (hs : s ≠ 0)
    (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i)
    (hdet : IsUnit (Q0_mat_c_phys s sigma rho).det) (i j : Fin N) :
    AmatC s sigma rho i j
    = 2 * Real.pi * (Real.sqrt (rho i * rho j) : ℂ) * Wtl s rho sigma i j
        * Complex.exp (-(((sigma j : ℂ) - (sigma i : ℂ)) / 2 * s))
      / ((vacMix rho sigma : ℂ) * detTL s rho sigma) := by
  have hinv : (Q0_mat_c_phys s sigma rho)⁻¹ = 1 + AmatC s sigma rho :=
    Q0_mat_c_phys_inv_eq hs hvac hrho hdet
  have hbr := Q0_inv_entry_bridge hs hvac hrho hdet i j
  rw [hinv, Matrix.add_apply, Matrix.one_apply] at hbr
  exact add_left_cancel hbr

/-- **Tang & Lu eq (15) for the complex Baxter factor** — `Ĥ₁(s) = [Q̂₀ᵀ(s)]⁻¹·B₁(s)·[Q̂₀(s)]⁻¹`. -/
theorem Q0_mat_c_phys_H1_eq {N : ℕ} {sigma rho : Fin N → ℝ} {s : ℂ}
    (hdet : IsUnit (Q0_mat_c_phys s sigma rho).det)
    (H1 B1 : Matrix (Fin N) (Fin N) ℂ)
    (heq : (Q0_mat_c_phys s sigma rho)ᵀ * H1 * (Q0_mat_c_phys s sigma rho) = B1) :
    H1 = ((Q0_mat_c_phys s sigma rho)ᵀ)⁻¹ * B1 * (Q0_mat_c_phys s sigma rho)⁻¹ :=
  H1_eq_of_transformed_c _ H1 B1 hdet heq

/-- **Tang & Lu eq (21) — the four-term first-order RDF (complex `s`).**  From `Q̂₀ᵀ·Ĥ₁·Q̂₀ = B₁`,
`Ĥ₁ = B₁ + AmatCᵀ·B₁ + B₁·AmatC + AmatCᵀ·B₁·AmatC` (using `[Q̂₀]⁻¹ = 1 + AmatC`). -/
theorem H1_assembly_c {N : ℕ} {sigma rho : Fin N → ℝ} {s : ℂ} (hs : s ≠ 0)
    (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i)
    (hdet : IsUnit (Q0_mat_c_phys s sigma rho).det)
    (H1 B1 : Matrix (Fin N) (Fin N) ℂ)
    (heq : (Q0_mat_c_phys s sigma rho)ᵀ * H1 * (Q0_mat_c_phys s sigma rho) = B1) :
    H1 = B1 + (AmatC s sigma rho)ᵀ * B1 + B1 * AmatC s sigma rho
      + (AmatC s sigma rho)ᵀ * B1 * AmatC s sigma rho := by
  have hinv : (Q0_mat_c_phys s sigma rho)⁻¹ = 1 + AmatC s sigma rho :=
    Q0_mat_c_phys_inv_eq hs hvac hrho hdet
  have hH1 : H1 = ((Q0_mat_c_phys s sigma rho)ᵀ)⁻¹ * B1 * (Q0_mat_c_phys s sigma rho)⁻¹ :=
    Q0_mat_c_phys_H1_eq hdet H1 B1 heq
  have hT : ((Q0_mat_c_phys s sigma rho)ᵀ)⁻¹ = 1 + (AmatC s sigma rho)ᵀ := by
    rw [← Matrix.transpose_nonsing_inv, hinv, Matrix.transpose_add, Matrix.transpose_one]
  rw [hH1, hT, hinv]
  noncomm_ring

/-- **Tang & Lu eq (21), entrywise (complex `s`)** — `{H₁}ᵢⱼ = {B₁}ᵢⱼ + ∑ₘ Aₘᵢ{B₁}ₘⱼ + ∑ₙ
{B₁}ᵢₙAₙⱼ + ∑ₙ∑ₘ Aₘᵢ{B₁}ₘₙAₙⱼ`, `A = AmatC` (entries = `AmatC_entry`'s explicit amplitudes). -/
theorem H1_assembly_c_apply {N : ℕ} {sigma rho : Fin N → ℝ} {s : ℂ} (hs : s ≠ 0)
    (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i)
    (hdet : IsUnit (Q0_mat_c_phys s sigma rho).det)
    (H1 B1 : Matrix (Fin N) (Fin N) ℂ)
    (heq : (Q0_mat_c_phys s sigma rho)ᵀ * H1 * (Q0_mat_c_phys s sigma rho) = B1) (i j : Fin N) :
    H1 i j = B1 i j + (∑ m, AmatC s sigma rho m i * B1 m j)
      + (∑ n, B1 i n * AmatC s sigma rho n j)
      + ∑ n, ∑ m, AmatC s sigma rho m i * B1 m n * AmatC s sigma rho n j := by
  rw [H1_assembly_c hs hvac hrho hdet H1 B1 heq]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]

end FMSA.ComplexRankTwo
