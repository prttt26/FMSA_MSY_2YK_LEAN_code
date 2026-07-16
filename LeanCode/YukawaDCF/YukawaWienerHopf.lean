/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Tasks Y1.4 / Y1.6 — residue → `B₁`, and the first-order RDF `Ĥ₁` ([LN] §6.4)

**Y1.4 (residue theorem, matrix form).**  The Wiener–Hopf projection ([LN] Eq. 63) is a
matrix-valued function with simple Yukawa poles; the residue at each pole ([LN] Eq. 65–66) is the
scalar `U₁`-residue **conjugated** by the inverse-Baxter factors.  `matrix_conj_residue`
is that step abstractly: if every entry of `bfun` has residue `Bres` at `s₀`, then `L·bfun·R` has
residue `L·Bres·R`.  (The full derivation of the Eq. 63 integrand itself — the §6.1–§6.3
Hilbert-transform Wiener–Hopf split, Y1.3 — is deferred; here the projected form is the input.)

**Y1.6 (first-order RDF).**  `Ĥ₁ = [Q̂₀ᵀ]⁻¹ · B₁ · [Q̂₀]⁻¹` ([LN] Eq. 68), equivalent to
`Q̂₀ᵀ · Ĥ₁ · Q̂₀ = B₁` (Eq. 69) for invertible `Q̂₀` — pure matrix algebra.  Its residue is the
conjugated residue of `B₁` (`Hhat1_residue`, via `matrix_conj_residue`).  With `B₁`'s spectral form
from Y1.5 (`SpectralAmplitude.bMulti`/`spectralAmp`, residue `[Q̂₀⁻¹·K·Q̂₀⁻ᵀ]`), this records the
**exact** [LN] form of the first-order Yukawa-pole residue — no `K·G` simplification.

**Y1.3c support (`matrix_conj_residue_analytic`).**  The `s`-dependent-factor generalization of
`matrix_conj_residue`: for conjugating factors analytic (convergent) at the pole, the residue of
`Lf s · bfun s · Rf s` is `Lval · Bres · Rval`.  This is the tool the Wiener–Hopf outer term
`T_U = [Q̂₀(−k)]⁻¹ U₁ [Q̂₀ᵀ(−k)]⁻¹` needs (inverse-Baxter factors depend on `s` but are analytic at
the Yukawa pole).  Consumed by `YukawaCausalResidue.lean` (Y1.3c).

Status: ✓ DONE (2026-07-15), axiom-clean (`matrix_conj_residue`, `matrix_conj_residue_analytic`,
`Hhat1`, `Hhat1_spec`, `Hhat1_residue`).  Full Y1.3-dependent derivation of `B₁` from the OZ equation:
Y1.3a (supports) + Y1.3c (residue extraction) done; Y1.3b (projection identity) remains open.
-/

set_option linter.style.longLine false
set_option linter.style.whitespace false

open Filter Topology Matrix

namespace FMSA.YukawaWH

/-- Entry of a triple matrix product as a double sum: `(L·X·R)_{ij} = Σ_q Σ_p L_{ip} X_{pq} R_{qj}`. -/
theorem triple_apply {n : ℕ} (L X R : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (L * X * R) i j = ∑ q, ∑ p, L i p * X p q * R q j := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_mul]

/-- **Y1.4 — residue through matrix conjugation** (matrix form of the residue-theorem step).
If each entry of `bfun` has residue `Bres` at `s₀` (`(s−s₀)·bfun s p q → Bres p q`), then the
conjugated matrix `L·bfun·R` has residue `L·Bres·R` entrywise. -/
theorem matrix_conj_residue {n : ℕ} (L R : Matrix (Fin n) (Fin n) ℂ)
    (bfun : ℂ → Matrix (Fin n) (Fin n) ℂ) (s0 : ℂ) (Bres : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n)
    (hb : ∀ p q, Tendsto (fun s => (s - s0) * bfun s p q) (𝓝[≠] s0) (𝓝 (Bres p q))) :
    Tendsto (fun s => (s - s0) * (L * bfun s * R) i j) (𝓝[≠] s0)
      (𝓝 ((L * Bres * R) i j)) := by
  rw [triple_apply]
  have hstep : ∀ s, (s - s0) * (L * bfun s * R) i j
      = ∑ q, ∑ p, L i p * ((s - s0) * bfun s p q) * R q j := by
    intro s
    rw [triple_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_); ring
  simp_rw [hstep]
  apply tendsto_finsetSum; intro q _
  apply tendsto_finsetSum; intro p _
  exact (tendsto_const_nhds.mul (hb p q)).mul tendsto_const_nhds

/-- **Y1.3c support — residue through *analytic* matrix conjugation.**  Generalizes
`matrix_conj_residue` to `s`-dependent conjugating factors `Lf s`, `Rf s` that are merely *analytic*
(here: convergent) at the pole `s₀`: if `Lf → Lval`, `Rf → Rval` and each entry of `bfun` has residue
`Bres` at `s₀`, then `Lf s · bfun s · Rf s` has residue `Lval · Bres · Rval`.  This is exactly what the
Wiener–Hopf outer term `T_U = [Q̂₀(−k)]⁻¹ U₁ [Q̂₀ᵀ(−k)]⁻¹` needs: the inverse-Baxter factors depend on
`s` but are analytic at the Yukawa pole, so only their pole-values enter the residue. -/
theorem matrix_conj_residue_analytic {n : ℕ} (Lf Rf bfun : ℂ → Matrix (Fin n) (Fin n) ℂ) (s0 : ℂ)
    (Lval Rval Bres : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n)
    (hL : ∀ p q, Tendsto (fun s => Lf s p q) (𝓝[≠] s0) (𝓝 (Lval p q)))
    (hR : ∀ p q, Tendsto (fun s => Rf s p q) (𝓝[≠] s0) (𝓝 (Rval p q)))
    (hb : ∀ p q, Tendsto (fun s => (s - s0) * bfun s p q) (𝓝[≠] s0) (𝓝 (Bres p q))) :
    Tendsto (fun s => (s - s0) * (Lf s * bfun s * Rf s) i j) (𝓝[≠] s0)
      (𝓝 ((Lval * Bres * Rval) i j)) := by
  rw [triple_apply]
  have hstep : ∀ s, (s - s0) * (Lf s * bfun s * Rf s) i j
      = ∑ q, ∑ p, Lf s i p * ((s - s0) * bfun s p q) * Rf s q j := by
    intro s
    rw [triple_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_); ring
  simp_rw [hstep]
  apply tendsto_finsetSum; intro q _
  apply tendsto_finsetSum; intro p _
  exact ((hL i p).mul (hb p q)).mul (hR q j)

/-- First-order RDF `Ĥ₁ = [Q̂₀ᵀ]⁻¹ · B₁ · [Q̂₀]⁻¹` ([LN] Eq. 68). -/
noncomputable def Hhat1 {n : ℕ} (Q0 B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (Q0ᵀ)⁻¹ * B * Q0⁻¹

/-- **Y1.6 — Eq. 68 ⟺ 69.**  For invertible `Q̂₀`, `Ĥ₁` satisfies `Q̂₀ᵀ · Ĥ₁ · Q̂₀ = B₁`.  Pure
matrix algebra (`Matrix.mul_nonsing_inv` / `nonsing_inv_mul`). -/
theorem Hhat1_spec {n : ℕ} (Q0 B : Matrix (Fin n) (Fin n) ℂ) (h : IsUnit Q0.det) :
    Q0ᵀ * Hhat1 Q0 B * Q0 = B := by
  have hT : IsUnit (Q0ᵀ).det := by rwa [Matrix.det_transpose]
  unfold Hhat1
  rw [show Q0ᵀ * ((Q0ᵀ)⁻¹ * B * Q0⁻¹) * Q0
        = (Q0ᵀ * (Q0ᵀ)⁻¹) * B * (Q0⁻¹ * Q0) by simp only [Matrix.mul_assoc],
      Matrix.mul_nonsing_inv Q0ᵀ hT, Matrix.nonsing_inv_mul Q0 h, Matrix.one_mul, Matrix.mul_one]

/-- **Y1.6 — the first-order RDF residue is the conjugated `B₁` residue.**  If `B₁ = bfun s` has
entrywise residue `Bres` at `s₀`, then `Ĥ₁(s) = [Q̂₀ᵀ]⁻¹ bfun s [Q̂₀]⁻¹` has residue
`[Q̂₀ᵀ]⁻¹ · Bres · [Q̂₀]⁻¹` = `Hhat1 Q̂₀ Bres`.  With Y1.5's single-tail `Bres = [Q̂₀⁻¹·K·Q̂₀⁻ᵀ]`
this is the exact [LN] Yukawa-pole residue of the first-order RDF. -/
theorem Hhat1_residue {n : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℂ)
    (bfun : ℂ → Matrix (Fin n) (Fin n) ℂ) (s0 : ℂ) (Bres : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n)
    (hb : ∀ p q, Tendsto (fun s => (s - s0) * bfun s p q) (𝓝[≠] s0) (𝓝 (Bres p q))) :
    Tendsto (fun s => (s - s0) * Hhat1 Q0 (bfun s) i j) (𝓝[≠] s0) (𝓝 (Hhat1 Q0 Bres i j)) := by
  unfold Hhat1
  exact matrix_conj_residue (Q0ᵀ)⁻¹ Q0⁻¹ bfun s0 Bres i j hb

end FMSA.YukawaWH
