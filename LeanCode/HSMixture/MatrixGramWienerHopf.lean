/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.MixtureCoercivityReduction

/-!
# General-N: the value-route Gram input from the matrix WH factorization (Gram mechanics)

The value-route Gram input `hfack`/`hfac0` (`matSymbolCoercive_of_gramFactors`) is the squared-norm
shape `∑vᵢ² − ρ∑ᵢⱼ radial_fourier(Φᵢⱼ) vᵢvⱼ = ∑ₗ|(Q̂₀ᵀ·v)ₗ|²`.  This file proves the pure
linear-algebra **mechanics** that reduce this, for general `N`, to the single matrix Wiener–Hopf
factorization (structure-factor) identity `(Q̂₀·Q̂₀ᵀ)ᵢⱼ = δᵢⱼ − ρ·radial_fourier(Φᵢⱼ)` — the mixture
Wertheim content:

* `matGram_normSq_expand` — `∑ₗ|(B·v)ₗ|² = ∑ₗ∑ᵢ∑ⱼ Bₗᵢ·conj(Bₗⱼ)·vᵢ·vⱼ` (raw Gram, real `v`).
* `matGram_normSq_eq_QQ` — with the Hermitian reality `Qneg = conj Q` (on the imaginary axis,
  `Q0_mat_c_phys_neg_axis`), `∑ₗ|(Qᵀ·v)ₗ|² = ∑ᵢⱼ (Q·Qnegᵀ)ᵢⱼ vᵢvⱼ`.
* `matWH_hfack_of_structureFactor` — **the reduction**: given `(Q·Qnegᵀ)ᵢⱼ = δᵢⱼ − ρ·Cᵢⱼ` (the WH
  factorization, `Cᵢⱼ = radial_fourier(Φᵢⱼ)`) and `Qneg = conj Q`, the Gram input `hfack` holds.

So the general-`N` value-route Gram input is now **entirely reduced to the single structure-factor
identity `hSF`** — the matrix analog of `baxter_wiener_hopf_factorization`.  At `N = 1` it is
the proven scalar theorem (`hfac_fin_one_of_baxterWH`); the general-`N` `hSF` (`matShellKernel` ⟷
`MatBaxterFactorization`/`Q̂₀`) is the sole remaining open piece.
-/

open scoped BigOperators
namespace FMSA.MixtureOzStar
variable {N : ℕ}

/-- **Gram expansion.**  For a complex matrix `B` and real vector `v`, the squared-norm form
`∑ₗ|(B·v)ₗ|²` expands to `∑ₗ∑ᵢ∑ⱼ Bₗᵢ·conj(Bₗⱼ)·vᵢ·vⱼ` (complex, via `z·conj z = |z|²`). -/
theorem matGram_normSq_expand (B : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℝ) :
    ((∑ l, Complex.normSq (B.mulVec (fun i => (v i : ℂ)) l) : ℝ) : ℂ)
      = ∑ l, ∑ i, ∑ j, B l i * (starRingEnd ℂ) (B l j) * (v i : ℂ) * (v j : ℂ) := by
  push_cast
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← Complex.mul_conj]
  simp only [Matrix.mulVec, dotProduct, map_sum]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [map_mul, Complex.conj_ofReal]; ring

/-- `∑ₗ|(Qᵀ·v)ₗ|² = ∑ᵢⱼ (Q·Qnegᵀ)ᵢⱼ vᵢvⱼ` when `Qneg = conj Q` (Hermitian reality on the imaginary
axis — the physical `Q0_mat_c_phys_neg_axis`). -/
theorem matGram_normSq_eq_QQ (Q Qneg : Matrix (Fin N) (Fin N) ℂ)
    (hherm : Qneg = Q.map (starRingEnd ℂ)) (v : Fin N → ℝ) :
    ((∑ l, Complex.normSq (Q.transpose.mulVec (fun i => (v i : ℂ)) l) : ℝ) : ℂ)
      = ∑ i, ∑ j, (Q * Qneg.transpose) i j * ((v i : ℂ) * (v j : ℂ)) := by
  rw [matGram_normSq_expand, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp only [Matrix.transpose_apply, hherm, Matrix.map_apply]; ring

/-- **General-N matrix WH factorization ⟹ the value-route Gram input `hfack`.**  Given the matrix WH
factorization `(Q·Qnegᵀ)ᵢⱼ = δᵢⱼ − ρ·Cᵢⱼ` (the mixture-Wertheim structure factor, with
`Cᵢⱼ = radial_fourier(Φᵢⱼ)`) and the Hermitian reality `Qneg = conj Q`, the `∑ₗ|(Qᵀ·v)ₗ|²` shape is
`∑vᵢ² − ρ∑ᵢⱼ Cᵢⱼ vᵢvⱼ`.  Reduces the general-`N` Gram input to the single (open) structure-factor
identity `hSF`. -/
theorem matWH_hfack_of_structureFactor (Q Qneg : Matrix (Fin N) (Fin N) ℂ) (rho : ℝ)
    (C : Fin N → Fin N → ℝ) (hherm : Qneg = Q.map (starRingEnd ℂ))
    (hSF : ∀ i j, (Q * Qneg.transpose) i j
      = (if i = j then (1 : ℂ) else 0) - (rho : ℂ) * (C i j : ℂ))
    (v : Fin N → ℝ) :
    (∑ i, v i ^ 2) - rho * ∑ i, ∑ j, C i j * v i * v j
      = ∑ l, Complex.normSq (Q.transpose.mulVec (fun i => (v i : ℂ)) l) := by
  apply Complex.ofReal_injective
  rw [matGram_normSq_eq_QQ Q Qneg hherm v]
  have h1 : (∑ i, ∑ j, (if i = j then (1 : ℂ) else 0) * ((v i : ℂ) * (v j : ℂ)))
      = ∑ i, ((v i : ℂ)) ^ 2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]; ring
  simp only [hSF, sub_mul, Finset.sum_sub_distrib, h1]
  push_cast
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x1 _ => ?_); ring

end FMSA.MixtureOzStar
