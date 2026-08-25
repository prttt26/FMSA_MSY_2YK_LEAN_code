/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Mixture MSA — positivity, the stability determinant, and what `∂βp/∂ρ` does *not* see

Group **MSAEMIX** (the mixture; the scalar case is `MSAEXACT`, `YukawaOZ/MSAClosedForm.lean`).
Numerical partner: Group **MSAX** task MSAX.6, `msa_exact_mix.py` — closed 2026-08-13, gated on
the 24 Tang & Lu states / 72 published full-MSA contact values (agreement `4.7e-05`, i.e. every
value to the last digit they print).

**Source.** L. Blum & J. S. Høye, *J. Stat. Phys.* **19**, 317 (1978).  Their Eq. (39),

    χ⁻¹ = ∂βp/∂ρ = (1/ρ) Σ_j ρ_j (A_j/2π)²                                     (39)

and Baxter's factorization at `k = 0`,

    δ_ij − √(ρ_iρ_j) ĉ_ij(0) = (F Fᵀ)_ij,   F_ij = δ_ij − √(ρ_iρ_j) Q̂_ij(0).    (5)

## What this file adds over the scalar `MSAEXACT` results

`MSAClosedForm.lean` proves the `N = 1` wall: `a = B²` is a perfect square, so `a < 0` is outside
the range and no real Baxter factor exists inside the spinodal.  At `N ≥ 2` **there are two
different squares**, and conflating them is a genuine trap that this file closes:

* Eq. (39) makes `∂βp/∂ρ` a **sum of squares** — still `≥ 0`, still a wall;
* the **stability determinant** is the square of `det F` — a *different* object;
* ⭐ and `∂βp/∂ρ > 0` **does not imply** the mixture is stable.  Eq. (39) is mechanical stability
  at *fixed composition*; a binary goes unstable against **composition** fluctuations first, and
  the spinodal is `det F = 0`.  Measured (MSAX.6): at the mixture spinodal `∂βp/∂ρ` runs
  `0.4 … 24.5` — it never goes near zero.  Lifting the scalar rule "spinodal ⟺ `A = 0`" to
  "`A_j = 0` for every `j`" would be `N` conditions for one parameter, and is wrong.

`mixCompressibility_pos_of_det_zero_example` is the formal record of that: an explicit `F` with
`det F = 0` — the fluid is *on* its spinodal — and every column sum strictly positive, so Eq. (39)
returns a strictly positive compressibility there.

## Results

* `mixCompressibility` and `mixCompressibility_nonneg` — (39) as a sum of squares.
* `no_real_mix_baxter_of_neg_compressibility` — `< 0` is outside the range, at every `N`.
* `mixStability_eq_det_sq`, `mixStability_nonneg` — `det(F Fᵀ) = (det F)²`, the `N`-component
  wall: **no real Baxter factorization represents a thermodynamically unstable mixture.**
* `mixStability_eq_zero_iff` — the spinodal is exactly `det F = 0`.
* ⭐ `mixCompressibility_pos_of_det_zero_example` — (39) does **not** detect that spinodal.
* `mixCompressibility_fin_one`, `mixStability_fin_one` — the `N = 1` specialisations reduce to the
  scalar objects of `MSAEXACT` (MSAEMIX.2's non-vacuity discipline, applied here).

No new axiom: everything is `Matrix.det_mul`, `Matrix.det_transpose` and `Finset.sum_nonneg`.
-/

namespace MSAMixture

open Matrix Finset

variable {N : ℕ}

/-- Blum & Høye (39) without the `1/ρ`: `Σ_j ρ_j B_j²` with `B_j = A_j/2π`.

The overall `1/ρ` is dropped because it is a positive constant and every statement below is about
the sign; keeping it would only add a hypothesis `0 < ρ`. -/
def mixCompressibility (ρ B : Fin N → ℝ) : ℝ := ∑ j, ρ j * B j ^ 2

/-- **(39) is a sum of squares**, so the compressibility of any real solution is `≥ 0`.

The `N = 1` case is `MSAEXACT`'s `compressibility_nonneg_of_baxter_sq`; the content at general `N`
is that *no cancellation between species is possible* — each term carries its own square. -/
theorem mixCompressibility_nonneg {ρ B : Fin N → ℝ} (hρ : ∀ j, 0 ≤ ρ j) :
    0 ≤ mixCompressibility ρ B := by
  refine Finset.sum_nonneg fun j _ => ?_
  exact mul_nonneg (hρ j) (sq_nonneg _)

/-- A negative compressibility is **outside the range** of (39): no real amplitudes produce it.

The `N`-component form of `no_real_baxter_factor_of_neg`. -/
theorem no_real_mix_baxter_of_neg_compressibility {ρ : Fin N → ℝ} {S : ℝ}
    (hρ : ∀ j, 0 ≤ ρ j) (hS : S < 0) : ¬ ∃ B : Fin N → ℝ, S = mixCompressibility ρ B := by
  rintro ⟨B, rfl⟩
  exact absurd (mixCompressibility_nonneg hρ) (not_le.mpr hS)

/-- The `k = 0` stability matrix `δ_ij − √(ρ_iρ_j)ĉ_ij(0) = (F Fᵀ)_ij` of Baxter's Eq. (5). -/
def stabilityMat (F : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ := F * Fᵀ

/-- **The stability determinant is a perfect square** — the `N`-component wall. -/
theorem mixStability_eq_det_sq (F : Matrix (Fin N) (Fin N) ℝ) :
    (stabilityMat F).det = F.det ^ 2 := by
  simp [stabilityMat, Matrix.det_mul, Matrix.det_transpose, sq]

/-- ⇒ `det[δ_ij/ρ_i − ĉ_ij(0)]·∏ρ_i ≥ 0` always: **no real Baxter factorization represents a
thermodynamically unstable mixture.**  Not an MSA fact — a property of any single-phase OZ closure
admitting a real factorization. -/
theorem mixStability_nonneg (F : Matrix (Fin N) (Fin N) ℝ) : 0 ≤ (stabilityMat F).det := by
  rw [mixStability_eq_det_sq]; exact sq_nonneg _

/-- **The mixture spinodal is exactly `det F = 0`** — one condition, not `N`. -/
theorem mixStability_eq_zero_iff (F : Matrix (Fin N) (Fin N) ℝ) :
    (stabilityMat F).det = 0 ↔ F.det = 0 := by
  rw [mixStability_eq_det_sq]; exact sq_eq_zero_iff

/-- Blum & Høye (13): `A_j/2π` is the `j`-th **column sum** of `F`. -/
def colSum (F : Matrix (Fin N) (Fin N) ℝ) (j : Fin N) : ℝ := ∑ i, F i j

/-- ⭐ **Eq. (39) does not detect the mixture spinodal.**

An explicit binary `F` sitting exactly *on* the spinodal (`det F = 0`) whose column sums are all
strictly positive, so `∂βp/∂ρ = (1/ρ)Σρ_j(A_j/2π)² > 0` there for any positive densities.

This is the formal counterpart of the MSAX.6 measurement (`∂βp/∂ρ = 0.4 … 24.5` at the spinodal)
and the reason the scalar rule "spinodal ⟺ `A = 0`" must **not** be lifted to "`A_j = 0` ∀ `j`":
that would be `N` conditions for one parameter, and the true condition `det F = 0` is compatible
with every `A_j` bounded away from zero. -/
theorem mixCompressibility_pos_of_det_zero_example :
    ∃ F : Matrix (Fin 2) (Fin 2) ℝ, F.det = 0 ∧ ∀ j, 0 < colSum F j := by
  refine ⟨!![1, 1; 1, 1], ?_, ?_⟩
  · simp [Matrix.det_fin_two_of]
  · intro j
    fin_cases j <;> norm_num [colSum, Fin.sum_univ_two]

/-- …and then the compressibility itself is strictly positive on that spinodal state. -/
theorem mixCompressibility_pos_at_spinodal_example {ρ : Fin 2 → ℝ} (hρ : ∀ j, 0 < ρ j) :
    ∃ F : Matrix (Fin 2) (Fin 2) ℝ,
      F.det = 0 ∧ 0 < mixCompressibility ρ (colSum F) := by
  obtain ⟨F, hdet, hcol⟩ := mixCompressibility_pos_of_det_zero_example
  refine ⟨F, hdet, ?_⟩
  have : ∀ j ∈ (Finset.univ : Finset (Fin 2)), 0 < ρ j * colSum F j ^ 2 := by
    intro j _
    exact mul_pos (hρ j) (pow_pos (hcol j) 2)
  exact Finset.sum_pos this ⟨0, Finset.mem_univ 0⟩

/-! ### MSAEMIX.2 discipline — the `N = 1` specialisations

Not decoration: these are what says the matrix statements are the right generalisation of
`MSAEXACT`'s scalar ones rather than differently-normalised objects. -/

/-- At one component (39) is the scalar perfect square `ρ·B²`. -/
theorem mixCompressibility_fin_one (ρ B : Fin 1 → ℝ) :
    mixCompressibility ρ B = ρ 0 * B 0 ^ 2 := by
  simp [mixCompressibility]

/-- At one component the stability determinant is `F₀₀²` — `MSAEXACT`'s `a = B²`. -/
theorem mixStability_fin_one (F : Matrix (Fin 1) (Fin 1) ℝ) :
    (stabilityMat F).det = F 0 0 ^ 2 := by
  rw [mixStability_eq_det_sq, Matrix.det_fin_one]

/-- Non-vacuity: a non-degenerate binary `F` (not the dilute `F = I` point) with a strictly
positive stability determinant and a strictly positive compressibility — the state the gate's
Tang & Lu points live at. -/
example : ((stabilityMat (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ)).det = 9)
    ∧ mixCompressibility (fun _ => (1 : ℝ)) (colSum (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ))
        = 18 := by
  constructor
  · rw [mixStability_eq_det_sq]; norm_num [Matrix.det_fin_two_of]
  · norm_num [mixCompressibility, colSum, Fin.sum_univ_two]

end MSAMixture
