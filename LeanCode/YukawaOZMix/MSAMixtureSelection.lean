/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Mixture MSA root selection — Blum & Høye's Eq. (41) — Group `MSAEMIX`, task MSAEMIX.3

Companion to `MSAMixturePositivity.lean` (MSAEMIX.0).  Numerical partner: `msa_exact_mix.py`
(Group MSAX task MSAX.6, closed 2026-08-13).

**The problem this closes.** Blum & Høye, *J. Stat. Phys.* **19**, 317 (1978), p. 323: with the
`K_ij` given rather than the `γ_ij`, "one must expect multiple solutions to occur, **of which only
one is acceptable**".  Their acceptability criterion is Eq. (41), derived from the physical
requirement `g_ij(r) = g_ji(r)`.  ⚠ It is **vacuous at `N = 1`** — which is why the scalar group
had to supply a different rule (`MSAEXACT.3`'s `physical_baxter_factor_unique`, `A/2π > 0`).

**Their equations, as used here.**

    q′_ij = q^{0′}_ij (1 + M_j) + A_i⁰ N_j                                            (24)
    g_ij(σ_ij⁺) = [ q′_ij − z C_ij e^{−zσ_ij} ] / (2π σ_ij)                           (38)
    q^{0′}_ij M_j + A_i⁰ N_j − z C_ij e^{−zσ_ij} = (i ↔ j)                            (41)

## Results

* `bh41_iff_contact_symm` — Eq. (41) **is** `g_ij = g_ji`: with `σ` symmetric and positive, the
  contact matrix is symmetric iff the (41) bracket is.
* `bh41_expand` — substituting (24) turns that bracket difference into Blum & Høye's printed
  Eq. (41), given only that `q^{0′}` is symmetric.  A `ring` identity: (41) is not an extra
  physical input, it is `g_ij = g_ji` rewritten.
* `bh41_vacuous_at_fin_one` — ⚠ **at `N = 1` the criterion holds for every candidate**.  The formal
  record of why single-component root selection needed `MSAEXACT.3` instead.
* `bh41_not_vacuous` — and at `N = 2` it is a *proper* filter: an explicit candidate it rejects.
  Without this the criterion could be trivially true and every "acceptable root" theorem vacuous.
* `bh41_conditions_card` — it is exactly `N(N−1)/2` independent equations; `0` at `N = 1`.
* ⭐ `A0_row_index_forced` — **(24)'s `A_i⁰` carries the ROW index, and that is forced, not a
  typo.**  From (13)/(14), `q′_ij = B_j + σ_ij A_j`; expanding with (23) makes the `N_j` coefficient
  `A_j⁰ + 4 B_j⁰ λ_ji / σ_j²`, and this collapses **identically** to `A_i⁰`.  Misreading it is
  invisible at equal diameters and wrong at unequal ones — the trap MSAX.6 had to clear before the
  Tang & Lu gate would pass.

No new axiom: `ring`, `field_simp` and `Finset` cardinality only.
-/

namespace MSAMixture

open Matrix Finset

variable {N : ℕ}

/-! ### The hard-sphere coefficients of Blum & Høye Eq. (25) -/

/-- `A_j⁰ = [2π/(1−ξ₃)²](1 − ξ₃ + 3σ_j ξ₂)`. -/
noncomputable def A0 (Δ ξ₂ : ℝ) (σ : Fin N → ℝ) (j : Fin N) : ℝ :=
  2 * Real.pi / Δ ^ 2 * (Δ + 3 * σ j * ξ₂)

/-- `B_j⁰ = [2π/(1−ξ₃)²](−(3/2)σ_j² ξ₂)`. -/
noncomputable def B0 (Δ ξ₂ : ℝ) (σ : Fin N → ℝ) (j : Fin N) : ℝ :=
  2 * Real.pi / Δ ^ 2 * (-(3 / 2) * σ j ^ 2 * ξ₂)

/-- `λ_ji = (σ_j − σ_i)/2`. -/
noncomputable def lam (σ : Fin N → ℝ) (j i : Fin N) : ℝ := (σ j - σ i) / 2

/-- ⭐ **(24)'s `A_i⁰` carries the row index, and it is forced.**

From (13)/(14) one has `q′_ij = B_j + σ_ij A_j`; expanding with (23) makes the coefficient of `N_j`
equal to `A_j⁰ + 4 B_j⁰ λ_ji / σ_j²`, and *that expression collapses to `A_i⁰`*.  So the printed
`A_i⁰` — the one object in (24) carrying the row rather than the column index, alone among
`M_j, N_j, A_j, B_j` — is not a typo.

⚠ At equal diameters `λ_ji = 0` and the two readings coincide, which is exactly why the misreading
survives every equal-`σ` check. -/
theorem A0_row_index_forced {Δ ξ₂ : ℝ} {σ : Fin N → ℝ} (i j : Fin N)
    (hΔ : Δ ≠ 0) (hσ : σ j ≠ 0) :
    A0 Δ ξ₂ σ j + 4 * B0 Δ ξ₂ σ j * lam σ j i / σ j ^ 2 = A0 Δ ξ₂ σ i := by
  unfold A0 B0 lam
  field_simp
  ring

/-! ### Eq. (41) and the contact matrix -/

variable (qp0 zC : Matrix (Fin N) (Fin N) ℝ) (A0v Mv Nv : Fin N → ℝ)

/-- Blum & Høye (24): `q′_ij = q^{0′}_ij(1 + M_j) + A_i⁰ N_j`. -/
def qp (i j : Fin N) : ℝ := qp0 i j * (1 + Mv j) + A0v i * Nv j

/-- The bracket of (38): `q′_ij − z C_ij e^{−zσ_ij}`, i.e. `2π σ_ij g_ij(σ_ij⁺)`. -/
def contactBracket (i j : Fin N) : ℝ := qp qp0 A0v Mv Nv i j - zC i j

/-- **Eq. (41) is exactly `g_ij = g_ji`.**  With `σ_ij` symmetric and nonzero, the contact values
agree iff the (41) bracket does — (38) divides by `2π σ_ij`, which is common to both sides. -/
theorem bh41_iff_contact_symm {σm : Matrix (Fin N) (Fin N) ℝ} (i j : Fin N)
    (hsym : σm i j = σm j i) (hne : σm i j ≠ 0) :
    contactBracket qp0 zC A0v Mv Nv i j / (2 * Real.pi * σm i j)
      = contactBracket qp0 zC A0v Mv Nv j i / (2 * Real.pi * σm j i)
    ↔ contactBracket qp0 zC A0v Mv Nv i j = contactBracket qp0 zC A0v Mv Nv j i := by
  rw [← hsym]
  constructor
  · intro h
    have hπ : (2 : ℝ) * Real.pi * σm i j ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hne
    field_simp at h
    exact h
  · intro h; rw [h]

/-- **Substituting (24) gives Blum & Høye's printed Eq. (41)**, provided only that `q^{0′}` is
symmetric.  So (41) is not an extra physical input — it is `g_ij = g_ji` rewritten. -/
theorem bh41_expand (i j : Fin N) (hq0 : qp0 i j = qp0 j i) :
    contactBracket qp0 zC A0v Mv Nv i j - contactBracket qp0 zC A0v Mv Nv j i
      = qp0 i j * (Mv j - Mv i) + A0v i * Nv j - A0v j * Nv i - (zC i j - zC j i) := by
  unfold contactBracket qp
  rw [hq0]
  ring

/-- A candidate is **acceptable** when its contact matrix is symmetric — Blum & Høye's Eq. (41). -/
def Acceptable (Y : Matrix (Fin N) (Fin N) ℝ) : Prop := ∀ i j, Y i j = Y j i

/-- ⚠ **At `N = 1` the criterion is vacuous**: every candidate passes.

This is the formal record of why single-component root selection could not use it, and had to be
supplied instead by `MSAEXACT.3` (`physical_baxter_factor_unique`: the acceptable root is the one
with `A/2π > 0`). -/
theorem bh41_vacuous_at_fin_one (Y : Matrix (Fin 1) (Fin 1) ℝ) : Acceptable Y := by
  intro i j
  fin_cases i; fin_cases j; rfl

/-- …and at `N = 2` it is a **proper** filter: here is a candidate it rejects.

Non-vacuity in the sense the group's own discipline demands — without it, "the acceptable root"
theorems could all be vacuously true. -/
theorem bh41_not_vacuous : ¬ Acceptable (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  have := h 0 1
  norm_num at this

/-- The criterion is one equation per off-diagonal pair `i < j`, i.e. `N(N−1)/2` of them —
**zero at `N = 1`**, which is `bh41_vacuous_at_fin_one` counted rather than proved.

⚠ Stated concretely for `N = 1, 2, 3` rather than in general: the general count is a routine
bijection with 2-element subsets, and the only load-bearing entry is the `0`. -/
theorem bh41_conditions_card_one :
    ((Finset.univ : Finset (Fin 1 × Fin 1)).filter fun p => p.1 < p.2).card = 0 := by decide

theorem bh41_conditions_card_two :
    ((Finset.univ : Finset (Fin 2 × Fin 2)).filter fun p => p.1 < p.2).card = 1 := by decide

theorem bh41_conditions_card_three :
    ((Finset.univ : Finset (Fin 3 × Fin 3)).filter fun p => p.1 < p.2).card = 3 := by decide

end MSAMixture
