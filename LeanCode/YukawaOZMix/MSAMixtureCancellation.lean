/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# MSAEMIX.1 (bounded down-payment) — the mixture cancellation identity (★)

Group **MSAEMIX** (`proof_notes_msa_exact.md`).  Numerical partner: `msa_exact_mix.py`, MSAX.6.

The scalar down-payment for MSAEXACT.1 (`YukawaOZ/MSABaxterTransform.lean`) is *transform
infrastructure*: the ansatz, its `D = 0` reduction, and two Laplace integrals.  The mixture has one
piece of genuinely **new algebra** that the scalar case cannot see, and it is load-bearing rather
than infrastructural, so it is the natural first payment here.

**The problem.** Blum & Høye's `M_j` and `N_j` (their (20)/(21)) are built from `D_lj + C_lj`.  Each
term is `O(e^{+zσ_l})` while the sum is `O(K)`.  At `N = 1` the cancellation is visible on the face
of it — `D + C = (1 − γ)D` with `1 − γ = 2πρĝ(z)/z` — and one simply writes it down.  At `N ≥ 2` it
is **not** term-by-term: it runs through the *off-diagonal* of `γ`.  Forming `M`, `N` from the
unscaled `D`, `C` loses `zσ_max/ln 10` digits to cancellation.

**The identity.**  In the variables `Dt_ij = D_ij e^{−zσ_ij}`, `Gt_ij = ĝ_ij(z) e^{+zσ_ij}`,

    (★)   Dt_lj − Ct_lj = e^{−zσ_l} · (2π/z) · Σ_k ρ_k Gt_lk Dt_kj

whose right-hand side is manifestly `O(K)` and free of growing exponentials.  It holds because the
single expression

    δ_lk − γ_lk · e^{z(σ_k − σ_l)/2} = (2π/z) ρ_k Gt_lk e^{−zσ_l}

covers **both** `k = l` (where the two Kronecker deltas cancel and the exponential is `1`) and
`k ≠ l` (where `−σ_lk + (σ_k − σ_l)/2 = −σ_l` exactly, with `σ_lk = (σ_l + σ_k)/2`).  That the same
formula serves both cases is the whole content; `entry_cancel` below is that statement.

## Results

* `sigMix`, `gam`, `Ct`, `Wt` — Blum & Høye (35) [with the `/z` their print inverts] and the scaled
  auxiliaries of `msa_exact_mix._pieces`.
* `sigMix_exponent` — the exponent bookkeeping `−σ_lk + (σ_k − σ_l)/2 = −σ_l`, the reason one
  formula covers both cases.
* `entry_cancel` — the per-entry identity, `k = l` and `k ≠ l` alike.
* ⭐ `cancellation_star` — **(★)**, the mixture form of the `e^{zσ}` cancellation.
* `cancellation_star_fin_one` — at `N = 1` it degenerates to `(1 − γ)D`, the scalar statement:
  MSAEMIX.2's discipline applied to this piece.

⚠ **Scope.** This is (★) and its bookkeeping, not the factorization.  MSAEMIX.1's analytic core —
that the matrix ansatz *recovers* the MSA closure `c_ij = −βu_ij` on the exterior — re-runs the
`BAXTER` machinery at general `N` with Yukawa tails in both `Q` and `c`, exactly as flagged for
MSAEXACT.1, and is not attempted here.
-/

namespace MSAEMix

open Finset Real

variable {N : ℕ}

/-- Additive hard-core contact distance `σ_ij = (σ_i + σ_j)/2`. -/
noncomputable def sigMix (σ : Fin N → ℝ) (i j : Fin N) : ℝ := (σ i + σ j) / 2

/-- Blum & Høye (35), with the `/z` their print inverts (their (27) forces it):
`γ_ij = δ_ij − 2πρ_j ĝ_ij(z)/z`, written in `Gt_ij = ĝ_ij(z)e^{+zσ_ij}`. -/
noncomputable def gam (z : ℝ) (ρ σ : Fin N → ℝ) (Gt : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) : ℝ :=
  (if i = j then (1 : ℝ) else 0)
    - 2 * Real.pi * ρ j * Gt i j * Real.exp (-z * sigMix σ i j) / z

/-- `Ct_ij = −C_ij e^{−zσ_ij} = Σ_l γ_il Dt_lj e^{z(σ_l − σ_i)/2}` (from their (27)). -/
noncomputable def Ct (z : ℝ) (ρ σ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) : ℝ :=
  ∑ l, gam z ρ σ Gt i l * Dt l j * Real.exp (z * (σ l - σ i) / 2)

/-- `W̃_ij = (2π/z) Σ_k ρ_k Gt_ik Dt_kj` — manifestly `O(K)`, no growing exponential. -/
noncomputable def Wt (z : ℝ) (ρ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) : ℝ :=
  2 * Real.pi / z * ∑ k, ρ k * Gt i k * Dt k j

/-- The exponent bookkeeping that makes one formula cover both cases:
`−σ_lk + (σ_k − σ_l)/2 = −σ_l`. -/
theorem sigMix_exponent (σ : Fin N → ℝ) (l k : Fin N) :
    -(sigMix σ l k) + (σ k - σ l) / 2 = -(σ l) := by
  unfold sigMix; ring

/-- **The per-entry identity.**  `δ_lk − γ_lk e^{z(σ_k−σ_l)/2} = (2π/z)ρ_k Gt_lk e^{−zσ_l}`,
for `k = l` and `k ≠ l` alike.

At `k = l` the two Kronecker deltas cancel and the exponential is `1`; at `k ≠ l` the delta is
absent and `sigMix_exponent` does the work.  That both land on the same right-hand side is what
makes `cancellation_star` a single sum rather than a diagonal plus a remainder. -/
theorem entry_cancel (z : ℝ) (ρ σ : Fin N → ℝ) (Gt : Matrix (Fin N) (Fin N) ℝ)
    (l k : Fin N) :
    (if l = k then (1 : ℝ) else 0) - gam z ρ σ Gt l k * Real.exp (z * (σ k - σ l) / 2)
      = 2 * Real.pi / z * (ρ k * Gt l k) * Real.exp (-z * σ l) := by
  have hexp : Real.exp (-z * sigMix σ l k) * Real.exp (z * (σ k - σ l) / 2)
      = Real.exp (-z * σ l) := by
    rw [← Real.exp_add]
    congr 1
    unfold sigMix; ring
  unfold gam
  by_cases h : l = k
  · subst h
    have h1 : Real.exp (z * (σ l - σ l) / 2) = 1 := by
      simp
    rw [if_pos rfl, h1]
    have : Real.exp (-z * sigMix σ l l) = Real.exp (-z * σ l) := by
      congr 1; unfold sigMix; ring
    rw [this]; ring
  · rw [if_neg h]
    have : (0 : ℝ) - (0 - 2 * Real.pi * ρ k * Gt l k * Real.exp (-z * sigMix σ l k) / z)
          * Real.exp (z * (σ k - σ l) / 2)
        = 2 * Real.pi * ρ k * Gt l k / z
          * (Real.exp (-z * sigMix σ l k) * Real.exp (z * (σ k - σ l) / 2)) := by
      ring
    rw [this, hexp]; ring

/-- ⭐ **(★) — the mixture `e^{zσ}` cancellation.**

`Dt_lj − Ct_lj = e^{−zσ_l}·W̃_lj`, with `W̃` free of growing exponentials.  This is what makes
Blum & Høye's `M_j`, `N_j` computable at `N ≥ 2`: their raw form is a difference of terms each
`O(e^{+zσ_l})`, and the cancellation is **not** term-by-term but runs through `γ`'s off-diagonal.

At `N = 1` it degenerates to the scalar `D + C = (1 − γ)D` — see `cancellation_star_fin_one`. -/
theorem cancellation_star (z : ℝ) (ρ σ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (l j : Fin N) :
    Dt l j - Ct z ρ σ Gt Dt l j = Real.exp (-z * σ l) * Wt z ρ Gt Dt l j := by
  have key : ∀ k : Fin N,
      (if l = k then (1 : ℝ) else 0) * Dt k j
        - gam z ρ σ Gt l k * Dt k j * Real.exp (z * (σ k - σ l) / 2)
        = Real.exp (-z * σ l) * (2 * Real.pi / z * (ρ k * Gt l k * Dt k j)) := by
    intro k
    have h := entry_cancel z ρ σ Gt l k
    calc (if l = k then (1 : ℝ) else 0) * Dt k j
          - gam z ρ σ Gt l k * Dt k j * Real.exp (z * (σ k - σ l) / 2)
        = ((if l = k then (1 : ℝ) else 0)
            - gam z ρ σ Gt l k * Real.exp (z * (σ k - σ l) / 2)) * Dt k j := by ring
      _ = 2 * Real.pi / z * (ρ k * Gt l k) * Real.exp (-z * σ l) * Dt k j := by rw [h]
      _ = Real.exp (-z * σ l) * (2 * Real.pi / z * (ρ k * Gt l k * Dt k j)) := by ring
  have hsplit : Dt l j - Ct z ρ σ Gt Dt l j
      = ∑ k, ((if l = k then (1 : ℝ) else 0) * Dt k j
          - gam z ρ σ Gt l k * Dt k j * Real.exp (z * (σ k - σ l) / 2)) := by
    rw [Finset.sum_sub_distrib]
    unfold Ct
    congr 1
    simp
  rw [hsplit, Finset.sum_congr rfl fun k _ => key k]
  unfold Wt
  simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- MSAEMIX.2 discipline for this piece: at one component (★) **is** the scalar
`D + C = (1 − γ)D`, i.e. `Dt − Ct = (2πρ Gt/z)·e^{−zσ}·Dt`. -/
theorem cancellation_star_fin_one (z : ℝ) (ρ σ : Fin 1 → ℝ)
    (Gt Dt : Matrix (Fin 1) (Fin 1) ℝ) :
    Dt 0 0 - Ct z ρ σ Gt Dt 0 0
      = Real.exp (-z * σ 0) * (2 * Real.pi / z * (ρ 0 * Gt 0 0 * Dt 0 0)) := by
  have := cancellation_star z ρ σ Gt Dt 0 0
  simpa [Wt] using this

end MSAEMix
