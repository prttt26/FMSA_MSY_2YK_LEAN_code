/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAMixtureBHRoot
import LeanCode.Closures.MSASolutionFamily

/-!
# MSAEMIX.6 — the matrix Blum–Høye residual map (item 2) and the assembly plan

The general-`N` analogue of the `N = 1` `exists_contDiffAt_bhRoot`: the physical mixture MSA
amplitudes `(Dt, Gt)` are a `C^∞` family of the coupling near `K = 0`.  Route: the implicit function
theorem `exists_contDiffAt_root_of_prodDomain_ift` (generalised in item 1 to any complete normed
space `E`, here `E = Matrix × Matrix`) applied to the **residual map** with zero set `MixBHRoot`.

This file lands **item 2**: the residual map `matBhResidual` and the proof that its zero set is
exactly `MixBHRoot` (`matBhResidual_eq_zero_iff`).  Both are std-3, purely algebraic — no analysis.

Remaining items (scoped in `proof_notes_msa_exact.md`):

* item 3 — `ContDiffAt` of `matBhResidual` at the base point (matrix-valued smoothness of
  `qpMat/Wt/Ct/AVec/qhatMixR` in `(Dt, Gt)`); no reusable infrastructure exists yet;
* item 4 — the base equation `matBhResidual (0, (0, Gt₀)) = 0`;
* item 5 — the partial Jacobian in `(Dt, Gt)` is invertible (block-triangular, diagonal blocks
  = multiplication by `Q̂₀`, discharged with `FMSA.MatrixQ0.Q0_mat_phys_isUnit_det`).

⚠ Items 3–5 and the IFT capstone need `Matrix (Fin N) (Fin N) ℝ` **as a normed space** — Mathlib
gives `Matrix` no global norm (only opt-in Frobenius/`linfty` instances), so the capstone must first
activate one (`Matrix.frobeniusNormedAddCommGroup` / `…NormedSpace`) before `ContDiffAt` / `fderiv`
even typecheck.  That analytic assembly is the substantial remaining work.
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

end MSAMixture
