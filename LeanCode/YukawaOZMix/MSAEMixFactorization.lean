/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HSMixture.MatrixBaxterFourierWH

/-!
# MSAEMIX.1 — the matrix factorization staged; reduced to a matrix `hcore` (analog of MSAEXACT.6)

Group **MSAEMIX** (`proof_notes_msa_exact.md`).  Numerical partner: `msa_exact_mix.py`, MSAX.6.

The scalar MSAEXACT.1 was reduced (`YukawaOZ/MSAFullFactorization.factorization_of_core`) to a
single satisfiable core ring `hcore` = **MSAEXACT.6**, by staging the *non-compact* Baxter product
`|1 − ρQ̂(ik)|²` into its coupling-`0` (hard-sphere) part plus the `O(K)` increment.  This file
does the **matrix analog**: the mixture MSA Baxter product `(Q̂·Q̂(−·)ᵀ)` splits the same way, its
coupling-`0` part is the hard-sphere mixture Wiener–Hopf factorization
(`FMSA.MixtureOzStar.matSF_of_baxterFourierWH`), and the remainder is a **matrix core ring**
`hcore` — the matrix analog of MSAEXACT.6.

* `matBaxterProd_split` — pure `Matrix` algebra: with the full factor `Q = Q₀ + Q₁` (coupling-`0`
  factor `Q₀` plus the `O(K)` increment `Q₁`, and likewise `Qneg`), the Baxter product entrywise is
  `(Q₀ Q₀ⁿᵀ)ᵢⱼ + [(Q₀ Q₁ⁿᵀ) + (Q₁ Q₀ⁿᵀ) + (Q₁ Q₁ⁿᵀ)]ᵢⱼ`.  The matrix analog of the scalar
  `msa_lhs_split`.
* `matEMIXfactorization_of_core` — the matrix analog of `factorization_of_core`: given the
  coupling-`0` factorization `hHS` and that the increment matches `−ρ(Ĉ_MSA − Ĉ_HS)` (the matrix
  `hcore`), the full MSA matrix Baxter factorization `(Q Qnegᵀ)ᵢⱼ = δᵢⱼ − ρ Ĉ_MSA` holds.
* `matEMIXfactorization_of_baxterFourierWH` — discharges `hHS` through the HS-mixture Fourier
  Wiener–Hopf (`matSF_of_baxterFourierWH`: KDEF + shell bridge + `MatBaxterFourierWH`), so the
  **sole** remaining input is the matrix `hcore`.  This is the concrete statement that MSAEMIX.1
  "pushes to the same gap" as MSAEXACT.6.

⚠ **What is still open (the gap).** As at `N = 1`, the matrix `hcore` for the *specific* MSA Baxter
factor — the increment `Q₁` assembled from Blum & Høye's `M_j, N_j` (via the (★) cancellation,
`MSAEMixture`/`cancellation_star`) and the Yukawa tails, matched against the mixture core+tail DCF
transforms — is the analytic core, not discharged here.  It is the matrix analog of MSAEXACT.6's
`hcore` ring; the scalar one already has no small-multiplier route, so the matrix one is at least as
hard.  This file establishes the reduction, not the ring.
-/

open MeasureTheory
open FMSA.MixtureOzStar FMSA.HardSphere

namespace MSAEMix

variable {N : ℕ}

/-- **The matrix Baxter product splits into the coupling-`0` product plus the increment.**  With the
full factor `Q = Q₀ + Q₁` and its reflected companion `Qneg = Q₀ⁿ + Q₁ⁿ`, entrywise

    ((Q₀+Q₁)(Q₀ⁿ+Q₁ⁿ)ᵀ)ᵢⱼ = (Q₀ Q₀ⁿᵀ)ᵢⱼ + [(Q₀ Q₁ⁿᵀ) + (Q₁ Q₀ⁿᵀ) + (Q₁ Q₁ⁿᵀ)]ᵢⱼ.

Pure `Matrix` algebra (`transpose_add`, `add_mul`, `mul_add`) — the matrix analog of the scalar
`msa_lhs_split`. -/
theorem matBaxterProd_split (Q0 Q1 Q0neg Q1neg : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    ((Q0 + Q1) * (Q0neg + Q1neg).transpose) i j
      = (Q0 * Q0neg.transpose) i j
        + ((Q0 * Q1neg.transpose) i j + (Q1 * Q0neg.transpose) i j
            + (Q1 * Q1neg.transpose) i j) := by
  simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_apply]
  ring

/-- ⭐ **MSAEMIX.1 reduced to the matrix `hcore` ring — the matrix analog of MSAEXACT.6.**  Given

* `hHS` — the coupling-`0` (hard-sphere mixture) Baxter factorization
  `(Q₀ Q₀ⁿᵀ)ᵢⱼ = δᵢⱼ − ρ Ĉ_HS,ᵢⱼ`, and
* `hcore` — that the coupling increment matches `−ρ (Ĉ_MSA − Ĉ_HS)ᵢⱼ` (**the matrix core ring**),

the full MSA matrix Baxter factorization `((Q₀+Q₁)(Q₀ⁿ+Q₁ⁿ)ᵀ)ᵢⱼ = δᵢⱼ − ρ Ĉ_MSA,ᵢⱼ` holds.  Pure
algebra on top of `matBaxterProd_split`, exactly as the scalar `factorization_of_core` sits on
`msa_factor_split`. -/
theorem matEMIXfactorization_of_core (Q0 Q1 Q0neg Q1neg : Matrix (Fin N) (Fin N) ℂ)
    (rho : ℝ) (cHShat cMSAhat : Fin N → Fin N → ℂ)
    (hHS : ∀ i j, (Q0 * Q0neg.transpose) i j
      = (if i = j then (1 : ℂ) else 0) - (rho : ℂ) * cHShat i j)
    (hcore : ∀ i j, (Q0 * Q1neg.transpose) i j + (Q1 * Q0neg.transpose) i j
        + (Q1 * Q1neg.transpose) i j = -(rho : ℂ) * (cMSAhat i j - cHShat i j))
    (i j : Fin N) :
    ((Q0 + Q1) * (Q0neg + Q1neg).transpose) i j
      = (if i = j then (1 : ℂ) else 0) - (rho : ℂ) * cMSAhat i j := by
  rw [matBaxterProd_split, hHS, hcore]; ring

/-- ⭐⭐ **The reduction with `hHS` discharged — MSAEMIX.1 pushes to the same gap as MSAEXACT.6.**
Taking the coupling-`0` factor to be the hard-sphere mixture Fourier Baxter factor whose product is
given by `matSF_of_baxterFourierWH` (the mixture Wiener–Hopf: matrix Baxter factorization `hKDEF` +
shell `hbridge` + the pure-`q` core identity `hWH`), the full MSA matrix factorization reduces
to the **single** matrix `hcore` — the matrix analog of MSAEXACT.6's closure-recovery ring, with the
hard-sphere part no longer assumed but produced. -/
theorem matEMIXfactorization_of_baxterFourierWH
    (Q Qneg Q1 Q1neg : Matrix (Fin N) (Fin N) ℂ)
    (K q Phi : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (rho sigma k : ℝ) (hsigma : 0 < sigma)
    (hKDEF : MatBaxterFactorization K q rho sigma)
    (hbridge : ∀ i j,
      2 * ∫ v in (0 : ℝ)..sigma, K i j v * Real.cos (k * v) = radial_fourier (Phi i j) k)
    (hWH : MatBaxterFourierWH Q Qneg q sigma k)
    (cMSAhat : Fin N → Fin N → ℂ)
    (hcore : ∀ i j, (Q * Q1neg.transpose) i j + (Q1 * Qneg.transpose) i j
        + (Q1 * Q1neg.transpose) i j
        = -(rho : ℂ) * (cMSAhat i j - (radial_fourier (Phi i j) k : ℂ)))
    (i j : Fin N) :
    ((Q + Q1) * (Qneg + Q1neg).transpose) i j
      = (if i = j then (1 : ℂ) else 0) - (rho : ℂ) * cMSAhat i j :=
  matEMIXfactorization_of_core Q Q1 Qneg Q1neg rho
    (fun i j => (radial_fourier (Phi i j) k : ℂ)) cMSAhat
    (fun i j => matSF_of_baxterFourierWH Q Qneg K q Phi rho sigma k hsigma hKDEF hbridge hWH i j)
    hcore i j

/-- Non-vacuity: at coupling `0` (`Q₁ = Q₁ⁿ = 0`, `Ĉ_MSA = Ĉ_HS`) the matrix `hcore`
is `0 = 0` and `matEMIXfactorization_of_core` returns the coupling-`0` factorization itself — so the
implication is not vacuously satisfied by an unsatisfiable `hcore`. -/
theorem matEMIXfactorization_of_core_zero_coupling
    (Q0 Q0neg : Matrix (Fin N) (Fin N) ℂ) (rho : ℝ) (cHShat : Fin N → Fin N → ℂ)
    (hHS : ∀ i j, (Q0 * Q0neg.transpose) i j
      = (if i = j then (1 : ℂ) else 0) - (rho : ℂ) * cHShat i j)
    (i j : Fin N) :
    ((Q0 + 0) * (Q0neg + 0).transpose) i j
      = (if i = j then (1 : ℂ) else 0) - (rho : ℂ) * cHShat i j :=
  matEMIXfactorization_of_core Q0 0 Q0neg 0 rho cHShat cHShat hHS
    (by intro i j; simp) i j

end MSAEMix
