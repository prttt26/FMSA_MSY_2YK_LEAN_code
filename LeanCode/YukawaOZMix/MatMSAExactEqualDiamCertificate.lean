/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAEMixBHRoot

/-!
# MSAEMIX.4 equal-diameter `hcore`, Fourier layer discharged (out-of-build certificate)

Group **MSAEMIX** (`proof_notes_msa_exact.md`).  This file is **not** imported by the `LeanCode`
root, so a normal `lake build` never compiles it; build it on demand only
(`lake build MatMSAExactEqualDiamCertificate`).

## What this file does

`MSAEMixBHRoot.matMSAexactEqualDiam_hcore` (the equal-σ matrix closure-recovery axiom) is stated
with two `radial_fourier` integrals on its right (`𝓕[matMSACoreCorr]ᵢⱼ`, `𝓕[matMSAtail]ᵢⱼ`).  This
file **discharges that Fourier/definitional layer** — the genuinely provable part — reducing the
equal-diameter `hcore` to one **pure cos/sin/exp k-space identity**
(`matMSAexactEqualDiam_kspace_residual`), which carries *no* `radial_fourier` and *no* integral.
Concretely, `matMSAexactEqualDiam_hcore_of_residual` proves the *exact statement* of the axiom from
the residual by rewriting both transforms into closed form via the matrix Fourier bridges
`radial_fourier_matMSACoreCorr` / `radial_fourier_matMSAtail` and then the five scalar interval
formulas `psi1/2/4_formula` / `one_sub_exp_sin_integral` / `coshRatio_sin_integral` (both at the
per-entry upper limit `σ_ij = sigMix σ i j`).  This part compiles.

So the *only* thing left axiomatic is the k-space polynomial identity itself — the direct matrix
analog of the scalar `MSAExactCertificate.msaexact_hcore_of_residual` reduction.

## Why the residual stays an axiom

The residual is the matrix closure-recovery relation
`ĉ_ij = Q̂_ij(ik) + Q̂_ji(−ik) − Σ_l ρ_l Q̂_il(ik) Q̂_jl(−ik)` at the physical Blum–Høye root
(equal σ), gated by `hroot`/`hσ` and false off-root.  It is **certified in sympy**
(`msaemix_core_coeffs.py`, parent repo): all five closed-form core coefficients `c₁..c₅` match the
exact factor-product extraction (held-out `~1e-12`, binary/ternary, unequal ρ).  Its Lean discharge
is the same `ring`-infeasible high-degree normalization as the scalar `msaexact_kspace_residual`
(measured weeks/~200 GB), asserted here as one explicit sympy-computation axiom.
-/

open MSAEMix Real FMSA.HardSphere FMSA.MSAExact

namespace FMSA.MSAExact.MatEqualDiamCertificate

variable {N : ℕ}

/-- ⭐ **MSAEMIX.4 equal-diameter, reduced to pure k-space algebra.**  The equal-σ matrix
closure-recovery identity with *both* radial transforms in closed `cos/sin/exp` form — with **no**
`radial_fourier` and **no** integral.  Left: the matrix Baxter factor-product coupling increment
(`FtHS`/`Ft1` complex-Laplace factors).  Right: `−√(ρᵢρⱼ)·(𝓕[c_core]ᵢⱼ + 𝓕[c_tail]ᵢⱼ)` with the two
transforms evaluated by the `psi1/2/4`/`one_sub_exp`/`coshRatio` interval formulas at `σ_ij`.  Gated
by the physical root `hroot` and equal-σ `hσ` (false off-root).  **Certified in sympy**
(`msaemix_core_coeffs.py`); ring-infeasible in Lean (see module docstring). -/
axiom matMSAexactEqualDiam_kspace_residual (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (k : ℝ) (hk : k ≠ 0) (hz : 0 < z) (hsig1 : 0 < sig)
    (hσ : ∀ i, sigma i = sig) (hroot : MixBHRoot z sig rho sigma Gt Dt K) (i j : Fin N) :
    (FtHS z sig rho sigma (Complex.I * k)
          * (Ft1 z sig rho sigma Gt Dt (-(Complex.I * k))).transpose) i j
        + (Ft1 z sig rho sigma Gt Dt (Complex.I * k)
            * (FtHS z sig rho sigma (-(Complex.I * k))).transpose) i j
        + (Ft1 z sig rho sigma Gt Dt (Complex.I * k)
            * (Ft1 z sig rho sigma Gt Dt (-(Complex.I * k))).transpose) i j
      = -(√(rho i * rho j) : ℂ)
        * (((4 * π / k *
                (coreC1 z rho sigma Gt Dt K i j *
                    ((sin (k * sigMix sigma i j)
                        - k * sigMix sigma i j * cos (k * sigMix sigma i j)) / k ^ 2)
                  + coreC2 z rho sigma Gt Dt K i j *
                    ((2 / k ^ 3 - sigMix sigma i j ^ 2 / k) * cos (k * sigMix sigma i j)
                      + 2 * sigMix sigma i j / k ^ 2 * sin (k * sigMix sigma i j) - 2 / k ^ 3)
                  + coreC3 z rho sigma Gt Dt K i j *
                    ((-24 / k ^ 5 + 12 * sigMix sigma i j ^ 2 / k ^ 3 - sigMix sigma i j ^ 4 / k)
                          * cos (k * sigMix sigma i j)
                      + (-24 * sigMix sigma i j / k ^ 4 + 4 * sigMix sigma i j ^ 3 / k ^ 2)
                          * sin (k * sigMix sigma i j)
                      + 24 / k ^ 5)
                  + coreC4 z rho sigma Gt Dt K i j *
                    ((1 - cos (k * sigMix sigma i j)) / k
                      - (k - rexp (-z * sigMix sigma i j)
                            * (k * cos (k * sigMix sigma i j) + z * sin (k * sigMix sigma i j)))
                          / (z ^ 2 + k ^ 2))
                  + coreC5 z rho sigma Gt Dt K i j *
                    (1 / 2 * rexp (-z * sigMix sigma i j)
                          * ((k - rexp (z * sigMix sigma i j)
                                * (k * cos (k * sigMix sigma i j) - z * sin (k * sigMix sigma i j)))
                              / (z ^ 2 + k ^ 2))
                      + 1 / 2 * rexp (-z * sigMix sigma i j)
                          * ((k - rexp (-z * sigMix sigma i j)
                                * (k * cos (k * sigMix sigma i j) + z * sin (k * sigMix sigma i j)))
                              / (z ^ 2 + k ^ 2))
                      - rexp (-z * sigMix sigma i j)
                          * ((1 - cos (k * sigMix sigma i j)) / k))) : ℝ) : ℂ)
          + ((4 * π * K i j / k
              * ((k * cos (k * sigMix sigma i j) + z * sin (k * sigMix sigma i j))
                  / (z ^ 2 + k ^ 2)) : ℝ) : ℂ))

/-- ⭐ **MSAEMIX.4 equal-diameter `hcore`, Fourier layer fully formalized.**  The *exact* statement
of `MSAEMixBHRoot.matMSAexactEqualDiam_hcore`, here **derived** from the pure-k-space
`matMSAexactEqualDiam_kspace_residual`: the two `radial_fourier` transforms are rewritten into
closed form by the matrix bridges + interval formulas, isolating the remaining gap to the single
identity.  (Requires the physical `0 < z`, `0 < sig`, which the axiom leaves implicit.) -/
theorem matMSAexactEqualDiam_hcore_of_residual (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (k : ℝ) (hk : k ≠ 0) (hz : 0 < z) (hsig1 : 0 < sig)
    (hσ : ∀ i, sigma i = sig) (hroot : MixBHRoot z sig rho sigma Gt Dt K) (i j : Fin N) :
    (FtHS z sig rho sigma (Complex.I * k)
        * (Ft1 z sig rho sigma Gt Dt (-(Complex.I * k))).transpose) i j
      + (Ft1 z sig rho sigma Gt Dt (Complex.I * k)
          * (FtHS z sig rho sigma (-(Complex.I * k))).transpose) i j
      + (Ft1 z sig rho sigma Gt Dt (Complex.I * k)
          * (Ft1 z sig rho sigma Gt Dt (-(Complex.I * k))).transpose) i j
      = -(Real.sqrt (rho i * rho j) : ℂ)
          * ((radial_fourier (matMSACoreCorr z rho sigma Gt Dt K i j) k : ℂ)
            + (radial_fourier (matMSAtail K z sigma i j) k : ℂ)) := by
  have hsig : ∀ i, 0 < sigma i := fun i => by rw [hσ i]; exact hsig1
  have hzk : z ^ 2 + k ^ 2 ≠ 0 := by positivity
  rw [radial_fourier_matMSACoreCorr z rho sigma Gt Dt K hsig k i j,
      radial_fourier_matMSAtail K hz sigma hsig k i j,
      psi1_formula hk (sigMix sigma i j), psi2_formula hk (sigMix sigma i j),
      psi4_formula hk (sigMix sigma i j),
      one_sub_exp_sin_integral hzk hk, coshRatio_sin_integral hzk hk]
  exact matMSAexactEqualDiam_kspace_residual z sig rho sigma Gt Dt K k hk hz hsig1 hσ hroot i j

end FMSA.MSAExact.MatEqualDiamCertificate
