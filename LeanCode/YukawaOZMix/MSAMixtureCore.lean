/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAMixtureConcrete
import LeanCode.YukawaOZ.MSACoreTransform

/-!
# MSAEMIX.4 — the concrete equal-σ mixture core correction `matMSACoreCorr` (general `N`)

Group **MSAEMIX** (`proof_notes_msa_exact.md`).  Numerical partner: `msaemix_core_coeffs.py`,
`msaemix_core_derivation.py` (parent repo).

The scalar `msaCoreCorr` (`YukawaOZ/MSAFullFactorization.lean`) is the `N = 1` MSA core-DCF
correction in `coreCorrection` form.  This file gives its **equal-diameter mixture** analog, per
entry `(i,j)`, with the five coefficients `c₁..c₅` **derived** from the corrected Baxter real-space
relation

    2π r c_ij(r) = −Q'_ij(r) + Σ_l ρ_l ∫₀^∞ Q'_il(t+r) Q_jl(t) dt        (r > 0)

(the Wiener–Hopf split of `ĉ_ij = Q̂_ij(ik) + Q̂_ji(−ik) − Σ_l ρ_l Q̂_il(ik) Q̂_jl(−ik)`) and
verified against the `mpmath`-exact coefficient extraction to `~1e-12` (`msaemix_core_coeffs.py`,
all-five closed-form, no fitting, binary/ternary, unequal ρ).  Every coefficient is a **per-`(i,j)`
linear term plus a `Σ_l ρ_l` (or `Σ_{l,m}`) species sum**, so the formulas hold for **all `N`** (the
`N = 1` reduction is the scalar `msaCoreCorr`; e.g. `c₄ → −4πρKG/z = −v/z`, `c₃ → −ξ·da/2`).

⚠ **Equal σ only.**  At unequal σ the core is *piecewise* (breakpoints, `_compute_mediated`); these
single-piece formulas are the equal-diameter case, verified as such.

Amplitudes are the already-Lean-defined mixture Baxter quantities: `q'_ij = Q0phys + mixDqp`,
`A_j = Qppphys + mixDA`, `W̃ = Wt`, `C̃ = Ct` (from `MSAMixtureCancellation`/`MatrixQ0`), and the
inputs `Gt` (Laplace moment), `Dt`, `K` (contact-normalised Yukawa amplitudes).
-/

open Real
open FMSA.Q0Complex FMSA.ExactMSA FMSA.HardSphere FMSA.MatrixQ0

namespace MSAMixture

variable {N : ℕ}

/-! ### The MSA-dressed amplitudes (HS reference + coupling increment) -/

/-- The MSA Baxter `q′` amplitude: HS `q^{0′}_ij` (`Q0phys`) plus the coupling increment
`mixDqp`. -/
noncomputable def qpMSA (z : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) : ℝ :=
  Q0phys rho sigma i j + mixDqp z rho sigma Gt Dt i j

/-- The MSA Baxter `A` amplitude (column-`j`): HS `A_j⁰` (`Qppphys`) plus the increment `mixDA`. -/
noncomputable def AMSA (z : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (j : Fin N) : ℝ :=
  Qppphys rho sigma j j + mixDA z rho sigma Gt Dt j

/-! ### The five core-DCF coefficients (equal σ, general `N`) -/

/-- The pairwise `(i,l),(j,l)` contribution to the constant coefficient `c₁`, from the symbolic
Baxter convolution.  ⚠ The `σ^k` factors on the poly-amplitude terms (`A²→σ³`, `A·C̃jl→σ`,
`A·q'jl→σ²`) were DROPPED by the old `σ=1` derivation (`0<r<1`) and RESTORED here
(`eqsig_symbolic.py`): correct for general `σ` (the tail-amplitude terms are `σ`-independent). -/
noncomputable def c1pair (z Al qil qjl Wil Wjl Ctil Ctjl sigma : ℝ) : ℝ :=
  (6 * Al * Ctil + 6 * Al * Wjl
    + z * (sigma ^ 3 * Al ^ 2 + 6 * sigma * Al * Ctjl - 3 * sigma ^ 2 * Al * qjl
        + 6 * Ctil * qjl - 6 * Ctjl * qil))
  / (12 * Real.pi * z)

/-- `c₁` (constant term): linear `−(A_j − A_j⁰)/2π = −mixDA/2π` plus the `Σ_l ρ_l` pairwise
contribution (MSA minus hard-sphere; HS has `W̃ = C̃ = 0`). -/
noncomputable def coreC1 (z : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) : ℝ :=
  -(mixDA z rho sigma Gt Dt j) / (2 * Real.pi)
    + ∑ l, rho l * (c1pair z (AMSA z rho sigma Gt Dt l) (qpMSA z rho sigma Gt Dt i l)
          (qpMSA z rho sigma Gt Dt j l) (Wt z rho Gt Dt i l) (Wt z rho Gt Dt j l)
          (Ct z rho sigma Gt Dt i l) (Ct z rho sigma Gt Dt j l) (sigMix sigma i j)
        - c1pair z (Qppphys rho sigma l l) (Q0phys rho sigma i l) (Q0phys rho sigma j l) 0 0 0 0
            (sigMix sigma i j))

/-- `c₂` (coeff of `r`): `(1/4π)[Σ_l ρ_l(q'q' − q'⁰q'⁰) − Σ_l ρ_l A_l(C̃_il + C̃_jl)]`. -/
noncomputable def coreC2 (z : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) : ℝ :=
  (1 / (4 * Real.pi)) *
    (∑ l, rho l * (qpMSA z rho sigma Gt Dt i l * qpMSA z rho sigma Gt Dt j l
          - Q0phys rho sigma i l * Q0phys rho sigma j l)
      - ∑ l, rho l * AMSA z rho sigma Gt Dt l
          * (Ct z rho sigma Gt Dt i l + Ct z rho sigma Gt Dt j l))

/-- `c₃` (coeff of `r³`): `−(1/48π) Σ_l ρ_l(A_l² − A_l⁰²)` — independent of `(i,j)`. -/
noncomputable def coreC3 (z : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) : ℝ :=
  -(1 / (48 * Real.pi)) *
    ∑ l, rho l * ((AMSA z rho sigma Gt Dt l) ^ 2 - (Qppphys rho sigma l l) ^ 2)

/-- `c₄` (coeff of `(1−e^{−zr})/r`): `−(2π/z) Σ_l ρ_l(K_il Gt_jl + Gt_il K_jl)`. -/
noncomputable def coreC4 (z : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) : ℝ :=
  -(2 * Real.pi / z) * ∑ l, rho l * (K i l * Gt j l + Gt i l * K j l)

/-- `c₅` (coeff of `coshRatio/r`): `−(8π²/z²) Σ_{l,m} ρ_l ρ_m Gt_il K_lm Gt_jm`.  (The `σ_ij` tail
factor `e^{−zσ_ij}` now lives in the σ-aware `coshRatio z σ_ij r`, not in this coefficient.) -/
noncomputable def coreC5 (z : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) : ℝ :=
  -(8 * Real.pi ^ 2 / z ^ 2) * ∑ l, ∑ m, rho l * rho m * Gt i l * K l m * Gt j m

/-! ### The matrix core correction and its radial transform -/

/-- ⭐ **The equal-σ mixture MSA core-DCF correction** `c_ij(r) − c^HS_ij(r)`, per entry the scalar
`coreCorrection` with the derived coefficients `c₁..c₅` and `σ_ij = (σ_i+σ_j)/2`.  The matrix analog
of the scalar `msaCoreCorr`; general `N`. -/
noncomputable def matMSACoreCorr (z : ℝ) (rho sigma : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) : ℝ → ℝ :=
  coreCorrection (coreC1 z rho sigma Gt Dt K i j) (coreC2 z rho sigma Gt Dt K i j)
    (coreC3 z rho sigma Gt Dt K i j) (coreC4 z rho sigma Gt Dt K i j)
    (coreC5 z rho sigma Gt Dt K i j) z (sigMix sigma i j)

/-- **The matrix core-correction transform is per-entry `radial_fourier_coreCorrection`.**
So the matrix `𝓕[c_core]ᵢⱼ` in the mixture `hcore`'s `Ĉ_MSA` is the closed form assembled from the
five core sub-integrals at `σ_ij` — no new integral, the scalar one lifts (as for `matMSAtail`). -/
theorem radial_fourier_matMSACoreCorr (z : ℝ) (rho sigma : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (hsig : ∀ i, 0 < sigma i) (k : ℝ) (i j : Fin N) :
    radial_fourier (matMSACoreCorr z rho sigma Gt Dt K i j) k
      = (4 * Real.pi / k) *
          (coreC1 z rho sigma Gt Dt K i j * (∫ r in (0 : ℝ)..sigMix sigma i j, r * Real.sin (k * r))
            + coreC2 z rho sigma Gt Dt K i j
                * (∫ r in (0 : ℝ)..sigMix sigma i j, r ^ 2 * Real.sin (k * r))
            + coreC3 z rho sigma Gt Dt K i j
                * (∫ r in (0 : ℝ)..sigMix sigma i j, r ^ 4 * Real.sin (k * r))
            + coreC4 z rho sigma Gt Dt K i j
                * (∫ r in (0 : ℝ)..sigMix sigma i j, (1 - Real.exp (-z * r)) * Real.sin (k * r))
            + coreC5 z rho sigma Gt Dt K i j
                * (∫ r in (0 : ℝ)..sigMix sigma i j,
                    coshRatio z (sigMix sigma i j) r * Real.sin (k * r))) := by
  have hsij : 0 < sigMix sigma i j := by
    have h1 := hsig i; have h2 := hsig j; unfold sigMix; linarith
  unfold matMSACoreCorr
  exact radial_fourier_coreCorrection _ _ _ _ _ z (sigMix sigma i j) k hsij

end MSAMixture
