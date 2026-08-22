/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAEMixCore
import LeanCode.YukawaOZMix.MSAEMixFactorization

/-!
# MSAEMIX.4 — the matrix `hcore` axiom (equal σ, BH-root gated) and MSAEMIX.1 at equal diameter

Group **MSAEMIX** (`proof_notes_msa_exact.md`).  Numerical partner: `msaemix_hcore_cert.py`,
`msaemix_core_coeffs.py` (parent repo).

`MSAEMixCore.lean` gives the concrete equal-σ core correction `matMSACoreCorr` (derived + verified).
This file supplies the **BH-root gate** and lands the closure-recovery `hcore` as a documented
physics-computation axiom, then closes MSAEMIX.1 at equal diameter.

* `qhatMixC`/`qhatMixR` — the **full** mixture Baxter factor `Q̂_ij(s)` at equal σ (with the Yukawa
  tails `W̃/(s+z)`, `C̃·[e^{−sσ}/(s+z) + σ(1−e^{−sσ})/s]`), complex/real `s`.  Its poly part is the
  `q0_entry_c` Baxter factor; the tails are what `Q0_mat_c` lacks.
* `ftilde` — the symmetric Baxter factor entry `δ_ij − √(ρ_iρ_j)Q̂_ij(s)`; `FtHS`/`FtMSA` its HS and
  MSA instances, `Ft1` the coupling increment.
* `MixBHRoot` — Blum–Høye (29′)/(33′) at equal σ: the physical-solution gate (the matrix analog of
  the scalar `h29`/`h33`).  This is what makes the `hcore` **true** (it is false off-root).
* `matMSAexact6_hcore` — ⭐ the axiom: at a `MixBHRoot`, the Baxter-product coupling increment matches
  `−√(ρ_iρ_j)(𝓕[matMSACoreCorr] + 𝓕[matMSAtail])`.  Certified in `msaemix_core_coeffs.py`
  (all-five closed-form, no fitting, held-out `~1e-12`, binary/ternary/unequal ρ).  A
  *physics-computation* axiom, not a new mathematical assumption.
* `matMSAemix1_equalDiam` — ⭐ MSAEMIX.1 at equal diameter: chains the axiom through the abstract
  `matEMIXfactorization_of_core` (with the symmetric √-weight folded into `cHShat`/`cMSAhat`, `ρ:=1`),
  given the hard-sphere symmetric factorization `hHS`.  The matrix analog of `msaexact1_factorization`.

⚠ Equal σ only; unequal σ has a piecewise core (separate).
-/

open Real
open FMSA.Q0Complex FMSA.MSAExact FMSA.HardSphere FMSA.MatrixQ0

namespace MSAEMix

variable {N : ℕ}

/-! ### The full mixture Baxter factor `Q̂(s)` (equal σ, with Yukawa tails) -/

/-- The full mixture Baxter factor `Q̂_ij(s)` at **equal σ** (`σ_i = σ`, `λ = 0`), complex `s`:
`φ₁(sσ)q'_ij + φ₂(sσ)A_j + W̃_ij/(s+z) + C̃_ij[e^{−sσ}/(s+z) + σ(1−e^{−sσ})/s]`, with
`φ₁(x)=(1−x−e^{−x})/s²`, `φ₂(x)=(1−x+x²/2−e^{−x})/s³` (the `q0_entry_c` Baxter poly plus the tails). -/
noncomputable def qhatMixC (z sigma : ℝ) (qp Wt Ct : Matrix (Fin N) (Fin N) ℝ) (Av : Fin N → ℝ)
    (s : ℂ) (i j : Fin N) : ℂ :=
  (1 - s * sigma - Complex.exp (-(s * sigma))) / s ^ 2 * (qp i j : ℂ)
    + (1 - s * sigma + (s * sigma) ^ 2 / 2 - Complex.exp (-(s * sigma))) / s ^ 3 * (Av j : ℂ)
    + (Wt i j : ℂ) / (s + z)
    + (Ct i j : ℂ) * (Complex.exp (-(s * sigma)) / (s + z)
        + sigma * (1 - Complex.exp (-(s * sigma))) / s)

/-- The full mixture Baxter factor at **real** `s` (for the (29′)/(33′) residual gate). -/
noncomputable def qhatMixR (z sigma : ℝ) (qp Wt Ct : Matrix (Fin N) (Fin N) ℝ) (Av : Fin N → ℝ)
    (s : ℝ) (i j : Fin N) : ℝ :=
  (1 - s * sigma - Real.exp (-(s * sigma))) / s ^ 2 * qp i j
    + (1 - s * sigma + (s * sigma) ^ 2 / 2 - Real.exp (-(s * sigma))) / s ^ 3 * Av j
    + Wt i j / (s + z)
    + Ct i j * (Real.exp (-(s * sigma)) / (s + z) + sigma * (1 - Real.exp (-(s * sigma))) / s)

/-! ### The MSA and hard-sphere amplitude bundles -/

/-- The MSA `q′` amplitude matrix. -/
noncomputable def qpMat (z : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ := fun i j => qpMSA z rho sigma Gt Dt i j

/-- The MSA `A` amplitude vector (column). -/
noncomputable def AVec (z : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ) :
    Fin N → ℝ := fun j => AMSA z rho sigma Gt Dt j

/-- The HS `q^{0′}` amplitude matrix. -/
noncomputable def qp0Mat (rho sigma : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => Q0phys rho sigma i j

/-- The HS `A⁰` amplitude vector. -/
noncomputable def A0Vec (rho sigma : Fin N → ℝ) : Fin N → ℝ := fun j => Qppphys rho sigma j j

/-! ### The symmetric Baxter factor and its HS / MSA / increment instances -/

/-- The symmetric Baxter factor entry `F̃_ij(Q) = δ_ij − √(ρ_iρ_j) Q_ij`. -/
noncomputable def ftilde (rho : Fin N → ℝ) (Q : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (if i = j then (1 : ℂ) else 0) - (Real.sqrt (rho i * rho j) : ℂ) * Q i j

/-- The hard-sphere symmetric factor at `s` (coupling-`0`: `W̃ = C̃ = 0`); `sig` is the common σ. -/
noncomputable def FtHS (z sig : ℝ) (rho sigma : Fin N → ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ftilde rho (fun i j => qhatMixC z sig (qp0Mat rho sigma) 0 0 (A0Vec rho sigma) s i j)

/-- The full MSA symmetric factor at `s`; `sig` is the common σ. -/
noncomputable def FtMSA (z sig : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ftilde rho (fun i j => qhatMixC z sig (qpMat z rho sigma Gt Dt)
    (Wt z rho Gt Dt) (Ct z rho sigma Gt Dt) (AVec z rho sigma Gt Dt) s i j)

/-- The coupling increment `Q₁ = F̃_MSA − F̃_HS`. -/
noncomputable def Ft1 (z sig : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  FtMSA z sig rho sigma Gt Dt s - FtHS z sig rho sigma s

/-! ### The Blum–Høye BH-root gate (equal σ) -/

/-- **The mixture MSA Blum–Høye root** (equal σ = `sig`): (29′) `Σ_l Dt_il(δ_lj − ρ_l Q̂_jl(z)) =
2πK_ij/z` and (33′) `2π Σ_l Gt_il(δ_lj − ρ_l Q̂_lj(z)) = (A_j + z q'_ij + ½z² C̃_ij)/z²`, with `Q̂` the
full MSA Baxter factor at `s = z` (`qhatMixR`).  The physical-solution gate — the matrix analog of the
scalar `h29`/`h33`; the `hcore` identity holds **only** at such a root. -/
def MixBHRoot (z sig : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ i j, ∑ l, Dt i l * ((if l = j then (1 : ℝ) else 0)
      - rho l * qhatMixR z sig (qpMat z rho sigma Gt Dt) (Wt z rho Gt Dt)
          (Ct z rho sigma Gt Dt) (AVec z rho sigma Gt Dt) z j l)
    = 2 * Real.pi * K i j / z)
  ∧ (∀ i j, 2 * Real.pi * ∑ l, Gt i l * ((if l = j then (1 : ℝ) else 0)
      - rho l * qhatMixR z sig (qpMat z rho sigma Gt Dt) (Wt z rho Gt Dt)
          (Ct z rho sigma Gt Dt) (AVec z rho sigma Gt Dt) z l j)
    = (AVec z rho sigma Gt Dt j + z * qpMat z rho sigma Gt Dt i j
        + z ^ 2 * Ct z rho sigma Gt Dt i j / 2) / z ^ 2)

/-! ### The closure-recovery axiom and MSAEMIX.1 at equal diameter -/

/-- ⭐ **MSAEMIX.4 (axiom).**  At the equal-σ mixture MSA Blum–Høye root (`MixBHRoot`), the Baxter
product's coupling increment `(F̃₀ F̃₁ⁿᵀ + F̃₁ F̃₀ⁿᵀ + F̃₁ F̃₁ⁿᵀ)ᵢⱼ` equals
`−√(ρ_iρ_j)(𝓕[matMSACoreCorr]ᵢⱼ + 𝓕[matMSAtail]ᵢⱼ)` — the matrix closure-recovery ring, the matrix
analog of `msaexact6_hcore`.

**Certified** in `msaemix_core_coeffs.py` (parent repo): all five equal-σ core coefficients
`c₁..c₅` are closed forms (derived from the Baxter real-space convolution) matching the exact
factor-product extraction with held-out residual `~1e-12` (binary/ternary, unequal ρ, `z∈[1.5,2.6]`),
and reducing to the scalar `msaCoreCorr` at `N = 1`.  A *physics-computation* axiom (a specific
verified polynomial identity gated by the physical root), not a new mathematical assumption. -/
axiom matMSAexact6_hcore (z sig : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (k : ℝ) (hσ : ∀ i, sigma i = sig) (hroot : MixBHRoot z sig rho sigma Gt Dt K) (i j : Fin N) :
    (FtHS z sig rho sigma (Complex.I * k)
        * (Ft1 z sig rho sigma Gt Dt (-(Complex.I * k))).transpose) i j
      + (Ft1 z sig rho sigma Gt Dt (Complex.I * k)
          * (FtHS z sig rho sigma (-(Complex.I * k))).transpose) i j
      + (Ft1 z sig rho sigma Gt Dt (Complex.I * k)
          * (Ft1 z sig rho sigma Gt Dt (-(Complex.I * k))).transpose) i j
      = -(Real.sqrt (rho i * rho j) : ℂ)
          * ((radial_fourier (matMSACoreCorr z rho sigma Gt Dt K i j) k : ℂ)
            + (radial_fourier (matMSAtail K z sigma i j) k : ℂ))

/-- ⭐ **MSAEMIX.1 at equal diameter.**  Given the hard-sphere symmetric factorization `hHS`
(`(F̃₀ F̃₀ⁿᵀ)ᵢⱼ = δᵢⱼ − √(ρ_iρ_j)ĉ_HS,ij`) and the closure-recovery axiom at a `MixBHRoot`, the full
MSA symmetric factorization holds:
`((F̃₀+F̃₁)(F̃₀ⁿ+F̃₁ⁿ)ᵀ)ᵢⱼ = δᵢⱼ − √(ρ_iρ_j)(ĉ_HS,ij + 𝓕[c_core]ᵢⱼ + 𝓕[c_tail]ᵢⱼ)`
— the physical MSA mixture direct correlation function.  Pure algebra on top of the abstract
`matEMIXfactorization_of_core` (symmetric √-weight folded into the DCFs, `ρ := 1`), the matrix analog
of `msaexact1_factorization`. -/
theorem matMSAemix1_equalDiam (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (k : ℝ) (hσ : ∀ i, sigma i = sig) (hroot : MixBHRoot z sig rho sigma Gt Dt K)
    (cHShat : Fin N → Fin N → ℂ)
    (hHS : ∀ i j, (FtHS z sig rho sigma (Complex.I * k)
        * (FtHS z sig rho sigma (-(Complex.I * k))).transpose) i j
      = (if i = j then (1 : ℂ) else 0) - cHShat i j) (i j : Fin N) :
    ((FtHS z sig rho sigma (Complex.I * k) + Ft1 z sig rho sigma Gt Dt (Complex.I * k))
        * (FtHS z sig rho sigma (-(Complex.I * k))
            + Ft1 z sig rho sigma Gt Dt (-(Complex.I * k))).transpose) i j
      = (if i = j then (1 : ℂ) else 0)
        - (cHShat i j + (Real.sqrt (rho i * rho j) : ℂ)
            * ((radial_fourier (matMSACoreCorr z rho sigma Gt Dt K i j) k : ℂ)
              + (radial_fourier (matMSAtail K z sigma i j) k : ℂ))) := by
  have h := matEMIXfactorization_of_core (FtHS z sig rho sigma (Complex.I * k))
    (Ft1 z sig rho sigma Gt Dt (Complex.I * k)) (FtHS z sig rho sigma (-(Complex.I * k)))
    (Ft1 z sig rho sigma Gt Dt (-(Complex.I * k))) 1 cHShat
    (fun i j => cHShat i j + (Real.sqrt (rho i * rho j) : ℂ)
      * ((radial_fourier (matMSACoreCorr z rho sigma Gt Dt K i j) k : ℂ)
        + (radial_fourier (matMSAtail K z sigma i j) k : ℂ)))
    (by intro i j; simpa using hHS i j)
    (by
      intro i j
      have hc := matMSAexact6_hcore z sig rho sigma Gt Dt K k hσ hroot i j
      simpa using hc) i j
  simpa using h

end MSAEMix
