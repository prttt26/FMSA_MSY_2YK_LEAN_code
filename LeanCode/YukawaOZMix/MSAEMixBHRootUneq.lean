/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAEMixBHRoot
import LeanCode.YukawaOZMix.MSAEMixConcrete
import LeanCode.YukawaOZMix.MSAEMixFactorization
import LeanCode.YukawaOZMix.MSAEMixCoreUneq

/-!
# MSAEMIX.4 — the UNEQUAL-σ matrix `hcore` axiom (BH-root gated) and MSAEMIX.1 at unequal diameter

The unequal-σ analog of `MSAEMixBHRoot.lean`.  The unequal-σ mixture Baxter factor `qhatMixCuneq` is
the Laplace transform of the real-space `Q_ij` (poly on `[λ_ij, σ_ij]` with the `λ_ij=(σ_j−σ_i)/2`
support shift and row width `σ_i`, plus the Yukawa tail); at equal σ (`σ_i=σ_j`) it collapses to the
equal-σ `qhatMixC` (`λ_ij=0`, common `σ`).  With the unequal-σ HS / MSA / increment factors, the
BH-root gate `MixBHRootUneq`, and the closure-recovery axiom `matMSAexactUnequalDiam_hcore` (whose
core is the exactly-derived, validated `MSAEMixCoreUneq.matCoreUneq`), MSAEMIX.1 closes at unequal
diameter through the abstract `matEMIXfactorization_of_core` — mirroring `matMSAemix1_equalDiam`.
-/

open Real MeasureTheory
open FMSA.Q0Complex FMSA.MSAExact FMSA.HardSphere FMSA.MatrixQ0 FMSA.MixtureOzStar

namespace MSAEMix

open scoped BigOperators

variable {N : ℕ}

/-! ### The unequal-σ mixture Baxter factor -/

/-- The unequal-σ mixture Baxter factor entry `∫₀^∞ Q_ij(r) e^{−sr} dr`, `λ_ij=(σ_j−σ_i)/2`,
`σ_ij=(σ_i+σ_j)/2`, row width `a=σ_i`.  Reduces to `qhatMixC z σ …` at equal σ. -/
noncomputable def qhatMixCuneq (z : ℝ) (σ : Fin N → ℝ) (qp Wt Ct : Matrix (Fin N) (Fin N) ℝ)
    (Av : Fin N → ℝ) (s : ℂ) (i j : Fin N) : ℂ :=
  let lam : ℂ := (((σ j - σ i) / 2 : ℝ) : ℂ)
  let a : ℂ := ((σ i : ℝ) : ℂ)
  let sij : ℂ := (((σ i + σ j) / 2 : ℝ) : ℂ)
  Complex.exp (-(s * lam)) * ((1 - s * a - Complex.exp (-(s * a))) / s ^ 2 * (qp i j : ℂ)
      + (1 - s * a + (s * a) ^ 2 / 2 - Complex.exp (-(s * a))) / s ^ 3 * (Av j : ℂ)
      + (Wt i j : ℂ) / (s + z)
      + (Ct i j : ℂ) * ((1 - Complex.exp (-(s * a))) / s))
    + (Ct i j : ℂ) * (Complex.exp (-(s * sij)) / (s + z))

/-- Real-`s` version of `qhatMixCuneq` (for the (29′)/(33′) residual gate). -/
noncomputable def qhatMixRuneq (z : ℝ) (σ : Fin N → ℝ) (qp Wt Ct : Matrix (Fin N) (Fin N) ℝ)
    (Av : Fin N → ℝ) (s : ℝ) (i j : Fin N) : ℝ :=
  let lam := (σ j - σ i) / 2
  let a := σ i
  let sij := (σ i + σ j) / 2
  Real.exp (-(s * lam)) * ((1 - s * a - Real.exp (-(s * a))) / s ^ 2 * qp i j
      + (1 - s * a + (s * a) ^ 2 / 2 - Real.exp (-(s * a))) / s ^ 3 * Av j
      + Wt i j / (s + z)
      + Ct i j * ((1 - Real.exp (-(s * a))) / s))
    + Ct i j * (Real.exp (-(s * sij)) / (s + z))

/-! ### Unequal-σ HS / MSA / increment symmetric factors -/

/-- Unequal-σ hard-sphere symmetric factor (coupling 0: `W̃ = C̃ = 0`). -/
noncomputable def FtHSuneq (z : ℝ) (rho σ : Fin N → ℝ) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ftilde rho (fun i j => qhatMixCuneq z σ (qp0Mat rho σ) 0 0 (A0Vec rho σ) s i j)

/-- Unequal-σ full MSA symmetric factor. -/
noncomputable def FtMSAuneq (z : ℝ) (rho σ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ftilde rho (fun i j => qhatMixCuneq z σ (qpMat z rho σ Gt Dt) (Wt z rho Gt Dt)
    (Ct z rho σ Gt Dt) (AVec z rho σ Gt Dt) s i j)

/-- Unequal-σ coupling increment `Q₁ = F̃_MSA − F̃_HS`. -/
noncomputable def Ft1uneq (z : ℝ) (rho σ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (s : ℂ) : Matrix (Fin N) (Fin N) ℂ := FtMSAuneq z rho σ Gt Dt s - FtHSuneq z rho σ s

/-- The unequal-σ **core-DCF correction** = `matCoreUneq` at the MSA amplitudes minus at the HS
amplitudes (`qp0, A0, Wt=Ct=0`).  Kernels are σ_l-free (shared by MSA and HS) so this is exactly the
MSA−HS increment core (the exp part has no HS piece).  Unequal-σ analog of `matMSACoreCorr`. -/
noncomputable def matCoreCorrUneq (z : ℝ) (rho σ : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) : ℝ → ℝ := fun r =>
  MSAEMixCoreUneq.matCoreUneq z rho σ (AVec z rho σ Gt Dt) (qpMat z rho σ Gt Dt)
      (Wt z rho Gt Dt) (Ct z rho σ Gt Dt) i j r
    - MSAEMixCoreUneq.matCoreUneq z rho σ (A0Vec rho σ) (qp0Mat rho σ) 0 0 i j r

/-! ### The unequal-σ BH-root gate -/

/-- The unequal-σ mixture MSA Blum–Høye root: (29′)/(33′) with the unequal-σ real Baxter factor
`qhatMixRuneq`.  The physical-solution gate (no `∀ i, σ i = sig` constraint). -/
def MixBHRootUneq (z : ℝ) (rho σ : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ i j, ∑ l, Dt i l * ((if l = j then (1 : ℝ) else 0)
      - rho l * qhatMixRuneq z σ (qpMat z rho σ Gt Dt) (Wt z rho Gt Dt) (Ct z rho σ Gt Dt)
          (AVec z rho σ Gt Dt) z j l)
    = 2 * Real.pi * K i j / z)
  ∧ (∀ i j, 2 * Real.pi * ∑ l, Gt i l * ((if l = j then (1 : ℝ) else 0)
      - rho l * qhatMixRuneq z σ (qpMat z rho σ Gt Dt) (Wt z rho Gt Dt) (Ct z rho σ Gt Dt)
          (AVec z rho σ Gt Dt) z l j)
    = (AVec z rho σ Gt Dt j + z * qpMat z rho σ Gt Dt i j
        + z ^ 2 * Ct z rho σ Gt Dt i j / 2) / z ^ 2)

/-! ### The unequal-σ closure-recovery axiom and MSAEMIX.1 at unequal diameter -/

/-- ⭐ **MSAEMIX.4 (axiom, unequal σ).**  At the unequal-σ MSA Blum–Høye root (`MixBHRootUneq`) the
Baxter product's coupling increment equals `−√(ρ_iρ_j)(𝓕[matCoreCorrUneq]ᵢⱼ + 𝓕[matMSAtail]ᵢⱼ)`
(the MSA−HS core increment).

**Certified** (`symbolic_{outer,inner}.py`, `verify_{outer,inner}.py`, parent repo): every per-piece
kernel of `matCoreUneq` is the EXACT closed form from the case-split-free symbolic-σ Baxter
convolution (σ_l-independent), reproducing the numerical convolution to `1e-14` on both pieces.  A
*physics-computation* axiom at the physical root (unequal-σ analog of
`matMSAexactEqualDiam_hcore`). -/
axiom matMSAexactUnequalDiam_hcore (z : ℝ) (rho σ : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (k : ℝ) (hroot : MixBHRootUneq z rho σ Gt Dt K) (i j : Fin N) :
    (FtHSuneq z rho σ (Complex.I * k) * (Ft1uneq z rho σ Gt Dt (-(Complex.I * k))).transpose) i j
      + (Ft1uneq z rho σ Gt Dt (Complex.I * k)
          * (FtHSuneq z rho σ (-(Complex.I * k))).transpose) i j
      + (Ft1uneq z rho σ Gt Dt (Complex.I * k)
          * (Ft1uneq z rho σ Gt Dt (-(Complex.I * k))).transpose) i j
      = -(Real.sqrt (rho i * rho j) : ℂ)
          * ((radial_fourier (matCoreCorrUneq z rho σ Gt Dt i j) k : ℂ)
            + (radial_fourier (matMSAtail K z σ i j) k : ℂ))

/-- ⭐ **MSAEMIX.1 at unequal diameter.**  Given the unequal-σ hard-sphere symmetric factorization
`hHS` and the closure-recovery axiom at a `MixBHRootUneq`, the full MSA factorization holds:
`((F̃₀+F̃₁)(F̃₀ⁿ+F̃₁ⁿ)ᵀ)ᵢⱼ = δᵢⱼ − √(ρ_iρ_j)(ĉ_HS,ij + 𝓕[c_core]ᵢⱼ + 𝓕[c_tail]ᵢⱼ)`, the physical
unequal-σ MSA mixture DCF.  Pure algebra on the abstract `matEMIXfactorization_of_core` (√-weight
folded into the DCFs, `ρ := 1`), mirroring `matMSAemix1_equalDiam`. -/
theorem matMSAemix1_unequalDiam (z : ℝ) (rho σ : Fin N → ℝ) (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (k : ℝ) (hroot : MixBHRootUneq z rho σ Gt Dt K) (cHShat : Fin N → Fin N → ℂ)
    (hHS : ∀ i j, (FtHSuneq z rho σ (Complex.I * k)
        * (FtHSuneq z rho σ (-(Complex.I * k))).transpose) i j
      = (if i = j then (1 : ℂ) else 0) - cHShat i j) (i j : Fin N) :
    ((FtHSuneq z rho σ (Complex.I * k) + Ft1uneq z rho σ Gt Dt (Complex.I * k))
        * (FtHSuneq z rho σ (-(Complex.I * k))
            + Ft1uneq z rho σ Gt Dt (-(Complex.I * k))).transpose) i j
      = (if i = j then (1 : ℂ) else 0)
        - (cHShat i j + (Real.sqrt (rho i * rho j) : ℂ)
            * ((radial_fourier (matCoreCorrUneq z rho σ Gt Dt i j) k : ℂ)
              + (radial_fourier (matMSAtail K z σ i j) k : ℂ))) := by
  have h := matEMIXfactorization_of_core (FtHSuneq z rho σ (Complex.I * k))
    (Ft1uneq z rho σ Gt Dt (Complex.I * k)) (FtHSuneq z rho σ (-(Complex.I * k)))
    (Ft1uneq z rho σ Gt Dt (-(Complex.I * k))) 1 cHShat
    (fun i j => cHShat i j + (Real.sqrt (rho i * rho j) : ℂ)
      * ((radial_fourier (matCoreCorrUneq z rho σ Gt Dt i j) k : ℂ)
        + (radial_fourier (matMSAtail K z σ i j) k : ℂ)))
    (by intro i j; simpa using hHS i j)
    (by
      intro i j
      have hc := matMSAexactUnequalDiam_hcore z rho σ Gt Dt K k hroot i j
      simpa using hc) i j
  simpa using h

end MSAEMix
