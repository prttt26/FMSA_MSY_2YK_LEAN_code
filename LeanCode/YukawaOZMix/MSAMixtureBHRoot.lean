/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAMixtureBHRootDefs
import LeanCode.YukawaOZMix.MSAMixtureEqualCoreBridge

/-!
# Kernel-checked equal-diameter matrix closure recovery

The original five-coefficient DCF is recovered from the actual Baxter
convolution: the origin constraint follows from automatic Wronskian
reciprocity, and species contractions of both BH equations identify the
exponential coefficients. The faithful unequal-diameter Fourier theorem
then proves the old hcore interface. Definitions live independently in
MSAMixtureBHRootDefs to avoid a cycle through the nonlinear construction.

The former SymPy-supported axiom is retired. The public interfaces expose
positive z and sig, nonzero k, nonnegative densities, positive vacMix,
symmetric K and the actual root. No g positivity or thermodynamic
consistency statement is implied.
-/

open Real MeasureTheory
open FMSA.Q0Complex FMSA.ExactMSA FMSA.HardSphere FMSA.MatrixQ0 FMSA.MixtureOzStar

namespace MSAMixture

variable {N : ℕ}

/-! ### The closure-recovery theorem and MSAEMIX.1 at equal diameter -/

/-- Original equal-diameter coupling increment, now a proved theorem.
The old five-coefficient core and Yukawa tail are unchanged. -/
theorem matExactMSAEqualDiam_hcore (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (k : ℝ) (hσ : ∀ i, sigma i = sig) (hroot : MixBHRoot z sig rho sigma Gt Dt K)
    (hz : 0 < z) (hk : k ≠ 0) (hsig : 0 < sig) (hrho : ∀ l, 0 ≤ rho l)
    (hvac : 0 < vacMix rho sigma) (hK : ∀ a b, K a b = K b a) (i j : Fin N) :
    (FtHS z sig rho sigma (Complex.I * k)
        * (Ft1 z sig rho sigma Gt Dt (-(Complex.I * k))).transpose) i j
      + (Ft1 z sig rho sigma Gt Dt (Complex.I * k)
          * (FtHS z sig rho sigma (-(Complex.I * k))).transpose) i j
      + (Ft1 z sig rho sigma Gt Dt (Complex.I * k)
          * (Ft1 z sig rho sigma Gt Dt (-(Complex.I * k))).transpose) i j
      = -(Real.sqrt (rho i * rho j) : ℂ)
          * ((radial_fourier (matMSACoreCorr z rho sigma Gt Dt K i j) k : ℂ)
            + (radial_fourier (matMSAtail K z sigma i j) k : ℂ)) := by
  have hsigma : ∀ l, 0 < sigma l := fun l => by rw [hσ l]; exact hsig
  have h := FMSA.ExactMSA.MultiTailMixture.legacyUnequal_hcore z hz rho sigma Gt Dt K
    hsigma hrho hvac (FMSA.ExactMSA.MixLeg3.MixBHRootUneq_of_MixBHRoot
      z sig rho sigma Gt Dt K hσ hroot) hK k hk i j
  rw [FMSA.ExactMSA.MultiTailMixture.radial_fourier_congr_positive_ae _ _
    (FMSA.ExactMSA.MultiTailMixture.legacyEqual_core_ae z sig hz rho sigma Gt Dt K
      hsig hσ hrho hvac hroot hK i j) k] at h
  simpa only [FMSA.ExactMSA.MixLeg3.FtHSuneq_eq_FtHS z sig rho sigma hσ,
    FMSA.ExactMSA.MixLeg3.Ft1uneq_eq_Ft1 z sig rho sigma Gt Dt hσ] using h

/-- ⭐ **MSAEMIX.1 at equal diameter.**  Given the hard-sphere symmetric factorization `hHS`
(`(F̃₀ F̃₀ⁿᵀ)ᵢⱼ = δᵢⱼ − √(ρ_iρ_j)ĉ_HS,ij`) and the closure-recovery theorem at a `MixBHRoot`, the full
MSA symmetric factorization holds:
`((F̃₀+F̃₁)(F̃₀ⁿ+F̃₁ⁿ)ᵀ)ᵢⱼ = δᵢⱼ − √(ρ_iρ_j)(ĉ_HS,ij + 𝓕[c_core]ᵢⱼ + 𝓕[c_tail]ᵢⱼ)`
— the physical MSA mixture direct correlation function.  Pure algebra on top of the abstract
`matMixtureFactorization_of_core` (symmetric √-weight folded into the DCFs, `ρ := 1`), the matrix analog
of `exactMSA_factorization`. -/
theorem matMSAmixture_equalDiam (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ)
    (k : ℝ) (hσ : ∀ i, sigma i = sig) (hroot : MixBHRoot z sig rho sigma Gt Dt K)
    (hz : 0 < z) (hk : k ≠ 0) (hsig : 0 < sig) (hrho : ∀ l, 0 ≤ rho l)
    (hvac : 0 < vacMix rho sigma) (hK : ∀ a b, K a b = K b a)
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
  have h := matMixtureFactorization_of_core (FtHS z sig rho sigma (Complex.I * k))
    (Ft1 z sig rho sigma Gt Dt (Complex.I * k)) (FtHS z sig rho sigma (-(Complex.I * k)))
    (Ft1 z sig rho sigma Gt Dt (-(Complex.I * k))) 1 cHShat
    (fun i j => cHShat i j + (Real.sqrt (rho i * rho j) : ℂ)
      * ((radial_fourier (matMSACoreCorr z rho sigma Gt Dt K i j) k : ℂ)
        + (radial_fourier (matMSAtail K z sigma i j) k : ℂ)))
    (by intro i j; simpa using hHS i j)
    (by
      intro i j
      have hc := matExactMSAEqualDiam_hcore z sig rho sigma Gt Dt K k hσ hroot hz hk hsig hrho hvac hK i j
      simpa using hc) i j
  simpa using h

/-- ⭐⭐ **MSAEMIX.1 at equal diameter, `hHS` DISCHARGED via the HS-mixture Wiener–Hopf.**  Instead
of assuming the hard-sphere symmetric factorization `hHS`, this takes the *standard* HS-mixture WH
atoms — the Baxter core factorization `hKDEF` (`MatBaxterFactorization`), the shell-cosine bridge
`hbridge`, and the pure-`q` Fourier identity `hWH` (`MatBaxterFourierWH`) for the HS factor `F̃₀` —
and produces the full MSA factorization through `matMixtureFactorization_of_baxterFourierWH` (which
discharges the HS part via `matSF_of_baxterFourierWH`).  So the HS factorization is no longer an
ad-hoc hypothesis but the same shared WH machinery the mixture-RDF/OZ★ work rests on (symmetric
√-weight, `ρ := 1`, `Φ` the √-weighted HS DCF).  The `hcore` fed to it is exactly
`matExactMSAEqualDiam_hcore`. -/
theorem matMSAmixture_equalDiam_WH (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (k : ℝ)
    (cHSker qbax PhiHS : Matrix (Fin N) (Fin N) (ℝ → ℝ)) (hsig1 : 0 < sig)
    (hσ : ∀ i, sigma i = sig) (hroot : MixBHRoot z sig rho sigma Gt Dt K)
    (hz : 0 < z) (hk : k ≠ 0) (hrho : ∀ l, 0 ≤ rho l)
    (hvac : 0 < vacMix rho sigma) (hK : ∀ a b, K a b = K b a)
    (hKDEF : MatBaxterFactorization cHSker qbax 1 sig)
    (hbridge : ∀ i j,
      2 * ∫ v in (0 : ℝ)..sig, cHSker i j v * Real.cos (k * v) = radial_fourier (PhiHS i j) k)
    (hWH : MatBaxterFourierWH (FtHS z sig rho sigma (Complex.I * k))
      (FtHS z sig rho sigma (-(Complex.I * k))) qbax sig k) (i j : Fin N) :
    ((FtHS z sig rho sigma (Complex.I * k) + Ft1 z sig rho sigma Gt Dt (Complex.I * k))
        * (FtHS z sig rho sigma (-(Complex.I * k))
            + Ft1 z sig rho sigma Gt Dt (-(Complex.I * k))).transpose) i j
      = (if i = j then (1 : ℂ) else 0)
        - ((radial_fourier (PhiHS i j) k : ℂ) + (Real.sqrt (rho i * rho j) : ℂ)
            * ((radial_fourier (matMSACoreCorr z rho sigma Gt Dt K i j) k : ℂ)
              + (radial_fourier (matMSAtail K z sigma i j) k : ℂ))) := by
  have h := matMixtureFactorization_of_baxterFourierWH (FtHS z sig rho sigma (Complex.I * k))
    (FtHS z sig rho sigma (-(Complex.I * k))) (Ft1 z sig rho sigma Gt Dt (Complex.I * k))
    (Ft1 z sig rho sigma Gt Dt (-(Complex.I * k))) cHSker qbax PhiHS 1 sig k hsig1 hKDEF hbridge hWH
    (fun i j => (radial_fourier (PhiHS i j) k : ℂ) + (Real.sqrt (rho i * rho j) : ℂ)
      * ((radial_fourier (matMSACoreCorr z rho sigma Gt Dt K i j) k : ℂ)
        + (radial_fourier (matMSAtail K z sigma i j) k : ℂ)))
    (by
      intro i j
      have hc := matExactMSAEqualDiam_hcore z sig rho sigma Gt Dt K k hσ hroot hz hk hsig1 hrho hvac hK i j
      simp only [Complex.ofReal_one]
      linear_combination hc) i j
  simpa using h

end MSAMixture
