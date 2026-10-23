/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAMixtureBHRoot

/-!
# Proved equal-diameter matrix Fourier certificate

The former SymPy-supported residual is now a kernel-checked theorem, derived
from the proved matrix hcore identity and the scalar Fourier formulas. Both
interfaces preserve their original DCF and closed trigonometric expressions.
The explicit domain is a supplied equal-diameter BH root, positive z and
sig, nonzero k, nonnegative densities, positive vacMix, and symmetric K.
No symbolic-computation axiom or independent compatibility certificate is
assumed. This module is imported and guarded by the default ExactMSA track.
This structural Fourier identity does not certify g nonnegativity,
thermodynamic route consistency, or Maxwell/binodal physical accuracy.
-/

open MSAMixture Real FMSA.HardSphere FMSA.ExactMSA

namespace FMSA.ExactMSA.MatEqualDiamCertificate

variable {N : ℕ}

/-- The original closed cos/sin/exp residual, proved from the actual BH root.
SymPy is no longer a proof premise. -/
theorem matExactMSAEqualDiam_kspace_residual (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (k : ℝ) (hk : k ≠ 0) (hz : 0 < z) (hsig1 : 0 < sig)
    (hσ : ∀ i, sigma i = sig) (hroot : MixBHRoot z sig rho sigma Gt Dt K)
    (hrho : ∀ l, 0 ≤ rho l) (hvac : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hK : ∀ a b, K a b = K b a) (i j : Fin N) :
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
                  / (z ^ 2 + k ^ 2)) : ℝ) : ℂ)) := by
  have h := MSAMixture.matExactMSAEqualDiam_hcore z sig rho sigma Gt Dt K k
    hσ hroot hz hk hsig1 hrho hvac hK i j
  have hsig : ∀ i, 0 < sigma i := fun i => by rw [hσ i]; exact hsig1
  have hzk : z ^ 2 + k ^ 2 ≠ 0 := by positivity
  rw [radial_fourier_matMSACoreCorr z rho sigma Gt Dt K hsig k i j,
      radial_fourier_matMSAtail K hz sigma hsig k i j,
      psi1_formula hk (sigMix sigma i j), psi2_formula hk (sigMix sigma i j),
      psi4_formula hk (sigMix sigma i j),
      one_sub_exp_sin_integral hzk hk, coshRatio_sin_integral hzk hk] at h
  exact h

/-- Compatibility interface: the original radial Fourier identity follows
from the proved closed residual on the same explicit physical domain. -/
theorem matExactMSAEqualDiam_hcore_of_residual (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Gt Dt K : Matrix (Fin N) (Fin N) ℝ) (k : ℝ) (hk : k ≠ 0) (hz : 0 < z) (hsig1 : 0 < sig)
    (hσ : ∀ i, sigma i = sig) (hroot : MixBHRoot z sig rho sigma Gt Dt K)
    (hrho : ∀ l, 0 ≤ rho l) (hvac : 0 < FMSA.MatrixQ0.vacMix rho sigma)
    (hK : ∀ a b, K a b = K b a) (i j : Fin N) :
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
  exact matExactMSAEqualDiam_kspace_residual z sig rho sigma Gt Dt K k hk hz hsig1 hσ hroot hrho hvac hK i j

end FMSA.ExactMSA.MatEqualDiamCertificate
