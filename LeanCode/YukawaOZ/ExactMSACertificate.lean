/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZ.MSAFullFactorization

/-!
# MSAEXACT.6 — compatibility certificate for proved scalar closure recovery

The original pure k-space residual and its Fourier bridge are now theorems.
`MSAFullFactorization.exactMSA_hcore` imports the fully kernel-checked scalar
proof chain. This optional target preserves the earlier certificate API with
explicit `z > 0` and `xi ≠ 1` regularity assumptions. The matrix certificate
is separate and is not discharged by these scalar results.
-/

open Real MeasureTheory

namespace FMSA.ExactMSA.Certificate

open FMSA.HardSphere FMSA.ExactMSA

variable (xi z : ℝ)

/-- The original closed k-space identity, proved from the checked rational
residual rather than assumed as a polynomial axiom. -/
theorem exactMSA_kspace_residual (Dt G K : ℝ) {k : ℝ} (hk : k ≠ 0) (hz : 0 < z)
    (hzk : z ^ 2 + k ^ 2 ≠ 0) (hvac : 1 - xi ≠ 0)
    (h29 : Dt * bhF xi z (Dt, G) - 2 * π * K / z = 0)
    (h33 : 2 * π * (G * bhF xi z (Dt, G)) - bhP xi z (Dt, G) = 0) :
    rhoOf xi *
        (4 * π / k *
            (-((msaA xi z Dt G / (2 * π)) ^ 2 - (1 + 2 * xi) ^ 2 / (1 - xi) ^ 4) *
                    ((sin k - k * cos k) / k ^ 2) +
                  -((msaQp xi z Dt G + z * gam xi z G * Dt) / (2 * π) - K -
                              (msaA xi z Dt G / (2 * π)) ^ 2 -
                            xi * (msaA xi z Dt G / (2 * π)) ^ 2 / 2 -
                          24 * xi * K * G * (1 - rexp (-z)) / z -
                        (24 * xi * K * G) ^ 2 * (1 - rexp (-z)) ^ 2 / (4 * K * z ^ 2) -
                      -6 * xi * (1 + xi / 2) ^ 2 / (1 - xi) ^ 4) *
                    ((2 / k ^ 3 - 1 / k) * cos k + 2 / k ^ 2 * sin k - 2 / k ^ 3) +
                -(xi * ((msaA xi z Dt G / (2 * π)) ^ 2 - (1 + 2 * xi) ^ 2 / (1 - xi) ^ 4) / 2) *
                  ((-24 / k ^ 5 + 12 / k ^ 3 - 1 / k) * cos k +
                      (-24 / k ^ 4 + 4 / k ^ 2) * sin k + 24 / k ^ 5) +
              -(24 * xi * K * G / z) *
                ((1 - cos k) / k -
                  (k - rexp (-z) * (k * cos k + z * sin k)) / (z ^ 2 + k ^ 2)) +
            -((24 * xi * K * G) ^ 2 / (2 * K * z ^ 2)) *
              (1 / 2 * rexp (-z) *
                    ((k - rexp z * (k * cos k - z * sin k)) / (z ^ 2 + k ^ 2)) +
                  1 / 2 * rexp (-z) *
                    ((k - rexp (-z) * (k * cos k + z * sin k)) / (z ^ 2 + k ^ 2)) -
                rexp (-z) * ((1 - cos k) / k))) +
          4 * π * K / k * ((k * cos k + z * sin k) / (z ^ 2 + k ^ 2))) =
      2 * Dt * ((1 - msaQre xi z 0 G k) * msaRez xi z G k -
            msaQim xi z 0 G k * msaImz xi z G k) -
        Dt ^ 2 * (msaRez xi z G k ^ 2 + msaImz xi z G k ^ 2) := by
  exact sub_eq_zero.mp (RationalBridge.deltaActual_zero xi z k Dt G K hvac hz.ne' hk h29 h33)

/-- Compatibility form of the proved scalar Fourier closure identity. -/
theorem exactMSA_hcore_of_residual (Dt G K : ℝ) {k : ℝ} (hk : k ≠ 0) (hz : 0 < z)
    (hvac : 1 - xi ≠ 0)
    (h29 : Dt * bhF xi z (Dt, G) - 2 * π * K / z = 0)
    (h33 : 2 * π * (G * bhF xi z (Dt, G)) - bhP xi z (Dt, G) = 0) :
    rhoOf xi * (radial_fourier (msaCoreCorr xi z Dt G K) k
        + radial_fourier (cMSAtail K z 1) k)
      = 2 * Dt * ((1 - msaQre xi z 0 G k) * msaRez xi z G k
          - msaQim xi z 0 G k * msaImz xi z G k)
        - Dt ^ 2 * (msaRez xi z G k ^ 2 + msaImz xi z G k ^ 2) :=
  exactMSA_hcore xi z Dt G K hk hz hvac h29 h33

/-- info: 'FMSA.ExactMSA.Certificate.exactMSA_kspace_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exactMSA_kspace_residual

/-- info: 'FMSA.ExactMSA.Certificate.exactMSA_hcore_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exactMSA_hcore_of_residual

end FMSA.ExactMSA.Certificate
