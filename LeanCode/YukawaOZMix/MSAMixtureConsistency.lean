/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAMixtureBHRootSmooth

/-!
# Transcription consistency cross-checks for the mixture Blum–Høye / MSA amplitudes

The `MixBHRoot` gate and its amplitudes (`qhatMixR`, `qpMat`, `Wt`, `Ct`, `AVec`, `mixM/mixN`, …)
are **posited** transcriptions of the physical Blum–Høye MSA system.  Their faithfulness is the one
part of the FMSA formalisation that is human-audited rather than machine-proved (the same grade the
`N = 1` `exists_contDiffAt_bhRoot` carries).  It cannot be *eliminated* inside the system — proving
"the spec matches physics" would require formalising the physics, which just relocates the question
— but it can be **shrunk and cross-checked**.  This file collects the cheap, high-value checks: each
is an *independent* physical fact that the transcription must satisfy, so a sign/factor bug in the
amplitudes would make one of them fail to prove.

**Zero-coupling limit (`Q₁ = 0`, this file).**  With no Yukawa tail (`Dt = 0`) the MSA closure must
collapse to Percus–Yevick hard spheres.  `FtMSA_zero_eq_FtHS`: the MSA symmetric Baxter factor
equals the hard-sphere one; `Ft1_zero_of_Dt_zero`: the increment `Q₁ = F̃_MSA − F̃_HS` vanishes.

**The other anchors already in place** (cited, not re-proved here):

* **N=1 reduction (the observable DCF).**  `msaMixture_reduces_to_scalar_at_fin_one` (MSAEMIX.2,
  `MSAMixtureFinOne.lean`) shows the `N = 1` mixture MSA *factorization* collapses to the scalar
  `MSAEXACT.1` Baxter modulus `A² + B² = 1 − ρĉ` — i.e. the one-component mixture **is** the scalar
  exact-MSA, whose closed form is independently checked against Tang & Lu 1993 to `1e-14`
  (`FMSA_pure.get_h1L_laplace`).  The scalar HS bridge is `sqrt_rho_qhatMixC_HS_fin_one`.
* **HS-limit identification (the recognised physical Baxter matrix).**  `resH_eq_baxter` /
  `Q0phys_eq_baxter` / `detH_eq_Q0` (`MSAMixtureBHRootSmooth.lean`) show the `Dt = 0` MSA Baxter
  block `resH (0, Gt₀)` is the physical hard-sphere OZ matrix — it shares its determinant with the
  Lebowitz/Baxter `Q0_mat_phys` (via Sylvester), which is where the unconditional non-degeneracy
  `Q0_mat_phys_isUnit_det` enters.
* **Zero-coupling of the discrete amplitudes.**  `Wt_zero_of_Dt_zero`, `Ct_zero_of_Dt_zero`,
  `mixDqp_zero_of_Dt_zero`, `mixDA_zero_of_Dt_zero` (`MSAMixtureConcrete.lean`), and the base-point
  root equation `matBhResidual_base_eq`.
-/

open scoped BigOperators

namespace MSAMixture

variable {N : ℕ}

/-- **Zero-coupling consistency (`Q₁ = 0`).**  At `Dt = 0` (no Yukawa coupling) the MSA symmetric
Baxter factor equals the hard-sphere one, `F̃_MSA = F̃_HS` — the fundamental MSA → Percus–Yevick-HS
reduction.  Every dressing amplitude (`Wt`, `Ct`, `mixDqp`, `mixDA`) vanishes at `Dt = 0`, so the
factor's argument reduces entrywise to the HS `(qp0Mat, 0, 0, A0Vec)`. -/
theorem FtMSA_zero_eq_FtHS (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Gt : Matrix (Fin N) (Fin N) ℝ) (s : ℂ) :
    FtMSA z sig rho sigma Gt 0 s = FtHS z sig rho sigma s := by
  ext i j
  simp only [FtMSA, FtHS, ftilde, qhatMixC, qpMat_zero_Dt, Wt_zero_Dt, Ct_zero_Dt, AVec_zero_Dt,
    Matrix.zero_apply, Pi.zero_apply, Complex.ofReal_zero, zero_div, zero_mul, add_zero]

/-- **The coupling increment vanishes at zero coupling**: `Q₁ = F̃_MSA − F̃_HS = 0` at `Dt = 0`.
The consistency check that the transcribed MSA amplitudes carry no spurious `O(1)` (coupling-free)
contribution — any such bug would leave a nonzero `Q₁` here. -/
theorem Ft1_zero_of_Dt_zero (z sig : ℝ) (rho sigma : Fin N → ℝ)
    (Gt : Matrix (Fin N) (Fin N) ℝ) (s : ℂ) :
    Ft1 z sig rho sigma Gt 0 s = 0 := by
  rw [Ft1, FtMSA_zero_eq_FtHS, sub_self]

end MSAMixture
