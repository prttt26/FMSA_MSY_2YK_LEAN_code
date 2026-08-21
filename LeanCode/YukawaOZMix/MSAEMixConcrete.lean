/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HSMixture.Q0Complex
import LeanCode.YukawaOZ.MSADCFTransform
import LeanCode.YukawaOZMix.MSAMixtureCancellation

/-!
# MSAEMIX.1 — the concrete matrix Baxter increment `Q₁` (amplitude-difference form + Yukawa tail)

Group **MSAEMIX** (`proof_notes_msa_exact.md`).

`matEMIXfactorization_of_core` reduces the mixture MSA factorisation to a matrix `hcore` from an
*abstract* coupling-`0` factor `Q₀` and increment `Q₁`.  This file makes
those concrete, reusing the validated mixture Baxter entry `Q0_mat_c` (`HSMixture/Q0Complex.lean`) —
the matrix Baxter factor `Q̂₀,ᵢⱼ(s) = δᵢⱼ − ρgeoᵢⱼ e^{−λᵢⱼs}(q′ᵢⱼ φ₁(s,σᵢ) + q″ᵢⱼ φ₂(s,σᵢ))`.

Two concrete pieces, each grounded in already-proved scalar/matrix infrastructure:

* **The `q`-side amplitude increment.** `Q0_mat_c` is **linear in the amplitudes** `(q′, q″)`,
  so the coupling increment of the factor — `Q̂(q′_MSA, q″_MSA) − Q̂(q′_HS, q″_HS)` — is the *same*
  `Q0_mat_c` form at the amplitude **differences** (`Q0_mat_c_sub`).  The differences are the
  Blum–Høye `M_j, N_j` dressing (their `(20)/(21)`, made exponential-free by the (★) cancellation
  `MSAMixtureCancellation.cancellation_star`); this file supplies the *form*, the values are that
  transcription.
* **The `c`-side exterior tail.** The mixture MSA exterior DCF is `c_ij(r) = K_ij e^{−z(r−σ_ij)}/r`
  for `r > σ_ij` — per-entry the scalar `cMSAtail`, so its radial-Fourier transform is per-entry the
  scalar `radial_fourier_cMSAtail` (`matMSAtail`, `radial_fourier_matMSAtail`).  This is the matrix
  `𝓕[c_tail]` that the matrix `hcore`'s `Ĉ_MSA` needs.

⚠ **What is still open.** The amplitude-difference *values* (`M_j, N_j`-dressed `q′, q″`) are the
mixture Blum–Høye transcription — not attempted here, and to be pinned against `msa_exact_mix.py`
before use (the scalar compact-ansatz cautionary tale).  With them the matrix `hcore` is the
analytic core, the matrix analog of MSAEXACT.6.
-/

open Real
open FMSA.Q0Complex FMSA.MSAExact FMSA.HardSphere

namespace MSAEMix

variable {N : ℕ}

/-! ### The `q`-side amplitude increment — `Q0_mat_c` is linear in the Baxter amplitudes -/

/-- **The mixture Baxter factor is affine in the Baxter amplitudes.**  `Q0_mat_c` is
`δᵢⱼ − ρgeoᵢⱼ e^{−λᵢⱼs}(q′ᵢⱼ φ₁ + q″ᵢⱼ φ₂)`, linear in `(q′, q″)`, so its coupling **increment** is
the same form at the amplitude *differences*:
`Q̂(q′₂,q″₂)ᵢⱼ − Q̂(q′₁,q″₁)ᵢⱼ = Q̂(Δq′,Δq″)ᵢⱼ − δᵢⱼ`.  With `(q′₂,q″₂)` the MSA-dressed and
`(q′₁,q″₁)` the hard-sphere amplitudes, this is the concrete `q`-side Baxter increment `Q₁`. -/
theorem Q0_mat_c_sub (s : ℂ) (sigma : Fin N → ℂ) (rho_geo : Fin N → Fin N → ℂ)
    (Qp1 Qpp1 Qp2 Qpp2 : Fin N → Fin N → ℂ) (i j : Fin N) :
    Q0_mat_c s sigma rho_geo Qp2 Qpp2 i j - Q0_mat_c s sigma rho_geo Qp1 Qpp1 i j
      = Q0_mat_c s sigma rho_geo (Qp2 - Qp1) (Qpp2 - Qpp1) i j
        - (if i = j then (1 : ℂ) else 0) := by
  simp only [Q0_mat_c, q0_entry_c, Pi.sub_apply]
  ring

/-- The coupling increment vanishes when the MSA amplitudes equal the hard-sphere ones — the
consistency check that `Q₁ = 0` at zero coupling. -/
theorem Q0_mat_c_sub_self (s : ℂ) (sigma : Fin N → ℂ) (rho_geo : Fin N → Fin N → ℂ)
    (Qp Qpp : Fin N → Fin N → ℂ) (i j : Fin N) :
    Q0_mat_c s sigma rho_geo Qp Qpp i j - Q0_mat_c s sigma rho_geo Qp Qpp i j = 0 := by
  ring

/-! ### The `c`-side exterior tail — per-entry the scalar Yukawa DCF tail -/

/-- The mixture MSA exterior DCF matrix: entry `(i,j)` is the scalar Yukawa tail
`c_ij(r) = K_ij e^{−z(r−σ_ij)}/r` for `r > σ_ij`, `σ_ij = (σ_i + σ_j)/2` (`cMSAtail` per entry). -/
noncomputable def matMSAtail (K : Matrix (Fin N) (Fin N) ℝ) (z : ℝ) (sigma : Fin N → ℝ)
    (i j : Fin N) (r : ℝ) : ℝ :=
  cMSAtail (K i j) z (sigMix sigma i j) r

/-- **The matrix exterior-tail transform is per-entry the scalar `radial_fourier_cMSAtail`.** So
matrix `𝓕[c_tail]ᵢⱼ` in the mixture `hcore`'s `Ĉ_MSA` is the closed form
`(4πK_ij/k)·(k cos(kσ_ij) + z sin(kσ_ij))/(z²+k²)` — no new integral, the scalar one lifts. -/
theorem radial_fourier_matMSAtail (K : Matrix (Fin N) (Fin N) ℝ) {z : ℝ} (hz : 0 < z)
    (sigma : Fin N → ℝ) (hsig : ∀ i, 0 < sigma i) (k : ℝ) (i j : Fin N) :
    radial_fourier (matMSAtail K z sigma i j) k
      = 4 * π * (K i j) / k
        * ((k * Real.cos (k * sigMix sigma i j) + z * Real.sin (k * sigMix sigma i j))
            / (z ^ 2 + k ^ 2)) := by
  have hsij : 0 < sigMix sigma i j := by
    have h1 := hsig i; have h2 := hsig j; unfold sigMix; linarith
  unfold matMSAtail
  exact radial_fourier_cMSAtail hz hsij (K i j) k

end MSAEMix
