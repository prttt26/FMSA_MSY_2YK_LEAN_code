/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HSMixture.Q0Complex
import LeanCode.HSMixture.MatrixQ0
import LeanCode.YukawaOZ.MSADCFTransform
import LeanCode.YukawaOZMix.MSAMixtureCancellation

/-!
# MSAEMIX.1 — the concrete matrix Baxter increment `Q₁` (amplitude-difference form + Yukawa tail)

Group **MSAEMIX** (`proof_notes_msa_exact.md`).

`matMixtureFactorization_of_core` reduces the mixture MSA factorisation to a matrix `hcore` from an
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
open FMSA.Q0Complex FMSA.ExactMSA FMSA.HardSphere

namespace MSAMixture

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

/-! ### The amplitude-difference values `Δq′, ΔA` (the Blum–Høye `M_j, N_j` dressing)

⭐ **Numerically validated against `msa_exact_mix.py` `_pieces`** (`msaemix_MN_check.py`, binary
equal/unequal σ + ternary): `M`/`N` err `0`, `ΔA`/`Δq′` err `≤1.8e-15`; the Baxter increment's
amplitude part is **linear** in `(Δq′,ΔA)` to `1e-16` (so `Q0_mat_c_sub` applies), and `σ²φ₁/σ³φ₂`
= `q0_entry_c`'s `φ` (so `Qp↔q′`, `Qpp↔A`).  `Q0phys = q^{0′}` (`= _pieces` `QP0`),
`Qppphys = A⁰` (`= A0`), `−4B⁰_j/σ_j² = 2π²ξ₂/vac²` — all confirmed `≤7e-15`. -/

open FMSA.MatrixQ0

/-- Blum–Høye `M_j` (their `(20)`, `C` eliminated), single tail:
`M_j = −(1/z) Σ_l ρ_l (W̃_lj + (1+zσ_l) C̃_lj)` — exponential-free via the (★) `Wt, Ct`. -/
noncomputable def mixM (z : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (j : Fin N) : ℝ :=
  -(1 / z) * ∑ l, rho l * (Wt z rho Gt Dt l j + (1 + z * sigma l) * Ct z rho sigma Gt Dt l j)

/-- Blum–Høye `N_j` (their `(21)`), single tail, `λ_jl = (σ_j−σ_l)/2`. -/
noncomputable def mixN (z : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (j : Fin N) : ℝ :=
  ∑ l, rho l * (((1 + z * ((sigma j - sigma l) / 2)) / z ^ 2) * Wt z rho Gt Dt l j
    + (((1 + z * sigma l + (z * sigma l) ^ 2 / 2) / z ^ 2)
        + ((sigma j - sigma l) / 2) * (1 + z * sigma l) / z) * Ct z rho sigma Gt Dt l j)

/-- `ΔA_j = A_j − A_j⁰ = A_j⁰ M_j − 4 B_j⁰ N_j/σ_j²`, with `A_j⁰ = Qppphys`,
`−4B_j⁰/σ_j² = 2π²ξ₂/vac²` (`ξ₂ = xi2`, `vac = vacMix`).  The `q″`-amplitude difference. -/
noncomputable def mixDA (z : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (j : Fin N) : ℝ :=
  Qppphys rho sigma j j * mixM z rho sigma Gt Dt j
    + (2 * π ^ 2 * xi2 rho sigma / vacMix rho sigma ^ 2) * mixN z rho sigma Gt Dt j

/-- `Δq′_ij = q′_ij − q^{0′}_ij = q^{0′}_ij M_j + A_i⁰ N_j`, with `q^{0′}_ij = Q0phys` and
`A_i⁰ = Qppphys _ i` — carrying the **row** index `i` (Blum–Høye `(24)`'s `A_i⁰`, forced).  The
`q′`-amplitude difference. -/
noncomputable def mixDqp (z : ℝ) (rho sigma : Fin N → ℝ) (Gt Dt : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) : ℝ :=
  Q0phys rho sigma i j * mixM z rho sigma Gt Dt j
    + Qppphys rho sigma i i * mixN z rho sigma Gt Dt j

/-! ### Zero-coupling consistency — `Q₁ = 0` at `Dt = 0` -/

/-- `W̃ = 0` at zero coupling (`Dt = 0`). -/
theorem Wt_zero_of_Dt_zero (z : ℝ) (rho : Fin N → ℝ) (Gt : Matrix (Fin N) (Fin N) ℝ) (l j : Fin N) :
    Wt z rho Gt 0 l j = 0 := by simp [Wt]

/-- `C̃ = 0` at zero coupling (`Dt = 0`). -/
theorem Ct_zero_of_Dt_zero (z : ℝ) (rho sigma : Fin N → ℝ) (Gt : Matrix (Fin N) (Fin N) ℝ)
    (l j : Fin N) : Ct z rho sigma Gt 0 l j = 0 := by simp [Ct]

/-- The `q′` amplitude difference vanishes at zero coupling (`M = N = 0` ⇒ `Δq′ = 0`) — the
consistency check that the concrete increment `Q₁` is `0` at `K = 0`. -/
theorem mixDqp_zero_of_Dt_zero (z : ℝ) (rho sigma : Fin N → ℝ) (Gt : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) : mixDqp z rho sigma Gt 0 i j = 0 := by
  simp [mixDqp, mixM, mixN, Wt_zero_of_Dt_zero, Ct_zero_of_Dt_zero]

/-- The `q″` amplitude difference vanishes at zero coupling. -/
theorem mixDA_zero_of_Dt_zero (z : ℝ) (rho sigma : Fin N → ℝ) (Gt : Matrix (Fin N) (Fin N) ℝ)
    (j : Fin N) : mixDA z rho sigma Gt 0 j = 0 := by
  simp [mixDA, mixM, mixN, Wt_zero_of_Dt_zero, Ct_zero_of_Dt_zero]

end MSAMixture
