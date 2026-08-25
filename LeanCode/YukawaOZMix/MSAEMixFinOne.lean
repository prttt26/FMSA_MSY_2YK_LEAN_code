/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZMix.MSAEMixBHRoot
import LeanCode.HardSphere.BaxterZeros
import LeanCode.HardSphere.BaxterWienerHopfComplex
import LeanCode.HSMixture.MixtureNoSpinodalN1

/-!
# MSAEMIX.1 at `N = 1` — HS Wiener–Hopf FULLY discharged (no `hWH`/`hKDEF`/`hbridge`/`hHS`)

Group **MSAEMIX**.  `matMSAemix1_equalDiam_WH` reduces the HS symmetric factorization to the shared
WH atoms.  At `N = 1` those atoms are **fully proved** — the scalar Baxter Wiener–Hopf
(`baxter_wiener_hopf_complex`) — so this file lands the `N = 1` MSAEMIX.1 factorization depending
only on `MixBHRoot` and the physics axiom `matMSAexactEqualDiam_hcore`, with **no** HS hypothesis.

The one bridge: the `N = 1` symmetric HS factor `FtHS` (√-weighted complex-Laplace `qhatMixC`)
equals the scalar HS Baxter factor `1 − Q̂_complex(k)` (real-space cosine/sine).  Both are the same
`q0_poly` Laplace transform, matched via `Qhat_complex_formula` (closed form) and the `N = 1`
amplitude bridges `Q0phys_n1`/`Qppphys_n1` (`Q0phys = q'_py`, `Qppphys = q''_py`, `η = πρσ³/6`).
-/

open Real Complex
open FMSA.Q0Complex FMSA.MSAExact FMSA.HardSphere FMSA.MatrixQ0 FMSA.MixtureNoSpinodalN1

namespace MSAEMix

/-! ### The `N = 1` bridge: `√(ρ₀²)·qhatMixC(HS)(ik) = Q̂_complex(k)` -/

/-- At `N = 1`, the √-weighted HS `qhatMixC` (complex-Laplace at `s = ik`) equals the scalar HS
Baxter factor `Qhat_complex` (`∫₀^σ q0_poly e^{−ikr}`).  Both are the `q0_poly` Laplace transform;
matched through `Qhat_complex_formula` + `Q0phys_n1`/`Qppphys_n1`.  `s = I·k` is kept opaque so the
identity is a rational identity in `(s, e^{−sσ})` — no `I² = −1` algebra needed. -/
theorem sqrt_rho_qhatMixC_HS_fin_one (rho sigma : Fin 1 → ℝ) (z : ℝ) {k : ℝ} (hk : k ≠ 0)
    (hsig : 0 < sigma 0) (hrho : 0 ≤ rho 0) (heta : etaMix rho sigma ≠ 1) :
    (Real.sqrt (rho 0 * rho 0) : ℂ)
        * qhatMixC z (sigma 0) (qp0Mat rho sigma) 0 0 (A0Vec rho sigma) (Complex.I * (k : ℂ)) 0 0
      = Qhat_complex (etaMix rho sigma) (sigma 0) (rho 0) (k : ℂ) := by
  have hsqrt : Real.sqrt (rho 0 * rho 0) = rho 0 := Real.sqrt_mul_self hrho
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hQ0 : Q0phys rho sigma 0 0 = q_prime_py (etaMix rho sigma) (sigma 0) := Q0phys_n1 hsig heta
  have hQpp : Qppphys rho sigma 0 0 = q_doubleprime_py (etaMix rho sigma) := Qppphys_n1 hsig heta
  -- s := I*k, opaque; both sides rational in (s, E = exp(-s σ₀))
  set s : ℂ := Complex.I * (k : ℂ) with hs_def
  have hs0 : s ≠ 0 := by
    rw [hs_def]; exact mul_ne_zero Complex.I_ne_zero hkC
  -- Qhat_complex in closed form; rewrite its `-I*k` as `-s`
  rw [Qhat_complex_formula (etaMix rho sigma) (sigma 0) (rho 0) hsig hkC]
  simp only [qhatMixC, qp0Mat, A0Vec, Matrix.zero_apply, hQ0, hQpp, hsqrt]
  have hIk : -Complex.I * (k : ℂ) = -s := by rw [hs_def]; ring
  rw [hIk]
  push_cast
  field_simp
  ring

/-! ### The `N = 1` HS symmetric factorization, fully discharged -/

/-- The `N = 1` hard-sphere symmetric Baxter factorization, PROVED (no hypothesis): the `FtHS`
product is `1 − ρ₀·𝓕[c_HS]`, from the scalar complex Wiener–Hopf `baxter_wiener_hopf_complex`
via the bridge `sqrt_rho_qhatMixC_HS_fin_one` and `Chat_complex_eq_radial_fourier`. -/
theorem FtHS_mul_fin_one (rho sigma : Fin 1 → ℝ) (z : ℝ) {k : ℝ} (hk : k ≠ 0)
    (hsig : 0 < sigma 0) (hrho : 0 ≤ rho 0) (hlt : etaMix rho sigma < 1) (i j : Fin 1) :
    (FtHS z (sigma 0) rho sigma (Complex.I * k)
        * (FtHS z (sigma 0) rho sigma (-(Complex.I * k))).transpose) i j
      = (if i = j then (1 : ℂ) else 0)
        - ((rho 0 * radial_fourier (c_HS (etaMix rho sigma) (sigma 0)) k : ℝ) : ℂ) := by
  have heta : etaMix rho sigma ≠ 1 := ne_of_lt hlt
  have hkneg : -k ≠ 0 := neg_ne_zero.mpr hk
  -- the two 1×1 factor entries via the bridge
  have hF1 : (FtHS z (sigma 0) rho sigma (Complex.I * k)) 0 0
      = 1 - Qhat_complex (etaMix rho sigma) (sigma 0) (rho 0) (k : ℂ) := by
    simp only [FtHS, ftilde, if_true,
      sqrt_rho_qhatMixC_HS_fin_one rho sigma z hk hsig hrho heta]
  have hbridge2 := sqrt_rho_qhatMixC_HS_fin_one rho sigma z hkneg hsig hrho heta
  have hF2 : (FtHS z (sigma 0) rho sigma (-(Complex.I * k))) 0 0
      = 1 - Qhat_complex (etaMix rho sigma) (sigma 0) (rho 0) (-(k : ℂ)) := by
    have hrw : (-(Complex.I * (k : ℂ))) = Complex.I * ((-k : ℝ) : ℂ) := by push_cast; ring
    simp only [FtHS, ftilde, if_true, hrw, hbridge2]
    push_cast; ring
  have hi0 : i = 0 := Subsingleton.elim i 0
  have hj0 : j = 0 := Subsingleton.elim j 0
  subst hi0; subst hj0
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.transpose_apply, hF1, hF2]
  have hwh := baxter_wiener_hopf_complex (eta := etaMix rho sigma) (sigma := sigma 0) (rho := rho 0)
    hsig hlt (etaMix_n1 rho sigma) (k := (k : ℂ)) (by exact_mod_cast hk)
  rw [hwh, Chat_complex_eq_radial_fourier hsig]
  push_cast; ring

/-! ### MSAEMIX.1 at `N = 1` — fully discharged (only `MixBHRoot` + the physics axiom) -/

/-- ⭐⭐⭐ **MSAEMIX.1 at `N = 1`, HS Wiener–Hopf fully discharged.**  At one component, given only the
Blum–Høye root `MixBHRoot` (and `η < 1`, `σ > 0`, `ρ ≥ 0`), the MSA symmetric Baxter factorization
holds with the physical HS DCF `ρ₀·𝓕[c_HS]` — **no** `hHS`/`hWH`/`hKDEF`/`hbridge` hypothesis (the
scalar Baxter WH `baxter_wiener_hopf_complex` discharges them).  Its only physics axiom is
`matMSAexactEqualDiam_hcore`; `#print axioms` = the standard three + that axiom. -/
theorem matMSAemix1_fin_one (rho sigma : Fin 1 → ℝ) (z : ℝ) (Gt Dt K : Matrix (Fin 1) (Fin 1) ℝ)
    {k : ℝ} (hk : k ≠ 0) (hsig : 0 < sigma 0) (hrho : 0 ≤ rho 0) (hlt : etaMix rho sigma < 1)
    (hroot : MixBHRoot z (sigma 0) rho sigma Gt Dt K) (i j : Fin 1) :
    ((FtHS z (sigma 0) rho sigma (Complex.I * k) + Ft1 z (sigma 0) rho sigma Gt Dt (Complex.I * k))
        * (FtHS z (sigma 0) rho sigma (-(Complex.I * k))
            + Ft1 z (sigma 0) rho sigma Gt Dt (-(Complex.I * k))).transpose) i j
      = (if i = j then (1 : ℂ) else 0)
        - (((rho 0 * radial_fourier (c_HS (etaMix rho sigma) (sigma 0)) k : ℝ) : ℂ)
            + (Real.sqrt (rho i * rho j) : ℂ)
              * ((radial_fourier (matMSACoreCorr z rho sigma Gt Dt K i j) k : ℂ)
                + (radial_fourier (matMSAtail K z sigma i j) k : ℂ))) :=
  matMSAemix1_equalDiam z (sigma 0) rho sigma Gt Dt K k (fun i => by fin_cases i; rfl) hroot
    (fun _ _ => ((rho 0 * radial_fourier (c_HS (etaMix rho sigma) (sigma 0)) k : ℝ) : ℂ))
    (FtHS_mul_fin_one rho sigma z hk hsig hrho hlt) i j

/-- ⭐⭐ **MSAEMIX.2 — the `N = 1` mixture MSA factorization IS the scalar MSAEXACT.1 Baxter
modulus.**  Writing the (conjugate-pair) mixture factor as `(F̃_HS + F̃₁)(±ik)₀₀ = A ∓ iB` (real
`A, B`), the fully-discharged `N = 1` factorization `matMSAemix1_fin_one` collapses — through the
scalar bridge `matEMIX_factorization_fin_one_iff` and `√(ρ₀ρ₀) = ρ₀` — to the **scalar Baxter
modulus** `A² + B² = 1 − ρ₀·ĉ`, `ĉ = 𝓕[c_HS] + 𝓕[c_core] + 𝓕[c_tail]`.  This is exactly the shape of
`MSAEXACT.1`'s `factorization_of_core` conclusion (`A = 1 − ρReQ̂`, `B = ρImQ̂`), so the
one-component mixture *is* the scalar exact-MSA.  Positivity half: `mixCompressibility_fin_one` /
`mixStability_fin_one` (`MSAMixturePositivity.lean`) reduce the matrix `(39)` / stability det to the
scalar `ρB²` / `B²`.  Footprint = std-3 + `matMSAexactEqualDiam_hcore` (inherited). -/
theorem msaMixture_reduces_to_scalar_at_fin_one (rho sigma : Fin 1 → ℝ) (z : ℝ)
    (Gt Dt K : Matrix (Fin 1) (Fin 1) ℝ) {k : ℝ} (hk : k ≠ 0) (hsig : 0 < sigma 0)
    (hrho : 0 ≤ rho 0) (hlt : etaMix rho sigma < 1)
    (hroot : MixBHRoot z (sigma 0) rho sigma Gt Dt K) (A B : ℝ)
    (hfull : (FtHS z (sigma 0) rho sigma (Complex.I * k)
        + Ft1 z (sigma 0) rho sigma Gt Dt (Complex.I * k)) 0 0 = (A : ℂ) - Complex.I * (B : ℂ))
    (hfullneg : (FtHS z (sigma 0) rho sigma (-(Complex.I * k))
        + Ft1 z (sigma 0) rho sigma Gt Dt (-(Complex.I * k))) 0 0 = (A : ℂ) + Complex.I * (B : ℂ)) :
    A ^ 2 + B ^ 2
      = 1 - rho 0 * (radial_fourier (c_HS (etaMix rho sigma) (sigma 0)) k
          + radial_fourier (matMSACoreCorr z rho sigma Gt Dt K 0 0) k
          + radial_fourier (matMSAtail K z sigma 0 0) k) := by
  refine (matEMIX_factorization_fin_one_iff A B _ (rho 0) _ _ hfull hfullneg).mp ?_
  rw [matMSAemix1_fin_one rho sigma z Gt Dt K hk hsig hrho hlt hroot 0 0,
    Real.sqrt_mul_self hrho, if_pos rfl]
  push_cast
  ring

end MSAEMix
