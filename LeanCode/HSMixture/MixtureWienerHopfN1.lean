/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.MixtureSymbolBridge
import LeanCode.HSMixture.MatrixGramWienerHopf
import LeanCode.HardSphere.BaxterWienerHopf

/-!
# The MRS.8 Gram factorization at `N = 1`, from the scalar Baxter WH factorization

The correct MRS.8 bridge is the shell-kernel / WH route (`matRadialSymbol_eq_shellKernel_cos`); its
content is the matrix WH factorization `I − ρĈ(k) = Q̂₀Q̂₀ᵀ` — the `∑ₗ|(B·v)ₗ|²` Gram shape
`hfack`/`hfac0` that `matSymbolCoercive_of_gramFactors` consumes.  At ONE component this is exactly
the proven scalar `baxter_wiener_hopf_factorization`
`(1 − ∫q0·cos)² + (∫q0·sin)² = 1 − ρ·radial_fourier(c_HS)(k)` — the modulus `|1 − q̃₀(k)|²` of the
scalar Baxter factor.

`hfac_fin_one_of_baxterWH` discharges the value-route Gram input at `N = 1`: with `B = 1 − q̃₀(k)`
(real part `1 − ∫q0·cos`, imaginary part `−∫q0·sin`), the `∑ₗ|(B·v)ₗ|²` shape equals
`∑vᵢ² − ρ∑ᵢⱼ matRadialSymbol(c_HS) uᵢuⱼ`.  This is the shell-kernel/WH route's non-vacuity at one
component — the genuine MRS.8 identity, proved (not axiomatized) at `N = 1` from the scalar theorem.

The single remaining open input of the general-`N` value route (after `MatrixGramWienerHopf`) is the
matrix **structure-factor identity** `hSF`: `(Q̂₀·Q̂₀(−·)ᵀ)ᵢⱼ = δᵢⱼ − ρ·radial_fourier(Φᵢⱼ)`.
`hSF_fin_one_of_baxterWH` proves this identity at `N = 1` from the same scalar WH theorem, where
`Q̂₀ = Q0fourier_fin_one` is the `1×1` Fourier Baxter factor `1 − q̃₀(k)` and `Q̂₀(−·) = conj Q̂₀`
(Hermitian reality on the axis).  `hfack_fin_one_via_reduction` then feeds this `hSF` through the
general-`N` reduction (`matWH_hfack_of_structureFactor`), reproducing the `N = 1` Gram input — a
consistency check that the general mechanics specialize to the proven scalar case.  The general-`N`
`hSF` (`matShellKernel` ⟷ `Q̂₀`) remains the sole open piece.

**Update (2026-08-19).**  The general-`N` `hSF` Fourier factorization has since landed as
`matDCFfullN_laplace` (`MixtureDCFAEInjective.lean`): `𝓛(matDCFfullN)(i·k) = Cmix0 = I − Q̂₀Q̂₀ᵀ`.
⚠ `matDCFfullN(v) = cMixDCFN(v)` was a MIS-STATEMENT: `matDCFfullN = (matDCFreCoreN : ℂ)`, the
reconstruction *core*, not the DCF.  The correct identity — the core is the shell-integral of the
DCF, `matDCFfullN(w) = ↑(2π·rg·∫_w^{Rᵢₖ} s·cMixDCFN)` — is PROVED in `MixtureDCFShellForm.lean`
(`matDCFfullN_eq_shellIntegral`, std-3).  The remaining transform step to
`ρ·radial_fourier(cMixDCFN)` = the coercivity symbol is a Fourier IBP.  See `MixtureSymbolBridge`.
-/

open MeasureTheory
namespace FMSA.MixtureOzStar
open FMSA.HardSphere

/-- **N=1 Gram factorization `hfac` from the scalar Baxter WH factorization.**  At one component the
`∑ₗ|(B·v)ₗ|²` shape of `matSymbolCoercive_of_gramFactors`'s `hfack`/`hfac0` input, with
`B = 1 − q̃₀(k)` (real part `1 − ∫q0·cos`, imaginary part `−∫q0·sin`), IS exactly
`baxter_wiener_hopf_factorization`: `|1 − q̃₀(k)|² = 1 − ρ·radial_fourier(c_HS)(k)`.  Discharges the
value-route Gram input at `N = 1` from the proven scalar WH factorization — the correct
(shell-kernel/WH) MRS.8 route, at one component. -/
theorem hfac_fin_one_of_baxterWH (eta sigma rho : ℝ) (hsigma : 0 < sigma) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) {k : ℝ} (hk : k ≠ 0) (v : Fin 1 → ℝ) :
    (∑ i, v i ^ 2) - rho * ∑ i, ∑ j,
        matRadialSymbol (fun _ _ => c_HS eta sigma) k i j * v i * v j
      = ∑ l, Complex.normSq
          ((!![((1 - ∫ r in (0 : ℝ)..sigma, q0_poly eta sigma rho r * Real.cos (k * r) : ℝ) : ℂ)
              - ((∫ r in (0 : ℝ)..sigma, q0_poly eta sigma rho r * Real.sin (k * r) : ℝ) : ℂ)
                * Complex.I] : Matrix (Fin 1) (Fin 1) ℂ).mulVec (fun i => (v i : ℂ)) l) := by
  set Cc := ∫ r in (0 : ℝ)..sigma, q0_poly eta sigma rho r * Real.cos (k * r) with hCc
  set Cs := ∫ r in (0 : ℝ)..sigma, q0_poly eta sigma rho r * Real.sin (k * r) with hCs
  have hwh := baxter_wiener_hopf_factorization eta sigma rho k hsigma hk heta heta_def
  rw [← hCc, ← hCs] at hwh
  simp only [Fin.sum_univ_one, matRadialSymbol_eq_radial_fourier]
  have hmv : (!![((1 - Cc : ℝ) : ℂ) - ((Cs : ℝ) : ℂ) * Complex.I]
        : Matrix (Fin 1) (Fin 1) ℂ).mulVec (fun i => (v i : ℂ)) 0
      = (((1 - Cc : ℝ) : ℂ) - ((Cs : ℝ) : ℂ) * Complex.I) * (v 0 : ℂ) := by
    simp [Matrix.mulVec, dotProduct]
  rw [hmv, Complex.normSq_mul]
  have hB : Complex.normSq (((1 - Cc : ℝ) : ℂ) - ((Cs : ℝ) : ℂ) * Complex.I)
      = (1 - Cc) ^ 2 + Cs ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hB, Complex.normSq_ofReal, hwh]; ring

/-- **N=1 Fourier Baxter factor** `Q̂₀(ik) = 1 − q̃₀(k)` as a `1×1` matrix: real part `1 − ∫q0·cos`,
imaginary part `−∫q0·sin`.  The `N = 1` case of the mixture `Q̂₀` whose Hermitian companion is
`conj Q̂₀` (`Q0_mat_c_phys_neg_axis`) and whose Gram square is `I − ρĈ`. -/
noncomputable def Q0fourier_fin_one (eta sigma rho k : ℝ) : Matrix (Fin 1) (Fin 1) ℂ :=
  !![((1 - ∫ r in (0 : ℝ)..sigma, q0_poly eta sigma rho r * Real.cos (k * r) : ℝ) : ℂ)
      - ((∫ r in (0 : ℝ)..sigma, q0_poly eta sigma rho r * Real.sin (k * r) : ℝ) : ℂ) * Complex.I]

/-- **N=1 matrix structure-factor identity `hSF`, from the scalar Baxter WH factorization.**  With
`Q̂₀ = Q0fourier_fin_one` (the `1×1` factor `1 − q̃₀(k)`) and its Hermitian companion `conj Q̂₀`,
`(Q̂₀·(conj Q̂₀)ᵀ)ᵢⱼ = δᵢⱼ − ρ·radial_fourier(c_HS)(k)`.  This is the `N = 1` instance of the
Wertheim identity `hSF` that `matWH_hfack_of_structureFactor` consumes; its single-component content
`|1 − q̃₀(k)|² = 1 − ρ·radial_fourier(c_HS)` is exactly `baxter_wiener_hopf_factorization`. -/
theorem hSF_fin_one_of_baxterWH (eta sigma rho : ℝ) (hsigma : 0 < sigma) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) {k : ℝ} (hk : k ≠ 0) (i j : Fin 1) :
    ((Q0fourier_fin_one eta sigma rho k)
        * ((Q0fourier_fin_one eta sigma rho k).map (starRingEnd ℂ)).transpose) i j
      = (if i = j then (1 : ℂ) else 0) - (rho : ℂ) * (radial_fourier (c_HS eta sigma) k : ℂ) := by
  have hwh := baxter_wiener_hopf_factorization eta sigma rho k hsigma hk heta heta_def
  fin_cases i; fin_cases j
  simp only [Q0fourier_fin_one, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Fin.sum_univ_one, Matrix.of_apply, Matrix.cons_val_fin_one, if_true]
  set Cc := ∫ r in (0 : ℝ)..sigma, q0_poly eta sigma rho r * Real.cos (k * r) with hCc
  set Cs := ∫ r in (0 : ℝ)..sigma, q0_poly eta sigma rho r * Real.sin (k * r) with hCs
  rw [Complex.mul_conj]
  have hB : Complex.normSq (((1 - Cc : ℝ) : ℂ) - ((Cs : ℝ) : ℂ) * Complex.I)
      = (1 - Cc) ^ 2 + Cs ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hB, hwh]; push_cast; ring

/-- **Consistency of the reduction at `N = 1`.**  Feeding the proved `N = 1` structure factor `hSF`
(`hSF_fin_one_of_baxterWH`) through the general-`N` Gram reduction `matWH_hfack_of_structureFactor`
reproduces the `N = 1` Gram input — the general mechanics specialize to the scalar case. -/
theorem hfack_fin_one_via_reduction (eta sigma rho : ℝ) (hsigma : 0 < sigma) (heta : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) {k : ℝ} (hk : k ≠ 0) (v : Fin 1 → ℝ) :
    (∑ i, v i ^ 2) - rho * ∑ i, ∑ j,
        (fun _ _ => radial_fourier (c_HS eta sigma) k) i j * v i * v j
      = ∑ l, Complex.normSq
          ((Q0fourier_fin_one eta sigma rho k).transpose.mulVec (fun i => (v i : ℂ)) l) :=
  matWH_hfack_of_structureFactor _ _ rho _ rfl
    (hSF_fin_one_of_baxterWH eta sigma rho hsigma heta heta_def hk) v

end FMSA.MixtureOzStar
