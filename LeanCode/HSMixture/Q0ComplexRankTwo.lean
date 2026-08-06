/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.MixtureNoSpinodal
import LeanCode.HSMixture.Q0DetRankTwo

/-!
# Complex-`s` rank-2 factorisation and Woodbury inverse of `Q̂₀(s)` (general `N`)

The structural heart of Tang & Lu's Appendix (general-`N` bridge, `s = ik`): the complex Baxter
factor `Q̂₀(s)` is a **rank-2** perturbation of the identity, so its `N×N` inverse reduces to the
inverse of a fixed `2×2` matrix — Tang & Lu's "one disadvantage" (inverse of an arbitrary `n×n`)
made explicit.

This is the **complex-`s` analogue** of the project's real-`z` machinery
(`Q0DetRankTwo`: `fFun`/`gFun`/`Umat`/`Vmat`/`Q0_mat_phys_eq_one_sub_mul`;
`MixtureQ0Inverse`: `Q0_mat_phys_inv_eq`) — the complexification that the general-`N` bridge needs
(the contour uses complex `s`, while the real-`z` Woodbury objects live over `ℝ`).  Each object here
is the real one with `p1 → φ1`, `p2 → φ2`, `z → s`:

* `fFunC = (2π/Δ)(σᵢ/2·φ1ᵢ + φ2ᵢ)`, `gFunC = (2π/Δ)((½+πξ₂σᵢ/4Δ)φ1ᵢ + (πξ₂/2Δ)φ2ᵢ)` — the two
  Woodbury columns (`fFunC_gFunC_eq` ties `fFunC + gFunC·σⱼ` to the `q0_entry_c` combination);
* `UmatC` (`N×2`), `VmatC` (`2×N`) with `UmatC i k = √ρᵢ e^{sσᵢ/2}(fFunC | gFunC)`,
  `VmatC k j = √ρⱼ e^{−sσⱼ/2}(1 | σⱼ)`;
* **`Q0_mat_c_phys_eq_one_sub_mul`** : `Q̂₀(s) = I − UₒVₒ` (the rank-2 fact, complex `s`);
* **`det_Q0_mat_c_phys_eq_two_by_two`** : `det Q̂₀(s) = det(I − VₒUₒ)` (a fixed `2×2` for every `N`,
  via `Matrix.det_one_sub_mul_comm`);
* **`Q0_mat_c_phys_inv_eq`** : `[Q̂₀(s)]⁻¹ = I + Uₒ(I − VₒUₒ)⁻¹Vₒ` — the Woodbury inverse,
  **conditional on `det Q̂₀(s) ≠ 0`** (the complex `2×2` can be singular at the HS poles, unlike
  real `z` where `det ≥ 1`; `Q0DetContourOrientation` gives non-vanishing on the contour region).

**What remains for the literal Appendix bridge** (`detTL`/`Wtl` of `AppendixWDet`): expand the
complex `2×2` `(I − VₒUₒ)⁻¹ = adj/det` and match its entries to `2π√(ρρ)Wtl e^{−sλ}/(Δ detTL)` —
scalar algebra with the `φ2 = φ1/s + σ²/2s` identity.  This file supplies everything up to that
final match; the `N = 1` case of the match is `AppendixBridgeN1` (`bridge_N1`, `detTL_eq_q0_N1`).

All axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Complex Matrix

namespace FMSA.ComplexRankTwo

open FMSA.MatrixQ0 FMSA.Q0Complex FMSA.MixtureNoSpinodal

/-- Complex quadratic-pole kernel `φ1(σ,s) = (1 − sσ − e^{−sσ})/s²` (the `q0_entry_c` `p1` term). -/
noncomputable def p1c (s σ : ℂ) : ℂ := (1 - s * σ - Complex.exp (-(s * σ))) / s ^ 2

/-- Complex cubic-pole kernel `φ2(σ,s) = (1 − sσ + (sσ)²/2 − e^{−sσ})/s³` (`q0_entry_c`'s `p2`). -/
noncomputable def p2c (s σ : ℂ) : ℂ :=
  (1 - s * σ + (s * σ) ^ 2 / 2 - Complex.exp (-(s * σ))) / s ^ 3

/-- First Woodbury column `fFunC = (2π/Δ)(σᵢ/2·φ1ᵢ + φ2ᵢ)` (complex-`s` `fFun`). -/
noncomputable def fFunC {N : ℕ} (rho sigma : Fin N → ℝ) (i : Fin N) (s : ℂ) : ℂ :=
  ((Real.pi / vacMix rho sigma : ℝ) : ℂ)
    * (p1c s (sigma i) * (sigma i : ℂ) + 2 * p2c s (sigma i))

/-- Second Woodbury column `gFunC = (π/Δ)φ1ᵢ + (π²ξ₂/Δ²)(σᵢ/2·φ1ᵢ + φ2ᵢ)` (complex-`s` `gFun`). -/
noncomputable def gFunC {N : ℕ} (rho sigma : Fin N → ℝ) (i : Fin N) (s : ℂ) : ℂ :=
  ((Real.pi / vacMix rho sigma : ℝ) : ℂ) * p1c s (sigma i)
    + ((Real.pi ^ 2 * xi2 rho sigma / vacMix rho sigma ^ 2 : ℝ) : ℂ)
        * (p1c s (sigma i) * (sigma i : ℂ) / 2 + p2c s (sigma i))

/-- Complex analogue of `fFun_gFun_eq`: the `fFunC + gFunC·σⱼ` column combination equals the
`Q0phys·φ1 + Qppphys·φ2` combination inside `q0_entry_c`.  `field_simp; ring` over `ℂ`. -/
theorem fFunC_gFunC_eq {N : ℕ} {sigma rho : Fin N → ℝ} (i j : Fin N) (s : ℂ)
    (hs : s ≠ 0) (hvac : vacMix rho sigma ≠ 0) :
    fFunC rho sigma i s + gFunC rho sigma i s * (sigma j : ℂ) =
    (Q0phys rho sigma i j : ℂ) * p1c s (sigma i)
      + (Qppphys rho sigma i j : ℂ) * p2c s (sigma i) := by
  have hvacC : (vacMix rho sigma : ℂ) ≠ 0 := by exact_mod_cast hvac
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hs3 : s ^ 3 ≠ 0 := pow_ne_zero 3 hs
  simp only [fFunC, gFunC, p1c, p2c, Q0phys, Qppphys]
  push_cast
  field_simp
  ring

/-- Woodbury left factor `Uₒ` (`N×2`, complex `s`): `Uₒ i 0 = √ρᵢ e^{sσᵢ/2} fFunC`,
`Uₒ i 1 = √ρᵢ e^{sσᵢ/2} gFunC`. -/
noncomputable def UmatC {N : ℕ} (s : ℂ) (sigma rho : Fin N → ℝ) : Matrix (Fin N) (Fin 2) ℂ :=
  fun i k => (Real.sqrt (rho i) : ℂ) * Complex.exp (s * (sigma i : ℂ) / 2) *
    (if k = 0 then fFunC rho sigma i s else gFunC rho sigma i s)

/-- Woodbury right factor `Vₒ` (`2×N`, complex `s`): `Vₒ 0 j = √ρⱼ e^{−sσⱼ/2}`,
`Vₒ 1 j = √ρⱼ e^{−sσⱼ/2} σⱼ`. -/
noncomputable def VmatC {N : ℕ} (s : ℂ) (sigma rho : Fin N → ℝ) : Matrix (Fin 2) (Fin N) ℂ :=
  fun k j => (Real.sqrt (rho j) : ℂ) * Complex.exp (-(s * (sigma j : ℂ) / 2)) *
    (if k = 0 then 1 else (sigma j : ℂ))

/-- Complex analogue of `UV_apply`: `(UₒVₒ) i j` with the `√ρᵢ√ρⱼ` and `exp` factors merged
(`Real.sqrt_mul`, `Complex.exp_add` — the only non-`ring` step). -/
theorem UV_apply_C {N : ℕ} (s : ℂ) (sigma rho : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i)
    (i j : Fin N) :
    (UmatC s sigma rho * VmatC s sigma rho) i j =
    (Real.sqrt (rho i * rho j) : ℂ)
      * Complex.exp (-(((sigma j : ℂ) - (sigma i : ℂ)) / 2 * s))
      * (fFunC rho sigma i s + gFunC rho sigma i s * (sigma j : ℂ)) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, UmatC, VmatC, Fin.isValue]
  norm_num
  rw [show (Real.sqrt (rho i * rho j) : ℂ) = (Real.sqrt (rho i) : ℂ) * (Real.sqrt (rho j) : ℂ) by
        rw [← Complex.ofReal_mul, Real.sqrt_mul (hrho i)],
      show Complex.exp (-(((sigma j : ℂ) - (sigma i : ℂ)) / 2 * s))
          = Complex.exp (s * (sigma i : ℂ) / 2) * Complex.exp (-(s * (sigma j : ℂ) / 2)) by
        rw [← Complex.exp_add]; ring_nf]
  ring

/-- **Complex rank-2 decomposition of `Q̂₀(s)`** (general `N`, complex `s`).  The complex-`s`
analogue of `Q0_mat_phys_eq_one_sub_mul`: `Q̂₀(s) = I − UₒVₒ`, `Uₒ` `N×2`, `Vₒ` `2×N`.  Requires
`s ≠ 0`, `Δ ≠ 0`, `ρ ≥ 0` (the last for `√(ρᵢρⱼ) = √ρᵢ√ρⱼ`). -/
theorem Q0_mat_c_phys_eq_one_sub_mul {N : ℕ} {sigma rho : Fin N → ℝ} {s : ℂ}
    (hs : s ≠ 0) (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i) :
    Q0_mat_c_phys s sigma rho = 1 - UmatC s sigma rho * VmatC s sigma rho := by
  funext i j
  rw [Matrix.sub_apply, Matrix.one_apply, UV_apply_C s sigma rho hrho i j,
      fFunC_gFunC_eq i j s hs hvac]
  simp only [Q0_mat_c_phys, Q0_mat_c, q0_entry_c, p1c, p2c, rhoGeoPhys]

/-- **`det Q̂₀(s) = det(I − VₒUₒ)`**, a fixed `2×2` for all `N` (`Matrix.det_one_sub_mul_comm`). -/
theorem det_Q0_mat_c_phys_eq_two_by_two {N : ℕ} {sigma rho : Fin N → ℝ} {s : ℂ}
    (hs : s ≠ 0) (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i) :
    (Q0_mat_c_phys s sigma rho).det
      = (1 - VmatC s sigma rho * UmatC s sigma rho).det := by
  rw [Q0_mat_c_phys_eq_one_sub_mul hs hvac hrho]
  exact Matrix.det_one_sub_mul_comm _ _

/-- **Complex Woodbury right inverse** — `Q̂₀(s) · (I + Uₒ(I−VₒUₒ)⁻¹Vₒ) = I`.  The complex-`s`
analogue of `Q0_mat_phys_inv_closed_form`; invertibility of the `2×2` `I−VₒUₒ` (= `det Q̂₀(s) ≠ 0`)
is now a **hypothesis** (the complex `2×2` can be singular at the HS poles, unlike real `z` where
`det ≥ 1`). -/
theorem Q0_mat_c_phys_inv_closed_form {N : ℕ} {sigma rho : Fin N → ℝ} {s : ℂ}
    (hs : s ≠ 0) (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i)
    (hdet : IsUnit (Q0_mat_c_phys s sigma rho).det) :
    (Q0_mat_c_phys s sigma rho) *
      (1 + UmatC s sigma rho * (1 - VmatC s sigma rho * UmatC s sigma rho)⁻¹
        * VmatC s sigma rho) = 1 := by
  have heq : (Q0_mat_c_phys s sigma rho).det
      = (1 - VmatC s sigma rho * UmatC s sigma rho).det :=
    det_Q0_mat_c_phys_eq_two_by_two hs hvac hrho
  have hdet2 : IsUnit (1 - VmatC s sigma rho * UmatC s sigma rho).det := heq ▸ hdet
  rw [Q0_mat_c_phys_eq_one_sub_mul hs hvac hrho]
  set U := UmatC s sigma rho
  set V := VmatC s sigma rho
  set W := (1 - V * U)⁻¹ with hWdef
  have hVU : (1 - V * U) * W = 1 := Matrix.mul_nonsing_inv _ hdet2
  have expand : (1 - U * V) * (1 + U * W * V)
      = 1 - U * V + U * ((1 - V * U) * W) * V := by
    simp only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one]
  rw [expand, hVU, Matrix.mul_one]
  abel

/-- **Closed-form complex inverse** `[Q̂₀(s)]⁻¹ = I + Uₒ(I−VₒUₒ)⁻¹Vₒ` (general `N`, complex `s`,
`det Q̂₀(s) ≠ 0`).  Tang & Lu's Appendix Woodbury inverse — the "unique difficulty" (inverse of an
arbitrary `n×n` reduced to a fixed `2×2`) — for the complex contour argument. -/
theorem Q0_mat_c_phys_inv_eq {N : ℕ} {sigma rho : Fin N → ℝ} {s : ℂ}
    (hs : s ≠ 0) (hvac : vacMix rho sigma ≠ 0) (hrho : ∀ i, 0 ≤ rho i)
    (hdet : IsUnit (Q0_mat_c_phys s sigma rho).det) :
    (Q0_mat_c_phys s sigma rho)⁻¹
      = 1 + UmatC s sigma rho * (1 - VmatC s sigma rho * UmatC s sigma rho)⁻¹
          * VmatC s sigma rho :=
  Matrix.inv_eq_right_inv (Q0_mat_c_phys_inv_closed_form hs hvac hrho hdet)

end FMSA.ComplexRankTwo
