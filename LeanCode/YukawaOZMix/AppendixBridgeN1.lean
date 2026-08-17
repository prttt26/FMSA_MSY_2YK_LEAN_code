/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.AppendixWDet
import LeanCode.HSMixture.Q0Complex
import LeanCode.HSMixture.MatrixQ0

/-!
# The Appendix bridge at `N = 1` — `[Q̂₀]⁻¹ = 1 + 2π√(ρρ)W/(Δ det)` (scalar case)

The final connective piece of Tang & Lu's residue programme: their inverse formula
`{[Q̂₀(k)]⁻¹}ᵢⱼ = δᵢⱼ + 2π(ρᵢρⱼ)^{1/2}Wᵢⱼ(ik)/(Δ det(ik))·e^{−ikλᵢⱼ}` ties the explicit
`Wtl`/`detTL` (bounded in `AppendixWDet`) to the *actual* Baxter inverse.  Here it is proved for
`N = 1`, where the matrix is scalar (`det = q0`, `λ₀₀ = 0`) so the bridge is one algebraic identity.

**Why `N = 1` closes to `ring`.**  At `N = 1` the two `∑ₘ` terms of `Wtl` vanish
(`(Rₘ − Rᵢ) = 0`), so `Wtl₀₀ = φ₂(σ₀)(1+πξ₃/2Δ) + φ₁(σ₀)(σ₀ + πξ₂σ₀²/4Δ)`, and `q0_entry_c` with
`λ₀₀ = 0` is `1 − √(ρ₀²)(Q'·φ₁(σ₀) + Q''·φ₂(σ₀))`.  Both sides are `1 − (c₁φ₁ + c₂φ₂)`, and the PY
coefficients are *exactly* Tang & Lu's `W` coefficients — `ρ₀·Q''phys = 2πρ₀(1+2η)/vac²` matches the
`φ₂` coefficient, `ρ₀·Q'phys = 2πρ₀(σ₀+πξ₂σ₀²/4vac)/vac` the `φ₁` one — with `Δ = vacMix = 1−η`
(`Delta ρ σ = vacMix ρ σ` by definition).  So after unfolding, evaluating the `Fin 1` sums, and
`field_simp` (clearing `s²`, `s³`, `vac`), it is `ring`-true.  Axiom-clean.

`bridge_N1` states it as `q0 = 1 − 2π√(ρρ)W₀₀/Δ` (the Baxter-factor form); `bridge_N1_inv`
rearranges to the inverse form `q0⁻¹ = 1 + 2π√(ρρ)W₀₀/(Δ·q0)`; and `detTL_eq_q0_N1` matches the
denominator (`detTL = q0 = det Q̂₀`) — so at `N = 1` **both** the `W` numerator and the `det`
denominator are tied to the actual objects: `[Q̂₀]⁻¹ = 1 + 2π√(ρρ)W₀₀/(Δ·detTL)`, `detTL = det Q̂₀`.

**Remaining (general `N`):** the same for the `N×N` Woodbury inverse `[Q̂₀]⁻¹ = I + U(I−VU)⁻¹V`
(`Q0_mat_phys_inv_eq`) — Tang & Lu's Appendix A2–A7, computing the `2×2` inverse `(I−VU)⁻¹` and
matching its entries to `2π√(ρρ)W/(Δ det)·e^{−ikλ}`.  This is a whole-appendix algebraic derivation
*and* requires complexifying the project's real-`z` rank-2/Woodbury machinery (`Umat`/`Vmat`,
`Q0_mat_phys_eq_one_sub_mul`) to the complex argument `s = ik` the contour uses.  `N = 1` is the
scalar base case (no `2×2` inverse), which is why it closes to `ring`.
-/

set_option linter.style.longLine false

open Complex

namespace FMSA.MixtureRDF

open FMSA.MatrixQ0 FMSA.Q0Complex FMSA.MixtureArcBound

/-- **Appendix bridge, `N = 1` (Baxter-factor form).**  The scalar Baxter factor `q0` equals
`1 − 2π√(ρ₀ρ₀)·W₀₀/Δ` — the `N = 1` case of Tang & Lu's inverse formula (the physical PY
coefficients `Q'phys`, `Q''phys` are precisely the `Wtl` coefficients; `Δ = vacMix`). -/
theorem bridge_N1 {sigma rho : Fin 1 → ℝ} (s : ℂ) (hs : s ≠ 0) (hvac : vacMix rho sigma ≠ 0) :
    q0_entry_c s (sigma 0) 0 (Q0phys rho sigma 0 0) (Qppphys rho sigma 0 0) (rhoGeoPhys rho 0 0) 1
      = 1 - 2 * Real.pi * (rhoGeoPhys rho 0 0 : ℂ) * Wtl s rho sigma 0 0 / (vacMix rho sigma : ℂ) := by
  have hvacC : (vacMix rho sigma : ℂ) ≠ 0 := by exact_mod_cast hvac
  have hDvac : (Delta rho sigma : ℂ) = (vacMix rho sigma : ℂ) := by norm_cast
  simp only [q0_entry_c, Wtl, phi1, phi2, Q0phys, Qppphys, rhoGeoPhys, xi2, xiMom,
    Fin.sum_univ_one, zero_mul, mul_zero, neg_zero, Complex.exp_zero, sub_self, hDvac]
  push_cast
  field_simp
  ring

/-- **Appendix bridge, `N = 1` (inverse form).**  The actual Tang & Lu bridge at `N = 1`:
`[Q̂₀]⁻¹ = q0⁻¹ = 1 + 2π√(ρρ)W₀₀/(Δ·det)` with `det = q0` (scalar).  From `bridge_N1` by
division. -/
theorem bridge_N1_inv {sigma rho : Fin 1 → ℝ} (s : ℂ) (hs : s ≠ 0) (hvac : vacMix rho sigma ≠ 0)
    (hq0 : q0_entry_c s (sigma 0) 0 (Q0phys rho sigma 0 0) (Qppphys rho sigma 0 0) (rhoGeoPhys rho 0 0) 1 ≠ 0) :
    (q0_entry_c s (sigma 0) 0 (Q0phys rho sigma 0 0) (Qppphys rho sigma 0 0) (rhoGeoPhys rho 0 0) 1)⁻¹
      = 1 + 2 * Real.pi * (rhoGeoPhys rho 0 0 : ℂ) * Wtl s rho sigma 0 0
          / ((vacMix rho sigma : ℂ)
              * q0_entry_c s (sigma 0) 0 (Q0phys rho sigma 0 0) (Qppphys rho sigma 0 0) (rhoGeoPhys rho 0 0) 1) := by
  have hvacC : (vacMix rho sigma : ℂ) ≠ 0 := by exact_mod_cast hvac
  have hb := bridge_N1 s hs hvac
  field_simp
  rw [eq_comm, mul_comm]
  field_simp at hb
  linear_combination hb

/-- **The `N=1` denominator match — `detTL` is the actual determinant.**  At `N=1` the Tang & Lu det
formula `detTL` equals the scalar Baxter factor `q0 = det Q̂₀` (`√(ρ₀²) = ρ₀`, `ρ₀ ≥ 0`).  With
`bridge_N1_inv` this closes the `N=1` bridge to the *actual* objects:
`[Q̂₀]⁻¹ = 1 + 2π√(ρρ)W₀₀/(Δ·detTL)` with `detTL = det Q̂₀`. -/
theorem detTL_eq_q0_N1 {sigma rho : Fin 1 → ℝ} (s : ℂ) (hs : s ≠ 0) (hvac : vacMix rho sigma ≠ 0)
    (hrho : 0 ≤ rho 0) :
    detTL s rho sigma
      = q0_entry_c s (sigma 0) 0 (Q0phys rho sigma 0 0) (Qppphys rho sigma 0 0) (rhoGeoPhys rho 0 0) 1 := by
  have hvacC : (vacMix rho sigma : ℂ) ≠ 0 := by exact_mod_cast hvac
  have hDvac : (Delta rho sigma : ℂ) = (vacMix rho sigma : ℂ) := by norm_cast
  have hsqrt : (rhoGeoPhys rho 0 0 : ℝ) = rho 0 := by
    simp only [rhoGeoPhys]; rw [Real.sqrt_mul_self hrho]
  simp only [q0_entry_c, detTL, phi1, phi2, Q0phys, Qppphys, xi2, xiMom, hsqrt,
    Fin.sum_univ_one, zero_mul, neg_zero, Complex.exp_zero, sub_self, hDvac]
  push_cast
  field_simp
  ring

end FMSA.MixtureRDF
