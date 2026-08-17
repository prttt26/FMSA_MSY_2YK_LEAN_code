/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.Q0ComplexRankTwo
import LeanCode.HSMixture.AppendixWDet

/-!
# Reduction of the Appendix denominator match `det Q̂₀(s) = detTL` to a scalar sum identity

The general-`N` Appendix bridge's **denominator** side: Tang & Lu's explicit `det(s)` formula (A7,
`detTL` of `AppendixWDet`) equals the actual determinant `det Q̂₀(s)`.  Combined with
`Q0ComplexRankTwo.det_Q0_mat_c_phys_eq_two_by_two` (`det Q̂₀(s) = det(I − VₒUₒ)`), this file reduces
`detTL = det Q̂₀(s)` to the **`2×2` scalar identity `det(I − VₒUₒ) = detTL`** and supplies the
ingredients:

* `p1c_eq_phi1`, `p2c_eq_phi2` — the two `φ`-kernel conventions agree (`Q0ComplexRankTwo`'s
  `p1c`/`p2c` = `AppendixWDet`'s `phi1`/`phi2` at a real diameter, `rfl`);
* **`p2c_eq_p1c`** — the Tang & Lu simplifying identity **`φ2 = φ1/s + σ²/(2s)`** (the term-shuffle
  engine: `detTL` and `det(I − VₒUₒ)` are *not* equal as polynomials in independent `{φ1,φ2}`, so it
  is essential — it moves the `φ2`-linear discrepancy into the `φ1φ1` double sum);
* `VU_C_apply` + `VU00`/`VU01`/`VU10`/`VU11` — the four reduced entries `(VₒUₒ)_kl = Σ_p ρ_p (1|σ_p)
  (fFunC|gFunC)` (the exp and `√ρ` factors cancel in the `2×2`);
* **`detVU_expand`** — `det(I − VₒUₒ) = (1 − Σρ fFunC)(1 − Σρσ gFunC) − (Σρ gFunC)(Σρσ fFunC)`,
  Tang & Lu's Appendix **A6** (the `2×2` reduced determinant).

**Remaining (the A6 → A7 scalar closure `det(I − VₒUₒ) = detTL`):** pure scalar sum algebra, checked
numerically (A6 = A7 to `9e-16`, random `N=3`, complex `s`).  The tractable route uses the key
cancellation
`b_q = φ1_q/2 + (πξ₂/2Δ)a_q` (with `fFunC = (2π/Δ)a`, `gFunC = (2π/Δ)b`, `a_p = σ_p/2·φ1_p + φ2_p`),
giving `fFunC_p·gFunC_q − gFunC_p·fFunC_q = (2π²/Δ²)(a_p φ1_q − a_q φ1_p)` — the `ξ₂` terms cancel
antisymmetrically, so the `2×2` double sum has no `ξ₂`.  Then substitute `φ2 = φ1/s + σ²/2s`
(`p2c_eq_p1c`), expand `ξ₃ = Σρσ³` into a sum, and match the single/double sums after a `p↔q`
reindex.  A whole-Appendix Finset derivation — the "tedious algebraic work" Tang & Lu name.

All lemmas here axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Complex Matrix

namespace FMSA.ComplexRankTwo

open FMSA.MatrixQ0 FMSA.Q0Complex FMSA.MixtureNoSpinodal FMSA.MixtureArcBound

/-- `p1c` (`Q0ComplexRankTwo`) = `phi1` (`AppendixWDet`) at a real diameter. -/
theorem p1c_eq_phi1 (s : ℂ) (R : ℝ) : p1c s (R : ℂ) = phi1 s R := rfl

/-- `p2c` (`Q0ComplexRankTwo`) = `phi2` (`AppendixWDet`) at a real diameter. -/
theorem p2c_eq_phi2 (s : ℂ) (R : ℝ) : p2c s (R : ℂ) = phi2 s R := rfl

/-- **The Tang & Lu simplifying identity `φ2 = φ1/s + σ²/(2s)`** (the `AppendixWDet` `φ2 = φ1/s +
R²/2s` relation).  This is the term-shuffle engine of the A6 → A7 (`det(I−VₒUₒ) = detTL`) match:
`det(I−VₒUₒ)` and `detTL` are not equal as polynomials in independent `{φ1,φ2}`; the identity moves
the `φ2`-linear discrepancy into the `φ1φ1` double sum. -/
theorem p2c_eq_p1c (s σ : ℂ) (hs : s ≠ 0) : p2c s σ = p1c s σ / s + σ ^ 2 / (2 * s) := by
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hs3 : s ^ 3 ≠ 0 := pow_ne_zero 3 hs
  simp only [p1c, p2c]
  field_simp
  ring

/-- The reduced `2×2` entry `(VₒUₒ)_kl = Σ_p ρ_p (1|σ_p)(fFunC|gFunC)` — the exp and `√ρ` factors of
`Uₒ`/`Vₒ` cancel (`Real.mul_self_sqrt`, `Complex.exp_add`). -/
theorem VU_C_apply {N : ℕ} (s : ℂ) (sigma rho : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i) (k l : Fin 2) :
    (VmatC s sigma rho * UmatC s sigma rho) k l =
    ∑ p, (rho p : ℂ) * (if k = 0 then 1 else (sigma p : ℂ))
          * (if l = 0 then fFunC rho sigma p s else gFunC rho sigma p s) := by
  simp only [Matrix.mul_apply, VmatC, UmatC]
  apply Finset.sum_congr rfl
  intro p _
  have hrr : (Real.sqrt (rho p) : ℂ) * (Real.sqrt (rho p) : ℂ) = (rho p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hrho p)]
  have hee : Complex.exp (-(s * (sigma p : ℂ) / 2)) * Complex.exp (s * (sigma p : ℂ) / 2) = 1 := by
    rw [← Complex.exp_add,
      show -(s * (sigma p : ℂ) / 2) + s * (sigma p : ℂ) / 2 = 0 by ring, Complex.exp_zero]
  calc (Real.sqrt (rho p) : ℂ) * Complex.exp (-(s * (sigma p : ℂ) / 2))
          * (if k = 0 then 1 else (sigma p : ℂ))
        * ((Real.sqrt (rho p) : ℂ) * Complex.exp (s * (sigma p : ℂ) / 2)
          * (if l = 0 then fFunC rho sigma p s else gFunC rho sigma p s))
      = ((Real.sqrt (rho p) : ℂ) * (Real.sqrt (rho p) : ℂ))
          * (Complex.exp (-(s * (sigma p : ℂ) / 2)) * Complex.exp (s * (sigma p : ℂ) / 2))
          * ((if k = 0 then 1 else (sigma p : ℂ))
              * (if l = 0 then fFunC rho sigma p s else gFunC rho sigma p s)) := by ring
    _ = (rho p : ℂ) * (if k = 0 then 1 else (sigma p : ℂ))
          * (if l = 0 then fFunC rho sigma p s else gFunC rho sigma p s) := by
        rw [hrr, hee]; ring

/-- `(VₒUₒ)₀₀ = Σ_p ρ_p fFunC_p`. -/
theorem VU00 {N : ℕ} (s : ℂ) (sigma rho : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i) :
    (VmatC s sigma rho * UmatC s sigma rho) 0 0 = ∑ p, (rho p : ℂ) * fFunC rho sigma p s := by
  rw [VU_C_apply s sigma rho hrho]; apply Finset.sum_congr rfl; intro p _; simp

/-- `(VₒUₒ)₀₁ = Σ_p ρ_p gFunC_p`. -/
theorem VU01 {N : ℕ} (s : ℂ) (sigma rho : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i) :
    (VmatC s sigma rho * UmatC s sigma rho) 0 1 = ∑ p, (rho p : ℂ) * gFunC rho sigma p s := by
  rw [VU_C_apply s sigma rho hrho]; apply Finset.sum_congr rfl; intro p _; simp

/-- `(VₒUₒ)₁₀ = Σ_p ρ_p σ_p fFunC_p`. -/
theorem VU10 {N : ℕ} (s : ℂ) (sigma rho : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i) :
    (VmatC s sigma rho * UmatC s sigma rho) 1 0
      = ∑ p, (rho p : ℂ) * (sigma p : ℂ) * fFunC rho sigma p s := by
  rw [VU_C_apply s sigma rho hrho]; apply Finset.sum_congr rfl; intro p _; simp

/-- `(VₒUₒ)₁₁ = Σ_p ρ_p σ_p gFunC_p`. -/
theorem VU11 {N : ℕ} (s : ℂ) (sigma rho : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i) :
    (VmatC s sigma rho * UmatC s sigma rho) 1 1
      = ∑ p, (rho p : ℂ) * (sigma p : ℂ) * gFunC rho sigma p s := by
  rw [VU_C_apply s sigma rho hrho]; apply Finset.sum_congr rfl; intro p _; simp

/-- **`det(I − VₒUₒ)` = Tang & Lu Appendix A6** — the reduced `2×2` Baxter determinant expanded into
the four ρ-weighted `fFunC`/`gFunC` sums:
`(1 − Σρ fFunC)(1 − Σρσ gFunC) − (Σρ gFunC)(Σρσ fFunC)`.  The A7 form (`detTL`) follows from this by
the scalar sum algebra documented in the module header (numerically A6 = A7 to `9e-16`). -/
theorem detVU_expand {N : ℕ} {sigma rho : Fin N → ℝ} {s : ℂ} (hrho : ∀ i, 0 ≤ rho i) :
    (1 - VmatC s sigma rho * UmatC s sigma rho).det =
      (1 - ∑ p, (rho p : ℂ) * fFunC rho sigma p s)
        * (1 - ∑ p, (rho p : ℂ) * (sigma p : ℂ) * gFunC rho sigma p s)
      - (∑ p, (rho p : ℂ) * gFunC rho sigma p s)
        * (∑ p, (rho p : ℂ) * (sigma p : ℂ) * fFunC rho sigma p s) := by
  rw [Matrix.det_fin_two, Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply,
      Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), Matrix.one_apply_eq,
      VU00 s sigma rho hrho, VU01 s sigma rho hrho, VU10 s sigma rho hrho, VU11 s sigma rho hrho]
  ring

end FMSA.ComplexRankTwo
