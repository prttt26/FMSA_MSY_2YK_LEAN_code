/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterDiluteDecay
import LeanCode.HardSphere.BaxterWienerHopfComplex

/-!
# Dilute-regime PY-HS symbol positivity ("no spinodal") — Task BAXTER.16, dilute case

For real `k ≠ 0` the Wiener–Hopf factorization (`baxter_wiener_hopf_factorization`) gives the
**real** identity

  `1 - ρ·Ĉ(k) = (1 - A(k))² + B(k)²`,  `A(k) = ∫₀^σ q0 cos(kr)`, `B(k) = ∫₀^σ q0 sin(kr)`.

In the dilute regime `M := ∫₀^σ|q0| < 1` (`η < (3-√7)/2`, `q0AbsL1_lt_one_of_dilute`) the cosine
transform is bounded `|A(k)| ≤ M < 1`, so `1 - A(k) ≥ 1 - M > 0` and hence
`1 - ρ·Ĉ(k) ≥ (1-M)² > 0` — the PY hard-sphere structure factor `S(k) = 1/(1-ρĈ)` is finite at
every nonzero wavevector = **no spinodal** (in the dilute regime).

* `q0_cos_transform_abs_le` — `|∫₀^σ q0 cos(kr)| ≤ M` (the Fourier-cosine bound).
* `one_sub_rho_radial_fourier_c_HS_ge_of_dilute` (`{_all}`) — the **uniform** lower bound
  `(1-M)² ≤ 1 - ρ·Ĉ(k)` (`k ≠ 0`, resp. all `k`).
* `one_sub_rho_radial_fourier_c_HS_pos_of_dilute` (`{_all}`) — `0 < 1 - ρ·Ĉ(k)`, the structure-
  factor positivity.
* `hs_symbol_coercive_of_dilute` — `∃ ε > 0, ∀ k, ε ≤ 1 - ρ·Ĉ(k)` (`ε = (1-M)²`): the exact
  coercivity (`haε`) hypothesis of `FMSA.wienerHopf_positive_symbol_injective` (MA.12,
  `Analysis/WienerHopf.lean`).  This closes the *coercivity* gap toward retiring
  `oz_fixed_pt_unique` in the dilute regime; the remaining gaps (routine measurability + global
  sup bound on the symbol, and the substantive OZ ↔ half-line-WH operator identification /
  3D-radial ↔ 1D reduction) are documented on that theorem and out of scope here.

**Caveat at `k=0`:** the `radial_fourier` object carries a `1/k` factor, so its Lean value at
`k=0` is the junk `0` (not the physical PY compressibility `(1+2η)²/(1-η)⁴`); the `∀ k` statements
hold there trivially (`1 - ρ·0 = 1`) but do NOT assert the compressibility — a separate (also
positive) fact about the genuine `k→0` limit, out of scope.

Full `η < 1` symbol positivity is research-scale (the coupled Re/Im positivity of an explicit
trig-rational — no `L¹` shortcut for `η ≳ 0.177`); see `proof_notes_baxter.md` BAXTER.16 and the
complex root-location task `POLE.11`.
-/

open MeasureTheory Set Real Filter Topology intervalIntegral

namespace FMSA.HardSphere

noncomputable section

/-- **Fourier-cosine bound.** `|∫₀^σ q0_poly·cos(kr)| ≤ ∫₀^σ|q0_poly| = M`, since `|cos| ≤ 1`. -/
theorem q0_cos_transform_abs_le {eta sigma rho k : ℝ} (hsigma : 0 < sigma) :
    |∫ r in (0:ℝ)..sigma, q0_poly eta sigma rho r * Real.cos (k * r)|
      ≤ q0AbsL1 eta sigma rho := by
  calc |∫ r in (0:ℝ)..sigma, q0_poly eta sigma rho r * Real.cos (k * r)|
      ≤ ∫ r in (0:ℝ)..sigma, |q0_poly eta sigma rho r * Real.cos (k * r)| := by
        have := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hsigma.le
          (f := fun r => q0_poly eta sigma rho r * Real.cos (k * r))
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∫ r in (0:ℝ)..sigma, |q0_poly eta sigma rho r| := by
        apply intervalIntegral.integral_mono_on hsigma.le
        · exact (((q0_poly_continuous eta sigma rho).mul
            (Real.continuous_cos.comp (continuous_const.mul continuous_id))).abs).intervalIntegrable
            _ _
        · exact ((q0_poly_continuous eta sigma rho).abs).intervalIntegrable _ _
        · intro r _
          rw [abs_mul]
          calc |q0_poly eta sigma rho r| * |Real.cos (k * r)|
              ≤ |q0_poly eta sigma rho r| * 1 :=
                mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
            _ = |q0_poly eta sigma rho r| := mul_one _
    _ = q0AbsL1 eta sigma rho := rfl

/-- **PY-HS symbol UNIFORM lower bound, dilute regime, `k ≠ 0`.**
`(1 - M)² ≤ 1 - ρ·Ĉ(k)` for all `η < (3-√7)/2`, `M := ∫₀^σ|q0| < 1`.  Via the real Wiener–Hopf
factorization `1 - ρĈ(k) = (1-A)² + B²` and `A ≤ |A| ≤ M`: `1 - A ≥ 1 - M`, and
`(1-A)² - (1-M)² = (M-A)(2-A-M) ≥ 0`.  This uniform bound (not just pointwise `> 0`) is what a
coercivity/Wiener–Hopf argument needs (`ε := (1-M)²`). -/
theorem one_sub_rho_radial_fourier_c_HS_ge_of_dilute {eta sigma rho : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 ≤ rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (hdilute : eta < (3 - Real.sqrt 7) / 2)
    {k : ℝ} (hk : k ≠ 0) :
    (1 - q0AbsL1 eta sigma rho) ^ 2 ≤ 1 - rho * radial_fourier (c_HS eta sigma) k := by
  have hM : q0AbsL1 eta sigma rho < 1 :=
    q0AbsL1_lt_one_of_dilute heta0 heta1 hsigma hrho heta_def hdilute
  rw [← baxter_wiener_hopf_factorization eta sigma rho k hsigma hk heta1 heta_def]
  set A := ∫ r in (0:ℝ)..sigma, q0_poly eta sigma rho r * Real.cos (k * r) with hAdef
  set B := ∫ r in (0:ℝ)..sigma, q0_poly eta sigma rho r * Real.sin (k * r) with hBdef
  have hA : A ≤ q0AbsL1 eta sigma rho := le_of_abs_le (q0_cos_transform_abs_le hsigma)
  have hAM : (0:ℝ) ≤ q0AbsL1 eta sigma rho - A := by linarith
  have h2AM : (0:ℝ) ≤ 2 - A - q0AbsL1 eta sigma rho := by linarith
  nlinarith [sq_nonneg B, mul_nonneg hAM h2AM]

/-- **PY-HS symbol positivity, dilute regime, `k ≠ 0`.** `0 < 1 - ρ·Ĉ(k)` for all `η < (3-√7)/2`.
Immediate from the uniform lower bound `(1-M)² ≤ 1-ρĈ` and `0 < (1-M)²`. -/
theorem one_sub_rho_radial_fourier_c_HS_pos_of_dilute {eta sigma rho : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 ≤ rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (hdilute : eta < (3 - Real.sqrt 7) / 2)
    {k : ℝ} (hk : k ≠ 0) :
    0 < 1 - rho * radial_fourier (c_HS eta sigma) k := by
  have hM : q0AbsL1 eta sigma rho < 1 :=
    q0AbsL1_lt_one_of_dilute heta0 heta1 hsigma hrho heta_def hdilute
  have hpos : 0 < (1 - q0AbsL1 eta sigma rho) ^ 2 := pow_pos (by linarith) 2
  have := one_sub_rho_radial_fourier_c_HS_ge_of_dilute heta0 heta1 hsigma hrho heta_def hdilute hk
  linarith

/-- **PY-HS symbol UNIFORM lower bound, dilute regime, all `k`.** `(1-M)² ≤ 1 - ρ·Ĉ(k)` for every
`k`.  For `k ≠ 0` this is the structure-factor bound; at `k = 0` the `radial_fourier` object is the
junk value `0` (its `1/k` factor), so the LHS `(1-M)² ≤ 1` holds trivially — the statement there
does *not* assert the physical PY compressibility (see module docstring). -/
theorem one_sub_rho_radial_fourier_c_HS_ge_of_dilute_all {eta sigma rho : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 ≤ rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (hdilute : eta < (3 - Real.sqrt 7) / 2)
    (k : ℝ) :
    (1 - q0AbsL1 eta sigma rho) ^ 2 ≤ 1 - rho * radial_fourier (c_HS eta sigma) k := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    have hM : q0AbsL1 eta sigma rho < 1 :=
      q0AbsL1_lt_one_of_dilute heta0 heta1 hsigma hrho heta_def hdilute
    have hMnn : 0 ≤ q0AbsL1 eta sigma rho := q0AbsL1_nonneg hsigma
    have hzero : radial_fourier (c_HS eta sigma) 0 = 0 := by
      unfold radial_fourier
      have hint : ∫ r in Set.Ioi (0:ℝ), r * c_HS eta sigma r * Real.sin (0 * r) = 0 := by simp
      rw [hint, mul_zero]
    rw [hzero, mul_zero, sub_zero]
    nlinarith [hM, hMnn]
  · exact one_sub_rho_radial_fourier_c_HS_ge_of_dilute heta0 heta1 hsigma hrho heta_def hdilute hk

/-- **PY-HS symbol positivity, dilute regime, all `k`.**  `0 < 1 - ρ·Ĉ(k)` for every `k` (`k=0` is
the junk-encoding `1 > 0`; see module docstring). -/
theorem one_sub_rho_radial_fourier_c_HS_pos_of_dilute_all {eta sigma rho : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 ≤ rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (hdilute : eta < (3 - Real.sqrt 7) / 2)
    (k : ℝ) :
    0 < 1 - rho * radial_fourier (c_HS eta sigma) k := by
  have hM : q0AbsL1 eta sigma rho < 1 :=
    q0AbsL1_lt_one_of_dilute heta0 heta1 hsigma hrho heta_def hdilute
  have hpos : 0 < (1 - q0AbsL1 eta sigma rho) ^ 2 := pow_pos (by linarith) 2
  have := one_sub_rho_radial_fourier_c_HS_ge_of_dilute_all heta0 heta1 hsigma hrho heta_def
    hdilute k
  linarith

/-- **The MA.12 coercivity input for the HS symbol, dilute regime.**
`∃ ε > 0, ∀ k, ε ≤ 1 - ρ·Ĉ(k)` — the exact `haε` hypothesis of
`FMSA.wienerHopf_positive_symbol_injective` (`Analysis/WienerHopf.lean`), with `ε = (1-M)²`.

**Interface note (what this does and does not give).** MA.12 concludes injectivity of the
half-line Wiener–Hopf operator `T_a` for a real symbol `a` satisfying (i) measurable, (ii) bounded
`|a| ≤ M_sup`, (iii) coercive `ε ≤ a`.  This theorem supplies **(iii)** — the substantive,
regime-dependent input — for `a k := 1 - ρ·radial_fourier (c_HS) k`.  Still missing before MA.12
could retire `oz_fixed_pt_unique` in the dilute regime: (i)/(ii) (routine measurability + a global
sup bound on `a`, the latter needing the genuine `k→0` value in place of the junk `0`), and — the
real work — the **operator identification** casting the difference of two bounded `OzFixedPt`s as
an `L²` half-line `u` with `T_a u = 0` (the 3D-radial ↔ 1D reduction, `Q̂` 1D vs `Ĉ` 3D-radial;
cf. `OZFIX.18`).  That bridge is out of scope here; this closes only the coercivity gap. -/
theorem hs_symbol_coercive_of_dilute {eta sigma rho : ℝ} (heta0 : 0 < eta)
    (heta1 : eta < 1) (hsigma : 0 < sigma) (hrho : 0 ≤ rho)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (hdilute : eta < (3 - Real.sqrt 7) / 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ 1 - rho * radial_fourier (c_HS eta sigma) k := by
  have hM : q0AbsL1 eta sigma rho < 1 :=
    q0AbsL1_lt_one_of_dilute heta0 heta1 hsigma hrho heta_def hdilute
  exact ⟨(1 - q0AbsL1 eta sigma rho) ^ 2, pow_pos (by linarith) 2,
    fun k => one_sub_rho_radial_fourier_c_HS_ge_of_dilute_all heta0 heta1 hsigma hrho heta_def
      hdilute k⟩

end

end FMSA.HardSphere
