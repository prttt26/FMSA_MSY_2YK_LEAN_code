/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The cancellation-tamed `A(−iy)` numerator bound (item (iii) of the `A(−iy)` wiring)

The `A(−iy)`-term arc bound feeds `arc_integral_tendsto_zero` (`YukawaDCF/YukawaArcBound`), which
asks the numerator `K·A(−iy)` to be bounded on the arc.  The `A(−iy)` in Tang & Lu's eq (20) is
**not** the raw inverse entry `[Q̂₀(−y)]⁻¹ − I` (that carries an `e^{iyλ}` factor which *grows* on
the arc for the unlike pairs `λ = (σⱼ−σᵢ)/2 < 0`); it is the **amplitude**
`A(−iy) = 2π(ρᵢρⱼ)^{1/2}W(−iy)/(Δ det(−iy))`, the growing exponential having been removed by the
`E(−y)` wrapping.  This file provides the two ingredients that boundedness rests on.

## (A) The additive-diameter cancellation — why the eq (20) terms are exponential-free

Each eq (20) term is `E(−y)ᵢᵢ · {[Q̂₀(−y)]⁻¹}ᵢₘ · U₁(y)ₘₙ · {[Q̂₀ᵀ(−y)]⁻¹}ₙⱼ · E(−y)ⱼⱼ`, whose net
`e^{iy·(…)}` exponent is `σᵢ/2 + λᵢₘ − Rₘₙ + λⱼₙ + σⱼ/2` with `Rₐᵦ = (σₐ+σᵦ)/2`, `λₐᵦ = (σᵦ−σₐ)/2`.
The four `expSum_…_eq_zero` lemmas show this **vanishes identically** (specialising `m = i` and/or
`n = j` for the terms where the inverse factor is the identity) — so no net exponential survives,
and `A(−iy)` reduces to the pure `W/det` amplitude.

## (B) The far-region bounds — `W(−iy)/det(−iy)` is bounded on the arc

`W`, `det` are built (Tang & Lu Appendix) from the *same* removable functions
`φ₁ = (1−sσ−e^{−sσ})/s²`, `φ₂ = (1−sσ+(sσ)²/2−e^{−sσ})/s³` as `q0_entry_c` (here `s = −iy`).  On the
arc `y = Re^{iθ}` we have `Re s = R sinθ ≥ 0`, so `‖e^{−sσ}‖ ≤ 1`, and
`normP2_arc_le`/`normP3_arc_le` bound `φ₁`, `φ₂` by constants for `‖s‖ ≥ 1` (in fact `→ 0` as
`‖s‖ → ∞`).  Hence `W(−iy)` is bounded (`→ 0`) and `det(−iy) → 1` on the arc, so the amplitude
`A(−iy)` is bounded — the cancellation-tamed numerator bound.  (These are the far-region duals of
`Q0ComplexRepr.normP2_le`/`normP3_le`, which bound the *same* `φ` near `s = 0`.)

## (C) The assembly logic — amplitude bounded from `W` bounded and `det` bounded below

`norm_ge_of_norm_sub_one_le` turns `det(−iy) → 1` (from the `φ`-decay bounds `normP{2,3}_arc_decay`,
`→ 0`) into `‖det(−iy)‖ ≥ 1/2` (bounded below); `amplitude_norm_le` then bounds
`A = c·W/(Δ·det)` by `‖c‖·Wb/(‖Δ‖·D)` given `‖W‖ ≤ Wb` and `‖det‖ ≥ D > 0` — the numerator bound
`arc_integral_tendsto_zero` consumes.

**Remaining for the full A-term arc bound:** supply the concrete `‖W(−iy)‖ ≤ Wb` and
`‖det(−iy) − 1‖ ≤ d` by expanding Tang & Lu's explicit Appendix `W`/`det` (finite sums of the `φ`
functions bounded here) — note these explicit `W`/`det` formulas are *not yet in the project*, whose
Baxter machinery is Woodbury-based (`Q0_mat_phys_inv_eq`) rather than the `2π√W/det` Appendix form;
introducing them is the one remaining piece.  The exponent cancellation, the far-region `φ`
bounds/decay, and the assembly logic (this file) are all in place.
-/

open Complex

namespace FMSA.MixtureArcBound

/-- **Additive-diameter cancellation, leading term** (`m = i`, `n = j`): the net exponent
`σᵢ/2 − Rᵢⱼ + σⱼ/2` of `E(−y)ᵢᵢ·U₁(y)ᵢⱼ·E(−y)ⱼⱼ` vanishes. -/
theorem expSum_diag_eq_zero {N : ℕ} (σ : Fin N → ℝ) (i j : Fin N) :
    σ i / 2 - (σ i + σ j) / 2 + σ j / 2 = 0 := by ring

/-- **Additive-diameter cancellation, left term** (`m = i`): the net exponent
`σᵢ/2 − Rᵢₙ + λⱼₙ + σⱼ/2` of `E(−y)ᵢᵢ·U₁(y)ᵢₙ·{[Q̂₀ᵀ(−y)]⁻¹}ₙⱼ·E(−y)ⱼⱼ` vanishes. -/
theorem expSum_left_eq_zero {N : ℕ} (σ : Fin N → ℝ) (i j n : Fin N) :
    σ i / 2 - (σ i + σ n) / 2 + (σ n - σ j) / 2 + σ j / 2 = 0 := by ring

/-- **Additive-diameter cancellation, right term** (`n = j`): the net exponent
`σᵢ/2 + λᵢₘ − Rₘⱼ + σⱼ/2` of `E(−y)ᵢᵢ·{[Q̂₀(−y)]⁻¹}ᵢₘ·U₁(y)ₘⱼ·E(−y)ⱼⱼ` vanishes. -/
theorem expSum_right_eq_zero {N : ℕ} (σ : Fin N → ℝ) (i j m : Fin N) :
    σ i / 2 + (σ m - σ i) / 2 - (σ m + σ j) / 2 + σ j / 2 = 0 := by ring

/-- **Additive-diameter cancellation, both** (general `m`, `n`): the net exponent
`σᵢ/2 + λᵢₘ − Rₘₙ + λⱼₙ + σⱼ/2` of the full product term vanishes. -/
theorem expSum_both_eq_zero {N : ℕ} (σ : Fin N → ℝ) (i j m n : Fin N) :
    σ i / 2 + (σ m - σ i) / 2 - (σ m + σ n) / 2 + (σ n - σ j) / 2 + σ j / 2 = 0 := by ring

/-- **Far-region bound on `φ₁ = (1−sσ−e^{−sσ})/s²`.**  For `‖s‖ ≥ 1` and `Re(sσ) ≥ 0` (the arc,
where `s = −iy`, `Re s = R sinθ ≥ 0`, `σ` real ≥ 0), `‖φ₁‖ ≤ 2 + ‖σ‖`.  (Uses `‖e^{−sσ}‖ ≤ 1`.) -/
theorem normP2_arc_le {s σ : ℂ} (hs : 1 ≤ ‖s‖) (hre : 0 ≤ (s * σ).re) :
    ‖(1 - s * σ - Complex.exp (-(s * σ))) / s ^ 2‖ ≤ 2 + ‖σ‖ := by
  have hexp : ‖Complex.exp (-(s * σ))‖ ≤ 1 := by
    rw [Complex.norm_exp, Complex.neg_re]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hnum : ‖1 - s * σ - Complex.exp (-(s * σ))‖ ≤ 2 + ‖s‖ * ‖σ‖ := by
    calc ‖1 - s * σ - Complex.exp (-(s * σ))‖
        ≤ ‖1 - s * σ‖ + ‖Complex.exp (-(s * σ))‖ := norm_sub_le _ _
      _ ≤ (‖(1:ℂ)‖ + ‖s * σ‖) + 1 := by gcongr; exact norm_sub_le _ _
      _ = 2 + ‖s‖ * ‖σ‖ := by rw [norm_one, norm_mul]; ring
  rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
  have hs2 : ‖s‖ ≤ ‖s‖ ^ 2 := by nlinarith [norm_nonneg s]
  nlinarith [norm_nonneg σ, norm_nonneg s, hnum, hs, hs2]

/-- **Far-region bound on `φ₂ = (1−sσ+(sσ)²/2−e^{−sσ})/s³`.**  For `‖s‖ ≥ 1` and `Re(sσ) ≥ 0`,
`‖φ₂‖ ≤ 2 + ‖σ‖ + ‖σ‖²/2`. -/
theorem normP3_arc_le {s σ : ℂ} (hs : 1 ≤ ‖s‖) (hre : 0 ≤ (s * σ).re) :
    ‖(1 - s * σ + (s * σ) ^ 2 / 2 - Complex.exp (-(s * σ))) / s ^ 3‖
      ≤ 2 + ‖σ‖ + ‖σ‖ ^ 2 / 2 := by
  have hexp : ‖Complex.exp (-(s * σ))‖ ≤ 1 := by
    rw [Complex.norm_exp, Complex.neg_re]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hsq : ‖(s * σ) ^ 2 / 2‖ = ‖s‖ ^ 2 * ‖σ‖ ^ 2 / 2 := by
    rw [norm_div, norm_pow, norm_mul, mul_pow]; simp
  have hnum : ‖1 - s * σ + (s * σ) ^ 2 / 2 - Complex.exp (-(s * σ))‖
      ≤ 2 + ‖s‖ * ‖σ‖ + ‖s‖ ^ 2 * ‖σ‖ ^ 2 / 2 := by
    calc ‖1 - s * σ + (s * σ) ^ 2 / 2 - Complex.exp (-(s * σ))‖
        ≤ ‖1 - s * σ + (s * σ) ^ 2 / 2‖ + ‖Complex.exp (-(s * σ))‖ := norm_sub_le _ _
      _ ≤ ((‖(1:ℂ)‖ + ‖s * σ‖) + ‖(s * σ) ^ 2 / 2‖) + 1 := by
            gcongr
            exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ = 2 + ‖s‖ * ‖σ‖ + ‖s‖ ^ 2 * ‖σ‖ ^ 2 / 2 := by rw [norm_one, norm_mul, hsq]; ring
  rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
  have h1 : ‖s‖ ≤ ‖s‖ ^ 3 := by nlinarith [norm_nonneg s]
  have h2 : ‖s‖ ^ 2 ≤ ‖s‖ ^ 3 := by nlinarith [norm_nonneg s]
  have h3 : (1:ℝ) ≤ ‖s‖ ^ 3 := by nlinarith [norm_nonneg s]
  nlinarith [norm_nonneg σ, norm_nonneg s, hnum, mul_nonneg (norm_nonneg σ) (norm_nonneg σ)]

/-! ### Decay versions — `φ → 0`, needed for `det(−iy) → 1` (bounded below) -/

/-- **Far-region decay of `φ₁`.**  `‖(1−sσ−e^{−sσ})/s²‖ ≤ (2+‖σ‖)/‖s‖ → 0` for `‖s‖ ≥ 1`,
`Re(sσ) ≥ 0` — the sharper `1/‖s‖` version of `normP2_arc_le`, so `φ₁ → 0` on the arc. -/
theorem normP2_arc_decay {s σ : ℂ} (hs : 1 ≤ ‖s‖) (hre : 0 ≤ (s * σ).re) :
    ‖(1 - s * σ - Complex.exp (-(s * σ))) / s ^ 2‖ ≤ (2 + ‖σ‖) / ‖s‖ := by
  have hs0 : (0:ℝ) < ‖s‖ := by linarith
  have hexp : ‖Complex.exp (-(s * σ))‖ ≤ 1 := by
    rw [Complex.norm_exp, Complex.neg_re]; exact Real.exp_le_one_iff.mpr (by linarith)
  have hnum : ‖1 - s * σ - Complex.exp (-(s * σ))‖ ≤ 2 + ‖s‖ * ‖σ‖ := by
    calc ‖1 - s * σ - Complex.exp (-(s * σ))‖
        ≤ ‖1 - s * σ‖ + ‖Complex.exp (-(s * σ))‖ := norm_sub_le _ _
      _ ≤ (‖(1:ℂ)‖ + ‖s * σ‖) + 1 := by gcongr; exact norm_sub_le _ _
      _ = 2 + ‖s‖ * ‖σ‖ := by rw [norm_one, norm_mul]; ring
  rw [norm_div, norm_pow, div_le_div_iff₀ (by positivity) hs0]
  nlinarith [norm_nonneg σ, norm_nonneg s, hnum, hs]

/-- **Far-region decay of `φ₂`.**  `‖(1−sσ+(sσ)²/2−e^{−sσ})/s³‖ ≤ (2+‖σ‖+‖σ‖²/2)/‖s‖ → 0` for
`‖s‖ ≥ 1`, `Re(sσ) ≥ 0` — the sharper `1/‖s‖` version of `normP3_arc_le`. -/
theorem normP3_arc_decay {s σ : ℂ} (hs : 1 ≤ ‖s‖) (hre : 0 ≤ (s * σ).re) :
    ‖(1 - s * σ + (s * σ) ^ 2 / 2 - Complex.exp (-(s * σ))) / s ^ 3‖
      ≤ (2 + ‖σ‖ + ‖σ‖ ^ 2 / 2) / ‖s‖ := by
  have hs0 : (0:ℝ) < ‖s‖ := by linarith
  have hexp : ‖Complex.exp (-(s * σ))‖ ≤ 1 := by
    rw [Complex.norm_exp, Complex.neg_re]; exact Real.exp_le_one_iff.mpr (by linarith)
  have hsq : ‖(s * σ) ^ 2 / 2‖ = ‖s‖ ^ 2 * ‖σ‖ ^ 2 / 2 := by
    rw [norm_div, norm_pow, norm_mul, mul_pow]; simp
  have hnum : ‖1 - s * σ + (s * σ) ^ 2 / 2 - Complex.exp (-(s * σ))‖
      ≤ 2 + ‖s‖ * ‖σ‖ + ‖s‖ ^ 2 * ‖σ‖ ^ 2 / 2 := by
    calc ‖1 - s * σ + (s * σ) ^ 2 / 2 - Complex.exp (-(s * σ))‖
        ≤ ‖1 - s * σ + (s * σ) ^ 2 / 2‖ + ‖Complex.exp (-(s * σ))‖ := norm_sub_le _ _
      _ ≤ ((‖(1:ℂ)‖ + ‖s * σ‖) + ‖(s * σ) ^ 2 / 2‖) + 1 := by
            gcongr
            exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ = 2 + ‖s‖ * ‖σ‖ + ‖s‖ ^ 2 * ‖σ‖ ^ 2 / 2 := by rw [norm_one, norm_mul, hsq]; ring
  rw [norm_div, norm_pow, div_le_div_iff₀ (by positivity) hs0]
  have h2 : ‖s‖ ^ 2 ≤ ‖s‖ ^ 3 := by nlinarith [norm_nonneg s]
  nlinarith [norm_nonneg σ, norm_nonneg s, hnum, hs, h2, mul_nonneg (norm_nonneg σ) (norm_nonneg σ)]

/-! ### (C) Assembly logic — amplitude bounded from `W` bounded and `det` bounded below -/

/-- **`det` bounded below from `det → 1`.**  If `‖det − 1‖ ≤ d` then `‖det‖ ≥ 1 − d`; so the arc
decay `‖det(−iy) − 1‖ → 0` gives `‖det(−iy)‖ ≥ 1/2` for large `‖s‖` (bounded below). -/
theorem norm_ge_of_norm_sub_one_le {dt : ℂ} {d : ℝ} (h : ‖dt - 1‖ ≤ d) : 1 - d ≤ ‖dt‖ := by
  have h1 : ‖(1:ℂ)‖ - ‖dt‖ ≤ ‖(1:ℂ) - dt‖ := norm_sub_norm_le _ _
  rw [norm_one, norm_sub_rev] at h1
  linarith

/-- **Amplitude bounded from `W` bounded and `det` bounded below.**  For the amplitude
`A = c·W/(Δ·det)` (`c = 2π√(ρρ)`), if `‖W‖ ≤ Wb`, `Δ ≠ 0` and `‖det‖ ≥ D > 0`, then
`‖A‖ ≤ ‖c‖·Wb/(‖Δ‖·D)`.  This is the final step: it turns the `W`-bound (finite sum of the
far-region `φ` bounds) and the `det` lower bound (`norm_ge_of_norm_sub_one_le`) into the numerator
bound `arc_integral_tendsto_zero` consumes. -/
theorem amplitude_norm_le {c : ℝ} {W Δ dt : ℂ} {Wb D : ℝ}
    (hW : ‖W‖ ≤ Wb) (hΔ : Δ ≠ 0) (hD : 0 < D) (hdet : D ≤ ‖dt‖) :
    ‖(c : ℂ) * W / (Δ * dt)‖ ≤ ‖c‖ * Wb / (‖Δ‖ * D) := by
  rw [norm_div, norm_mul, norm_mul, Complex.norm_real]
  have hΔ0 : (0:ℝ) < ‖Δ‖ := norm_pos_iff.mpr hΔ
  have hWb : 0 ≤ Wb := (norm_nonneg W).trans hW
  gcongr

end FMSA.MixtureArcBound
