/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterWienerHopfComplex

/-!
# Equivalence: real-axis Baxter root location ⟺ "no spinodal" — Task BAXTER.16 / POLE.11

This is **step 1** of the decomposition "prove `Q̂ ≠ 1` ⟺ no spinodal, then prove PY-HS has no
spinodal, then assemble".  On the **real axis** the Wiener–Hopf factorization
`baxter_wiener_hopf_factorization` gives the pointwise identity

  `1 − ρ·Ĉ(k) = (1 − A(k))² + B(k)²`,   `Q̂(k) = A(k) − i·B(k)`
  (`A = ∫₀^σ q0·cos(kr)`, `B = ∫₀^σ q0·sin(kr)`),

so the PY structure factor is finite (`1−ρĈ > 0`, "no spinodal") **iff** `Q̂(k) ≠ 1` (no Baxter pole
on the real axis: `Q̂ = 1 ⟺ A = 1 ∧ B = 0 ⟺ (1−A)² + B² = 0`).

**Scope caveat.**  This equivalence is **real-axis only**.  The full Hermite–Biehler root location
`MA.14` (`Q̂ ≠ 1` on the *closed lower half-plane* `{Im k ≤ 0}`) is *strictly stronger* than no
spinodal: it additionally excludes zeros in the *open* lower half-plane `{Im k < 0}` (the statement
that the Baxter factorization is the canonical Wiener–Hopf *plus*-factor / winding number 0).  So

  MA.14 (closed LHP)  =  no spinodal (real axis, `BAXTER.16`)  ∧  no open-LHP poles (winding),

and this file discharges only the *equivalence for the first conjunct*.  Proving PY-HS has no
spinodal (`1−ρĈ > 0 ∀k`) is itself research-scale — the elementary routes fail (`|Npoly|>|Dpoly|`
breaks near `k=0` on the real axis; `c_HS ≤ 0` gives the wrong-sign bound; `Re(1−Q̂)` is not
sign-definite for `η ≳ 0.45`).
-/

open MeasureTheory Set Real intervalIntegral

namespace FMSA.HardSphere

noncomputable section

variable {eta sigma rho : ℝ}

/-- **Equivalence (step 1): real-axis Baxter root location ⟺ no spinodal.**  For real `k ≠ 0`,
`Q̂(k) ≠ 1` (no Baxter pole at `k`) iff `1 − ρ·Ĉ(k) > 0` (PY structure factor finite there).  From
`1 − ρĈ = (1−A)² + B²` and `Q̂ = A − iB`, so `Q̂ = 1 ⟺ A = 1 ∧ B = 0 ⟺ (1−A)² + B² = 0`. -/
theorem qhat_complex_ne_one_iff_no_spinodal (hsigma : 0 < sigma) (heta1 : eta < 1)
    (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) {k : ℝ} (hk : k ≠ 0) :
    Qhat_complex eta sigma rho (k : ℂ) ≠ 1
      ↔ 0 < 1 - rho * radial_fourier (c_HS eta sigma) k := by
  rw [← baxter_wiener_hopf_factorization eta sigma rho k hsigma hk heta1 heta_def,
    Qhat_complex_eq_cos_sub_I_sin]
  set A := ∫ r in (0:ℝ)..sigma, q0_poly eta sigma rho r * Real.cos (k * r) with hA
  set B := ∫ r in (0:ℝ)..sigma, q0_poly eta sigma rho r * Real.sin (k * r) with hB
  -- `Q̂ = A − iB = 1 ⟺ A = 1 ∧ B = 0`
  have hQeq : ((A : ℂ) - Complex.I * (B : ℂ) = 1) ↔ (A = 1 ∧ B = 0) := by
    rw [Complex.ext_iff]
    simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [Ne, hQeq]
  constructor
  · intro h
    by_contra hle
    rw [not_lt] at hle
    have hz : (1 - A) ^ 2 + B ^ 2 = 0 := le_antisymm hle (by positivity)
    have hsq : (1 - A) ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg B]) (sq_nonneg _)
    have hB0 : B = 0 := by
      have : B ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg (1 - A)]) (sq_nonneg _)
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    exact h ⟨by nlinarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq], hB0⟩
  · rintro h ⟨hA1, hB0⟩
    rw [hA1, hB0] at h
    norm_num at h

/-! ### PY-HS no-spinodal — now a THEOREM — and its equivalent forms -/

/-- **PY-HS "no spinodal" — RETIRED as a physics axiom 2026-07-19, now a THEOREM.**  The PY
hard-sphere inverse structure factor is strictly positive on the real axis: `1 − ρ·Ĉ(k) > 0` for
`k ≠ 0` (and `= 1 > 0` at `k = 0`).

The proof is the *real-axis strict dominance* `‖Dpoly(k)‖ < ‖Npoly(k)‖` (`BaxterPoles.lean`): under
the physical coupling `η = πρσ³/6` the PY coefficients collapse so that
`‖Npoly(k)‖² − ‖Dpoly(k)‖² = k⁶` identically, hence `G_baxter(k) ≠ 0` for real `k ≠ 0` (a zero would
force `‖Npoly‖ = ‖Dpoly‖`, as `‖e^{-ikσ}‖ = 1` on the real axis).  Via
`Qhat_pole_iff_G_baxter_zero` this gives `Q̂(k) ≠ 1`, and `qhat_complex_ne_one_iff_no_spinodal`
converts that to positivity.  (The earlier "no elementary proof / no SOS certificate" note applied to
a *direct* attack on `1−ρĈ`; the Baxter `N/D` route sidesteps it entirely.)

`heta0`/`hrho` are retained for signature compatibility with the former axiom. -/
theorem pyhs_no_spinodal {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    ∀ k : ℝ, k ≠ 0 → 0 < 1 - rho * radial_fourier (c_HS eta sigma) k := by
  intro k hk
  refine (qhat_complex_ne_one_iff_no_spinodal hsigma heta1 heta_def hk).mp ?_
  have hk0 : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  have hG := G_baxter_ne_zero_of_real hsigma heta1 heta_def hk
  have hne : 1 - Qhat_complex eta sigma rho (k : ℂ) ≠ 0 :=
    fun h => hG ((Qhat_pole_iff_G_baxter_zero eta sigma rho hsigma hk0).mp h)
  exact fun h => hne (by rw [h]; ring)

/-- **Real-axis Baxter root location, from the no-spinodal axiom** (via the equivalence): `Q̂ ≠ 1`
for every real `k ≠ 0`.  No longer needs a separate axiom. -/
theorem qhat_complex_ne_one_of_real {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6)
    {k : ℝ} (hk : k ≠ 0) :
    Qhat_complex eta sigma rho (k : ℂ) ≠ 1 :=
  (qhat_complex_ne_one_iff_no_spinodal hsigma heta1 heta_def hk).mpr
    (pyhs_no_spinodal heta0 heta1 hsigma hrho heta_def k hk)

/-- **BAXTER.16 (PY-HS structure factor positivity), all `k`.**  `0 < 1 − ρ·Ĉ(k)` for every real
`k`; the `k ≠ 0` content is the no-spinodal axiom, and `k = 0` is the `radial_fourier` encoding
value `0` (`1 − ρ·0 = 1`). -/
theorem one_sub_rho_radial_fourier_c_HS_pos {eta sigma rho : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) (k : ℝ) :
    0 < 1 - rho * radial_fourier (c_HS eta sigma) k := by
  rcases eq_or_ne k 0 with hk0 | hk0
  · subst hk0
    have hzero : radial_fourier (c_HS eta sigma) 0 = 0 := by
      unfold radial_fourier
      have hint : ∫ r in Set.Ioi (0:ℝ), r * c_HS eta sigma r * Real.sin (0 * r) = 0 := by simp
      rw [hint, mul_zero]
    rw [hzero, mul_zero, sub_zero]; norm_num
  · exact pyhs_no_spinodal heta0 heta1 hsigma hrho heta_def k hk0

end

end FMSA.HardSphere
