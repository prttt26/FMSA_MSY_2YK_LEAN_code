/-
Copyright (c) 2026 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HSMixture.Q0DetContourOrientation

/-!
# Hermitian reality of the Baxter factor on the imaginary axis (MRS.8 bridge, sub-fact 2)

The Gram half of the value-route factorization `1 − ρĈ(k) = Q̂₀(ik)·Q̂₀(−ik)ᵀ` becomes a squared
complex norm `∑ₗ |(Q̂₀(ik)ᵀ v)ₗ|²` because, on the imaginary axis, the physical Baxter factor is
Hermitian-real: `Q̂₀(−ik) = conj(Q̂₀(ik))` for real `k` (the coefficients are real).  This is the
Schwarz reflection `conj(Q̂₀(s)) = Q̂₀(conj s)` at `s = ik` (where `conj(ik) = i(−k)`).

* `q0_entry_c_conj` — the entry-level Schwarz reflection for `conj`-fixed (real) coefficients.
* `Q0_mat_c_phys_conj` — the matrix version: `conj(Q̂₀(s)ᵢⱼ) = Q̂₀(conj s)ᵢⱼ`.
* `Q0_mat_c_phys_neg_axis` / `_map` — the on-axis reality `Q̂₀(−ik) = conj(Q̂₀(ik))` (entrywise / as
  a `Matrix.map (starRingEnd ℂ)`), the concrete sub-fact (2) of the MRS.8 bridge
  (`MixtureSymbolBridge.lean`).

The complementary sub-fact (1) — the radial-FT convolution theorem assembling `cHSmixRaw` into
`1 − Q̂₀Q̂₀ᵀ` — remains the open Wertheim content.
-/

set_option linter.style.longLine false

namespace FMSA.MixtureGenN
variable {N : ℕ}

/-- **Schwarz reflection of the Baxter entry.**  For `conj`-fixed (real) coefficients, the complex
Baxter entry commutes with conjugation in `s`: `conj(q̂₀(s)) = q̂₀(conj s)` — every factor is a real
coefficient (fixed by `conj`), an `exp` (commuting via `Complex.exp_conj`), or a power/quotient. -/
theorem q0_entry_c_conj {s sigma lam Qp Qpp rho δ : ℂ}
    (hsigma : starRingEnd ℂ sigma = sigma) (hlam : starRingEnd ℂ lam = lam) (hQp : starRingEnd ℂ Qp = Qp)
    (hQpp : starRingEnd ℂ Qpp = Qpp) (hrho : starRingEnd ℂ rho = rho) (hδ : starRingEnd ℂ δ = δ) :
    starRingEnd ℂ (FMSA.Q0Complex.q0_entry_c s sigma lam Qp Qpp rho δ)
      = FMSA.Q0Complex.q0_entry_c (starRingEnd ℂ s) sigma lam Qp Qpp rho δ := by
  unfold FMSA.Q0Complex.q0_entry_c
  simp only [map_sub, map_mul, map_div₀, map_pow, map_neg, map_add, ← Complex.exp_conj,
    map_one, map_ofNat, hsigma, hlam, hQp, hQpp, hrho, hδ]

/-- The physical Baxter matrix commutes entrywise with conjugation in `s` (real coefficients). -/
theorem Q0_mat_c_phys_conj (s : ℂ) (sigma rho : Fin N → ℝ) (i j : Fin N) :
    starRingEnd ℂ (FMSA.MixtureNoSpinodal.Q0_mat_c_phys s sigma rho i j)
      = FMSA.MixtureNoSpinodal.Q0_mat_c_phys (starRingEnd ℂ s) sigma rho i j := by
  unfold FMSA.MixtureNoSpinodal.Q0_mat_c_phys FMSA.Q0Complex.Q0_mat_c
  apply q0_entry_c_conj
  · exact Complex.conj_ofReal _
  · rw [map_div₀, map_sub, Complex.conj_ofReal, Complex.conj_ofReal, map_ofNat]
  · exact Complex.conj_ofReal _
  · exact Complex.conj_ofReal _
  · exact Complex.conj_ofReal _
  · split_ifs <;> simp

/-- **Hermitian reality on the imaginary axis.**  `Q̂₀(−ik) = conj(Q̂₀(ik))` for real `k` — from
`Q0_mat_c_phys_conj` at `s = ik` (`conj(ik) = i(−k)`).  This turns the structure-factor form
`vᵀ Q̂₀(ik)Q̂₀(−ik)ᵀ v` into the squared norm `∑ₗ|(Q̂₀(ik)ᵀ v)ₗ|²` (the `normSq` shape of the Gram
factorizations `hfack`/`hfac0`). -/
theorem Q0_mat_c_phys_neg_axis (k : ℝ) (sigma rho : Fin N → ℝ) (i j : Fin N) :
    FMSA.MixtureNoSpinodal.Q0_mat_c_phys (Complex.I * (-(k : ℂ))) sigma rho i j
      = starRingEnd ℂ (FMSA.MixtureNoSpinodal.Q0_mat_c_phys (Complex.I * (k : ℂ)) sigma rho i j) := by
  have hconj : (Complex.I * (-(k : ℂ)) : ℂ) = starRingEnd ℂ (Complex.I * (k : ℂ)) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [hconj, ← Q0_mat_c_phys_conj]

/-- Matrix form of the on-axis Hermitian reality: `Q̂₀(−ik) = (Q̂₀(ik)).map conj`. -/
theorem Q0_mat_c_phys_neg_axis_map (k : ℝ) (sigma rho : Fin N → ℝ) :
    FMSA.MixtureNoSpinodal.Q0_mat_c_phys (Complex.I * (-(k : ℂ))) sigma rho
      = (FMSA.MixtureNoSpinodal.Q0_mat_c_phys (Complex.I * (k : ℂ)) sigma rho).map (starRingEnd ℂ) := by
  funext i j
  rw [Matrix.map_apply]
  exact Q0_mat_c_phys_neg_axis k sigma rho i j

end FMSA.MixtureGenN
