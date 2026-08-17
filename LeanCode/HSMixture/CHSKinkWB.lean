/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HSMixture.CHSKink
import LeanCode.HSMixture.WhiteBearFMT

/-!
# Task OZ.18 closure — the White-Bear FMT kink is unconditional on `0 < η < 1`

`CHSKink.lean` proved the `λ_ij` kink of the FMT direct correlation function **conditionally** on
the two-coefficient nondegeneracy `χ₂₂ ≠ χ₁/(4π)` (`cHS_FMT_not_differentiableAt_of_chi`), with
the slope `F′(λ) = 2(χ₂₂ − χ₁/(4π))`. This file **discharges that hypothesis** for the concrete
White-Bear χ's, closing OZ.18 unconditionally on the physical domain.

The engine is the closed form (derived from the FMT Hessian; see `proof_notes_hard_sphere.md`
OZ.18):

  `χ₂₂ − χ₁/(4π) = n₂ · (1/(4v²) − 6π·φ) = n₂ · g(η) / (12 η² v²)`,   `v := 1 − η`,
  `g(η) := 3η² − 2η − 2(1−η)² log(1−η)`,   `φ := (η + v² log v)/(36π η² v²)` (White-Bear I),

together with the **elementary positivity `g(η) > 0` on `(0,1)`** (`g_wb_pos`), proved by nested
monotonicity: `g′ = 4p` with `p(η) := η + (1−η)log(1−η)`, and `p′(η) = −log(1−η) > 0`. Since
`n₂ = 4π ΣρR² > 0`, the kink coefficient is strictly positive for **every** physical state, and it
vanishes only in the `ρ → 0` (`η = 0`) ideal-gas limit — an exterior boundary, not an interior
coincidence. Hence the FMT kink holds unconditionally on `0 < η < 1`.

**Status:** ✓ closure of OZ.18 — `g_wb_pos`, `E_WB`/`E_WB_eq`/`E_WB_pos`, and the unconditional
kink `cHS_FMT_kink_WB`, axiom-clean.
-/

set_option linter.style.longLine false

open Set

namespace FMSA.HSKink

/-! ### The scalar positivity `g(η) > 0` on `(0,1)` -/

/-- `g(η) := 3η² − 2η − 2(1−η)²·log(1−η)` — the numerator of the White-Bear kink coefficient
`χ₂₂ − χ₁/(4π) = n₂·g(η)/(12η²(1−η)²)`. -/
noncomputable def g_wb (η : ℝ) : ℝ := 3 * η ^ 2 - 2 * η - 2 * (1 - η) ^ 2 * Real.log (1 - η)

/-- `p(η) := η + (1−η)·log(1−η)` — the antiderivative-companion with `g′ = 4p`. -/
noncomputable def p_wb (η : ℝ) : ℝ := η + (1 - η) * Real.log (1 - η)

/-- `p_wb` has derivative `−log(1−η)`. -/
theorem hasDerivAt_p_wb {η : ℝ} (hη : η < 1) :
    HasDerivAt p_wb (-Real.log (1 - η)) η := by
  have hne : (1 : ℝ) - η ≠ 0 := by linarith
  have h1 : HasDerivAt (fun x : ℝ => (1 : ℝ) - x) (-1) η := by
    simpa using (hasDerivAt_id η).const_sub 1
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - η)) η := h1.log hne
  have hp : HasDerivAt p_wb
      (1 + (-1 * Real.log (1 - η) + (1 - η) * (-1 / (1 - η)))) η :=
    (hasDerivAt_id η).add (h1.mul hlog)
  refine hp.congr_deriv ?_
  field_simp
  ring

/-- **`p_wb > 0` on `(0,1)`** — `p_wb 0 = 0` and `p_wb′ = −log(1−η) > 0`. -/
theorem p_wb_pos {η : ℝ} (h0 : 0 < η) (h1 : η < 1) : 0 < p_wb η := by
  have hmono : StrictMonoOn p_wb (Ico 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico 0 1)
    · apply ContinuousOn.add continuousOn_id
      apply ContinuousOn.mul (by fun_prop)
      apply ContinuousOn.log (by fun_prop)
      intro x hx; simp only [mem_Ico] at hx; nlinarith [hx.1, hx.2]
    · intro x hx
      rw [interior_Ico, mem_Ioo] at hx
      rw [(hasDerivAt_p_wb hx.2).deriv]
      have hlogneg : Real.log (1 - x) < 0 := Real.log_neg (by linarith [hx.1]) (by linarith [hx.2])
      linarith
  have hp0 : p_wb 0 = 0 := by simp [p_wb]
  have := hmono (left_mem_Ico.mpr (by norm_num)) (mem_Ico.mpr ⟨h0.le, h1⟩) h0
  rwa [hp0] at this

/-- `g_wb` has derivative `4·p_wb η`. -/
theorem hasDerivAt_g_wb {η : ℝ} (hη : η < 1) :
    HasDerivAt g_wb (4 * p_wb η) η := by
  have hne : (1 : ℝ) - η ≠ 0 := by linarith
  have h1 : HasDerivAt (fun x : ℝ => (1 : ℝ) - x) (-1) η := by
    simpa using (hasDerivAt_id η).const_sub 1
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - η)) η := h1.log hne
  have hsq2 : HasDerivAt (fun x : ℝ => 2 * (1 - x) ^ 2) (2 * ((2 : ℕ) * (1 - η) ^ (2 - 1) * (-1))) η :=
    (h1.pow 2).const_mul 2
  have hC : HasDerivAt (fun x : ℝ => 2 * (1 - x) ^ 2 * Real.log (1 - x))
      (2 * ((2 : ℕ) * (1 - η) ^ (2 - 1) * (-1)) * Real.log (1 - η) +
        2 * (1 - η) ^ 2 * (-1 / (1 - η))) η :=
    hsq2.mul hlog
  have hA : HasDerivAt (fun x : ℝ => 3 * x ^ 2) (3 * ((2 : ℕ) * η ^ (2 - 1))) η :=
    (hasDerivAt_pow 2 η).const_mul 3
  have hB : HasDerivAt (fun x : ℝ => 2 * x) 2 η := by simpa using (hasDerivAt_id η).const_mul 2
  have hg : HasDerivAt g_wb
      (3 * ((2 : ℕ) * η ^ (2 - 1)) - 2 - (2 * ((2 : ℕ) * (1 - η) ^ (2 - 1) * (-1)) * Real.log (1 - η) +
        2 * (1 - η) ^ 2 * (-1 / (1 - η)))) η :=
    (hA.sub hB).sub hC
  refine hg.congr_deriv ?_
  rw [p_wb]
  push_cast
  field_simp
  ring

/-- **The White-Bear kink numerator is positive on `(0,1)`.** `g_wb 0 = 0`, `g_wb′ = 4p_wb > 0`. -/
theorem g_wb_pos {η : ℝ} (h0 : 0 < η) (h1 : η < 1) : 0 < g_wb η := by
  have hmono : StrictMonoOn g_wb (Ico 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico 0 1)
    · apply ContinuousOn.sub (ContinuousOn.sub (by fun_prop) (by fun_prop))
      apply ContinuousOn.mul (by fun_prop)
      apply ContinuousOn.log (by fun_prop)
      intro x hx; simp only [mem_Ico] at hx; nlinarith [hx.1, hx.2]
    · intro x hx
      rw [interior_Ico, mem_Ioo] at hx
      rw [(hasDerivAt_g_wb hx.2).deriv]
      have := p_wb_pos hx.1 hx.2
      linarith
  have hg0 : g_wb 0 = 0 := by simp [g_wb]
  have := hmono (left_mem_Ico.mpr (by norm_num)) (mem_Ico.mpr ⟨h0.le, h1⟩) h0
  rwa [hg0] at this

/-! ### The concrete White-Bear kink coefficient `E_WB` and its positivity -/

/-- White-Bear I free-energy coefficient `φ(η) = (η + (1−η)²log(1−η))/(36π η²(1−η)²)` — the `n₂³`
coefficient of `wbPhi` (`WhiteBearFMT.lean`), i.e. `get_HS_FMT`'s `ph`. -/
noncomputable def phiWB (η : ℝ) : ℝ :=
  (η + (1 - η) ^ 2 * Real.log (1 - η)) / (36 * Real.pi * η ^ 2 * (1 - η) ^ 2)

/-- **The White-Bear kink coefficient** `E_WB = n₂·(1/(4v²) − 6π·φ)` — equals `χ₂₂ − χ₁/(4π)`
for the FMT direct correlation function (derived from the FMT Hessian; `proof_notes_hard_sphere.md`
OZ.18). Here `n₂` is the FMT surface-area density and `v = 1 − η`. -/
noncomputable def E_WB (n2 η : ℝ) : ℝ :=
  n2 * (1 / (4 * (1 - η) ^ 2) - 6 * Real.pi * phiWB η)

/-- **Closed form** `E_WB = n₂·g(η)/(12η²(1−η)²)` — the `φ` and the `1/(4v²)` combine over the
common denominator, and `g` is exactly the surviving numerator. -/
theorem E_WB_eq {n2 η : ℝ} (h0 : 0 < η) (h1 : η < 1) :
    E_WB n2 η = n2 * g_wb η / (12 * η ^ 2 * (1 - η) ^ 2) := by
  unfold E_WB phiWB g_wb
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hη : η ≠ 0 := h0.ne'
  have hv : (1 : ℝ) - η ≠ 0 := by linarith
  field_simp
  ring

/-- **`E_WB > 0` for every physical state** (`0 < η < 1`, `n₂ > 0`) — the discharge of OZ.18's
nondegeneracy hypothesis. It vanishes only in the `ρ → 0` (`η → 0`) limit. -/
theorem E_WB_pos {n2 η : ℝ} (hn2 : 0 < n2) (h0 : 0 < η) (h1 : η < 1) : 0 < E_WB n2 η := by
  rw [E_WB_eq h0 h1]
  have hg := g_wb_pos h0 h1
  have hv : (0 : ℝ) < 1 - η := by linarith
  have hden : (0 : ℝ) < 12 * η ^ 2 * (1 - η) ^ 2 := by positivity
  exact div_pos (mul_pos hn2 hg) hden

/-! ### OZ.18 closure — the FMT kink, unconditional on `0 < η < 1` -/

/-- **OZ.18 closed (general form).** The FMT direct correlation function whose kink coefficient
`χ₂₂ − χ₁/(4π)` is the physical `E_WB` (i.e. `χ₂₂ = E_WB + χ₁/(4π)`) is **not differentiable** at
the sub-contact cutoff `λ_ij = |R_i − R_j|`, for **any** `χ₀,χ₁,χ₂,χ₃` (the kink is independent of
them) and **every** physical state `0 < η < 1`, `n₂ > 0`. The `χ₂₂ ≠ χ₁/(4π)` hypothesis of
`cHS_FMT_not_differentiableAt_of_chi` is discharged by `E_WB_pos`. -/
theorem cHS_FMT_kink_WB (χ0 χ1 χ2 χ3 : ℝ) {n2 η Ri Rj : ℝ}
    (hn2 : 0 < n2) (h0 : 0 < η) (h1 : η < 1) (hne : Ri ≠ Rj) :
    ¬ DifferentiableAt ℝ
      (cHS_FMT χ0 χ1 χ2 χ3 (E_WB n2 η + χ1 / (4 * Real.pi)) Ri Rj) |Ri - Rj| := by
  refine cHS_FMT_not_differentiableAt_of_chi χ0 χ1 χ2 χ3 _ Ri Rj hne ?_
  have hpos := E_WB_pos hn2 h0 h1
  intro heq
  exact hpos.ne' (by linarith)

/-- **OZ.18 closed (FMT-density form).** Same, with the kink coefficient built from the actual FMT
weighted densities `n₂ = wbN2 ρ d`, `η = wbN3 ρ d` — the "FMT Lean entry". Physical hypotheses:
positive surface density `0 < wbN2`, packing fraction `0 < η < 1`, and unlike radii. -/
theorem cHS_FMT_kink_WB_fmt {N : ℕ} (rho d : Fin N → ℝ) (χ0 χ1 χ2 χ3 : ℝ) {Ri Rj : ℝ}
    (hn2 : 0 < FMSA.WhiteBear.wbN2 rho d) (h0 : 0 < FMSA.WhiteBear.wbN3 rho d) (h1 : FMSA.WhiteBear.wbN3 rho d < 1) (hne : Ri ≠ Rj) :
    ¬ DifferentiableAt ℝ
      (cHS_FMT χ0 χ1 χ2 χ3 (E_WB (FMSA.WhiteBear.wbN2 rho d) (FMSA.WhiteBear.wbN3 rho d) + χ1 / (4 * Real.pi)) Ri Rj)
      |Ri - Rj| :=
  cHS_FMT_kink_WB χ0 χ1 χ2 χ3 hn2 h0 h1 hne

end FMSA.HSKink
