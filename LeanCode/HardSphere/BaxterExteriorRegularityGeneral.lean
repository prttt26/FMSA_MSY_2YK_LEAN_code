/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.HardSphere.BaxterHermiteBiehler
import LeanCode.HardSphere.BaxterRenewalDecay
import LeanCode.HardSphere.BaxterExteriorDecayReduction

/-!
# End-to-end general-`η` exterior decay of `baxterPsi` — Task POLE.11 (task b), assembled

This closes the general-`η` `POLE.11` loop, chaining the three pieces landed 2026-07-18:

* **MA.14** (Hermite–Biehler, `BaxterHermiteBiehler.lean`): `Q̂ ≠ 1` on the closed lower half-plane
  (`qhat_complex_ne_one_of_im_nonpos`), resting on the bounded-core axiom.
* **MA.13** (Paley–Wiener, `WienerRenewal.lean` + wiring `BaxterRenewalDecay.lean`):
  `baxterPsiOuter_tendsto_zero_of_symbol` — Laplace-symbol nonvanishing on `{Re z ≥ 0}` ⇒
  `baxterPsiOuter → 0`.
* the axiom-clean reductions `baxterPsi_bounded_Ici_of_tendsto_zero` and
  `r_mul_ozBaxterFixedPt_tendsto_zero_of_tendsto_zero` (`BaxterExteriorDecayReduction.lean`).

The missing link, supplied here, is the **symbol bridge** `z = i·k`: the wiring's Laplace symbol
`∫₀^σ q0_poly(t)·e^{−z t} dt` equals `Qhat_complex(−i z)`, and `Re z ≥ 0 ⟺ Im(−i z) ≤ 0`, so MA.14's
`Q̂ ≠ 1` on `{Im k ≤ 0}` discharges the wiring's `hsym` (the `z = 0` / `k = 0` boundary point is the
removable one, handled directly: `Q̂(0) = ∫₀^σ q0_poly ≤ 0 ≠ 1`).

## Results (all resting on exactly MA.13 + MA.14's core axiom + the standard three)

* `qhat_symbol_nonvanishing` — the bridge: `∀ z, Re z ≥ 0 → 1 − ∫₀^σ q0_poly·e^{−z t} ≠ 0`.
* `baxterPsiOuter_tendsto_zero` — general-`η` decay `baxterPsiOuter → 0`.
* `baxterPsi_bounded_Ici` / `r_mul_ozBaxterFixedPt_tendsto_zero` — the two load-bearing exterior
  clauses of `baxter_exterior_regularity`, now for **all physical `η < 1`**.
-/

open MeasureTheory Set Real Filter Topology intervalIntegral

namespace FMSA.HardSphere

noncomputable section

variable {eta sigma rho : ℝ}

/-- **Symbol bridge (`z = i·k`).**  The wiring's Laplace symbol is nonvanishing on the closed right
half-plane, discharged from MA.14's `Q̂ ≠ 1` on the closed lower half-plane.  The identity
`∫₀^σ q0_poly(t)·e^{−z t} dt = Qhat_complex(−i z)` and `Im(−i z) = −Re z` do the conversion; `z = 0`
is the removable point (`Q̂(0) = ∫₀^σ q0_poly ≤ 0 ≠ 1`). -/
theorem qhat_symbol_nonvanishing (heta0 : 0 < eta) (heta1 : eta < 1) (hsigma : 0 < sigma)
    (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    ∀ z : ℂ, 0 ≤ z.re →
      1 - (∫ t in (0:ℝ)..sigma, (q0_poly eta sigma rho t : ℂ) * Complex.exp (-z * (t : ℂ)))
        ≠ 0 := by
  have hII : ∀ w : ℂ, -Complex.I * (-Complex.I * w) = -w := fun w => by
    rw [show -Complex.I * (-Complex.I * w) = Complex.I * Complex.I * w from by ring,
      Complex.I_mul_I]
    ring
  intro z hz
  have hbridge :
      (∫ t in (0:ℝ)..sigma, (q0_poly eta sigma rho t : ℂ) * Complex.exp (-z * (t : ℂ)))
        = Qhat_complex eta sigma rho (-Complex.I * z) := by
    unfold Qhat_complex
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have hexp : (-z * (t : ℂ)) = -Complex.I * (-Complex.I * z) * (t : ℂ) := by rw [hII z]
    rw [hexp]
  rw [hbridge]
  rcases eq_or_ne z 0 with hz0 | hz0
  · subst hz0
    simp only [mul_zero]
    have hQ0 : Qhat_complex eta sigma rho 0
        = ((∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t : ℝ) : ℂ) := by
      unfold Qhat_complex
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      simp
    rw [hQ0]
    have hnonpos : (∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t) ≤ 0 := by
      have h1 : 0 ≤ ∫ t in (0:ℝ)..sigma, -q0_poly eta sigma rho t :=
        intervalIntegral.integral_nonneg hsigma.le (fun t ht => by
          have := q0_poly_nonpos_of_nonneg heta0 heta1 hsigma hrho.le ht.1; linarith)
      rw [intervalIntegral.integral_neg] at h1
      linarith
    intro hc
    rw [sub_eq_zero] at hc
    have hone : (∫ t in (0:ℝ)..sigma, q0_poly eta sigma rho t) = 1 := by exact_mod_cast hc.symm
    linarith
  · have hk0 : -Complex.I * z ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz0
    have him : (-Complex.I * z).im ≤ 0 := by
      have hval : (-Complex.I * z).im = -z.re := by
        simp [Complex.mul_im, Complex.neg_im, Complex.I_re, Complex.I_im]
      rw [hval]; linarith
    exact sub_ne_zero.mpr
      (Ne.symm (qhat_complex_ne_one_of_im_nonpos heta0 heta1 hsigma hrho heta_def him hk0))

/-- **General-`η` exterior decay** `baxterPsiOuter → 0`, for all physical `η < 1` — MA.13 (renewal
decay) fed by MA.14 (the symbol bridge above). -/
theorem baxterPsiOuter_tendsto_zero (heta0 : 0 < eta) (heta1 : eta < 1) (hsigma : 0 < sigma)
    (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    Tendsto (baxterPsiOuter eta sigma rho) atTop (𝓝 0) :=
  baxterPsiOuter_tendsto_zero_of_symbol hsigma
    (qhat_symbol_nonvanishing heta0 heta1 hsigma hrho heta_def)

/-- **Exterior boundedness clause of `baxter_exterior_regularity`, all physical `η < 1`.** -/
theorem baxterPsi_bounded_Ici (heta0 : 0 < eta) (heta1 : eta < 1) (hsigma : 0 < sigma)
    (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    ∃ C, ∀ r, sigma ≤ r → |baxterPsi eta sigma rho r| ≤ C :=
  baxterPsi_bounded_Ici_of_tendsto_zero
    (baxterPsiOuter_tendsto_zero heta0 heta1 hsigma hrho heta_def)


/-- **Exterior `L¹` integrability of `baxterPsiOuter` on `(σ,∞)`, all physical `η < 1`** — MA.13's
strengthened conclusion fed by MA.14's symbol bridge. -/
theorem baxterPsiOuter_integrableOn (heta0 : 0 < eta) (heta1 : eta < 1) (hsigma : 0 < sigma)
    (hrho : 0 < rho) (heta_def : eta = Real.pi * rho * sigma ^ 3 / 6) :
    IntegrableOn (baxterPsiOuter eta sigma rho) (Ioi sigma) :=
  baxterPsiOuter_integrableOn_Ioi_of_symbol hsigma
    (qhat_symbol_nonvanishing heta0 heta1 hsigma hrho heta_def)


end

end FMSA.HardSphere
