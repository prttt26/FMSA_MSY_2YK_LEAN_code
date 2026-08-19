/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZ.MSAFactorizationSplit
import LeanCode.HardSphere.BaxterWienerHopf

/-!
# MSAEXACT.1 — the core-DCF sine transforms (steps 1–2 of the core identity)

Group **MSAEXACT** (`proof_notes_msa_exact.md`).  Numerical partner: `msaexact1_cside_check.py`.

`msaexact1_iff_core` (`MSADCFTransform.lean`) reduces MSAEXACT.1 to matching a single scalar `cCore`
— the radial (sine) transform of the **core** correction of the MSA DCF — against an explicit
`D`-side closed form.  The core correction (theory note §7f, `msa_exact.minus_C`, with the `1/x`
repair) is

    a + b·r + ½ξa·r³        (the Baxter polynomial shift; monomials handled by `psiN_formula`)
    + v·(1 − e^{−zr})/(zr)   (the `yuk` term)
    + v²/(2Kz²)·coshRatio/r  (the `quad_t` term, `coshRatio = (cosh zr − 1)/e^z`)

Multiplied by the radial weight `r`, the `1/r`s cancel and every piece is elementary.  This file
supplies the two transforms that are **not** already in the library — the `yuk` piece and the
`coshRatio` piece — each assembled from `exp_sin_integral` (at `±z`) and `psi0_formula`.  The
monomial pieces are `HardSphere.psi{0,1,2,4}_formula`, already public.

⚠ This is the **integral layer only** (steps 1–2).  The remaining match `ρ·cCore = RHS(D)` needs the
`a,b,w ↔ D` solution relations (MSAEXACT.2 elimination) and is deferred — the closure-recovery core.
-/

open MeasureTheory intervalIntegral

namespace FMSA.MSAExact

open FMSA.HardSphere

/-! ### The `+z` companion of `exp_sin_integral` -/

/-- `∫₀^σ e^{z r} sin(k r) dr`, the sign-flipped partner of `exp_sin_integral` (which is the `−z`
case).  Obtained by substituting `z ↦ −z`. -/
theorem exp_pos_sin_integral {z k sigma : ℝ} (hzk : z ^ 2 + k ^ 2 ≠ 0) :
    ∫ r in (0 : ℝ)..sigma, Real.exp (z * r) * Real.sin (k * r)
      = (k - Real.exp (z * sigma) * (k * Real.cos (k * sigma) - z * Real.sin (k * sigma)))
        / (z ^ 2 + k ^ 2) := by
  have h := exp_sin_integral (z := -z) (k := k) (sigma := sigma) (by rw [neg_sq]; exact hzk)
  simp only [neg_neg, neg_mul, neg_sq] at h
  rw [h]; ring

/-! ### The `yuk` piece -/

/-- `∫₀^σ (1 − e^{−zr}) sin(kr) dr` — the `yuk` term's radial transform (the `1/(zr)` and the outer
`v` are constants pulled out in the assembly).  Splits into `psi0_formula − exp_sin_integral`. -/
theorem one_sub_exp_sin_integral {z k sigma : ℝ} (hzk : z ^ 2 + k ^ 2 ≠ 0) (hk : k ≠ 0) :
    ∫ r in (0 : ℝ)..sigma, (1 - Real.exp (-z * r)) * Real.sin (k * r)
      = (1 - Real.cos (k * sigma)) / k
        - (k - Real.exp (-z * sigma) * (k * Real.cos (k * sigma) + z * Real.sin (k * sigma)))
          / (z ^ 2 + k ^ 2) := by
  have hs : IntervalIntegrable (fun r => Real.sin (k * r)) volume 0 sigma :=
    (Real.continuous_sin.comp (by fun_prop)).intervalIntegrable 0 sigma
  have he : IntervalIntegrable (fun r => Real.exp (-z * r) * Real.sin (k * r)) volume 0 sigma :=
    ((Real.continuous_exp.comp (by fun_prop)).mul
      (Real.continuous_sin.comp (by fun_prop))).intervalIntegrable 0 sigma
  have hcongr : ∫ r in (0 : ℝ)..sigma, (1 - Real.exp (-z * r)) * Real.sin (k * r)
      = ∫ r in (0 : ℝ)..sigma, (Real.sin (k * r) - Real.exp (-z * r) * Real.sin (k * r)) :=
    intervalIntegral.integral_congr (fun r _ => by ring)
  rw [hcongr, intervalIntegral.integral_sub hs he, psi0_formula hk, exp_sin_integral hzk]

/-! ### The `coshRatio` piece -/

/-- `coshRatio z r = (cosh(zr) − 1)/e^z`, in the exp form that avoids forming `cosh` (matches
`msa_exact._cosh_ratio`). -/
noncomputable def coshRatio (z r : ℝ) : ℝ :=
  1 / 2 * (Real.exp (z * (r - 1)) + Real.exp (-z * (r + 1))) - Real.exp (-z)

/-- `∫₀^σ coshRatio z r · sin(kr) dr` — the `quad_t` term's radial transform.  Assembled from
`exp_pos_sin_integral`, `exp_sin_integral` and `psi0_formula`. -/
theorem coshRatio_sin_integral {z k sigma : ℝ} (hzk : z ^ 2 + k ^ 2 ≠ 0) (hk : k ≠ 0) :
    ∫ r in (0 : ℝ)..sigma, coshRatio z r * Real.sin (k * r)
      = 1 / 2 * Real.exp (-z) *
          ((k - Real.exp (z * sigma) * (k * Real.cos (k * sigma) - z * Real.sin (k * sigma)))
            / (z ^ 2 + k ^ 2))
        + 1 / 2 * Real.exp (-z) *
          ((k - Real.exp (-z * sigma) * (k * Real.cos (k * sigma) + z * Real.sin (k * sigma)))
            / (z ^ 2 + k ^ 2))
        - Real.exp (-z) * ((1 - Real.cos (k * sigma)) / k) := by
  have hep : IntervalIntegrable (fun r => Real.exp (z * r) * Real.sin (k * r)) volume 0 sigma :=
    ((Real.continuous_exp.comp (by fun_prop)).mul
      (Real.continuous_sin.comp (by fun_prop))).intervalIntegrable 0 sigma
  have hem : IntervalIntegrable (fun r => Real.exp (-z * r) * Real.sin (k * r)) volume 0 sigma :=
    ((Real.continuous_exp.comp (by fun_prop)).mul
      (Real.continuous_sin.comp (by fun_prop))).intervalIntegrable 0 sigma
  have hs : IntervalIntegrable (fun r => Real.sin (k * r)) volume 0 sigma :=
    (Real.continuous_sin.comp (by fun_prop)).intervalIntegrable 0 sigma
  -- Rewrite the integrand into `½e^{−z}·(e^{zr}sin) + ½e^{−z}·(e^{−zr}sin) − e^{−z}·sin`.
  have hcongr : ∫ r in (0 : ℝ)..sigma, coshRatio z r * Real.sin (k * r)
      = ∫ r in (0 : ℝ)..sigma,
          (1 / 2 * Real.exp (-z) * (Real.exp (z * r) * Real.sin (k * r))
            + 1 / 2 * Real.exp (-z) * (Real.exp (-z * r) * Real.sin (k * r))
            - Real.exp (-z) * Real.sin (k * r)) := by
    refine intervalIntegral.integral_congr (fun r _ => ?_)
    simp only [coshRatio]
    rw [show z * (r - 1) = z * r + -z by ring, show -z * (r + 1) = -z * r + -z by ring,
      Real.exp_add, Real.exp_add]
    ring
  rw [hcongr,
    intervalIntegral.integral_sub ((hep.const_mul _).add (hem.const_mul _)) (hs.const_mul _),
    intervalIntegral.integral_add (hep.const_mul _) (hem.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    exp_pos_sin_integral hzk, exp_sin_integral hzk, psi0_formula hk]

end FMSA.MSAExact
