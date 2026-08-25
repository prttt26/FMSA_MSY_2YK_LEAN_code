/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.YukawaOZ.MSAFactorizationSplit
import LeanCode.HardSphere.BaxterWienerHopf
import LeanCode.HardSphere.RadialFourier

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

/-- `coshRatio z σ r = e^{−zσ}(cosh(zr) − 1)`, in the exp form that avoids forming `cosh`.  ⚠ NOW
`σ`-aware (was hardcoded `σ=1`/`e^{−z}` — fine for single-component σ=1, WRONG when the mixture
`coreCorrection` reuses it at `σ_ij≠1`; `σ=1` recovers the old value). -/
noncomputable def coshRatio (z sigma r : ℝ) : ℝ :=
  1 / 2 * (Real.exp (z * (r - sigma)) + Real.exp (-z * (r + sigma))) - Real.exp (-z * sigma)

/-- `∫₀^σ coshRatio z sigma r · sin(kr) dr` — the `quad_t` term's radial transform.  Assembled from
`exp_pos_sin_integral`, `exp_sin_integral` and `psi0_formula`. -/
theorem coshRatio_sin_integral {z k sigma : ℝ} (hzk : z ^ 2 + k ^ 2 ≠ 0) (hk : k ≠ 0) :
    ∫ r in (0 : ℝ)..sigma, coshRatio z sigma r * Real.sin (k * r)
      = 1 / 2 * Real.exp (-z * sigma) *
          ((k - Real.exp (z * sigma) * (k * Real.cos (k * sigma) - z * Real.sin (k * sigma)))
            / (z ^ 2 + k ^ 2))
        + 1 / 2 * Real.exp (-z * sigma) *
          ((k - Real.exp (-z * sigma) * (k * Real.cos (k * sigma) + z * Real.sin (k * sigma)))
            / (z ^ 2 + k ^ 2))
        - Real.exp (-z * sigma) * ((1 - Real.cos (k * sigma)) / k) := by
  have hep : IntervalIntegrable (fun r => Real.exp (z * r) * Real.sin (k * r)) volume 0 sigma :=
    ((Real.continuous_exp.comp (by fun_prop)).mul
      (Real.continuous_sin.comp (by fun_prop))).intervalIntegrable 0 sigma
  have hem : IntervalIntegrable (fun r => Real.exp (-z * r) * Real.sin (k * r)) volume 0 sigma :=
    ((Real.continuous_exp.comp (by fun_prop)).mul
      (Real.continuous_sin.comp (by fun_prop))).intervalIntegrable 0 sigma
  have hs : IntervalIntegrable (fun r => Real.sin (k * r)) volume 0 sigma :=
    (Real.continuous_sin.comp (by fun_prop)).intervalIntegrable 0 sigma
  -- Rewrite the integrand into `½e^{−z}·(e^{zr}sin) + ½e^{−z}·(e^{−zr}sin) − e^{−z}·sin`.
  have hcongr : ∫ r in (0 : ℝ)..sigma, coshRatio z sigma r * Real.sin (k * r)
      = ∫ r in (0 : ℝ)..sigma,
          (1 / 2 * Real.exp (-z * sigma) * (Real.exp (z * r) * Real.sin (k * r))
            + 1 / 2 * Real.exp (-z * sigma) * (Real.exp (-z * r) * Real.sin (k * r))
            - Real.exp (-z * sigma) * Real.sin (k * r)) := by
    refine intervalIntegral.integral_congr (fun r _ => ?_)
    simp only [coshRatio]
    rw [show z * (r - sigma) = z * r + -z * sigma by ring,
      show -z * (r + sigma) = -z * r + -z * sigma by ring, Real.exp_add, Real.exp_add]
    ring
  rw [hcongr,
    intervalIntegral.integral_sub ((hep.const_mul _).add (hem.const_mul _)) (hs.const_mul _),
    intervalIntegral.integral_add (hep.const_mul _) (hem.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    exp_pos_sin_integral hzk, exp_sin_integral hzk, psi0_formula hk]

/-! ### Step 1 — the support collapse `(0,∞) → (0,σ)` -/

/-- **The radial (sine) transform of a core-supported function collapses to an interval integral.**
If `f` vanishes on `[σ,∞)`, then `radial_fourier f k = (4π/k)·∫₀^σ r·f(r)·sin(kr)` — the `Set.Ioi 0`
integral in `radial_fourier`'s definition reduces to `Set.Ioc 0 σ`, i.e. the `intervalIntegral` on
`[0,σ]`.  Generalises `HardSphere.radial_fourier_c_HS_eq_intervalIntegral` from `c_HS` to any core
function; this is what lets the core-DCF correction (supported on the core) be transformed with the
`psiN`/`yuk`/`coshRatio` interval formulas of this file. -/
theorem radial_fourier_of_core_support (f : ℝ → ℝ) {k sigma : ℝ} (hsigma : 0 < sigma)
    (hsupp : ∀ r, sigma < r → f r = 0) :
    radial_fourier f k = (4 * Real.pi / k) * ∫ r in (0 : ℝ)..sigma, r * f r * Real.sin (k * r) := by
  unfold radial_fourier
  congr 1
  have hpt : Set.EqOn (fun r => r * f r * Real.sin (k * r))
      ((Set.Ioc 0 sigma).indicator (fun r => r * f r * Real.sin (k * r)))
      (Set.Ioi (0 : ℝ)) := by
    intro r hr0
    by_cases hr : r ∈ Set.Ioc (0 : ℝ) sigma
    · rw [Set.indicator_of_mem hr]
    · rw [Set.indicator_of_notMem hr]
      have hrgt : sigma < r := by
        simp only [Set.mem_Ioc, not_and, not_le] at hr
        exact hr hr0
      simp [hsupp r hrgt]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt,
    MeasureTheory.setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_self_of_subset_right Set.Ioc_subset_Ioi_self,
    ← intervalIntegral.integral_of_le hsigma.le]

/-! ### Step 2 — the assembly (linearity)

`r · coreCorrection(r)` — the radial-weighted core-DCF correction, the smooth integrand of the
transform — is `−[da·r + db·r² + ½ξ·da·r⁴ + (v/z)(1−e^{−zr}) + (v²/2Kz²)·coshRatio]` with
`da = a − a_HS`, `db = b − b_HS`.  Its sine integral splits, by linearity alone, into the five
sub-integrals whose closed forms are `psi1/2/4_formula`, `one_sub_exp_sin_integral` and
`coshRatio_sin_integral`.  Keeping the sub-integrals unexpanded here makes this a pure-linearity
lemma; the caller (step 3, the `a,b,w↔D` match) rewrites them with the closed forms. -/

/-- The radial-weighted core-DCF correction's sine integral, split by linearity into the five
sub-integrals of the integral layer.  Fully generic in the coefficients `c₁…c₅`; the caller
(step 3) supplies `c₁ = da`, `c₂ = db`, `c₃ = ½ξ·da`, `c₄ = v/z`, `c₅ = v²/(2Kz²)` and the overall
sign. -/
theorem coreCorr_sine_integral (c1 c2 c3 c4 c5 z sigma k : ℝ) :
    ∫ r in (0 : ℝ)..sigma,
        (c1 * r + c2 * r ^ 2 + c3 * r ^ 4 + c4 * (1 - Real.exp (-z * r))
          + c5 * coshRatio z sigma r) * Real.sin (k * r)
      = c1 * (∫ r in (0 : ℝ)..sigma, r * Real.sin (k * r))
        + c2 * (∫ r in (0 : ℝ)..sigma, r ^ 2 * Real.sin (k * r))
        + c3 * (∫ r in (0 : ℝ)..sigma, r ^ 4 * Real.sin (k * r))
        + c4 * (∫ r in (0 : ℝ)..sigma, (1 - Real.exp (-z * r)) * Real.sin (k * r))
        + c5 * (∫ r in (0 : ℝ)..sigma, coshRatio z sigma r * Real.sin (k * r)) := by
  have h1 : IntervalIntegrable (fun r => c1 * (r * Real.sin (k * r))) volume 0 sigma :=
    (continuous_const.mul (continuous_id.mul
      (Real.continuous_sin.comp (by fun_prop)))).intervalIntegrable 0 sigma
  have h2 : IntervalIntegrable (fun r => c2 * (r ^ 2 * Real.sin (k * r))) volume 0 sigma :=
    (continuous_const.mul ((continuous_id.pow 2).mul
      (Real.continuous_sin.comp (by fun_prop)))).intervalIntegrable 0 sigma
  have h3 : IntervalIntegrable (fun r => c3 * (r ^ 4 * Real.sin (k * r))) volume 0 sigma :=
    (continuous_const.mul ((continuous_id.pow 4).mul
      (Real.continuous_sin.comp (by fun_prop)))).intervalIntegrable 0 sigma
  have h4 : IntervalIntegrable
      (fun r => c4 * ((1 - Real.exp (-z * r)) * Real.sin (k * r))) volume 0 sigma :=
    (continuous_const.mul (((continuous_const.sub (Real.continuous_exp.comp (by fun_prop))).mul
      (Real.continuous_sin.comp (by fun_prop))))).intervalIntegrable 0 sigma
  have h5 : IntervalIntegrable (fun r => c5 * (coshRatio z sigma r * Real.sin (k * r)))
      volume 0 sigma := by
    apply Continuous.intervalIntegrable
    unfold coshRatio; fun_prop
  have hcongr : ∫ r in (0 : ℝ)..sigma,
        (c1 * r + c2 * r ^ 2 + c3 * r ^ 4 + c4 * (1 - Real.exp (-z * r))
          + c5 * coshRatio z sigma r) * Real.sin (k * r)
      = ∫ r in (0 : ℝ)..sigma,
          (c1 * (r * Real.sin (k * r)) + c2 * (r ^ 2 * Real.sin (k * r))
            + c3 * (r ^ 4 * Real.sin (k * r))
            + c4 * ((1 - Real.exp (-z * r)) * Real.sin (k * r))
            + c5 * (coshRatio z sigma r * Real.sin (k * r))) :=
    intervalIntegral.integral_congr (fun r _ => by ring)
  rw [hcongr,
    intervalIntegral.integral_add (((h1.add h2).add h3).add h4) h5,
    intervalIntegral.integral_add ((h1.add h2).add h3) h4,
    intervalIntegral.integral_add (h1.add h2) h3,
    intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

/-! ### Step 3 glue — the core-DCF correction as a function, and its radial transform -/

/-- The MSA core-DCF correction as a **function** (core-supported): on `[0,σ]` it is
`c₁ + c₂r + c₃r³ + c₄(1−e^{−zr})/r + c₅·coshRatio/r` (so that `r··` is the smooth integrand of
`coreCorr_sine_integral`), and `0` beyond `σ`.  The `1/r` terms are `0/0 = 0` at `r = 0`, which is
harmless — the radial weight `r` and the `sin(kr)` factor both vanish there. -/
noncomputable def coreCorrection (c1 c2 c3 c4 c5 z sigma : ℝ) (r : ℝ) : ℝ :=
  if r ≤ sigma then
    c1 + c2 * r + c3 * r ^ 3 + c4 * (1 - Real.exp (-z * r)) / r + c5 * coshRatio z sigma r / r
  else 0

/-- **Step 3 glue — the closed form of `radial_fourier(coreCorrection)`.**  The support collapse
reduces it to `(4π/k)·∫₀^σ r·coreCorrection·sin`, the `1/r`s cancel the radial weight (`sin(kr)`
covers `r = 0`), and `coreCorr_sine_integral` splits it into the five sub-integrals of the layer.
Ready for the `a,b,w↔D` match: the caller supplies `c₁ = da`, `c₂ = db`, `c₃ = ½ξ·da`, `c₄ = v/z`,
`c₅ = v²/(2Kz²)` and rewrites the sub-integrals with `psi1/2/4_formula`,
`one_sub_exp_sin_integral`, `coshRatio_sin_integral`. -/
theorem radial_fourier_coreCorrection (c1 c2 c3 c4 c5 z sigma k : ℝ) (hsigma : 0 < sigma) :
    radial_fourier (coreCorrection c1 c2 c3 c4 c5 z sigma) k
      = (4 * Real.pi / k) *
          (c1 * (∫ r in (0 : ℝ)..sigma, r * Real.sin (k * r))
            + c2 * (∫ r in (0 : ℝ)..sigma, r ^ 2 * Real.sin (k * r))
            + c3 * (∫ r in (0 : ℝ)..sigma, r ^ 4 * Real.sin (k * r))
            + c4 * (∫ r in (0 : ℝ)..sigma, (1 - Real.exp (-z * r)) * Real.sin (k * r))
            + c5 * (∫ r in (0 : ℝ)..sigma, coshRatio z sigma r * Real.sin (k * r))) := by
  rw [radial_fourier_of_core_support _ hsigma
    (fun r hr => by simp only [coreCorrection, if_neg (not_le.mpr hr)])]
  rw [← coreCorr_sine_integral c1 c2 c3 c4 c5 z sigma k]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [Set.uIcc_of_le hsigma.le] at hr
  by_cases hr0 : r = 0
  · subst hr0; simp
  · simp only [coreCorrection, if_pos hr.2]
    field_simp

end FMSA.MSAExact
