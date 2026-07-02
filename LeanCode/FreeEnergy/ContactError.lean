/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib
import LeanCode.FreeEnergy.LJIntegral
import LeanCode.FMSAPoly.EijStructure

/-!
# Task F.5 — Contact-value approximation error formula

**Source:** [chsY] Eq. 41; FMSA_poly `betaf1_inner` (line 1435), `betaf2_lj` (line 1524)

The FMSA_poly code approximates the inner-core free energy integral
    ∫_sigma^R g(r) · u_LJ(r) · r^2 dr
by the *contact-value approximation*, replacing g(r) with its value at the cutoff g(R):
    g(R) · ∫_sigma^R u_LJ(r) · r^2 dr.

The error in this approximation is:

    err = ∫_sigma^R g(r)·u_LJ(r)·r^2 dr  -  g(R)·∫_sigma^R u_LJ(r)·r^2 dr

**Task F.5(a) — exact error formula** (no approximation):
    err = ∫_sigma^R (g(r) - g(R)) · u_LJ(r) · r^2 dr
This follows from linearity of integration.

**Task F.5(b) — Lipschitz error bound** (abstract; requires explicit g for numeric value):
    |err| ≤ M · ∫_sigma^R |u_LJ(r) · r^2| dr
when |g(r) - g(R)| ≤ M for all r ∈ [sigma, R].  Proved here for any M.
The explicit g = g0_HS + g^(1) carries a sorry (inverse Laplace), so the numeric
value of M cannot be closed in the current development.

**Prerequisites completed:**
- OZ.1: `c_HS_inner`, PY DCF (`PYDCF.lean`)
- OZ.3: `C_HS_laplace`, `S0` (`PYOZ.lean`)
- OZ.4: linearized OZ identity (`PYOZ.lean`)
- F.2b: `lj_integral` identity (`LJIntegral.lean`)  ← used directly here

**Notation note:** Lean 4's `∫ r in a..b, expr` notation is *greedy*: the body `expr`
extends to the end of the current expression.  So `∫ r, A r - ∫ r, B r` parses as the
single integral `∫ r, (A r - ∫ r, B r)`, NOT as two integrals subtracted.  Explicit
parentheses `(∫ r, A r) - (∫ r, B r)` are required wherever a standalone integral
appears on the subtracted side.
-/

open MeasureTheory intervalIntegral Real Set

namespace FMSA.FreeEnergy

/-! ### Part (a) — Abstract contact-value error formula -/

/-- **Task F.5(a) — Contact-value error formula (abstract):**

For any integrable functions `g, u : ℝ → ℝ` and any constant `gR` (the contact value g(R)),
the contact-value approximation error satisfies the exact identity:

    (∫_sigma^R g(r)·u(r)·r^2 dr) - gR · (∫_sigma^R u(r)·r^2 dr)
      =  ∫_sigma^R (g(r) - gR) · u(r) · r^2 dr

This is a pure linearity identity: the error equals the integral of the deviation
(g(r) - g(R)) weighted by u(r) · r^2.  No approximation or explicit form of g is needed.

Note: explicit parentheses around each `∫` in the LHS are required to prevent the greedy
`∫` notation from swallowing the subtraction (see module docstring). -/
theorem f5_contact_error_formula (sigma R gR : ℝ) (g u : ℝ → ℝ)
    (hgu : IntervalIntegrable (fun r => g r * u r * r ^ 2) volume sigma R)
    (hu : IntervalIntegrable (fun r => u r * r ^ 2) volume sigma R) :
    (∫ r in sigma..R, g r * u r * r ^ 2) - gR * (∫ r in sigma..R, u r * r ^ 2) =
    ∫ r in sigma..R, (g r - gR) * u r * r ^ 2 := by
  -- Bridge: rewrite RHS integrand via ring identity
  have hcongr : ∫ r in sigma..R, (g r - gR) * u r * r ^ 2 =
                ∫ r in sigma..R, (g r * u r * r ^ 2 - gR * (u r * r ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro r _; ring
  -- Split integral of difference into difference of integrals
  -- Explicit parens around each ∫ in the RHS prevent greedy-notation ambiguity
  have hsub : ∫ r in sigma..R, (g r * u r * r ^ 2 - gR * (u r * r ^ 2)) =
              (∫ r in sigma..R, g r * u r * r ^ 2) - (∫ r in sigma..R, gR * (u r * r ^ 2)) := by
    apply intervalIntegral.integral_sub hgu (hu.const_mul gR)
  -- Pull constant gR out of the integral
  have hconst : ∫ r in sigma..R, gR * (u r * r ^ 2) = gR * ∫ r in sigma..R, u r * r ^ 2 := by
    apply intervalIntegral.integral_const_mul
  linear_combination -hcongr - hsub + hconst

/-! ### LJ specialization (Task F.2b link) -/

/-- The original LJ integrand `((sigma/r)1^2-(sigma/r)^6)·r^2` is IntervalIntegrable on [sigma, R]
for 0 < sigma ≤ R (no singularity since r ≥ sigma > 0 on the interval).
Uses `lj_integrand_eq` to rewrite to the power-law form and `lj_integrable` from F.2b. -/
lemma lj_u_integrable {sigma R : ℝ} (hsigma : 0 < sigma) (hsigmaR : sigma <= R) :
    IntervalIntegrable (fun r => ((sigma / r) ^ 12 - (sigma / r) ^ 6) * r ^ 2) volume sigma R := by
  have heq : (fun r => ((sigma / r) ^ 12 - (sigma / r) ^ 6) * r ^ 2) =
             (fun r => sigma ^ 12 / r ^ 10 - sigma ^ 6 / r ^ 4) := by
    ext r
    by_cases hr : r = 0
    · simp [hr]
    · exact lj_integrand_eq hr
  rw [heq]
  exact lj_integrable hsigma hsigmaR

/-- **Task F.5 — LJ contact-value error formula:**

Specializing `f5_contact_error_formula` to the LJ potential u(r) = (sigma/r)1^2 - (sigma/r)^6
and substituting the closed form ∫_sigma^R u·r^2 dr from Task F.2b (`lj_integral`):

    (∫_sigma^R g(r)·((sigma/r)1^2-(sigma/r)^6)·r^2 dr)
      - gR · R^3·(-(sigma/R)1^2/9 + (sigma/R)^6/3 - 2(sigma/R)^3/9)
      = ∫_sigma^R (g(r) - gR)·((sigma/r)1^2-(sigma/r)^6)·r^2 dr -/
theorem f5_lj_contact_error {sigma R gR : ℝ} (hsigma : 0 < sigma) (hR : 0 < R)
    (hsigmaR : sigma <= R)
    (g : ℝ → ℝ)
    (hg : IntervalIntegrable (fun r => g r * ((sigma / r) ^ 12 - (sigma / r) ^ 6) * r ^ 2)
          volume sigma R) :
    (∫ r in sigma..R, g r * ((sigma / r) ^ 12 - (sigma / r) ^ 6) * r ^ 2) -
      gR * (R ^ 3 * (-(sigma / R) ^ 12 / 9 + (sigma / R) ^ 6 / 3 - 2 * (sigma / R) ^ 3 / 9)) =
    ∫ r in sigma..R, (g r - gR) * ((sigma / r) ^ 12 - (sigma / r) ^ 6) * r ^ 2 := by
  have hu : IntervalIntegrable
      (fun r => ((sigma / r) ^ 12 - (sigma / r) ^ 6) * r ^ 2) volume sigma R :=
    lj_u_integrable hsigma hsigmaR
  -- Bridge: ∫(sigma/r)1^2-(sigma/r)^6)·r^2 = R^3·(...) via lj_integral (which uses power-law form)
  have hint : ∫ r in sigma..R, ((sigma / r) ^ 12 - (sigma / r) ^ 6) * r ^ 2 =
              R ^ 3 * (-(sigma / R) ^ 12 / 9 + (sigma / R) ^ 6 / 3 - 2 * (sigma / R) ^ 3 / 9) := by
    have heq : (fun r => ((sigma / r) ^ 12 - (sigma / r) ^ 6) * r ^ 2) =
               (fun r => sigma ^ 12 / r ^ 10 - sigma ^ 6 / r ^ 4) := by
      ext r
      by_cases hr : r = 0
      · simp [hr]
      · exact lj_integrand_eq hr
    rw [heq]
    exact lj_integral hsigma hR hsigmaR
  rw [← hint]
  exact f5_contact_error_formula sigma R gR g (fun r => (sigma / r) ^ 12 - (sigma / r) ^ 6) hg hu

/-! ### Part (b) — Abstract Lipschitz error bound -/

/-- **Task F.5(b) — Lipschitz error bound (abstract):**

If |g(r) - gR| ≤ M for all r ∈ [sigma, R], then the contact-value error satisfies:

    |∫_sigma^R (g(r) - gR)·u(r)·r^2 dr| ≤ M · ∫_sigma^R |u(r)·r^2| dr

Proof: `|∫f| ≤ ∫|f|` (norm integral ≤ integral of norm), then
`|(g(r)-gR)·u(r)·r^2| = |g(r)-gR|·|u(r)·r^2| ≤ M·|u(r)·r^2|` pointwise,
then pull the constant M out of the integral.

**Note:** The explicit Lipschitz constant M for g = g0_HS + g^(1) requires the
closed-form pair correlation function, which carries a sorry (inverse Laplace transform
of `C_HS_laplace / (1 - rho·C_HS_laplace)`).  This theorem proves the bound for *any* M. -/
theorem f5_error_bound {sigma R gR M : ℝ} (hsigmaR : sigma <= R)
    (g u : ℝ → ℝ)
    (hbound : ∀ r ∈ Icc sigma R, |g r - gR| <= M)
    (hgu : IntervalIntegrable (fun r => (g r - gR) * u r * r ^ 2) volume sigma R)
    (huabs : IntervalIntegrable (fun r => |u r * r ^ 2|) volume sigma R) :
    |∫ r in sigma..R, (g r - gR) * u r * r ^ 2| <=
    M * ∫ r in sigma..R, |u r * r ^ 2| := by
  -- Step 1: |∫f| ≤ ∫|f| via norm bound, converting ‖·‖ → |·| for ℝ
  have h1 : |∫ r in sigma..R, (g r - gR) * u r * r ^ 2| <=
            ∫ r in sigma..R, |(g r - gR) * u r * r ^ 2| := by
    have h := intervalIntegral.norm_integral_le_integral_norm
      (f := fun r => (g r - gR) * u r * r ^ 2) (μ := volume) hsigmaR
    simpa only [Real.norm_eq_abs] using h
  -- Step 2: get |f| integrable from hgu.norm, converting ‖·‖ → |·|
  have hgu_abs : IntervalIntegrable (fun r => |(g r - gR) * u r * r ^ 2|) volume sigma R := by
    have h := hgu.norm
    simpa only [Real.norm_eq_abs] using h
  -- Step 3: pointwise: |(g-gR)·u·r^2| = |g-gR|·|u·r^2| ≤ M·|u·r^2|
  -- Regroup (g-gR) * u * r^2 = (g-gR) * (u * r^2) via ← mul_assoc, then abs_mul
  have h2 : ∀ r ∈ Icc sigma R, |(g r - gR) * u r * r ^ 2| <= M * |u r * r ^ 2| := by
    intro r hrI
    have heq : |(g r - gR) * u r * r ^ 2| = |g r - gR| * |u r * r ^ 2| := by
      have h := abs_mul (g r - gR) (u r * r ^ 2)
      rwa [← mul_assoc] at h
    rw [heq]
    exact mul_le_mul_of_nonneg_right (hbound r hrI) (abs_nonneg _)
  -- Step 4: integrate the pointwise bound
  have h3 : ∫ r in sigma..R, |(g r - gR) * u r * r ^ 2| <=
            ∫ r in sigma..R, M * |u r * r ^ 2| :=
    intervalIntegral.integral_mono_on hsigmaR hgu_abs (huabs.const_mul M) h2
  -- Step 5: pull constant M out of integral
  have h4 : ∫ r in sigma..R, M * |u r * r ^ 2| = M * ∫ r in sigma..R, |u r * r ^ 2| :=
    intervalIntegral.integral_const_mul M _
  linarith [le_trans h3 h4.le]

/-! ### FMSA_GA_matrix_mix improvement (F.5) — concrete Lipschitz bound via eij variation -/

section PathBImprovement

open FMSA.EijStructure

/-- **Exact variation formula for eij:**
`eij(R) - eij(r) = Σ_k A_k · (1 - exp(-z_k · (R-r)))`.
Follows from `eij_at_contact` and the definition. -/
theorem eij_contact_variation_formula {n : ℕ} (A z : Fin n → ℝ) (R r : ℝ) :
    eij A z R R - eij A z R r =
    ∑ k : Fin n, A k * (1 - Real.exp (-(z k) * (R - r))) := by
  unfold eij
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
  rw [← Finset.sum_sub_distrib]
  congr 1; ext k; ring

/-- **FMSA_GA_matrix_mix eij contact variation bound (for F.5):**

For r ∈ [sigma, R] with A_k ≥ 0 and z_k ≥ 0:
1. `eij(R) - eij(r) ≥ 0`  (eij increases toward contact when amplitudes are non-negative)
2. `eij(R) - eij(r) ≤ Σ_k A_k · (1 - exp(-z_k · (R-sigma)))`  (max variation is at r = sigma)

Part 2 gives a sorry-free explicit M for `f5_error_bound` applied to the FMSA_GA_matrix_mix DCF. -/
theorem eij_contact_variation_bound {n : ℕ} (A z : Fin n → ℝ) (sigma R r : ℝ)
    (hA : ∀ k, 0 <= A k) (hz : ∀ k, 0 <= z k)
    (hsigmar : sigma <= r) (hrR : r <= R) :
    0 <= eij A z R R - eij A z R r ∧
    eij A z R R - eij A z R r <=
    ∑ k : Fin n, A k * (1 - Real.exp (-(z k) * (R - sigma))) := by
  rw [eij_contact_variation_formula]
  refine ⟨Finset.sum_nonneg fun k _ => ?_, Finset.sum_le_sum fun k _ => ?_⟩
  · apply mul_nonneg (hA k)
    have harg : -(z k) * (R - r) <= 0 := by nlinarith [hz k, sub_nonneg.mpr hrR]
    have hexp : Real.exp (-(z k) * (R - r)) <= 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr harg
    linarith
  · apply mul_le_mul_of_nonneg_left _ (hA k)
    have hle : Real.exp (-(z k) * (R - sigma)) <= Real.exp (-(z k) * (R - r)) :=
      Real.exp_le_exp.mpr (by nlinarith [hz k, hsigmar])
    linarith

/-- **F.5 improvement — concrete Lipschitz error bound via FMSA_GA_matrix_mix eij:**

When g(r) = eij(r) (the FMSA_GA_matrix_mix inner-core exponential function),
the contact-value approximation error satisfies:

    |∫_sigma^R (eij(r) - eij(R)) · u(r) · r^2 dr|
      ≤  (Σ_k A_k · (1 - exp(-z_k · (R-sigma)))) · ∫_sigma^R |u(r) · r^2| dr

The Lipschitz constant M = Σ A_k · (1 - exp(-z_k · (R-sigma))) is the **total variation of eij
on [sigma, R]**, computable from FMSA_GA_matrix_mix parameters (A_k, z_k, sigma, R) with no sorry.
This improves `f5_error_bound` from abstract M to an explicit formula. -/
theorem f5_ga_matrix_mix_error_bound {n : ℕ} (A z : Fin n → ℝ) (sigma R : ℝ)
    (hA : ∀ k, 0 <= A k) (hz : ∀ k, 0 <= z k) (hsigmaR : sigma <= R)
    (u : ℝ → ℝ)
    (hgu : IntervalIntegrable
      (fun r => (eij A z R r - eij A z R R) * u r * r ^ 2) volume sigma R)
    (huabs : IntervalIntegrable (fun r => |u r * r ^ 2|) volume sigma R) :
    |∫ r in sigma..R, (eij A z R r - eij A z R R) * u r * r ^ 2| <=
    (∑ k : Fin n, A k * (1 - Real.exp (-(z k) * (R - sigma)))) *
    ∫ r in sigma..R, |u r * r ^ 2| := by
  exact f5_error_bound hsigmaR (fun r => eij A z R r) u
    (fun r hr => by
      have hvar := eij_contact_variation_bound A z sigma R r hA hz hr.1 hr.2
      rw [abs_of_nonpos (by linarith [hvar.1])]
      linarith [hvar.2])
    hgu huabs

end PathBImprovement

end FMSA.FreeEnergy
