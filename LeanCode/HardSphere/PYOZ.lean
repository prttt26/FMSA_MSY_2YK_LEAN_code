/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import LeanCode.HardSphere.BaxterFactor
import LeanCode.HardSphere.PYDCF

/-!
# Task OZ.3 — PY Reference DCF Laplace Transform and OZ Structure Factor

**Source:** Wertheim (1963), Thiele (1963), Baxter (1970)

## Overview

The Laplace-weighted inner-core transform of the PY DCF:

    Ĉ_HS(s) = ∫0^sigma r · c_HS(r) · e^{-sr} dr

equals the polynomial integral (the integrand agrees a.e. on [0,sigma]):

    Ĉ_HS(s) = -alpha0 · φ1(sigma,s) - (alpha1/sigma) · 2φ2(sigma,s) - (alpha3/sigma^3) · φ4(sigma,s)

with φ1, 2φ2 from Task 2.1 and the new φ4 integral proved here:

    φ4(sigma,s) = ∫0^sigma r^4 e^{-sr} dr
             = (24 - (24 + 24ssigma + 12s^2sigma^2 + 4s^3sigma^3 + s^4sigma^4) e^{-ssigma}) / s^5

The **structure factor** `S0(s) = 1/(1 - rho · Ĉ_HS(s))` and the **OZ algebraic identity**:

    H0 · (1 - rho · Ĉ_HS(s)) = Ĉ_HS(s)  →  H0 = Ĉ_HS(s) · S0(s)

provide the foundation for Task OZ.4.

## Sorries in this file

- `C_HS_laplace_eq_cHS`: the a.e. equality between the polynomial and piecewise integrands
  requires measure-theory congr_ae with singleton null set (clear but API-intensive).

## Note on g0_HS

`g0_HS_outer`, `g0_HS`, `g0_HS_core`, `g0_HS_laplace_spec`, and `g0_HS_contact_value` are
defined in `PYOZ_GHS.lean` (which imports this file), where `g0_HS_outer` is given the
concrete definition `fun r => 1 + oz_h eta sigma rho r` using the OZ fixed point.
-/

open MeasureTheory intervalIntegral Real Set

namespace FMSA.HardSphere

/-! ### φ4 auxiliary integral: ∫0^sigma r^4 · e^{-sr} dr -/

/-- Antiderivative of `r^4 · e^{-sr}`:
    `F4(r) = -(r^4/s + 4·(r^3/s^2) + 12·(r^2/s^3) + 24·(r/s^4) + 24/s^5) · e^{-sr}`.

    Differentiation: F4'(r) = (-B'(r) + s·B(r))·e^{-sr} where B(r) = r^4/s + 4(r^3/s^2) + …,
    and the telescoping cancellation gives r^4·e^{-sr}. -/
private lemma phi4_hasDerivAt {s : ℝ} (hs : s ≠ 0) (r : ℝ) :
    HasDerivAt (fun r => -(r ^ 4 / s + 4 * (r ^ 3 / s ^ 2) + 12 * (r ^ 2 / s ^ 3) +
                           24 * (r / s ^ 4) + 24 / s ^ 5) * Real.exp (-s * r))
               (r ^ 4 * Real.exp (-s * r)) r := by
  have hE : HasDerivAt (fun x => Real.exp (-s * x)) (Real.exp (-s * r) * (-s)) r := by
    have h := ((hasDerivAt_id r).const_mul (-s)).exp
    simp only [mul_one] at h; exact h
  -- Derivatives of each monomial
  have hx4 : HasDerivAt (fun x : ℝ => x ^ 4) (4 * r ^ 3) r := by
    have h := hasDerivAt_pow (𝕜 := ℝ) 4 r; simpa [Nat.cast_ofNat] using h
  have hx3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * r ^ 2) r := by
    have h := hasDerivAt_pow (𝕜 := ℝ) 3 r; simpa [Nat.cast_ofNat] using h
  have hx2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    have h := hasDerivAt_pow (𝕜 := ℝ) 2 r; simpa [Nat.cast_ofNat, pow_one] using h
  -- Derivative of each polynomial term (form matches .div_const / .const_mul output)
  have h1 : HasDerivAt (fun x => x ^ 4 / s) (4 * r ^ 3 / s) r := hx4.div_const s
  have h2 : HasDerivAt (fun x => 4 * (x ^ 3 / s ^ 2)) (12 * r ^ 2 / s ^ 2) r :=
    ((hx3.div_const (s ^ 2)).const_mul 4).congr_deriv (by ring)
  have h3 : HasDerivAt (fun x => 12 * (x ^ 2 / s ^ 3)) (24 * r / s ^ 3) r :=
    ((hx2.div_const (s ^ 3)).const_mul 12).congr_deriv (by ring)
  have h4 : HasDerivAt (fun x => 24 * (x / s ^ 4)) (24 / s ^ 4) r :=
    ((hasDerivAt_id r).div_const (s ^ 4) |>.const_mul 24).congr_deriv (by ring)
  have h5 : HasDerivAt (fun _ : ℝ => (24 : ℝ) / s ^ 5) 0 r := hasDerivAt_const _ _
  -- Derivative of B(r) = r^4/s + 4(r^3/s^2) + 12(r^2/s^3) + 24(r/s^4) + 24/s^5
  have hB : HasDerivAt (fun x => x ^ 4 / s + 4 * (x ^ 3 / s ^ 2) + 12 * (x ^ 2 / s ^ 3) +
                                  24 * (x / s ^ 4) + 24 / s ^ 5)
                       (4 * r ^ 3 / s + 12 * r ^ 2 / s ^ 2 + 24 * r / s ^ 3 + 24 / s ^ 4) r := by
    have h := ((((h1.add h2).add h3).add h4).add h5)
    simp only [add_zero] at h
    exact h
  -- Product rule: d/dr[-B · exp] = (-B' + s·B)·exp = r^4·exp (telescoping)
  exact (hB.neg.mul hE).congr_deriv (show
      -(4 * r ^ 3 / s + 12 * r ^ 2 / s ^ 2 + 24 * r / s ^ 3 + 24 / s ^ 4) *
        Real.exp (-s * r) +
      -(r ^ 4 / s + 4 * (r ^ 3 / s ^ 2) + 12 * (r ^ 2 / s ^ 3) +
        24 * (r / s ^ 4) + 24 / s ^ 5) * (Real.exp (-s * r) * (-s)) =
      r ^ 4 * Real.exp (-s * r) by field_simp [hs]; ring)

/-- **φ4 formula:** `∫0^sigma r^4 exp(-sr) dr = (24 - (24 + 24ssigma + 12s^2sigma^2 + 4s^3sigma^3 + s^4sigma^4) exp(-ssigma)) / s^5`

Antiderivative: `F4(r) = -(r^4/s + 4(r^3/s^2) + 12(r^2/s^3) + 24(r/s^4) + 24/s^5)·exp(-sr)`. -/
theorem phi4_formula {s : ℝ} (hs : s ≠ 0) (sigma : ℝ) :
    ∫ r in (0 : ℝ)..sigma, r ^ 4 * Real.exp (-s * r) =
    (24 - (24 + 24 * s * sigma + 12 * s ^ 2 * sigma ^ 2 + 4 * s ^ 3 * sigma ^ 3 + s ^ 4 * sigma ^ 4) *
      Real.exp (-s * sigma)) / s ^ 5 := by
  have hint : IntervalIntegrable (fun r => r ^ 4 * Real.exp (-s * r)) volume 0 sigma :=
    ((continuous_id.pow 4).mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).intervalIntegrable 0 sigma
  rw [integral_eq_sub_of_hasDerivAt (fun r _ => phi4_hasDerivAt hs r) hint]
  simp only [mul_zero, Real.exp_zero, mul_one, zero_div, zero_add, zero_pow,
             ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  field_simp [hs]; ring

/-! ### r^2 integral: ∫0^sigma r^2 · e^{-sr} dr = 2 · φ2(sigma,s) -/

/-- `∫0^sigma r^2 exp(-sr) dr = (2 - (2 + 2ssigma + s^2sigma^2) exp(-ssigma)) / s^3`

Derived from `phi2_formula` (which has `r^2/2`) by scaling. -/
private lemma phi2_r2_formula {s : ℝ} (hs : s ≠ 0) (sigma : ℝ) :
    ∫ r in (0 : ℝ)..sigma, r ^ 2 * Real.exp (-s * r) =
    (2 - (2 + 2 * s * sigma + s ^ 2 * sigma ^ 2) * Real.exp (-s * sigma)) / s ^ 3 := by
  have h2 : ∫ r in (0:ℝ)..sigma, r ^ 2 * Real.exp (-s * r) =
             2 * ∫ r in (0:ℝ)..sigma, r ^ 2 / 2 * Real.exp (-s * r) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext r; ring
  rw [h2, phi2_formula hs sigma]
  field_simp [pow_ne_zero 3 hs]

/-! ### Ĉ_HS: Laplace-weighted inner-core integral (polynomial form) -/

/-- **Task OZ.3 definition:** Laplace-weighted inner-core integral using the PY polynomial form:

    C_HS_laplace(eta, sigma, s) = ∫0^sigma r · (-alpha0 - alpha1·(r/sigma) - alpha3·(r/sigma)^3) · e^{-sr} dr

This equals `∫0^sigma r · c_HS(r) · e^{-sr} dr` a.e. (the integrand agrees on [0,sigma) where
c_HS = polynomial; they differ only at the measure-zero point {sigma}). -/
noncomputable def C_HS_laplace (eta sigma s : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..sigma,
    r * (-(py_a0 eta + py_a1 eta * (r / sigma) + py_a3 eta * (r / sigma) ^ 3)) * Real.exp (-s * r)

/-- **Task OZ.3 main result:** Closed form for `C_HS_laplace` via φ1, 2φ2, φ4:

    Ĉ_HS(s) = -alpha0 · (1-(1+ssigma)E)/s^2
             - (alpha1/sigma) · (2-(2+2ssigma+s^2sigma^2)E)/s^3
             - (alpha3/sigma^3) · (24-(24+24ssigma+12s^2sigma^2+4s^3sigma^3+s^4sigma^4)E)/s^5

where `E = exp(-ssigma)`. -/
theorem C_HS_laplace_formula {eta sigma s : ℝ} (hsigma : 0 < sigma) (hs : s ≠ 0) :
    C_HS_laplace eta sigma s =
    -py_a0 eta * (1 - (1 + s * sigma) * Real.exp (-s * sigma)) / s ^ 2 +
    -(py_a1 eta / sigma) * (2 - (2 + 2 * s * sigma + s ^ 2 * sigma ^ 2) * Real.exp (-s * sigma)) / s ^ 3 +
    -(py_a3 eta / sigma ^ 3) *
      (24 - (24 + 24 * s * sigma + 12 * s ^ 2 * sigma ^ 2 + 4 * s ^ 3 * sigma ^ 3 + s ^ 4 * sigma ^ 4) *
        Real.exp (-s * sigma)) / s ^ 5 := by
  unfold C_HS_laplace
  -- Expand: r·(-alpha0 - alpha1(r/sigma) - alpha3(r/sigma)^3)·exp = (-alpha0)·(r·exp) + (-alpha1/sigma)·(r^2·exp) + (-alpha3/sigma^3)·(r^4·exp)
  have hexpand : ∀ r : ℝ,
      r * (-(py_a0 eta + py_a1 eta * (r / sigma) + py_a3 eta * (r / sigma) ^ 3)) * Real.exp (-s * r) =
      (-py_a0 eta) * (r * Real.exp (-s * r)) +
      (-(py_a1 eta / sigma)) * (r ^ 2 * Real.exp (-s * r)) +
      (-(py_a3 eta / sigma ^ 3)) * (r ^ 4 * Real.exp (-s * r)) :=
    fun r => by field_simp [hsigma.ne']; ring
  simp_rw [hexpand]
  -- Integrability for each term
  have hi1 : IntervalIntegrable (fun r => (-py_a0 eta) * (r * Real.exp (-s * r))) volume 0 sigma :=
    (continuous_const.mul (continuous_id.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)))).intervalIntegrable 0 sigma
  have hi2 : IntervalIntegrable
      (fun r => (-(py_a1 eta / sigma)) * (r ^ 2 * Real.exp (-s * r))) volume 0 sigma :=
    (continuous_const.mul ((continuous_id.pow 2).mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)))).intervalIntegrable 0 sigma
  have hi4 : IntervalIntegrable
      (fun r => (-(py_a3 eta / sigma ^ 3)) * (r ^ 4 * Real.exp (-s * r))) volume 0 sigma :=
    (continuous_const.mul ((continuous_id.pow 4).mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)))).intervalIntegrable 0 sigma
  -- Split the integral and apply individual formulas
  rw [intervalIntegral.integral_add (hi1.add hi2) hi4,
      intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      phi1_formula hs sigma, phi2_r2_formula hs sigma, phi4_formula hs sigma]
  field_simp [hs, hsigma.ne']

/-- The polynomial-form integral equals the piecewise c_HS integral on [0,sigma].

The two integrands agree on [0,sigma): for r < sigma, c_HS r = -(alpha0+alpha1(r/sigma)+alpha3(r/sigma)^3).
They differ only at r = sigma (where c_HS(sigma) = 0 but the polynomial ≠ 0), a null set. -/
theorem C_HS_laplace_eq_cHS {eta sigma s : ℝ} (_hsigma : 0 < sigma) :
    C_HS_laplace eta sigma s = ∫ r in (0:ℝ)..sigma, r * c_HS eta sigma r * Real.exp (-s * r) := by
  unfold C_HS_laplace
  apply intervalIntegral.integral_congr_ae
  -- Goal: ∀ᵐ x ∂volume, x ∈ uIoc 0 sigma → lhs x = rhs x
  -- Bad set ⊆ {sigma} (null), since for x ∈ uIoc 0 sigma, x ≠ sigma forces x < sigma and c_HS = poly
  apply MeasureTheory.ae_iff.mpr
  apply measure_mono_null _
      (show MeasureTheory.volume ({sigma} : Set ℝ) = 0 from Real.volume_singleton)
  intro r hr
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at *
  push Not at hr
  obtain ⟨hrI, hrne⟩ := hr
  by_contra hne
  apply hrne
  have hr_lt : r < sigma := by
    simp only [Set.uIoc, min_eq_left _hsigma.le, max_eq_right _hsigma.le, Set.mem_Ioc] at hrI
    exact lt_of_le_of_ne hrI.2 hne
  simp only [c_HS_inner hr_lt]

/-! ### Structure factor and OZ algebraic identity -/

/-- **Structure factor** `S0(s) = 1/(1 - rho · Ĉ_HS(s))`.

This is the key object for OZ.4: the linearized OZ equation gives Ĥ^(1) = Ĉ^(1) · S0. -/
noncomputable def S0 (eta sigma rho s : ℝ) : ℝ :=
  1 / (1 - rho * C_HS_laplace eta sigma s)

/-- **Task OZ.3 — OZ algebraic identity:**

If `H0 · (1 - rho · Ĉ_HS(s)) = Ĉ_HS(s)` (the OZ equation) and the denominator is nonzero,
then `H0 = Ĉ_HS(s) · S0(s)`.

This is pure algebra: H0 = Ĉ/(1-rhoĈ) = Ĉ·S0. The same identity, applied to the linearised
OZ equation with c^(1) playing the role of Ĉ^(1), yields Task OZ.4. -/
theorem oz_laplace_identity {eta sigma rho s H0 : ℝ}
    (hne : 1 - rho * C_HS_laplace eta sigma s ≠ 0)
    (h_oz : H0 * (1 - rho * C_HS_laplace eta sigma s) = C_HS_laplace eta sigma s) :
    H0 = C_HS_laplace eta sigma s * S0 eta sigma rho s := by
  unfold S0
  rw [mul_one_div, eq_comm, div_eq_iff hne]
  linarith [h_oz]

/-! ### Task OZ.4 — Linearized OZ identity -/

/-- **Task OZ.4 — Linearized OZ algebraic identity:**

At first order in any perturbation `Ĉ^(1)`, the linearised OZ equation reads
`Ĥ^(1) · (1 - rho · Ĉ_HS(s)) = Ĉ^(1)`. Given this and the nonvanishing of the
HS denominator, we conclude `Ĥ^(1) = Ĉ^(1) · S0(s)`.

This is the same algebra as `oz_laplace_identity` with a generic `C1` in place of
`C_HS_laplace`: dividing both sides by `(1 - rho · Ĉ_HS)` gives the result directly.
No knowledge of the specific form of `Ĉ^(1)` is needed (Task 4.4 is not a prerequisite). -/
theorem oz_linearized_identity {eta sigma rho s H1 C1 : ℝ}
    (hne : 1 - rho * C_HS_laplace eta sigma s ≠ 0)
    (h_lin : H1 * (1 - rho * C_HS_laplace eta sigma s) = C1) :
    H1 = C1 * S0 eta sigma rho s := by
  unfold S0
  rw [mul_one_div, eq_comm, div_eq_iff hne]
  linarith [h_lin]

end FMSA.HardSphere
