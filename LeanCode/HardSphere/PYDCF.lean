/-
Copyright (c) 2024 FMSA Yukawa Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FMSA project
-/

-- Naming and notation conventions: see CONVENTIONS.md

import Mathlib

/-!
# Task OZ.1 — Percus-Yevick DCF for Hard-Sphere Reference

**Source:** Wertheim (1963), Thiele (1963)

The Percus-Yevick (PY) direct correlation function for hard spheres of diameter sigma
at packing fraction eta is:

    c_HS(r) = -(alpha0 + alpha1·(r/sigma) + alpha3·(r/sigma)^3)    for r < sigma
    c_HS(r) = 0                                    for r ≥ sigma

with rational coefficients:

    alpha0(eta) = (1 + 2eta)^2 / (1 - eta)^4
    alpha1(eta) = -6eta · (1 + eta/2)^2 / (1 - eta)^4
    alpha3(eta) = eta · (1 + 2eta)^2 / (2(1 - eta)^4)  =  (eta/2) · alpha0(eta)

**Physical origin:** The PY closure c(r) = -g(r) for r < sigma (hard core) combined with
the OZ equation yields this polynomial form by exact algebraic inversion.

**Role in Group OZ:**
- OZ.1 (this file): define c_HS, prove coefficient identities and measurability
- OZ.2: real-space g0_HS via OZ fixed point (Banach); `g0_HS_core` proved
- OZ.3: compute Ĉ_HS(s) = ∫0^sigma r·c_HS(r)·e^{-sr} dr; `oz_laplace_identity`; `g0_HS_laplace_spec`
- OZ.4: prove general identity Ĥ^(1)(s) = Ĉ^(1)(s)·S0(s) using S0 from OZ.3
-/

open MeasureTheory Set

namespace FMSA.HardSphere

/-! ### PY DCF coefficient definitions -/

/-- `alpha0(eta) = (1 + 2eta)^2 / (1 - eta)^4` — constant term of the inner-core polynomial. -/
noncomputable def py_a0 (eta : ℝ) : ℝ := (1 + 2 * eta) ^ 2 / (1 - eta) ^ 4

/-- `alpha1(eta) = -6eta(1 + eta/2)^2 / (1 - eta)^4` — linear term coefficient. -/
noncomputable def py_a1 (eta : ℝ) : ℝ := -6 * eta * (1 + eta / 2) ^ 2 / (1 - eta) ^ 4

/-- `alpha3(eta) = eta(1 + 2eta)^2 / (2(1 - eta)^4)` — cubic term coefficient (no r^2 term by symmetry). -/
noncomputable def py_a3 (eta : ℝ) : ℝ := eta * (1 + 2 * eta) ^ 2 / (2 * (1 - eta) ^ 4)

/-! ### Denominator lemmas -/

lemma py_one_sub_pow_pos {eta : ℝ} (heta : eta < 1) : 0 < (1 - eta) ^ 4 :=
  pow_pos (by linarith) 4

lemma py_one_sub_pow_ne {eta : ℝ} (heta : eta < 1) : (1 - eta) ^ 4 ≠ 0 :=
  (py_one_sub_pow_pos heta).ne'

/-! ### Coefficient sign and identity lemmas -/

lemma py_a0_pos {eta : ℝ} (heta0 : 0 <= eta) (heta1 : eta < 1) : 0 < py_a0 eta :=
  div_pos (pow_pos (by positivity) 2) (py_one_sub_pow_pos heta1)

/-- **Key identity:** `alpha3(eta) = (eta/2) · alpha0(eta)`.

This reflects the fact that the cubic coefficient is exactly half eta times the
constant coefficient in the PY polynomial. -/
theorem py_a3_eq {eta : ℝ} (heta : eta < 1) : py_a3 eta = eta / 2 * py_a0 eta := by
  unfold py_a3 py_a0
  have h2 : (2 : ℝ) * (1 - eta) ^ 4 ≠ 0 := by positivity
  field_simp [py_one_sub_pow_ne heta, h2]

/-- The denominator `2(1-eta)^4` is positive for eta < 1. -/
lemma py_two_denom_pos {eta : ℝ} (heta : eta < 1) : 0 < 2 * (1 - eta) ^ 4 := by positivity

/-! ### PY DCF definition -/

/-- **Task OZ.1 — Percus-Yevick hard-sphere DCF:**

    c_HS(r) = -(alpha0 + alpha1·(r/sigma) + alpha3·(r/sigma)^3)    for r < sigma   (inner: polynomial)
    c_HS(r) = 0                                    for r ≥ sigma   (outer: identically 0)

The absence of an r^2 term reflects the absence of a quadratic PY coefficient. -/
noncomputable def c_HS (eta sigma r : ℝ) : ℝ :=
  if r < sigma then -(py_a0 eta + py_a1 eta * (r / sigma) + py_a3 eta * (r / sigma) ^ 3)
  else 0

/-! ### Evaluation simp lemmas -/

@[simp] theorem c_HS_inner {eta sigma r : ℝ} (hr : r < sigma) :
    c_HS eta sigma r = -(py_a0 eta + py_a1 eta * (r / sigma) + py_a3 eta * (r / sigma) ^ 3) :=
  if_pos hr

@[simp] theorem c_HS_outer {eta sigma r : ℝ} (hr : sigma <= r) : c_HS eta sigma r = 0 :=
  if_neg (not_lt.mpr hr)

/-- At the contact point `r = sigma`, `c_HS` is zero (outer branch). -/
@[simp] theorem c_HS_contact (eta sigma : ℝ) : c_HS eta sigma sigma = 0 :=
  c_HS_outer (le_refl sigma)

/-- c_HS written using the alpha3 = (eta/2)·alpha0 identity. -/
theorem c_HS_inner_a3_eq {eta sigma r : ℝ} (heta : eta < 1) (hr : r < sigma) :
    c_HS eta sigma r = -(py_a0 eta + py_a1 eta * (r / sigma) + eta / 2 * py_a0 eta * (r / sigma) ^ 3) := by
  rw [c_HS_inner hr, py_a3_eq heta]

/-! ### Measurability -/

/-- `c_HS eta sigma` is measurable as a piecewise function (polynomial on `Iio sigma`, zero elsewhere). -/
theorem c_HS_measurable (eta sigma : ℝ) : Measurable (c_HS eta sigma) := by
  unfold c_HS
  apply Measurable.ite (measurableSet_Iio (a := sigma)) _ measurable_const
  apply Measurable.neg
  apply Measurable.add (Measurable.add measurable_const _) _
  · exact (measurable_id.div_const sigma).const_mul (py_a1 eta)
  · exact ((measurable_id.div_const sigma).pow_const 3).const_mul (py_a3 eta)

/-- `c_HS eta sigma` is AEMeasurable with respect to any measure. -/
theorem c_HS_aemeasurable (eta sigma : ℝ) (mu : MeasureTheory.Measure ℝ) :
    AEMeasurable (c_HS eta sigma) mu :=
  (c_HS_measurable eta sigma).aemeasurable

/-! ### Integrability on the core region -/

/-- `c_HS eta sigma` is integrable on `[0, sigma]`.

**Proof:** c_HS equals the continuous polynomial `g(r) = -(alpha0 + alpha1·(r/sigma) + alpha3·(r/sigma)^3)`
on `[0, sigma)`, and equals 0 at r = sigma (a null set).  So c_HS =ᵃᵉ g on [0, sigma];
since g is continuous, hence integrable on the compact set [0, sigma], so is c_HS. -/
theorem c_HS_integrableOn {eta sigma : ℝ} (_hsigma : 0 < sigma) :
    IntegrableOn (c_HS eta sigma) (Set.Icc 0 sigma) := by
  -- On Ico 0 sigma (which equals Icc up to the null set {sigma}), c_HS equals the polynomial g exactly.
  rw [integrableOn_Icc_iff_integrableOn_Ico]
  set g := fun r => -(py_a0 eta + py_a1 eta * (r / sigma) + py_a3 eta * (r / sigma) ^ 3)
  have hg : IntegrableOn g (Set.Ico 0 sigma) :=
    ((by fun_prop : Continuous g).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ico_subset_Icc_self
  exact hg.congr_fun (fun r hr => (c_HS_inner (Set.mem_Ico.mp hr).2).symm) measurableSet_Ico

end FMSA.HardSphere
