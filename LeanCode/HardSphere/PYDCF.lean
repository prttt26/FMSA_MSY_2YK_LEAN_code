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

/-- `alpha3(eta) = eta(1 + 2eta)^2 / (2(1 - eta)^4)`
— cubic term coefficient (no r^2 term by symmetry). -/
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

/-- `alpha3(eta) ≥ 0` for physical `eta ≥ 0` (numerator is a product of nonnegatives, and the
`(1-eta)^4` denominator is nonnegative for every real `eta`, even past `eta = 1`). -/
lemma py_a3_nonneg {eta : ℝ} (heta0 : 0 ≤ eta) : 0 ≤ py_a3 eta := by
  unfold py_a3
  positivity

/-- `f(1) = alpha0(eta) + alpha1(eta) + alpha3(eta) = (1 + eta/2) / (1 - eta)^2`, the value of
the inner-core bracket polynomial at the sphere boundary `x = 1`. Used as the anchor point for
`py_bracket_pos`'s minimum-at-the-boundary argument. -/
lemma py_f1_eq {eta : ℝ} (heta1 : eta < 1) :
    py_a0 eta + py_a1 eta + py_a3 eta = (1 + eta / 2) / (1 - eta) ^ 2 := by
  have h1 : (1 : ℝ) - eta ≠ 0 := by linarith
  have h2 : (1 - eta) ^ 2 ≠ 0 := pow_ne_zero 2 h1
  rw [eq_div_iff h2]
  unfold py_a0 py_a1 py_a3
  have h4 : (1 - eta) ^ 4 ≠ 0 := pow_ne_zero 4 h1
  field_simp
  ring

lemma py_f1_pos {eta : ℝ} (heta0 : 0 ≤ eta) (heta1 : eta < 1) :
    0 < py_a0 eta + py_a1 eta + py_a3 eta := by
  rw [py_f1_eq heta1]
  exact div_pos (by linarith) (by positivity)

/-- `alpha1(eta) + 3·alpha3(eta) = 9·eta·(eta^2-1) / (2(1-eta)^4) < 0` for physical
`eta ∈ (0,1)`. This is the key bound feeding `py_bracket_pos`: since `1+x+x^2 ≤ 3` on `[0,1]`
and `alpha3 ≥ 0`, replacing `1+x+x^2` by its max value `3` only makes the (negative)
`alpha1 + alpha3·(1+x+x^2)` term more negative. -/
lemma py_a1_add_three_a3_eq {eta : ℝ} (heta1 : eta < 1) :
    py_a1 eta + 3 * py_a3 eta = 9 * eta * (eta ^ 2 - 1) / (2 * (1 - eta) ^ 4) := by
  unfold py_a1 py_a3
  have h1 : (1 - eta) ^ 4 ≠ 0 := py_one_sub_pow_ne heta1
  field_simp
  ring

lemma py_a1_add_three_a3_neg {eta : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1) :
    py_a1 eta + 3 * py_a3 eta < 0 := by
  rw [py_a1_add_three_a3_eq heta1]
  apply div_neg_of_neg_of_pos _ (py_two_denom_pos heta1)
  nlinarith [mul_pos (mul_pos heta0 (sub_pos.mpr heta1)) (show (0:ℝ) < 1 + eta by linarith)]

/-- **Sign lemma (Task OZ.10, Piece 1):** the inner-core bracket
`alpha0(eta) + alpha1(eta)·x + alpha3(eta)·x^3` is strictly positive for all `x ∈ [0,1]` and
physical `eta ∈ (0,1)` — equivalently `c_HS eta sigma t < 0` throughout the hard core
(`c_HS_neg` below).

**Proof idea** (verified numerically and symbolically before formalizing): write
`f(x) = alpha0 + alpha1·x + alpha3·x^3`. The identity
`f(1) - f(x) = (1-x)·(alpha1 + alpha3·(1+x+x^2))` (a pure `ring` fact) reduces positivity of
`f` on `[0,1]` to two easier facts: `f(1) = (1+eta/2)/(1-eta)^2 > 0` (`py_f1_pos`), and
`alpha1 + alpha3·(1+x+x^2) ≤ alpha1 + 3·alpha3 < 0` (`py_a1_add_three_a3_neg`, using
`alpha3 ≥ 0` and `1+x+x^2 ≤ 3` on `[0,1]`). Since `(1-x) ≥ 0`, the product
`(1-x)·(alpha1+alpha3·(1+x+x^2))` is `≤ 0`, so `f(x) ≥ f(1) > 0`. -/
theorem py_bracket_pos {eta x : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 < py_a0 eta + py_a1 eta * x + py_a3 eta * x ^ 3 := by
  have hsum : 0 < py_a0 eta + py_a1 eta + py_a3 eta := py_f1_pos heta0.le heta1
  have hid : (py_a0 eta + py_a1 eta + py_a3 eta) -
      (py_a0 eta + py_a1 eta * x + py_a3 eta * x ^ 3) =
      (1 - x) * (py_a1 eta + py_a3 eta * (1 + x + x ^ 2)) := by ring
  have ha3 : 0 ≤ py_a3 eta := py_a3_nonneg heta0.le
  have hx2 : (1 : ℝ) + x + x ^ 2 ≤ 3 := by nlinarith
  have hbound : py_a1 eta + py_a3 eta * (1 + x + x ^ 2) ≤ py_a1 eta + 3 * py_a3 eta := by
    have := mul_le_mul_of_nonneg_left hx2 ha3
    linarith
  have hneg : py_a1 eta + py_a3 eta * (1 + x + x ^ 2) < 0 :=
    lt_of_le_of_lt hbound (py_a1_add_three_a3_neg heta0 heta1)
  have hrhs : (1 - x) * (py_a1 eta + py_a3 eta * (1 + x + x ^ 2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg.le
  linarith [hid, hsum, hrhs]

/-! ### PY DCF definition -/

/-- **Task OZ.1 — Percus-Yevick hard-sphere DCF:**

    c_HS(r) = -(alpha0 + alpha1·(r/sigma) + alpha3·(r/sigma)^3)
        for r < sigma   (inner: polynomial)
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
    c_HS eta sigma r =
    -(py_a0 eta + py_a1 eta * (r / sigma) + eta / 2 * py_a0 eta * (r / sigma) ^ 3) := by
  rw [c_HS_inner hr, py_a3_eq heta]

/-- **Sign lemma (Task OZ.10, Piece 1):** `c_HS` is strictly negative throughout the hard
core `(0, sigma)`, for physical `eta ∈ (0,1)`. Direct corollary of `py_bracket_pos`, applied at
`x = t/sigma ∈ [0,1]`. -/
theorem c_HS_neg {eta sigma t : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) (ht0 : 0 < t) (ht1 : t < sigma) :
    c_HS eta sigma t < 0 := by
  rw [c_HS_inner ht1]
  have hx0 : 0 ≤ t / sigma := div_nonneg ht0.le hsigma.le
  have hx1 : t / sigma ≤ 1 := (div_le_one hsigma).mpr ht1.le
  linarith [py_bracket_pos heta0 heta1 hx0 hx1]

/-! ### Core integral bound (Task OZ.10, Piece 2) -/

/-- **Closed-form core integral bound (Task OZ.10, Piece 2):** the `oz_linear_op`
operator-norm integral `∫₀^σ t²|c_HS(t)|dt` collapses to a rational function of `eta` alone
(scaled by `sigma^3`), independent of `sigma` beyond that explicit scaling. Numerically
verified before formalizing; the proof substitutes the sign fact `c_HS_neg` to remove the
absolute value (valid a.e. — everywhere except the single boundary point `t = sigma`, handled
via `Ioo_ae_eq_Ioc`), then integrates the resulting cubic polynomial term-by-term via
`integral_pow`. -/
theorem c_HS_abs_integral {eta sigma : ℝ} (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsigma : 0 < sigma) :
    (∫ t in (0:ℝ)..sigma, t ^ 2 * |c_HS eta sigma t|) =
      sigma ^ 3 * (py_a0 eta / 3 + py_a1 eta / 4 + py_a3 eta / 6) := by
  have hsne : sigma ≠ 0 := hsigma.ne'
  have hcongr : ∀ t ∈ Set.Ioo (0 : ℝ) sigma,
      t ^ 2 * |c_HS eta sigma t| =
        py_a0 eta * t ^ 2 + py_a1 eta / sigma * t ^ 3 + py_a3 eta / sigma ^ 3 * t ^ 5 := by
    intro t ht
    rw [abs_of_neg (c_HS_neg heta0 heta1 hsigma ht.1 ht.2), c_HS_inner ht.2]
    field_simp
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) sigma →
      t ^ 2 * |c_HS eta sigma t| =
        py_a0 eta * t ^ 2 + py_a1 eta / sigma * t ^ 3 + py_a3 eta / sigma ^ 3 * t ^ 5 := by
    have heq : Set.Ioo (0 : ℝ) sigma =ᵐ[volume] Set.Ioc (0 : ℝ) sigma := Ioo_ae_eq_Ioc
    filter_upwards [heq] with t ht htI
    rw [Set.uIoc_of_le hsigma.le] at htI
    exact hcongr t (ht.mpr htI)
  rw [intervalIntegral.integral_congr_ae hae]
  have hint1 : IntervalIntegrable (fun t => py_a0 eta * t ^ 2) volume 0 sigma :=
    (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun t => py_a1 eta / sigma * t ^ 3) volume 0 sigma :=
    (continuous_const.mul (continuous_pow 3)).intervalIntegrable _ _
  have hint3 : IntervalIntegrable (fun t => py_a3 eta / sigma ^ 3 * t ^ 5) volume 0 sigma :=
    (continuous_const.mul (continuous_pow 5)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hint1.add hint2) hint3,
      intervalIntegral.integral_add hint1 hint2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow, integral_pow, integral_pow]
  field_simp
  ring

/-! ### Measurability -/

/-- `c_HS eta sigma` is measurable as a piecewise function
(polynomial on `Iio sigma`, zero elsewhere). -/
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

**Proof:** c_HS equals the continuous polynomial
`g(r) = -(alpha0 + alpha1·(r/sigma) + alpha3·(r/sigma)^3)`
on `[0, sigma)`, and equals 0 at r = sigma (a null set).  So c_HS =ᵃᵉ g on [0, sigma];
since g is continuous, hence integrable on the compact set [0, sigma], so is c_HS. -/
theorem c_HS_integrableOn {eta sigma : ℝ} (_hsigma : 0 < sigma) :
    IntegrableOn (c_HS eta sigma) (Set.Icc 0 sigma) := by
  -- On Ico 0 sigma (which equals Icc up to the null set {sigma}),
  -- c_HS equals the polynomial g exactly.
  rw [integrableOn_Icc_iff_integrableOn_Ico]
  set g := fun r => -(py_a0 eta + py_a1 eta * (r / sigma) + py_a3 eta * (r / sigma) ^ 3)
  have hg : IntegrableOn g (Set.Ico 0 sigma) :=
    ((by fun_prop : Continuous g).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ico_subset_Icc_self
  exact hg.congr_fun (fun r hr => (c_HS_inner (Set.mem_Ico.mp hr).2).symm) measurableSet_Ico

/-- **`t²·|c_HS(t)|` is interval integrable on `[0,sigma]`.** `|c_HS|`'s known integrability
(`c_HS_integrableOn`, via `.abs`) times the bounded factor `t²` (`Integrable.mul_bdd`), swapped
via `mul_comm`. Used by the OZ fixed-point boundedness/contraction estimates
(`OzFixedPtDilute.lean`) to bound `oz_forcing`/`oz_linear_op` without re-deriving the
polynomial congruence used in `c_HS_abs_integral`. -/
theorem c_HS_abs_t2_integrableOn {eta sigma : ℝ} (hsigma : 0 < sigma) :
    IntervalIntegrable (fun t => t ^ 2 * |c_HS eta sigma t|) volume 0 sigma := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hsigma.le]
  have hbdd : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) sigma)), ‖t ^ 2‖ ≤ sigma ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
    exact pow_le_pow_left₀ ht.1 ht.2 2
  have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) sigma)) :=
    (continuous_pow 2).aestronglyMeasurable
  have hmul := (c_HS_integrableOn (eta := eta) hsigma).abs.mul_bdd hmeas hbdd
  exact hmul.congr (Filter.Eventually.of_forall fun t => mul_comm _ _)

end FMSA.HardSphere
