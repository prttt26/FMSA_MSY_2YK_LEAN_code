import Mathlib

/-!
# Strict truncation versus a real Baxter square

These are algebraic statements about prescribed real coefficients. They do not
identify those coefficients with a physical MSA branch, prove accuracy of a
spinodal, or establish coexistence. They make explicit why evaluating a finite
Taylor jet cannot itself introduce a coupling fold, and why the exact identity
`a = A²` must not be imposed on two independently truncated observables.

`A` here denotes the normalized scalar Baxter amplitude (the physical A / 2π).
-/

namespace FMSA.ExactMSA.FiniteOrderThermo

def amplitudeJet (c : ℕ → ℝ) (N : ℕ) (τ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), c i * τ ^ i

def squaredJetTrunc (c : ℕ → ℝ) (N : ℕ) (τ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
    if i + j ≤ N then c i * c j * τ ^ (i + j) else 0

def squaredJetRemainder (c : ℕ → ℝ) (N : ℕ) (τ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
    if N < i + j then c i * c j * τ ^ (i + j) else 0

/-- A prescribed finite jet is continuous at every real coupling. No claim about
solvability of its coefficient construction at a singular reference state. -/
theorem amplitudeJet_continuous (c : ℕ → ℝ) (N : ℕ) :
    Continuous (amplitudeJet c N) := by
  unfold amplitudeJet
  fun_prop

theorem squaredJetTrunc_continuous (c : ℕ → ℝ) (N : ℕ) :
    Continuous (squaredJetTrunc c N) := by
  unfold squaredJetTrunc
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  split_ifs
  · fun_prop
  · exact continuous_const

/-- Squaring the finite factor retains extra orders that a strict truncation drops. -/
theorem amplitudeJet_sq_eq_trunc_add_remainder (c : ℕ → ℝ) (N : ℕ) (τ : ℝ) :
    (amplitudeJet c N τ) ^ 2 =
      squaredJetTrunc c N τ + squaredJetRemainder c N τ := by
  unfold amplitudeJet squaredJetTrunc squaredJetRemainder
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : i + j ≤ N
  · simp only [h, not_lt_of_ge h, ite_true, ite_false, add_zero]
    rw [pow_add]
    ring
  · simp only [h, Nat.lt_of_not_ge h, ite_true, ite_false, zero_add]
    rw [pow_add]
    ring

theorem real_square_cannot_be_negative {a : ℝ} (ha : a < 0) :
    ¬ ∃ A : ℝ, a = A ^ 2 := by
  rintro ⟨A, rfl⟩
  exact (not_lt_of_ge (sq_nonneg A)) ha

/-- The real full-factor mixture expression also forces a nonnegative mechanical
derivative. This statement does not identify mechanical and compositional stability. -/
theorem weighted_real_squares_nonneg {Index : Type*} (I : Finset Index)
    (w A : Index → ℝ) (hw : ∀ i ∈ I, 0 ≤ w i) :
    0 ≤ ∑ i ∈ I, w i * (A i) ^ 2 := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw i hi) (sq_nonneg (A i))

/-- Real-wavevector scalar factors are complex. Strict first order of their
modulus square also differs from the complete modulus square of their jet.
This is coefficient algebra; it does not certify any numerical spectral scan. -/
def firstOrderSpectral (F0 F1 : ℂ) (τ : ℝ) : ℝ :=
  Complex.normSq F0 + 2 * τ * (F0.re * F1.re + F0.im * F1.im)

theorem firstOrderSpectral_eq_normSq_sub (F0 F1 : ℂ) (τ : ℝ) :
    firstOrderSpectral F0 F1 τ =
      Complex.normSq (F0 + (τ : ℂ) * F1) - τ ^ 2 * Complex.normSq F1 := by
  simp only [firstOrderSpectral, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- A nonnegative scalar structure factor with a finite reciprocal requires a
strictly positive inverse structure factor. This is conditional scalar algebra,
not an identification of a closure with a realizable correlation function. -/
theorem nonnegative_structure_factor_requires_positive_inverse {D S : ℝ}
    (hS : 0 ≤ S) (hreciprocal : D * S = 1) : 0 < D := by
  by_contra h
  have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hS
  linarith

/-- An already established spectral tail estimate reduces positivity to a
finite interval. Deriving that estimate for a Baxter kernel and certifying its
numerical coefficient bounds are separate obligations. -/
theorem spectral_tail_positive_of_bound {D C k : ℝ} (hk : k ≠ 0)
    (hbound : |D - 1| ≤ C / k ^ 2) (hcutoff : 2 * C ≤ k ^ 2) :
    1 / 2 ≤ D := by
  have hk2 : 0 < k ^ 2 := sq_pos_of_ne_zero hk
  have habs : |D - 1| * k ^ 2 ≤ C := (le_div_iff₀ hk2).mp hbound
  have hlow : -(D - 1) ≤ |D - 1| := neg_le_abs (D - 1)
  have hmul := mul_le_mul_of_nonneg_right hlow (le_of_lt hk2)
  nlinarith

def firstOrderDerivative (A0 A1 τ : ℝ) : ℝ := A0 ^ 2 + 2 * A0 * A1 * τ

theorem firstOrderDerivative_eq_square_sub (A0 A1 τ : ℝ) :
    firstOrderDerivative A0 A1 τ = (A0 + A1 * τ) ^ 2 - (A1 * τ) ^ 2 := by
  unfold firstOrderDerivative
  ring

/-- At a first-order spinodal the truncated factor is A0/2, not zero. -/
theorem firstOrder_spinodal_factor_value {A0 A1 τ : ℝ} (h0 : A0 ≠ 0)
    (hs : firstOrderDerivative A0 A1 τ = 0) : A0 + A1 * τ = A0 / 2 := by
  have h : A0 * (A0 + 2 * A1 * τ) = 0 := by
    unfold firstOrderDerivative at hs
    nlinarith [hs]
  have hz : A0 + 2 * A1 * τ = 0 := (mul_eq_zero.mp h).resolve_left h0
  linarith

theorem firstOrder_spinodal_factor_positive {A0 A1 τ : ℝ} (h0 : 0 < A0)
    (hs : firstOrderDerivative A0 A1 τ = 0) : 0 < A0 + A1 * τ := by
  rw [firstOrder_spinodal_factor_value (ne_of_gt h0) hs]
  linarith

def secondOrderDerivative (A0 A1 A2 τ : ℝ) : ℝ :=
  A0 ^ 2 + 2 * A0 * A1 * τ + (A1 ^ 2 + 2 * A0 * A2) * τ ^ 2

theorem secondOrder_square_remainder (A0 A1 A2 τ : ℝ) :
    (A0 + A1 * τ + A2 * τ ^ 2) ^ 2 = secondOrderDerivative A0 A1 A2 τ +
      2 * A1 * A2 * τ ^ 3 + A2 ^ 2 * τ ^ 4 := by
  unfold secondOrderDerivative
  ring

/-- A counterexample to unconditional nonnegativity of strict second order;
this is an algebraic example, not a Yukawa-state computation. -/
theorem secondOrder_can_be_negative : secondOrderDerivative 1 (-1) (-1) 1 < 0 := by
  norm_num [secondOrderDerivative]

/-- Positive quadratic curvature can restore a positive pressure derivative
at large positive coupling. Applying this to a physical coefficient family is
a separate obligation; the statement alone makes no binodal claim. -/
theorem quadratic_positive_beyond_linear_balance {a0 a1 a2 τ : ℝ}
    (h0 : 0 < a0) (hτ : 0 ≤ τ) (hbalance : 0 ≤ a1 + a2 * τ) :
    0 < a0 + a1 * τ + a2 * τ ^ 2 := by
  have h := mul_nonneg hτ hbalance
  nlinarith

/-- A verified error bound smaller than a negative target's margin preserves
its sign. No error bound or unstable physical target is postulated here. -/
theorem negative_sign_preserved_by_error_bound {a target δ : ℝ}
    (hmargin : target ≤ -δ) (herror : |a - target| < δ) : a < 0 := by
  have h := le_abs_self (a - target)
  linarith

/-- Strictly increasing pressure excludes two distinct equal-pressure
endpoints. Establishing strict monotonicity on the relevant density domain is
essential; a finite grid with positive derivatives does not establish it. -/
theorem strictly_monotone_pressure_excludes_binodal (p : ℝ → ℝ)
    (hp : StrictMono p) {ρg ρl : ℝ} (hdensities : ρg < ρl) : p ρg ≠ p ρl :=
  ne_of_lt (hp hdensities)

end FMSA.ExactMSA.FiniteOrderThermo
