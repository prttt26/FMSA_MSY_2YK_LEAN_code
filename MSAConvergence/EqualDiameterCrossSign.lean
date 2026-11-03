import Mathlib

set_option linter.style.header false

/-! Exact density/concentration cross-channel sign for a symmetric
binary tail, with a simpler criterion for positive rank-one tails.
The basis normalization is positive and hence does not alter the sign. -/
noncomputable section
namespace FMSA.Convergence.EqualDiameterCrossSign

open Matrix

private def density (a b : ℝ) : Fin 2 → ℝ := ![a, b]
private def concentration (a b : ℝ) : Fin 2 → ℝ := ![-b, a]
private def weight (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal (density a b)
private def rankOne (c r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => c * (![1, r] : Fin 2 → ℝ) i * (![1, r] : Fin 2 → ℝ) j

def crossGeneral (a b : ℝ) (H : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  dotProduct (density a b)
    ((weight a b * H * weight a b).mulVec (concentration a b))

/-- For any symmetric binary strength matrix, the cross entry is
the positive geometric-density factor times a linear expression in
the original strength entries. -/
theorem cross_general_factorization
    (a b : ℝ) (H : Matrix (Fin 2) (Fin 2) ℝ)
    (hH : H 1 0 = H 0 1) :
    crossGeneral a b H = a * b *
      (-(a ^ 2) * H 0 0 + (a ^ 2 - b ^ 2) * H 0 1 + b ^ 2 * H 1 1) := by
  simp [crossGeneral, density, concentration, weight,
    Matrix.mulVec, Matrix.mul_apply, Matrix.diagonal_apply,
    dotProduct, Fin.sum_univ_two, hH]
  ring

/-- At positive densities, the sign test for an arbitrary symmetric
binary strength matrix uses only its three original entries. -/
theorem cross_general_neg_iff
    (a b : ℝ) (H : Matrix (Fin 2) (Fin 2) ℝ)
    (ha : 0 < a) (hb : 0 < b) (hH : H 1 0 = H 0 1) :
    crossGeneral a b H < 0 ↔
      -(a ^ 2) * H 0 0 + (a ^ 2 - b ^ 2) * H 0 1 + b ^ 2 * H 1 1 < 0 := by
  rw [cross_general_factorization a b H hH]
  have hp : 0 < a * b := mul_pos ha hb
  have h := (mul_lt_mul_iff_of_pos_left hp :
    a * b * (-(a ^ 2) * H 0 0 + (a ^ 2 - b ^ 2) * H 0 1 + b ^ 2 * H 1 1) <
      a * b * 0 ↔
    -(a ^ 2) * H 0 0 + (a ^ 2 - b ^ 2) * H 0 1 + b ^ 2 * H 1 1 < 0)
  simpa only [mul_zero] using h

theorem cross_general_pos_iff
    (a b : ℝ) (H : Matrix (Fin 2) (Fin 2) ℝ)
    (ha : 0 < a) (hb : 0 < b) (hH : H 1 0 = H 0 1) :
    0 < crossGeneral a b H ↔
      0 < -(a ^ 2) * H 0 0 + (a ^ 2 - b ^ 2) * H 0 1 + b ^ 2 * H 1 1 := by
  rw [cross_general_factorization a b H hH]
  exact mul_pos_iff_of_pos_left (mul_pos ha hb)

theorem cross_general_zero_iff
    (a b : ℝ) (H : Matrix (Fin 2) (Fin 2) ℝ)
    (ha : 0 < a) (hb : 0 < b) (hH : H 1 0 = H 0 1) :
    crossGeneral a b H = 0 ↔
      -(a ^ 2) * H 0 0 + (a ^ 2 - b ^ 2) * H 0 1 + b ^ 2 * H 1 1 = 0 := by
  rw [cross_general_factorization a b H hH]
  exact mul_eq_zero_iff_left (mul_pos ha hb).ne'

/-- At fixed strengths, the sign test is affine in the two species
number densities. -/
theorem cross_general_affine_in_densities
    (a b : ℝ) (H : Matrix (Fin 2) (Fin 2) ℝ)
    (hH : H 1 0 = H 0 1) :
    crossGeneral a b H = a * b *
      (a ^ 2 * (H 0 1 - H 0 0) +
        b ^ 2 * (H 1 1 - H 0 1)) := by
  rw [cross_general_factorization a b H hH]
  ring

/-- For two arbitrary symmetric binary tails, opposite cross signs
are exactly opposite signs of the two affine density expressions. -/
theorem two_general_tails_opposite_iff
    (a b : ℝ) (H₁ H₂ : Matrix (Fin 2) (Fin 2) ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hH₁ : H₁ 1 0 = H₁ 0 1) (hH₂ : H₂ 1 0 = H₂ 0 1) :
    crossGeneral a b H₁ * crossGeneral a b H₂ < 0 ↔
      (a ^ 2 * (H₁ 0 1 - H₁ 0 0) + b ^ 2 * (H₁ 1 1 - H₁ 0 1)) *
        (a ^ 2 * (H₂ 0 1 - H₂ 0 0) + b ^ 2 * (H₂ 1 1 - H₂ 0 1)) < 0 := by
  rw [cross_general_affine_in_densities a b H₁ hH₁,
    cross_general_affine_in_densities a b H₂ hH₂]
  have hp : 0 < (a * b) ^ 2 := sq_pos_of_pos (mul_pos ha hb)
  have heq :
      (a * b * (a ^ 2 * (H₁ 0 1 - H₁ 0 0) + b ^ 2 * (H₁ 1 1 - H₁ 0 1))) *
        (a * b * (a ^ 2 * (H₂ 0 1 - H₂ 0 0) + b ^ 2 * (H₂ 1 1 - H₂ 0 1))) =
      (a * b) ^ 2 *
        ((a ^ 2 * (H₁ 0 1 - H₁ 0 0) + b ^ 2 * (H₁ 1 1 - H₁ 0 1)) *
          (a ^ 2 * (H₂ 0 1 - H₂ 0 0) + b ^ 2 * (H₂ 1 1 - H₂ 0 1))) := by ring
  rw [heq]
  have h := (mul_lt_mul_iff_of_pos_left hp :
    (a * b) ^ 2 *
        ((a ^ 2 * (H₁ 0 1 - H₁ 0 0) + b ^ 2 * (H₁ 1 1 - H₁ 0 1)) *
          (a ^ 2 * (H₂ 0 1 - H₂ 0 0) + b ^ 2 * (H₂ 1 1 - H₂ 0 1))) <
      (a * b) ^ 2 * 0 ↔
      (a ^ 2 * (H₁ 0 1 - H₁ 0 0) + b ^ 2 * (H₁ 1 1 - H₁ 0 1)) *
        (a ^ 2 * (H₂ 0 1 - H₂ 0 0) + b ^ 2 * (H₂ 1 1 - H₂ 0 1)) < 0)
  simpa only [mul_zero] using h

/-- The unnormalized cross entry in the common density/concentration
basis for equal-diameter binary hard spheres. `a,b` are the positive
square roots of the two number densities. -/
def cross (a b c r : ℝ) : ℝ :=
  dotProduct (density a b)
    ((weight a b * rankOne c r * weight a b).mulVec (concentration a b))

theorem cross_factorization (a b c r : ℝ) :
    cross a b c r = c * a * b * (r - 1) * (a ^ 2 + b ^ 2 * r) := by
  simp [cross, density, concentration, weight, rankOne,
    Matrix.mulVec, Matrix.mul_apply, Matrix.diagonal_apply,
    dotProduct, Fin.sum_univ_two]
  ring

/-- For positive rank-one strength and positive densities, the cross
sign depends only on whether the tail direction ratio is below one. -/
theorem cross_neg_iff_ratio_lt_one
    (a b c r : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hr : 0 < r) :
    cross a b c r < 0 ↔ r < 1 := by
  rw [cross_factorization]
  have hp : 0 < c * a * b * (a ^ 2 + b ^ 2 * r) := by positivity
  have heq : c * a * b * (r - 1) * (a ^ 2 + b ^ 2 * r) =
      (c * a * b * (a ^ 2 + b ^ 2 * r)) * (r - 1) := by ring
  rw [heq]
  have h := (mul_lt_mul_iff_of_pos_left hp :
    c * a * b * (a ^ 2 + b ^ 2 * r) * (r - 1) <
      c * a * b * (a ^ 2 + b ^ 2 * r) * 0 ↔ r - 1 < 0)
  simpa only [mul_zero, sub_neg] using h

theorem cross_pos_iff_ratio_gt_one
    (a b c r : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hr : 0 < r) :
    0 < cross a b c r ↔ 1 < r := by
  rw [cross_factorization]
  have hp : 0 < c * a * b * (a ^ 2 + b ^ 2 * r) := by positivity
  have heq : c * a * b * (r - 1) * (a ^ 2 + b ^ 2 * r) =
      (c * a * b * (a ^ 2 + b ^ 2 * r)) * (r - 1) := by ring
  rw [heq, mul_pos_iff_of_pos_left hp]
  exact sub_pos

/-- For two positive rank-one tails, opposite cross-channel signs
are exactly the parameter straddling condition `r₁ < 1 < r₂` or
`r₂ < 1 < r₁`, independent of the positive composition. -/
theorem two_tails_opposite_sign_iff_straddle
    (a b c₁ c₂ r₁ r₂ : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    cross a b c₁ r₁ * cross a b c₂ r₂ < 0 ↔
      (r₁ < 1 ∧ 1 < r₂) ∨ (1 < r₁ ∧ r₂ < 1) := by
  rw [mul_neg_iff]
  simp only [cross_neg_iff_ratio_lt_one a b c₁ r₁ ha hb hc₁ hr₁,
    cross_neg_iff_ratio_lt_one a b c₂ r₂ ha hb hc₂ hr₂,
    cross_pos_iff_ratio_gt_one a b c₁ r₁ ha hb hc₁ hr₁,
    cross_pos_iff_ratio_gt_one a b c₂ r₂ ha hb hc₂ hr₂]
  exact or_comm

end FMSA.Convergence.EqualDiameterCrossSign

/-- info: 'FMSA.Convergence.EqualDiameterCrossSign.cross_general_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EqualDiameterCrossSign.cross_general_factorization
/-- info: 'FMSA.Convergence.EqualDiameterCrossSign.cross_general_neg_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EqualDiameterCrossSign.cross_general_neg_iff
/-- info: 'FMSA.Convergence.EqualDiameterCrossSign.cross_general_pos_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EqualDiameterCrossSign.cross_general_pos_iff
/-- info: 'FMSA.Convergence.EqualDiameterCrossSign.cross_general_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EqualDiameterCrossSign.cross_general_zero_iff
/-- info: 'FMSA.Convergence.EqualDiameterCrossSign.cross_general_affine_in_densities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EqualDiameterCrossSign.cross_general_affine_in_densities
/-- info: 'FMSA.Convergence.EqualDiameterCrossSign.two_general_tails_opposite_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EqualDiameterCrossSign.two_general_tails_opposite_iff
/-- info: 'FMSA.Convergence.EqualDiameterCrossSign.cross_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EqualDiameterCrossSign.cross_factorization
/-- info: 'FMSA.Convergence.EqualDiameterCrossSign.cross_neg_iff_ratio_lt_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EqualDiameterCrossSign.cross_neg_iff_ratio_lt_one
/-- info: 'FMSA.Convergence.EqualDiameterCrossSign.cross_pos_iff_ratio_gt_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EqualDiameterCrossSign.cross_pos_iff_ratio_gt_one
/-- info: 'FMSA.Convergence.EqualDiameterCrossSign.two_tails_opposite_sign_iff_straddle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.EqualDiameterCrossSign.two_tails_opposite_sign_iff_straddle
