import LeanCode.YukawaOZ.MSAMultiTailCore
import LeanCode.YukawaOZ.MSAMultiTailSpectralAlgebra

/-!
# Finite-tail convolution blocks, before their Fourier integration

The endpoint formulas below are the elementary primitives of the three actual
bounded/improper convolution regions. Their simplifications are checked with
symbolic amplitudes and rates. No distinct-rate hypothesis is needed.
-/

noncomputable section
open Real MeasureTheory Set
open scoped BigOperators

namespace FMSA.ExactMSA.MultiTail.Blocks

def poly (A qp x : ℝ) : ℝ := qp * (x - 1) + A / 2 * (x - 1) ^ 2
def polyPrime (A qp x : ℝ) : ℝ := qp + A * (x - 1)

def polynomialCore (A qp r : ℝ) : ℝ :=
  -A ^ 2 * r ^ 4 / 24 + qp ^ 2 * r ^ 2 / 2 +
    (A ^ 2 / 6 - A * qp / 2) * r - A ^ 2 / 8 + A * qp / 2 - qp ^ 2 / 2

def polynomialEndpoint (A qp r : ℝ) : ℝ :=
  let a0 := qp + A * (r - 1)
  let b0 := A / 2 - qp
  let b1 := qp - A
  let b2 := A / 2
  FiniteYukawa.polyPrimitive (a0 * b0) (a0 * b1 + A * b0)
    (a0 * b2 + A * b1) (A * b2) (1 - r)

def polyLaplace (z A qp : ℝ) : ℝ :=
  qp * (1 - z - exp (-z)) / z ^ 2 + A * (1 - z + z ^ 2 / 2 - exp (-z)) / z ^ 3

def mixedCore (z A qp W C r : ℝ) : ℝ :=
  W * ((qp - A) / z + A / z ^ 2 + A / z * r) +
    C * (-A * r ^ 2 + A * (1 + 1 / z) * r + qp - A / 2 - qp / z - A / z ^ 2) +
    (-z * W * polyLaplace z A qp + C * (qp / z + A / z ^ 2)) * exp (-z * r) -
    W * exp (-z) * (qp / z + A / z ^ 2) * exp (z * r)

def mixedExterior (z A qp W C r : ℝ) : ℝ :=
  -z * (W + C * exp z) * polyLaplace z A qp * exp (-z * r)

def mixedEndpoint (z A qp W C r : ℝ) : ℝ :=
  let L := 1 - r
  let a0 := qp + A * (r - 1)
  let b0 := A / 2 - qp
  let b1 := qp - A
  let b2 := A / 2
  let U := -z * W * exp (-z * r)
  let V := -z * (W + C * exp z) * exp (-z * r)
  C * (a0 * L + A * L ^ 2 / 2) +
    W * (FiniteYukawa.expPrimitive z a0 A 0 L - FiniteYukawa.expPrimitive z a0 A 0 0) +
    U * (FiniteYukawa.expPrimitive z b0 b1 b2 L - FiniteYukawa.expPrimitive z b0 b1 b2 0) +
    V * (FiniteYukawa.expPrimitive z b0 b1 b2 1 - FiniteYukawa.expPrimitive z b0 b1 b2 L)

def pairCore (z w W C V D r : ℝ) : ℝ :=
  -C * D +
    (-z * W * V / (z + w) - (1 - w * exp (-z) / (z + w)) * W * D +
      w * C * D / (z + w)) * exp (-z * r) -
    z * C * V * exp (-w) / (z + w) * exp (w * r)

def tailLaplace (z w V D : ℝ) : ℝ :=
  V / (z + w) + D * ((1 - exp (-z)) / z + exp (-z) / (z + w))

def pairExterior (z w W C V D r : ℝ) : ℝ :=
  -z * (W + C * exp z) * tailLaplace z w V D * exp (-z * r)

def pairEndpoint (z w W C V D r : ℝ) : ℝ :=
  let L := 1 - r
  let U := -z * W * exp (-z * r)
  let T := -z * (W + C * exp z) * exp (-z * r)
  U * D * (1 - exp (-z * L)) / z +
    U * V * (1 - exp (-(z + w) * L)) / (z + w) +
    T * D * (exp (-z * L) - exp (-z)) / z +
    T * V * (exp (-(z + w) * L) - exp (-(z + w))) / (z + w) +
    T * (V + D * exp w) * exp (-(z + w)) / (z + w)

theorem polynomialEndpoint_eq (A qp r : ℝ) :
    polynomialEndpoint A qp r = polynomialCore A qp r := by
  unfold polynomialEndpoint polynomialCore FiniteYukawa.polyPrimitive
  dsimp only
  ring

private theorem exp_shift (z r : ℝ) : exp (-z * (1 - r)) = exp (-z) / exp (-z * r) := by
  rw [← exp_sub]
  congr 1
  ring

private theorem exp_inverse (z : ℝ) : exp z = 1 / exp (-z) := by
  rw [one_div, ← exp_neg]
  congr 1
  ring

theorem mixedEndpoint_eq (z A qp W C r : ℝ) (hz : z ≠ 0) :
    mixedEndpoint z A qp W C r = mixedCore z A qp W C r := by
  unfold mixedEndpoint mixedCore polyLaplace FiniteYukawa.expPrimitive
  dsimp only
  simp only [mul_zero, zero_mul, zero_add, add_zero, zero_div, mul_one, pow_one,
    zero_pow (by decide : 2 ≠ 0), exp_zero, exp_shift, exp_inverse z, exp_inverse (z * r)]
  field_simp [hz, exp_ne_zero (-z), exp_ne_zero (-z * r)]
  ring

theorem pairEndpoint_eq (z w W C V D r : ℝ) (hz : z ≠ 0) (hzw : z + w ≠ 0) :
    pairEndpoint z w W C V D r = pairCore z w W C V D r := by
  have eL : exp (-(z + w) * (1 - r)) =
      exp (-z) * exp (-w) / (exp (-z * r) * exp (-w * r)) := by
    have e0 : exp (-(z + w)) = exp (-z) * exp (-w) := by
      rw [← exp_add]
      congr 1
      ring
    have er : exp (-(z + w) * r) = exp (-z * r) * exp (-w * r) := by
      rw [← exp_add]
      congr 1
      ring
    rw [exp_shift, e0, er]
  have e0 : exp (-(z + w)) = exp (-z) * exp (-w) := by
    rw [show -(z + w) = -z + -w by ring, exp_add]
  unfold pairEndpoint pairCore
  dsimp only
  rw [exp_shift z r, eL, e0, exp_inverse z, exp_inverse w, exp_inverse (w * r)]
  field_simp [hz, hzw, exp_ne_zero (-z), exp_ne_zero (-w),
    exp_ne_zero (-z * r), exp_ne_zero (-w * r)]
  ring

/-- Actual compact polynomial/poly convolution integral. -/
theorem polynomialCore_integral (A qp r : ℝ) :
    (∫ t in (0 : ℝ)..(1 - r), polyPrime A qp (t + r) * poly A qp t) =
      polynomialCore A qp r := by
  have he : (fun t => polyPrime A qp (t + r) * poly A qp t) = fun t =>
      (qp + A * (r - 1)) * (A / 2 - qp) +
      ((qp + A * (r - 1)) * (qp - A) + A * (A / 2 - qp)) * t +
      ((qp + A * (r - 1)) * (A / 2) + A * (qp - A)) * t ^ 2 +
      (A * (A / 2)) * t ^ 3 := by
    funext t
    unfold polyPrime poly
    ring
  rw [he, FiniteYukawa.integral_cubic]
  have h0 : FiniteYukawa.polyPrimitive
      ((qp + A * (r - 1)) * (A / 2 - qp))
      ((qp + A * (r - 1)) * (qp - A) + A * (A / 2 - qp))
      ((qp + A * (r - 1)) * (A / 2) + A * (qp - A)) (A * (A / 2)) 0 = 0 := by
    simp [FiniteYukawa.polyPrimitive]
  rw [h0, sub_zero]
  exact polynomialEndpoint_eq A qp r

theorem poly_exp_integral (z A qp a b : ℝ) (hz : 0 < z) :
    (∫ t in a..b, exp (-z * t) * poly A qp t) =
      FiniteYukawa.expPrimitive z (A / 2 - qp) (qp - A) (A / 2) b -
        FiniteYukawa.expPrimitive z (A / 2 - qp) (qp - A) (A / 2) a := by
  have he : (fun t => exp (-z * t) * poly A qp t) =
      fun t => ((A / 2 - qp) + (qp - A) * t + A / 2 * t ^ 2) * exp (-z * t) := by
    funext t
    unfold poly
    ring
  rw [he, FiniteYukawa.integral_quadratic_exp a b z _ _ _ hz]

theorem polyPrime_exp_integral (z A qp r a b : ℝ) (hz : 0 < z) :
    (∫ t in a..b, polyPrime A qp (t + r) * exp (-z * t)) =
      FiniteYukawa.expPrimitive z (qp + A * (r - 1)) A 0 b -
        FiniteYukawa.expPrimitive z (qp + A * (r - 1)) A 0 a := by
  have he : (fun t => polyPrime A qp (t + r) * exp (-z * t)) =
      fun t => ((qp + A * (r - 1)) + A * t + 0 * t ^ 2) * exp (-z * t) := by
    funext t
    unfold polyPrime
    ring
  rw [he, FiniteYukawa.integral_quadratic_exp a b z _ _ _ hz]

theorem polyPrime_integral (A qp r L : ℝ) :
    (∫ t in (0 : ℝ)..L, polyPrime A qp (t + r)) =
      (qp + A * (r - 1)) * L + A * L ^ 2 / 2 := by
  have he : (fun t => polyPrime A qp (t + r)) = fun t =>
      (qp + A * (r - 1)) + A * t + 0 * t ^ 2 + 0 * t ^ 3 := by
    funext t
    unfold polyPrime
    ring
  rw [he, FiniteYukawa.integral_cubic]
  simp [FiniteYukawa.polyPrimitive]

def mixedIntegral (z A qp W C r : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..(1 - r), polyPrime A qp (t + r) * (W * exp (-z * t) + C)) +
    (∫ t in (0 : ℝ)..(1 - r), (-z * W * exp (-z * r)) * (exp (-z * t) * poly A qp t)) +
    (∫ t in (1 - r)..(1 : ℝ), (-z * (W + C * exp z) * exp (-z * r)) *
      (exp (-z * t) * poly A qp t))

/-- The mixed block is proved from its actual three bounded integrals. -/
theorem mixedIntegral_eq (z A qp W C r : ℝ) (hz : 0 < z) :
    mixedIntegral z A qp W C r = mixedCore z A qp W C r := by
  have he : (fun t => polyPrime A qp (t + r) * (W * exp (-z * t) + C)) =
      fun t => C * polyPrime A qp (t + r) + W * (polyPrime A qp (t + r) * exp (-z * t)) := by
    funext t
    ring
  unfold mixedIntegral
  rw [he, intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by unfold polyPrime; fun_prop) _ _)
    (Continuous.intervalIntegrable (by unfold polyPrime; fun_prop) _ _)]
  simp only [intervalIntegral.integral_const_mul]
  rw [polyPrime_integral, polyPrime_exp_integral z A qp r 0 (1 - r) hz,
    poly_exp_integral z A qp 0 (1 - r) hz, poly_exp_integral z A qp (1 - r) 1 hz]
  exact mixedEndpoint_eq z A qp W C r hz.ne'

def pairIntegral (z w W C V D r : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..(1 - r), (-z * W * exp (-z * r)) *
    (exp (-z * t) * (V * exp (-w * t) + D))) +
  (∫ t in (1 - r)..(1 : ℝ), (-z * (W + C * exp z) * exp (-z * r)) *
    (exp (-z * t) * (V * exp (-w * t) + D))) +
  (∫ t in Ioi (1 : ℝ), (-z * (W + C * exp z) * exp (-z * r)) * exp (-z * t) *
    ((V + D * exp w) * exp (-w * t)))

private theorem expPair_interval (z w V D a b : ℝ) (hz : 0 < z) (hw : 0 < w) :
    (∫ t in a..b, exp (-z * t) * (V * exp (-w * t) + D)) =
      D * (exp (-z * a) - exp (-z * b)) / z +
        V * (exp (-(z + w) * a) - exp (-(z + w) * b)) / (z + w) := by
  have he : (fun t => exp (-z * t) * (V * exp (-w * t) + D)) =
      fun t => D * exp (-z * t) + V * exp (-(z + w) * t) := by
    funext t
    rw [show -(z + w) * t = -z * t + -w * t by ring, exp_add]
    ring
  rw [he, intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [intervalIntegral.integral_const_mul]
  rw [FMSA.ExactMSA.Breakpoint.integral_exp_linear a b (-z) (neg_ne_zero.mpr hz.ne'),
    FMSA.ExactMSA.Breakpoint.integral_exp_linear a b (-(z + w))
      (neg_ne_zero.mpr (add_pos hz hw).ne')]
  field_simp [hz.ne', (add_pos hz hw).ne']
  ring

/-- The arbitrary-rate tail pair is proved from two bounded and one improper integral. -/
theorem pairIntegral_eq (z w W C V D r : ℝ) (hz : 0 < z) (hw : 0 < w) :
    pairIntegral z w W C V D r = pairCore z w W C V D r := by
  unfold pairIntegral
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    expPair_interval z w V D 0 (1 - r) hz hw,
    expPair_interval z w V D (1 - r) 1 hz hw,
    MultiTail.tailPair_integral z w _ _ 1 hz hw]
  simp only [mul_zero, exp_zero, mul_one]
  have hp := pairEndpoint_eq z w W C V D r hz.ne' (add_pos hz hw).ne'
  convert hp using 1 <;> dsimp only [pairEndpoint] <;> ring

end FMSA.ExactMSA.MultiTail.Blocks
