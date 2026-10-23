import LeanCode.YukawaOZ.MSAMultiTailConvolutionAssembly
import LeanCode.YukawaOZ.MSACoreTransform
import LeanCode.YukawaOZ.MSADCFTransform

/-! Actual sine integrals of all three convolution blocks. -/
noncomputable section
open MeasureTheory Set Real
open FMSA.HardSphere
open scoped BigOperators

namespace FMSA.ExactMSA.MultiTail.Blocks

def polynomialSine (c0 c1 c2 c4 k : ℝ) : ℝ :=
  c0 * (1 - cos k) / k + c1 * (sin k - k * cos k) / k ^ 2 +
    c2 * (-k ^ 2 * cos k + 2 * k * sin k + 2 * (cos k - 1)) / k ^ 3 +
    c4 * (-k ^ 4 * cos k + 4 * k ^ 3 * sin k + 12 * k ^ 2 * cos k -
      24 * k * sin k + 24 * (1 - cos k)) / k ^ 5

theorem polynomial_sine_integral (c0 c1 c2 c4 k : ℝ) (hk : k ≠ 0) :
    (∫ r in (0 : ℝ)..1, (c0 + c1 * r + c2 * r ^ 2 + c4 * r ^ 4) * sin (k * r)) =
      polynomialSine c0 c1 c2 c4 k := by
  have he : (fun r => (c0 + c1 * r + c2 * r ^ 2 + c4 * r ^ 4) * sin (k * r)) =
      fun r => c0 * sin (k * r) + c1 * (r * sin (k * r)) +
        c2 * (r ^ 2 * sin (k * r)) + c4 * (r ^ 4 * sin (k * r)) := by
    funext r
    ring
  rw [he, intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [intervalIntegral.integral_const_mul]
  rw [psi0_formula hk 1, psi1_formula hk 1, psi2_formula hk 1, psi4_formula hk 1]
  simp only [mul_one, one_pow]
  unfold polynomialSine
  field_simp [hk]
  ring

theorem exp_sin_integrable (z k a : ℝ) (hz : 0 < z) :
    IntegrableOn (fun r => exp (-z * r) * sin (k * r)) (Ioi a) := by
  exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos hz) a).mul_bdd
    (by apply Continuous.aestronglyMeasurable; fun_prop)
    (Filter.Eventually.of_forall (fun r => by simpa using abs_sin_le_one (k * r)))

theorem exp_sin_Ioi (z k : ℝ) (hz : 0 < z) :
    (∫ r in Ioi (1 : ℝ), exp (-z * r) * sin (k * r)) =
      exp (-z) * (k * cos k + z * sin k) / (z ^ 2 + k ^ 2) := by
  have he : (fun r => exp (-z * r) * sin (k * r)) =
      fun r => exp (-z) * (exp (-z * (r - 1)) * sin (k * r)) := by
    funext r
    rw [← mul_assoc, ← exp_add]
    congr 2
    ring
  rw [he, integral_const_mul, yukawa_tail_sine_integral hz k 1]
  simp only [mul_one, mul_div_assoc]

def negativeSine (z k : ℝ) : ℝ :=
  (k - exp (-z) * (z * sin k + k * cos k)) / (z ^ 2 + k ^ 2)

def positiveSine (z k : ℝ) : ℝ :=
  (k + exp z * (z * sin k - k * cos k)) / (z ^ 2 + k ^ 2)

theorem polyexp_sine_integral (c0 c1 c2 c4 bm bp z k : ℝ) (hk : k ≠ 0)
    (hzk : z ^ 2 + k ^ 2 ≠ 0) :
    (∫ r in (0 : ℝ)..1, (c0 + c1 * r + c2 * r ^ 2 + c4 * r ^ 4 +
      bm * exp (-z * r) + bp * exp (z * r)) * sin (k * r)) =
    polynomialSine c0 c1 c2 c4 k + bm * negativeSine z k + bp * positiveSine z k := by
  have he : (fun r => (c0 + c1 * r + c2 * r ^ 2 + c4 * r ^ 4 +
      bm * exp (-z * r) + bp * exp (z * r)) * sin (k * r)) =
      fun r => (c0 + c1 * r + c2 * r ^ 2 + c4 * r ^ 4) * sin (k * r) +
        bm * (exp (-z * r) * sin (k * r)) + bp * (exp (z * r) * sin (k * r)) := by
    funext r
    ring
  rw [he, intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [intervalIntegral.integral_const_mul]
  rw [polynomial_sine_integral _ _ _ _ k hk, exp_sin_integral hzk, exp_pos_sin_integral hzk]
  simp only [mul_one]
  unfold negativeSine positiveSine
  ring

theorem polynomialCore_sine (A qp k : ℝ) (hk : k ≠ 0) :
    (∫ r in (0 : ℝ)..1, polynomialCore A qp r * sin (k * r)) =
      SpectralAlgebra.polynomialPairIntegral k (sin k) (cos k) A qp := by
  have he : polynomialCore A qp = fun r =>
      (-A ^ 2 / 8 + A * qp / 2 - qp ^ 2 / 2) + (A ^ 2 / 6 - A * qp / 2) * r +
        qp ^ 2 / 2 * r ^ 2 + (-A ^ 2 / 24) * r ^ 4 := by
    funext r
    unfold polynomialCore
    ring
  rw [he, polynomial_sine_integral _ _ _ _ k hk]
  unfold polynomialSine SpectralAlgebra.polynomialPairIntegral
  field_simp [hk]
  ring

def mixedSine (z A qp W C k : ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..1, mixedCore z A qp W C r * sin (k * r)) +
    ∫ r in Ioi (1 : ℝ), mixedExterior z A qp W C r * sin (k * r)

theorem mixedSine_eq (z A qp W C k : ℝ) (hz : 0 < z) (hk : k ≠ 0) :
    mixedSine z A qp W C k =
      SpectralAlgebra.polynomialTailIntegral z k (sin k) (cos k) (exp (-z)) A qp W C := by
  have hzk : z ^ 2 + k ^ 2 ≠ 0 := by positivity
  have he : mixedCore z A qp W C = fun r =>
      (W * ((qp - A) / z + A / z ^ 2) + C * (qp - A / 2 - qp / z - A / z ^ 2)) +
      (W * A / z + C * A * (1 + 1 / z)) * r + (-C * A) * r ^ 2 + 0 * r ^ 4 +
      (-z * W * polyLaplace z A qp + C * (qp / z + A / z ^ 2)) * exp (-z * r) +
      (-W * exp (-z) * (qp / z + A / z ^ 2)) * exp (z * r) := by
    funext r
    unfold mixedCore
    ring
  have het : (fun r => mixedExterior z A qp W C r * sin (k * r)) =
      fun r => (-z * (W + C * exp z) * polyLaplace z A qp) * (exp (-z * r) * sin (k * r)) := by
    funext r
    unfold mixedExterior
    ring
  unfold mixedSine
  rw [he, polyexp_sine_integral _ _ _ _ _ _ z k hk hzk, het, integral_const_mul, exp_sin_Ioi z k hz]
  have ei : exp z = 1 / exp (-z) := by rw [one_div, ← exp_neg, neg_neg]
  unfold polynomialSine negativeSine positiveSine polyLaplace SpectralAlgebra.polynomialTailIntegral
  rw [ei]
  field_simp [hz.ne', hk, hzk, exp_ne_zero (-z)]
  ring

def pairSine (z w W C V D k : ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..1, pairCore z w W C V D r * sin (k * r)) +
    ∫ r in Ioi (1 : ℝ), pairExterior z w W C V D r * sin (k * r)

def orderedPairSine (z w W C V D k : ℝ) : ℝ :=
  -C * D * (1 - cos k) / k +
    (-z * W * V / (z + w) - (1 - w * exp (-z) / (z + w)) * W * D +
      w * C * D / (z + w)) * negativeSine z k -
    z * C * V * exp (-w) / (z + w) * positiveSine w k -
    z * (W + C * exp z) * tailLaplace z w V D *
      (exp (-z) * (k * cos k + z * sin k) / (z ^ 2 + k ^ 2))

theorem pairSine_eq_ordered (z w W C V D k : ℝ) (hz : 0 < z) (hw : 0 < w) (hk : k ≠ 0) :
    pairSine z w W C V D k = orderedPairSine z w W C V D k := by
  have hzk : z ^ 2 + k ^ 2 ≠ 0 := by positivity
  have hwk : w ^ 2 + k ^ 2 ≠ 0 := by positivity
  have he : (fun r => pairCore z w W C V D r * sin (k * r)) = fun r =>
      (-C * D) * sin (k * r) +
      (-z * W * V / (z + w) - (1 - w * exp (-z) / (z + w)) * W * D +
        w * C * D / (z + w)) * (exp (-z * r) * sin (k * r)) -
      (z * C * V * exp (-w) / (z + w)) * (exp (w * r) * sin (k * r)) := by
    funext r
    unfold pairCore
    ring
  have het : (fun r => pairExterior z w W C V D r * sin (k * r)) =
      fun r => (-z * (W + C * exp z) * tailLaplace z w V D) * (exp (-z * r) * sin (k * r)) := by
    funext r
    unfold pairExterior
    ring
  unfold pairSine
  rw [he, intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [intervalIntegral.integral_const_mul]
  rw [psi0_formula hk 1, exp_sin_integral hzk, exp_pos_sin_integral hwk, het,
    integral_const_mul, exp_sin_Ioi z k hz]
  simp only [mul_one]
  unfold orderedPairSine negativeSine positiveSine
  ring

theorem pairSine_polarized (z w W C V D k : ℝ) (hz : 0 < z) (hw : 0 < w) (hk : k ≠ 0) :
    pairSine z w W C V D k + pairSine w z V D W C k =
      SpectralAlgebra.tailPairIntegral z w k (sin k) (cos k) (exp (-z)) (exp (-w)) W C V D := by
  rw [pairSine_eq_ordered z w W C V D k hz hw hk, pairSine_eq_ordered w z V D W C k hw hz hk]
  have eiz : exp z = 1 / exp (-z) := by rw [one_div, ← exp_neg, neg_neg]
  have eiw : exp w = 1 / exp (-w) := by rw [one_div, ← exp_neg, neg_neg]
  unfold orderedPairSine negativeSine positiveSine tailLaplace SpectralAlgebra.tailPairIntegral
  rw [eiz, eiw]
  field_simp [hz.ne', hw.ne', hk, (add_pos hz hw).ne', (add_pos hw hz).ne',
    exp_ne_zero (-z), exp_ne_zero (-w),
    show z ^ 2 + k ^ 2 ≠ 0 by positivity, show w ^ 2 + k ^ 2 ≠ 0 by positivity]
  ring

def polyRe (A qp k : ℝ) : ℝ := qp * (cos k - 1) / k ^ 2 + A * (k - sin k) / k ^ 3
def polyIm (A qp k : ℝ) : ℝ := qp * (k - sin k) / k ^ 2 + A * (1 - cos k - k ^ 2 / 2) / k ^ 3
def tailRe (z W C k : ℝ) : ℝ :=
  W * z / (z ^ 2 + k ^ 2) + C * (sin k / k + (z * cos k - k * sin k) / (z ^ 2 + k ^ 2))
def tailIm (z W C k : ℝ) : ℝ :=
  -W * k / (z ^ 2 + k ^ 2) - C * ((1 - cos k) / k + (k * cos k + z * sin k) / (z ^ 2 + k ^ 2))

theorem polynomialCore_sine_product (A qp k : ℝ) (hk : k ≠ 0) :
    (∫ r in (0 : ℝ)..1, polynomialCore A qp r * sin (k * r)) =
      -k / 2 * (polyRe A qp k ^ 2 + polyIm A qp k ^ 2) := by
  have h := SpectralAlgebra.polynomialPair_identity k (sin k) (cos k) A qp hk (sin_sq_add_cos_sq k)
  rw [← polynomialCore_sine A qp k hk] at h
  have hp : SpectralAlgebra.polynomialPairProduct k (sin k) (cos k) A qp =
      k / 2 * (polyRe A qp k ^ 2 + polyIm A qp k ^ 2) := by
    unfold SpectralAlgebra.polynomialPairProduct polyRe polyIm
    field_simp [hk]
    ring
  rw [hp] at h
  linarith

theorem mixedSine_product (z A qp W C k : ℝ) (hz : 0 < z) (hk : k ≠ 0) :
    mixedSine z A qp W C k =
      -k * (polyRe A qp k * tailRe z W C k + polyIm A qp k * tailIm z W C k) := by
  have hzk : z ^ 2 + k ^ 2 ≠ 0 := by positivity
  have h := SpectralAlgebra.polynomialTail_identity z k (sin k) (cos k) (exp (-z)) A qp W C
    hk hz.ne' hzk (exp_ne_zero _) (sin_sq_add_cos_sq k)
  rw [← mixedSine_eq z A qp W C k hz hk] at h
  have hp : SpectralAlgebra.polynomialTailProduct z k (sin k) (cos k) (exp (-z)) A qp W C =
      k * (polyRe A qp k * tailRe z W C k + polyIm A qp k * tailIm z W C k) := by
    unfold SpectralAlgebra.polynomialTailProduct polyRe polyIm tailRe tailIm
    field_simp [hk, hzk]
    ring
  rw [hp] at h
  linarith

theorem pairSine_product (z w W C V D k : ℝ) (hz : 0 < z) (hw : 0 < w) (hk : k ≠ 0) :
    pairSine z w W C V D k + pairSine w z V D W C k =
      -k * (tailRe z W C k * tailRe w V D k + tailIm z W C k * tailIm w V D k) := by
  have hzk : z ^ 2 + k ^ 2 ≠ 0 := by positivity
  have hwk : w ^ 2 + k ^ 2 ≠ 0 := by positivity
  have h := SpectralAlgebra.tailPair_identity z w k (sin k) (cos k) (exp (-z)) (exp (-w)) W C V D
    hk hz.ne' hzk (exp_ne_zero _) hw.ne' (add_pos hz hw).ne' hwk (exp_ne_zero _) (sin_sq_add_cos_sq k)
  rw [← pairSine_polarized z w W C V D k hz hw hk] at h
  have hp : SpectralAlgebra.tailPairProduct z w k (sin k) (cos k) (exp (-z)) (exp (-w)) W C V D =
      k * (tailRe z W C k * tailRe w V D k + tailIm z W C k * tailIm w V D k) := by
    unfold SpectralAlgebra.tailPairProduct tailRe tailIm
    field_simp [hk, hzk, hwk]
    ring
  rw [hp] at h
  linarith

theorem mixedExterior_sine_integrable (z A qp W C k : ℝ) (hz : 0 < z) :
    IntegrableOn (fun r => mixedExterior z A qp W C r * sin (k * r)) (Ioi 1) := by
  simpa only [IntegrableOn, mixedExterior, mul_assoc] using
    (exp_sin_integrable z k 1 hz).const_mul (-z * (W + C * exp z) * polyLaplace z A qp)

theorem pairExterior_sine_integrable (z w W C V D k : ℝ) (hz : 0 < z) :
    IntegrableOn (fun r => pairExterior z w W C V D r * sin (k * r)) (Ioi 1) := by
  simpa only [IntegrableOn, pairExterior, mul_assoc] using
    (exp_sin_integrable z k 1 hz).const_mul (-z * (W + C * exp z) * tailLaplace z w V D)

@[fun_prop] theorem polynomialCore_continuous (A qp : ℝ) : Continuous (polynomialCore A qp) := by
  unfold polynomialCore
  fun_prop

@[fun_prop] theorem mixedCore_continuous (z A qp W C : ℝ) : Continuous (mixedCore z A qp W C) := by
  unfold mixedCore
  fun_prop

@[fun_prop] theorem pairCore_continuous (z w W C V D : ℝ) : Continuous (pairCore z w W C V D) := by
  unfold pairCore
  fun_prop

end FMSA.ExactMSA.MultiTail.Blocks
