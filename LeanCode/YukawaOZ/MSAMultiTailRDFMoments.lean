import LeanCode.YukawaOZ.MSAMultiTailRDFNormalization

/-! Actual zeroth and first Baxter moments and the RDF asymptotic normalization. -/
noncomputable section
open MeasureTheory Set Real
open scoped BigOperators

namespace FMSA.ExactMSA.MultiTail
variable {ι : Type*} [Fintype ι]

def qMoment0 (xi : ℝ) (z Dt G : ι → ℝ) : ℝ :=
  -amplitudeQp xi z Dt G / 2 + amplitudeA xi z Dt G / 6 +
    ∑ u, (W xi z Dt G u / z u + C xi z Dt G u * (1 + 1 / z u))

def qMoment1 (xi : ℝ) (z Dt G : ι → ℝ) : ℝ :=
  -amplitudeQp xi z Dt G / 6 + amplitudeA xi z Dt G / 24 +
    ∑ u, (W xi z Dt G u / (z u) ^ 2 +
      C xi z Dt G u * (1 / 2 + 1 / z u + 1 / (z u) ^ 2))

theorem exp_first_Ioi (z a : ℝ) (hz : 0 < z) :
    (∫ t in Ioi a, t * exp (-z * t)) = exp (-z * a) * (a / z + 1 / z ^ 2) := by
  rw [← GSide.integral_Ioi_shift (fun t => t * exp (-z * t)) a]
  have he : (fun u : ℝ => (u + a) * exp (-z * (u + a))) =
      fun u => exp (-z * a) * (u * exp (-z * u) + a * exp (-z * u)) := by
    funext u
    rw [show -z * (u + a) = -z * a + -z * u by ring, exp_add]
    ring
  rw [he, integral_const_mul, integral_add (integrableOn_Ioi_id_mul_exp_neg hz)
    ((integrableOn_exp_mul_Ioi (by linarith : -z < 0) 0).const_mul a),
    integral_const_mul, integral_Ioi_id_mul_exp_neg hz,
    integral_exp_mul_Ioi (by linarith : -z < 0)]
  simp only [mul_zero, exp_zero]
  field_simp [hz.ne']
  ring

theorem qMoment0_eq_integral (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u) :
    qMoment0 xi z Dt G = ∫ t in Ioi (0 : ℝ), q xi z Dt G t := by
  have ht (u : ι) : IntegrableOn (fun r => exp (-z u * r) * (1 : ℝ)) (Ioi 1) := by
    simpa using integrableOn_exp_mul_Ioi (show -z u < 0 by linarith [hz u]) 1
  have he := q_weight_blocks xi z Dt G (fun _ => 1) continuous_const ht
  rw [q_weight_eq_integral xi z Dt G _ continuous_const ht] at he
  simp only [mul_one] at he
  have hp : (∫ t in (0 : ℝ)..1, Blocks.poly (amplitudeA xi z Dt G)
      (amplitudeQp xi z Dt G) t) = -amplitudeQp xi z Dt G / 2 + amplitudeA xi z Dt G / 6 := by
    have ep : Blocks.poly (amplitudeA xi z Dt G) (amplitudeQp xi z Dt G) = fun t =>
        (amplitudeA xi z Dt G / 2 - amplitudeQp xi z Dt G) +
        (amplitudeQp xi z Dt G - amplitudeA xi z Dt G) * t +
        (amplitudeA xi z Dt G / 2) * t ^ 2 + 0 * t ^ 3 := by
      funext t; unfold Blocks.poly; ring
    rw [ep, FiniteYukawa.integral_cubic]
    unfold FiniteYukawa.polyPrimitive
    ring
  rw [hp] at he
  have htail (u : ι) :
      W xi z Dt G u * (∫ r in (0 : ℝ)..1, exp (-z u * r)) +
        C xi z Dt G u * (∫ _r in (0 : ℝ)..1, (1 : ℝ)) +
        (W xi z Dt G u + C xi z Dt G u * exp (z u)) *
          (∫ r in Ioi (1 : ℝ), exp (-z u * r)) =
      W xi z Dt G u / z u + C xi z Dt G u * (1 + 1 / z u) := by
    rw [Breakpoint.integral_exp_linear 0 1 (-z u) (by linarith [hz u]),
      integral_exp_mul_Ioi (by linarith [hz u] : -z u < 0)]
    simp only [mul_one, mul_zero, exp_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    have hx : exp (z u) * exp (-z u) = 1 := by rw [← exp_add]; simp
    field_simp [(hz u).ne']
    linear_combination C xi z Dt G u * hx
  simp_rw [htail] at he
  exact he.symm

theorem qMoment1_eq_integral (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u) :
    qMoment1 xi z Dt G = ∫ t in Ioi (0 : ℝ), q xi z Dt G t * t := by
  have ht (u : ι) : IntegrableOn (fun r => exp (-z u * r) * r) (Ioi 1) := by
    simpa only [mul_comm] using (integrableOn_Ioi_id_mul_exp_neg (hz u)).mono_set
      (Ioi_subset_Ioi zero_le_one)
  have he := q_weight_blocks xi z Dt G (fun t => t) continuous_id ht
  have hw := q_weight_eq_integral xi z Dt G (fun t => t) continuous_id ht
  rw [hw] at he
  have hp : (∫ t in (0 : ℝ)..1, Blocks.poly (amplitudeA xi z Dt G)
      (amplitudeQp xi z Dt G) t * t) =
      -amplitudeQp xi z Dt G / 6 + amplitudeA xi z Dt G / 24 := by
    have ep : (fun t => Blocks.poly (amplitudeA xi z Dt G) (amplitudeQp xi z Dt G) t * t) =
        fun t => (0 : ℝ) + (amplitudeA xi z Dt G / 2 - amplitudeQp xi z Dt G) * t +
        (amplitudeQp xi z Dt G - amplitudeA xi z Dt G) * t ^ 2 +
        (amplitudeA xi z Dt G / 2) * t ^ 3 := by
      funext t; unfold Blocks.poly; ring
    rw [ep, FiniteYukawa.integral_cubic]
    unfold FiniteYukawa.polyPrimitive
    ring
  rw [hp] at he
  have htail (u : ι) :
      W xi z Dt G u * (∫ r in (0 : ℝ)..1, exp (-z u * r) * r) +
        C xi z Dt G u * (∫ r in (0 : ℝ)..1, r) +
        (W xi z Dt G u + C xi z Dt G u * exp (z u)) *
          (∫ r in Ioi (1 : ℝ), exp (-z u * r) * r) =
      W xi z Dt G u / (z u) ^ 2 +
        C xi z Dt G u * (1 / 2 + 1 / z u + 1 / (z u) ^ 2) := by
    have hb : (∫ r in (0 : ℝ)..1, exp (-z u * r) * r) =
        FiniteYukawa.expPrimitive (z u) 0 1 0 1 - FiniteYukawa.expPrimitive (z u) 0 1 0 0 := by
      simpa only [zero_add, one_mul, mul_one, zero_mul, mul_zero, add_zero, mul_comm] using
        FiniteYukawa.integral_quadratic_exp 0 1 (z u) 0 1 0 (hz u)
    rw [hb]
    have hi : (∫ r in (0 : ℝ)..1, r) = 1 / 2 := by
      simpa using intervalIntegral.integral_id (a := (0 : ℝ)) (b := 1)
    rw [hi, show (∫ r in Ioi (1 : ℝ), exp (-z u * r) * r) =
      exp (-z u) * (1 / z u + 1 / (z u) ^ 2) by simpa only [mul_comm, mul_one] using exp_first_Ioi (z u) 1 (hz u)]
    unfold FiniteYukawa.expPrimitive
    simp only [zero_div, zero_mul, mul_zero, add_zero, sub_zero, mul_one, zero_add, exp_zero]
    have hx : exp (z u) * exp (-z u) = 1 := by rw [← exp_add]; simp
    field_simp [(hz u).ne']
    linear_combination 2 * C xi z Dt G u * (1 + z u) * hx
  simp_rw [htail] at he
  exact he.symm

/-- Both coefficients of the nondecaying polynomial cancel in the renewal
equation for y(u)-(u+1). These are consequences of the actual BH dictionary. -/
theorem rdf_background_normalization (xi : ℝ) (z Dt G : ι → ℝ)
    (hxi : 1 - xi ≠ 0) (hz : ∀ u, z u ≠ 0) :
    amplitudeA xi z Dt G / (2 * π) - 1 + rhoOf xi * qMoment0 xi z Dt G = 0 ∧
    amplitudeQp xi z Dt G / (2 * π) - 1 +
      rhoOf xi * (qMoment0 xi z Dt G - qMoment1 xi z Dt G) = 0 := by
  have hm := momentM_normalized xi z Dt G hz
  have hn := momentN_normalized xi z Dt G hz
  simp only [normW, normC, mul_div_assoc, ← Finset.mul_sum] at hm hn
  let U := ∑ u, W xi z Dt G u / z u
  let V := ∑ u, C xi z Dt G u / z u
  let H := ∑ u, C xi z Dt G u
  let J := ∑ u, (W xi z Dt G u + C xi z Dt G u) / (z u) ^ 2
  have hm' : momentM xi z Dt G = -rhoOf xi * (U + V + H) := by
    dsimp [U, V, H]; linear_combination hm
  have hn' : momentN xi z Dt G = rhoOf xi * (J + V + H / 2) := by
    dsimp [J, V, H]
    simp_rw [← mul_add, mul_div_assoc] at hn
    rw [← Finset.mul_sum] at hn
    linear_combination hn
  have hs0 : (∑ u, (W xi z Dt G u / z u + C xi z Dt G u * (1 + 1 / z u))) = U + H + V := by
    simp only [mul_add, mul_one, mul_one_div, Finset.sum_add_distrib, U, H, V]
    ring
  have hs1 : (∑ u, (W xi z Dt G u / (z u) ^ 2 +
      C xi z Dt G u * (1 / 2 + 1 / z u + 1 / (z u) ^ 2))) = J + H / 2 + V := by
    simp only [mul_add, mul_one_div, Finset.sum_add_distrib, J, H, V, add_div, Finset.sum_div]
    ring
  unfold qMoment0 qMoment1
  rw [hs0, hs1]
  unfold amplitudeA amplitudeQp
  rw [hm', hn']
  unfold bA0 bB0 qp0 rhoOf
  constructor <;> field_simp [hxi, pi_ne_zero] <;> ring

end FMSA.ExactMSA.MultiTail
