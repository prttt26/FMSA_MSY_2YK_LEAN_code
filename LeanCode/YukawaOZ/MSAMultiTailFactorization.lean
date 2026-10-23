import LeanCode.YukawaOZ.MSAMultiTailFourier

/-! Complete scalar finite-tail real-space/Fourier factorization. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.HardSphere
open scoped BigOperators

namespace FMSA.ExactMSA.MultiTail

variable {ι : Type*} [Fintype ι]

def primeSine (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..1, qPrimeCore xi z Dt G r * sin (k * r)) +
    ∫ r in Ioi (1 : ℝ), qPrimeTail xi z Dt G r * sin (k * r)

theorem qPrimeTail_exp (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) :
    qPrimeTail xi z Dt G r = ∑ u, -z u *
      (W xi z Dt G u + C xi z Dt G u * exp (z u)) * exp (-z u * r) := by
  rw [qPrimeTail_eq]
  apply Finset.sum_congr rfl
  intro u _
  rw [W_add_C_exp]
  ring

theorem qPrime_sine_intervalIntegrable (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ) :
    IntervalIntegrable (fun r => qPrime xi z Dt G r * sin (k * r)) volume 0 1 := by
  have hc : Continuous (fun r => qPrimeCore xi z Dt G r * sin (k * r)) := by
    unfold qPrimeCore
    fun_prop
  apply (hc.intervalIntegrable 0 1).congr
  intro r hr
  have hr' : r ∈ Ioc (0 : ℝ) 1 := by simpa using hr
  dsimp only
  rw [qPrime, if_neg (not_lt.mpr hr'.1.le), if_pos hr'.2]

theorem qPrime_sine_tailIntegrable (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ)
    (hz : ∀ u, 0 < z u) :
    IntegrableOn (fun r => qPrime xi z Dt G r * sin (k * r)) (Ioi 1) := by
  have hc : IntegrableOn (fun r => qPrimeTail xi z Dt G r * sin (k * r)) (Ioi 1) := by
    simp_rw [qPrimeTail_exp, Finset.sum_mul]
    exact integrable_finsetSum _ (fun u _ => by
      simpa only [IntegrableOn, mul_assoc] using (Blocks.exp_sin_integrable (z u) k 1 (hz u)).const_mul
        (-z u * (W xi z Dt G u + C xi z Dt G u * exp (z u))))
  apply hc.congr_fun _ measurableSet_Ioi
  intro r hr
  change 1 < r at hr
  dsimp only
  rw [qPrime, if_neg (by linarith [hr] : ¬ r < 0), if_neg (not_le.mpr hr)]

theorem qPrime_sine_integrable (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ)
    (hz : ∀ u, 0 < z u) :
    IntegrableOn (fun r => qPrime xi z Dt G r * sin (k * r)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one]
  exact ((qPrime_sine_intervalIntegrable xi z Dt G k).1).union
    (qPrime_sine_tailIntegrable xi z Dt G k hz)

theorem primeSine_eq_integral (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ)
    (hz : ∀ u, 0 < z u) : primeSine xi z Dt G k =
      ∫ r in Ioi (0 : ℝ), qPrime xi z Dt G r * sin (k * r) := by
  have hc : (∫ r in (0 : ℝ)..1, qPrime xi z Dt G r * sin (k * r)) =
      ∫ r in (0 : ℝ)..1, qPrimeCore xi z Dt G r * sin (k * r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) 1 := by simpa using hr
    dsimp only
    rw [qPrime, if_neg (not_lt.mpr hr'.1), if_pos hr'.2]
  have ht : (∫ r in Ioi (1 : ℝ), qPrime xi z Dt G r * sin (k * r)) =
      ∫ r in Ioi (1 : ℝ), qPrimeTail xi z Dt G r * sin (k * r) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change 1 < r at hr
    dsimp only
    rw [qPrime, if_neg (by linarith [hr] : ¬ r < 0), if_neg (not_le.mpr hr)]
  rw [← intervalIntegral.integral_interval_add_Ioi' (qPrime_sine_intervalIntegrable xi z Dt G k)
    (qPrime_sine_tailIntegrable xi z Dt G k hz), hc, ht]
  rfl

/-- Actual linear derivative term, paired with the unscaled Baxter real part. -/
theorem primeSine_eq (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ)
    (hz : ∀ u, 0 < z u) (hk : k ≠ 0) :
    primeSine xi z Dt G k = -k * Qre xi z Dt G k := by
  let A := amplitudeA xi z Dt G
  let qp := amplitudeQp xi z Dt G
  have hc : (∫ r in (0 : ℝ)..1, qPrimeCore xi z Dt G r * sin (k * r)) =
      -k * Blocks.polyRe A qp k +
        ∑ u, (-z u * W xi z Dt G u) * Blocks.negativeSine (z u) k := by
    have he : (fun r => qPrimeCore xi z Dt G r * sin (k * r)) = fun r =>
        (qp - A) * sin (k * r) + A * (r * sin (k * r)) +
          ∑ u, (-z u * W xi z Dt G u) * (exp (-z u * r) * sin (k * r)) := by
      funext r
      unfold qPrimeCore
      simp only [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      rw [add_mul, Finset.sum_mul]
      dsimp [A, qp]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro u _
        ring
    rw [he, intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_finsetSum (fun _ _ => Continuous.intervalIntegrable (by fun_prop) 0 1)]
    simp only [intervalIntegral.integral_const_mul]
    rw [psi0_formula hk 1, psi1_formula hk 1]
    simp_rw [exp_sin_integral (show (z _) ^ 2 + k ^ 2 ≠ 0 by positivity)]
    simp only [mul_one]
    unfold Blocks.polyRe Blocks.negativeSine
    congr 1
    · field_simp [hk]
      ring
    · apply Finset.sum_congr rfl
      intro u _
      ring
  have ht : (∫ r in Ioi (1 : ℝ), qPrimeTail xi z Dt G r * sin (k * r)) =
      ∑ u, (-z u * (W xi z Dt G u + C xi z Dt G u * exp (z u))) *
        (exp (-z u) * (k * cos k + z u * sin k) / ((z u) ^ 2 + k ^ 2)) := by
    simp_rw [qPrimeTail_exp, Finset.sum_mul]
    rw [integral_finsetSum _ (fun u _ => by
      simpa only [IntegrableOn, mul_assoc] using (Blocks.exp_sin_integrable (z u) k 1 (hz u)).const_mul
        (-z u * (W xi z Dt G u + C xi z Dt G u * exp (z u))))]
    apply Finset.sum_congr rfl
    intro u _
    rw [show (fun r => -z u * (W xi z Dt G u + C xi z Dt G u * exp (z u)) *
        exp (-z u * r) * sin (k * r)) =
        fun r => (-z u * (W xi z Dt G u + C xi z Dt G u * exp (z u))) *
          (exp (-z u * r) * sin (k * r)) by funext r; ring,
      integral_const_mul, Blocks.exp_sin_Ioi (z u) k (hz u)]
  rw [primeSine, hc, ht]
  unfold Qre
  dsimp only [A, qp]
  rw [mul_add, Finset.mul_sum]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  have ei : exp (z u) = 1 / exp (-z u) := by rw [one_div, ← exp_neg, neg_neg]
  unfold Blocks.negativeSine Blocks.tailRe
  rw [ei]
  field_simp [hk, exp_ne_zero (-z u), show (z u) ^ 2 + k ^ 2 ≠ 0 by positivity]
  ring

/-- Actual radial Fourier identity, with the direct correlation independently
defined from the real-space Baxter convolution. -/
theorem radial_fourier_correlation (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ)
    (hz : ∀ u, 0 < z u) (hk : k ≠ 0) :
    radial_fourier (correlation xi z Dt G) k =
      2 * Qre xi z Dt G k - rhoOf xi * (Qre xi z Dt G k ^ 2 + Qim xi z Dt G k ^ 2) := by
  have he : (∫ r in Ioi (0 : ℝ), r * correlation xi z Dt G r * sin (k * r)) =
      (1 / (2 * π)) * ∫ r in Ioi (0 : ℝ),
        (-qPrime xi z Dt G r * sin (k * r) + rhoOf xi * (convolution xi z Dt G r * sin (k * r))) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change 0 < r at hr
    dsimp only
    unfold correlation
    field_simp [Real.pi_ne_zero, hr.ne']
  unfold radial_fourier
  rw [he]
  simp only [neg_mul]
  rw [integral_add (f := fun r => -(qPrime xi z Dt G r * sin (k * r)))
    (qPrime_sine_integrable xi z Dt G k hz).neg
    ((convolution_sine_integrable xi z Dt G k hz).const_mul (rhoOf xi))]
  rw [integral_neg, integral_const_mul, ← primeSine_eq_integral xi z Dt G k hz,
    ← convolutionSine_eq_integral xi z Dt G k hz, primeSine_eq xi z Dt G k hz hk,
    convolutionSine_product xi z Dt G k hz hk]
  field_simp [Real.pi_ne_zero, hk]
  ring

/-- Full finite-tail factorization. Exterior closure at an IsRoot is supplied
separately; this theorem concerns the actual c-side Fourier integral. -/
theorem factorization (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ)
    (hz : ∀ u, 0 < z u) (hk : k ≠ 0) :
    1 - rhoOf xi * radial_fourier (correlation xi z Dt G) k =
      (1 - rhoOf xi * Qre xi z Dt G k) ^ 2 + (rhoOf xi * Qim xi z Dt G k) ^ 2 := by
  rw [radial_fourier_correlation xi z Dt G k hz hk]
  ring

theorem structureDen_nonneg (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ)
    (hz : ∀ u, 0 < z u) (hk : k ≠ 0) :
    0 ≤ 1 - rhoOf xi * radial_fourier (correlation xi z Dt G) k := by
  rw [factorization xi z Dt G k hz hk]
  positivity

end FMSA.ExactMSA.MultiTail
