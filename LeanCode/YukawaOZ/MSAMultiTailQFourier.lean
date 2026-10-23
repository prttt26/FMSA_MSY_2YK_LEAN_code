import LeanCode.YukawaOZ.MSAMultiTailFactorization

/-! Identification of the scalar spectral dictionary with actual Baxter Fourier integrals. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.HardSphere
open scoped BigOperators

namespace FMSA.ExactMSA.MultiTail

variable {ι : Type*} [Fintype ι]

theorem exp_cos_integrable (z k a : ℝ) (hz : 0 < z) :
    IntegrableOn (fun r => exp (-z * r) * cos (k * r)) (Ioi a) := by
  exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos hz) a).mul_bdd
    (by apply Continuous.aestronglyMeasurable; fun_prop)
    (Filter.Eventually.of_forall (fun r => by simpa using abs_cos_le_one (k * r)))

theorem exp_cos_Ioi (z k : ℝ) (hz : 0 < z) (hk : k ≠ 0) :
    (∫ r in Ioi (1 : ℝ), exp (-z * r) * cos (k * r)) =
      exp (-z) * (z * cos k - k * sin k) / (z ^ 2 + k ^ 2) := by
  let F := fun r : ℝ => exp (-z * r) * sin (k * r)
  have hd : ∀ r ∈ Ici (1 : ℝ), HasDerivAt F
      ((-z) * (exp (-z * r) * sin (k * r)) + k * (exp (-z * r) * cos (k * r))) r := by
    intro r _
    have he : HasDerivAt (fun x : ℝ => exp (-z * x)) (-z * exp (-z * r)) r := by
      simpa [mul_comm] using ((hasDerivAt_id r).const_mul (-z)).exp
    have hs : HasDerivAt (fun x : ℝ => sin (k * x)) (k * cos (k * r)) r := by
      simpa [mul_comm] using ((hasDerivAt_id r).const_mul k).sin
    exact (he.mul hs).congr_deriv (by ring)
  have hi : IntegrableOn (fun r => (-z) * (exp (-z * r) * sin (k * r)) +
      k * (exp (-z * r) * cos (k * r))) (Ioi 1) :=
    ((Blocks.exp_sin_integrable z k 1 hz).const_mul (-z)).add ((exp_cos_integrable z k 1 hz).const_mul k)
  have ht : Tendsto F atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun r => show ‖F r‖ ≤ exp (-z * r) from by
      dsimp [F]
      rw [abs_mul, abs_of_pos (exp_pos _)]
      simpa using mul_le_mul_of_nonneg_left (abs_sin_le_one (k * r))
        (exp_pos (-z * r)).le)
    exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hz))
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht
  rw [integral_add ((Blocks.exp_sin_integrable z k 1 hz).const_mul (-z))
    ((exp_cos_integrable z k 1 hz).const_mul k), integral_const_mul, integral_const_mul,
    Blocks.exp_sin_Ioi z k hz] at h
  dsimp [F] at h
  simp only [mul_one, zero_sub] at h
  apply (mul_left_cancel₀ hk)
  calc
    k * (∫ r in Ioi (1 : ℝ), exp (-z * r) * cos (k * r)) =
        -exp (-z) * sin k + z * (exp (-z) * (k * cos k + z * sin k) / (z ^ 2 + k ^ 2)) := by
      linarith
    _ = _ := by field_simp [show z ^ 2 + k ^ 2 ≠ 0 by positivity]; ring

theorem poly_cos_integral (A qp k : ℝ) (hk : k ≠ 0) :
    (∫ r in (0 : ℝ)..1, Blocks.poly A qp r * cos (k * r)) = Blocks.polyRe A qp k := by
  have he : (fun r => Blocks.poly A qp r * cos (k * r)) = fun r =>
      (A / 2 - qp) * cos (k * r) + (qp - A) * (r * cos (k * r)) + A / 2 * (r ^ 2 * cos (k * r)) := by
    funext r
    unfold Blocks.poly
    ring
  rw [he, intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [intervalIntegral.integral_const_mul]
  rw [chi0_formula hk 1, chi1_formula hk 1, chi2_formula hk 1]
  simp only [mul_one, one_pow]
  unfold Blocks.polyRe
  field_simp [hk]
  ring

theorem poly_sin_integral (A qp k : ℝ) (hk : k ≠ 0) :
    (∫ r in (0 : ℝ)..1, Blocks.poly A qp r * sin (k * r)) = -Blocks.polyIm A qp k := by
  have he : Blocks.poly A qp = fun r => (A / 2 - qp) + (qp - A) * r + A / 2 * r ^ 2 + 0 * r ^ 4 := by
    funext r
    unfold Blocks.poly
    ring
  rw [he, Blocks.polynomial_sine_integral _ _ _ _ k hk]
  unfold Blocks.polynomialSine Blocks.polyIm
  field_simp [hk]
  ring

def qCosine (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..1, qCore xi z Dt G r * cos (k * r)) +
    ∫ r in Ioi (1 : ℝ), qTail xi z Dt G r * cos (k * r)

def qSine (xi : ℝ) (z Dt G : ι → ℝ) (k : ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..1, qCore xi z Dt G r * sin (k * r)) +
    ∫ r in Ioi (1 : ℝ), qTail xi z Dt G r * sin (k * r)

/-- A finite-tail transform is assembled from actual core and improper-tail integrals. -/
theorem q_weight_blocks (xi : ℝ) (z Dt G : ι → ℝ) (h : ℝ → ℝ)
    (hc : Continuous h)
    (ht : ∀ u, IntegrableOn (fun r => exp (-z u * r) * h r) (Ioi (1 : ℝ))) :
    (∫ r in (0 : ℝ)..1, qCore xi z Dt G r * h r) +
      (∫ r in Ioi (1 : ℝ), qTail xi z Dt G r * h r) =
      (∫ r in (0 : ℝ)..1, Blocks.poly (amplitudeA xi z Dt G)
        (amplitudeQp xi z Dt G) r * h r) +
      ∑ u, (W xi z Dt G u * (∫ r in (0 : ℝ)..1, exp (-z u * r) * h r) +
        C xi z Dt G u * (∫ r in (0 : ℝ)..1, h r) +
        (W xi z Dt G u + C xi z Dt G u * exp (z u)) *
          (∫ r in Ioi (1 : ℝ), exp (-z u * r) * h r)) := by
  have hi : ∀ u, IntervalIntegrable (fun r =>
      (W xi z Dt G u * exp (-z u * r) + C xi z Dt G u) * h r) volume 0 1 := by
    intro u
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous (fun r => W xi z Dt G u * exp (-z u * r) + C xi z Dt G u)).mul hc
  have hp : IntervalIntegrable (fun r => Blocks.poly (amplitudeA xi z Dt G)
      (amplitudeQp xi z Dt G) r * h r) volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact (by unfold Blocks.poly; fun_prop : Continuous
      (fun r => Blocks.poly (amplitudeA xi z Dt G) (amplitudeQp xi z Dt G) r)).mul hc
  have hs := IntervalIntegrable.sum Finset.univ (fun u _ => hi u)
  have ec : (fun r => qCore xi z Dt G r * h r) = fun r =>
      Blocks.poly (amplitudeA xi z Dt G) (amplitudeQp xi z Dt G) r * h r +
      ∑ u, (W xi z Dt G u * exp (-z u * r) + C xi z Dt G u) * h r := by
    funext r
    rw [qCore_decomposition, add_mul, Finset.sum_mul]
    rfl
  have et : (fun r => qTail xi z Dt G r * h r) = fun r =>
      ∑ u, (W xi z Dt G u + C xi z Dt G u * exp (z u)) * (exp (-z u * r) * h r) := by
    funext r
    rw [qTail_decomposition, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    unfold tailQ
    ring
  rw [ec, intervalIntegral.integral_add hp (by simpa only [Finset.sum_fn] using hs),
    intervalIntegral.integral_finsetSum (fun u _ => hi u), et,
    integral_finsetSum _ (fun u _ => (ht u).const_mul _)]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [integral_const_mul]
  congr 1
  have e : (fun r => (W xi z Dt G u * exp (-z u * r) + C xi z Dt G u) * h r) =
      fun r => W xi z Dt G u * (exp (-z u * r) * h r) + C xi z Dt G u * h r := by
    funext r
    ring
  have hi1 : IntervalIntegrable (fun r => W xi z Dt G u * (exp (-z u * r) * h r)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact (((by fun_prop : Continuous (fun r => exp (-z u * r))).mul hc).const_mul _)
  have hi2 : IntervalIntegrable (fun r => C xi z Dt G u * h r) volume 0 1 :=
    (hc.const_mul _).intervalIntegrable 0 1
  rw [e, intervalIntegral.integral_add hi1 hi2]
  simp only [intervalIntegral.integral_const_mul]

theorem qCosine_eq (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    {k : ℝ} (hk : k ≠ 0) : qCosine xi z Dt G k = Qre xi z Dt G k := by
  unfold qCosine
  rw [q_weight_blocks xi z Dt G (fun r => cos (k * r)) (by fun_prop)
    (fun u => exp_cos_integrable (z u) k 1 (hz u)), poly_cos_integral _ _ k hk]
  unfold Qre
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [exp_cos_integral (show (z u) ^ 2 + k ^ 2 ≠ 0 by positivity), chi0_formula hk 1,
    exp_cos_Ioi (z u) k (hz u) hk]
  simp only [mul_one]
  unfold Blocks.tailRe
  have he : exp (z u) * exp (-z u) = 1 := by rw [← exp_add]; simp
  field_simp [hk, show (z u) ^ 2 + k ^ 2 ≠ 0 by positivity]
  linear_combination C xi z Dt G u * k * (z u * cos k - k * sin k) * he

theorem qSine_eq (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    {k : ℝ} (hk : k ≠ 0) : qSine xi z Dt G k = -Qim xi z Dt G k := by
  unfold qSine
  rw [q_weight_blocks xi z Dt G (fun r => sin (k * r)) (by fun_prop)
    (fun u => Blocks.exp_sin_integrable (z u) k 1 (hz u)), poly_sin_integral _ _ k hk]
  unfold Qim
  rw [neg_add, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [exp_sin_integral (show (z u) ^ 2 + k ^ 2 ≠ 0 by positivity), psi0_formula hk 1,
    Blocks.exp_sin_Ioi (z u) k (hz u)]
  simp only [mul_one]
  unfold Blocks.tailIm
  have he : exp (z u) * exp (-z u) = 1 := by rw [← exp_add]; simp
  field_simp [hk, show (z u) ^ 2 + k ^ 2 ≠ 0 by positivity]
  linear_combination C xi z Dt G u * k * (k * cos k + z u * sin k) * he

/-- The split transform is the ordinary half-line integral for every continuous
weight whose exponential tail products are integrable. -/
theorem q_weight_eq_integral (xi : ℝ) (z Dt G : ι → ℝ) (h : ℝ → ℝ)
    (hc : Continuous h)
    (ht : ∀ u, IntegrableOn (fun r => exp (-z u * r) * h r) (Ioi (1 : ℝ))) :
    (∫ r in (0 : ℝ)..1, qCore xi z Dt G r * h r) +
      (∫ r in Ioi (1 : ℝ), qTail xi z Dt G r * h r) =
      ∫ r in Ioi (0 : ℝ), q xi z Dt G r * h r := by
  have hcore : ∀ r ∈ Set.uIcc (0 : ℝ) 1, q xi z Dt G r = qCore xi z Dt G r := by
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) 1 := by simpa using hr
    rw [q, if_neg (not_lt.mpr hr'.1), if_pos hr'.2]
  have htail : ∀ r ∈ Ioi (1 : ℝ), q xi z Dt G r = qTail xi z Dt G r := by
    intro r hr
    change 1 < r at hr
    rw [q, if_neg (by linarith), if_neg (not_le.mpr hr)]
  have hb : IntervalIntegrable (fun r => q xi z Dt G r * h r) volume 0 1 := by
    have hh : Continuous (fun r => qCore xi z Dt G r * h r) := by
      unfold qCore
      exact (by fun_prop : Continuous (fun r =>
        amplitudeQp xi z Dt G * (r - 1) + amplitudeA xi z Dt G / 2 * (r - 1) ^ 2 +
          ∑ t, (W xi z Dt G t * exp (-z t * r) + C xi z Dt G t))).mul hc
    exact (hh.intervalIntegrable 0 1).congr (fun r hr => by rw [hcore r (uIoc_subset_uIcc hr)])
  have hi : IntegrableOn (fun r => qTail xi z Dt G r * h r) (Ioi 1) := by
    have he : (fun r => qTail xi z Dt G r * h r) = fun r =>
        ∑ u, (W xi z Dt G u + C xi z Dt G u * exp (z u)) * (exp (-z u * r) * h r) := by
      funext r
      rw [qTail_decomposition, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      unfold tailQ
      ring
    rw [he]
    exact integrable_finsetSum _ (fun u _ => (ht u).const_mul _)
  have hh : IntegrableOn (fun r => q xi z Dt G r * h r) (Ioi 1) :=
    hi.congr_fun (fun r hr => by rw [htail r hr]) measurableSet_Ioi
  rw [← intervalIntegral.integral_interval_add_Ioi' hb hh]
  congr 1
  · exact intervalIntegral.integral_congr (fun r hr => by rw [hcore r hr])
  · exact setIntegral_congr_fun measurableSet_Ioi (fun r hr => by rw [htail r hr])

theorem Qre_eq_integral (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    {k : ℝ} (hk : k ≠ 0) :
    Qre xi z Dt G k = ∫ r in Ioi (0 : ℝ), q xi z Dt G r * cos (k * r) := by
  rw [← qCosine_eq xi z Dt G hz hk]
  exact q_weight_eq_integral xi z Dt G _ (by fun_prop)
    (fun u => exp_cos_integrable (z u) k 1 (hz u))

theorem Qim_eq_neg_integral (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    {k : ℝ} (hk : k ≠ 0) :
    Qim xi z Dt G k = -(∫ r in Ioi (0 : ℝ), q xi z Dt G r * sin (k * r)) := by
  have he := q_weight_eq_integral xi z Dt G (fun r => sin (k * r)) (by fun_prop)
    (fun u => Blocks.exp_sin_integrable (z u) k 1 (hz u))
  change qSine xi z Dt G k = _ at he
  rw [qSine_eq xi z Dt G hz hk] at he
  linarith

/-- Fourier factorization stated entirely using actual real-space integrals. -/
theorem factorization_integrals (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    {k : ℝ} (hk : k ≠ 0) :
    1 - rhoOf xi * radial_fourier (correlation xi z Dt G) k =
      (1 - rhoOf xi * (∫ r in Ioi (0 : ℝ), q xi z Dt G r * cos (k * r))) ^ 2 +
      (rhoOf xi * (∫ r in Ioi (0 : ℝ), q xi z Dt G r * sin (k * r))) ^ 2 := by
  rw [factorization xi z Dt G k hz hk, Qre_eq_integral xi z Dt G hz hk,
    Qim_eq_neg_integral xi z Dt G hz hk]
  ring

end FMSA.ExactMSA.MultiTail
