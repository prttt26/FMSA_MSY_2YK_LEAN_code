import MSAConvergence.ScalarFourierTail

/-! Actual polynomial-exponential moments for scalar Fourier certificates.
All integrability and moment values are proved from positive rates. -/
noncomputable section
open MeasureTheory Set Real Filter Topology Asymptotics
open scoped BigOperators
namespace FMSA.Convergence.ScalarFourierMoments

/-- Every nonnegative integer moment of a positive-rate exponential is L1. -/
theorem exponential_moment_integrable (z : ℝ) (hz : 0 < z) (n : ℕ) :
    IntegrableOn (fun r : ℝ => r^n*exp (-z*r)) (Ioi 0) := by
  have htend : Tendsto (fun r : ℝ => r^n*exp (-(z/2)*r)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) (z/2) (by linarith)
  apply integrable_of_isBigO_exp_neg (b := z/2) (by linarith) (by fun_prop)
  rw [show (fun r : ℝ => r^n*exp (-z*r)) =
      fun r => (r^n*exp (-(z/2)*r))*exp (-(z/2)*r) by
    funext r
    rw [mul_assoc,← Real.exp_add,show -(z/2)*r+-(z/2)*r=-z*r by ring]]
  simpa using (htend.isBigO_one (F := ℝ)).mul
    (Asymptotics.isBigO_refl (fun r : ℝ => exp (-(z/2)*r)) atTop)

/-- The honest improper integral, with arbitrary integer order. -/
theorem exponential_moment (z : ℝ) (hz : 0 < z) (n : ℕ) :
    (∫ r in Ioi (0 : ℝ), r^n*exp (-z*r)) = (n.factorial : ℝ)/z^(n+1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ)+1) (by positivity) hz
  simp only [add_sub_cancel_right,Real.rpow_natCast,Real.Gamma_nat_eq_factorial] at h
  have hp : (1/z : ℝ)^((n : ℝ)+1) = (1/z)^(n+1) := by
    rw [show (n : ℝ)+1 = ((n+1 : ℕ) : ℝ) by simp,Real.rpow_natCast]
  rw [hp] at h
  convert h using 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    change r^n*exp (-z*r) = r^n*exp (-(z*r))
    rw [neg_mul]
  · simp [div_eq_mul_inv,mul_comm]

/-- Shifted exterior-tail moments are integrable before any Fourier damping. -/
theorem shifted_moment_integrable (z : ℝ) (hz : 0 < z) (n : ℕ) :
    IntegrableOn (fun r : ℝ => r^n*exp (-z*(r-1))) (Ioi 1) := by
  have he (r : ℝ) : r^n*exp (-z*(r-1)) = exp z*(r^n*exp (-z*r)) := by
    rw [show -z*(r-1) = z+(-z*r) by ring,Real.exp_add]
    ring
  simp_rw [he]
  exact ((exponential_moment_integrable z hz n).mono_set (Ioi_subset_Ioi (by norm_num))).const_mul _

/-- Translation of the genuine exterior moment to the positive half-line. -/
theorem shifted_moment_eq (z : ℝ) (n : ℕ) :
    (∫ r in Ioi (1 : ℝ), r^n*exp (-z*(r-1))) =
      ∫ r in Ioi (0 : ℝ), (r+1)^n*exp (-z*r) := by
  rw [← integral_indicator measurableSet_Ioi,← integral_indicator measurableSet_Ioi]
  have h := integral_add_right_eq_self (μ := volume) ((Ioi (1 : ℝ)).indicator
    (fun r : ℝ => r^n*exp (-z*(r-1)))) (1 : ℝ)
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with r
  by_cases hr : 0 < r
  · simp [indicator_of_mem,hr,show (1 : ℝ) < r+1 by linarith]
  · simp [indicator_of_notMem,hr,show ¬(1 : ℝ) < r+1 by linarith]

/-- The exact exterior second moment used by the all-wave certificates. -/
theorem shifted_moment_two (z : ℝ) (hz : 0 < z) :
    (∫ r in Ioi (1 : ℝ), r^2*exp (-z*(r-1))) = 1/z+2/z^2+2/z^3 := by
  rw [shifted_moment_eq]
  have he : (fun r : ℝ => (r+1)^2*exp (-z*r)) =
      fun r => r^2*exp (-z*r)+2*(r*exp (-z*r))+exp (-z*r) := by funext r; ring
  have hi0 : IntegrableOn (fun r : ℝ => exp (-z*r)) (Ioi 0) := by
    simpa using exponential_moment_integrable z hz 0
  have hi1 : IntegrableOn (fun r : ℝ => r*exp (-z*r)) (Ioi 0) := by
    simpa using exponential_moment_integrable z hz 1
  have hi2 := exponential_moment_integrable z hz 2
  rw [he,integral_add (hi2.fun_add (hi1.const_mul 2)) hi0,
    integral_add hi2 (hi1.const_mul 2),integral_const_mul]
  have h0 := exponential_moment z hz 0
  have h1 := exponential_moment z hz 1
  have h2 := exponential_moment z hz 2
  norm_num at h0 h1 h2
  simp only [neg_mul]
  rw [h0,h1,h2]
  ring

/-- The exact exterior third moment for small-frequency sine remainders. -/
theorem shifted_moment_three (z : ℝ) (hz : 0 < z) :
    (∫ r in Ioi (1 : ℝ), r^3*exp (-z*(r-1))) = 1/z+3/z^2+6/z^3+6/z^4 := by
  rw [shifted_moment_eq]
  have he : (fun r : ℝ => (r+1)^3*exp (-z*r)) = fun r =>
      r^3*exp (-z*r)+3*(r^2*exp (-z*r))+3*(r*exp (-z*r))+exp (-z*r) := by funext r; ring
  have h0 : IntegrableOn (fun r : ℝ => exp (-z*r)) (Ioi 0) := by
    simpa using exponential_moment_integrable z hz 0
  have h1 : IntegrableOn (fun r : ℝ => r*exp (-z*r)) (Ioi 0) := by
    simpa using exponential_moment_integrable z hz 1
  have h2 := exponential_moment_integrable z hz 2
  have h3 := exponential_moment_integrable z hz 3
  rw [he,integral_add ((h3.fun_add (h2.const_mul 3)).fun_add (h1.const_mul 3)) h0,
    integral_add (h3.fun_add (h2.const_mul 3)) (h1.const_mul 3),
    integral_add h3 (h2.const_mul 3),integral_const_mul,integral_const_mul]
  have e0 := exponential_moment z hz 0
  have e1 := exponential_moment z hz 1
  have e2 := exponential_moment z hz 2
  have e3 := exponential_moment z hz 3
  norm_num at e0 e1 e2 e3
  simp only [neg_mul]
  rw [e0,e1,e2,e3]
  ring

private theorem core_power_integrable (n : ℕ) :
    IntegrableOn (fun r : ℝ => r^n) (Icc 0 1) := by
  apply ContinuousOn.integrableOn_Icc
  fun_prop

/-- The compact monomial moment, including order zero. -/
theorem core_power_moment (n : ℕ) :
    (∫ r in Icc (0 : ℝ) 1, r^n) = 1/((n : ℝ)+1) := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),integral_pow]
  simp

/-- The compact linear basis has a positive beta-type absolute moment. -/
theorem core_linear_moment (n : ℕ) :
    (∫ r in Icc (0 : ℝ) 1, r^n*(1-r)) = 1/(((n : ℝ)+1)*((n : ℝ)+2)) := by
  have he : (fun r : ℝ => r^n*(1-r)) = fun r => r^n-r^(n+1) := by
    funext r
    rw [pow_succ]
    ring
  rw [he,integral_sub (core_power_integrable n) (core_power_integrable (n+1)),
    core_power_moment,core_power_moment]
  push_cast
  have h1 : (n : ℝ)+1 ≠ 0 := by positivity
  have h2 : (n : ℝ)+1+1 ≠ 0 := by positivity
  field_simp
  ring

/-- The compact quadratic basis has its exact half-normalized moment. -/
theorem core_quadratic_moment (n : ℕ) :
    (∫ r in Icc (0 : ℝ) 1, r^n*(r-1)^2/2) =
      1/(((n : ℝ)+1)*((n : ℝ)+2)*((n : ℝ)+3)) := by
  have he : (fun r : ℝ => r^n*(r-1)^2/2) =
      fun r => r^n/2-r^(n+1)+r^(n+2)/2 := by
    funext r
    simp only [pow_add,pow_one]
    ring
  have hi : IntegrableOn (fun r : ℝ => r^n/2-r^(n+1)) (Icc 0 1) := by
    apply ContinuousOn.integrableOn_Icc
    fun_prop
  rw [he,integral_add hi ((core_power_integrable (n+2)).div_const 2),
    integral_sub ((core_power_integrable n).div_const 2) (core_power_integrable (n+1))]
  simp only [div_eq_mul_inv]
  rw [integral_mul_const,integral_mul_const,core_power_moment,core_power_moment,core_power_moment]
  push_cast
  field_simp
  ring

open FMSA.ExactMSA.MultiTailMixture
variable {T : Type*} [Fintype T]

def scalarQ (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ) (r : ℝ) : ℝ :=
  q z (fun _ : Fin 1 => 1) (fun _ => A) (fun _ _ => qp)
    (fun u _ _ => W u) (fun u _ _ => C u) 0 0 r

private theorem scalarQ_negative (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ)
    (r : ℝ) (hr : r < 0) : scalarQ z qp A W C r = 0 := by
  norm_num [scalarQ,q,MSAMixture.edgeLo,MSAMixture.edgeHi,hr]

private theorem scalarQ_core (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    scalarQ z qp A W C r = qp*(r-1)+A/2*(r-1)^2+∑ u, (W u*exp (-z u*r)+C u) := by
  norm_num [scalarQ,q,MSAMixture.edgeLo,MSAMixture.edgeHi,not_lt.mpr hr0,hr1]

private theorem scalarQ_tail (z : T → ℝ) (qp A : ℝ) (W C : T → ℝ)
    (r : ℝ) (hr : 1 < r) :
    scalarQ z qp A W C r = ∑ u, (W u*exp (-z u*r)+C u*exp (-z u*(r-1))) := by
  have hr0 : 0 ≤ r := by linarith
  norm_num [scalarQ,q,MSAMixture.edgeLo,MSAMixture.edgeHi,not_lt.mpr hr0,not_le.mpr hr]

/-- All polynomially weighted ACTUAL Baxter kernels are integrable on the
whole real line. Positive rates internally discharge the tail hypotheses. -/
theorem weighted_q_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (qp A : ℝ) (W C : T → ℝ) (n : ℕ) :
    Integrable (fun r : ℝ => r^n*scalarQ z qp A W C r) := by
  let f0 : ℝ → ℝ := fun r =>
    r^n*(qp*(r-1)+A/2*(r-1)^2+∑ u, (W u*exp (-z u*r)+C u))
  have hc : Continuous f0 := by dsimp [f0]; fun_prop
  have hcore : IntegrableOn (fun r : ℝ => r^n*scalarQ z qp A W C r) (Icc 0 1) := by
    apply hc.continuousOn.integrableOn_Icc.congr_fun _ measurableSet_Icc
    intro r hr
    dsimp only [f0]
    rw [scalarQ_core z qp A W C r hr.1 hr.2]
  let f1 : ℝ → ℝ := fun r => ∑ u,
    (W u*(r^n*exp (-z u*r))+C u*(r^n*exp (-z u*(r-1))))
  have hi1 : IntegrableOn f1 (Ioi 1) := by
    apply integrable_finsetSum
    intro u _
    exact (((exponential_moment_integrable (z u) (hz u) n).mono_set
      (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).const_mul (W u)).fun_add
      ((shifted_moment_integrable (z u) (hz u) n).const_mul (C u))
  have htail : IntegrableOn (fun r : ℝ => r^n*scalarQ z qp A W C r) (Ioi 1) := by
    apply hi1.congr_fun _ measurableSet_Ioi
    intro r hr
    dsimp only [f1]
    rw [scalarQ_tail z qp A W C r hr,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  have hzero : IntegrableOn (fun r : ℝ => r^n*scalarQ z qp A W C r) (Iio 0) := by
    have h0 : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Iio 0) := by simp
    apply h0.congr_fun _ measurableSet_Iio
    intro r hr
    simp only [scalarQ_negative z qp A W C r hr,mul_zero]
  have hu : ((Icc (0 : ℝ) 1 ∪ Ioi 1) ∪ Iio 0) = univ := by
    ext r
    simp only [mem_union,mem_Icc,mem_Ioi,mem_Iio,mem_univ,iff_true]
    by_cases hneg : r < 0
    · exact Or.inr hneg
    · left
      by_cases hone : r ≤ 1
      · exact Or.inl ⟨le_of_not_gt hneg,hone⟩
      · exact Or.inr (lt_of_not_ge hone)
  simpa only [hu,integrableOn_univ] using (hcore.union htail).union hzero

/-- info: 'FMSA.Convergence.ScalarFourierMoments.exponential_moment_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierMoments.exponential_moment_integrable
/-- info: 'FMSA.Convergence.ScalarFourierMoments.exponential_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierMoments.exponential_moment
/-- info: 'FMSA.Convergence.ScalarFourierMoments.shifted_moment_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierMoments.shifted_moment_integrable
/-- info: 'FMSA.Convergence.ScalarFourierMoments.shifted_moment_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierMoments.shifted_moment_eq
/-- info: 'FMSA.Convergence.ScalarFourierMoments.shifted_moment_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierMoments.shifted_moment_two
/-- info: 'FMSA.Convergence.ScalarFourierMoments.shifted_moment_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierMoments.shifted_moment_three
/-- info: 'FMSA.Convergence.ScalarFourierMoments.core_power_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierMoments.core_power_moment
/-- info: 'FMSA.Convergence.ScalarFourierMoments.core_linear_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierMoments.core_linear_moment
/-- info: 'FMSA.Convergence.ScalarFourierMoments.core_quadratic_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierMoments.core_quadratic_moment
/-- info: 'FMSA.Convergence.ScalarFourierMoments.weighted_q_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ScalarFourierMoments.weighted_q_integrable
end FMSA.Convergence.ScalarFourierMoments
