import LeanCode.YukawaOZ.MSAMultiTailQFourier
import LeanCode.YukawaOZ.MSAGSideOZ

/-!
# Finite-tail g-side OZ bridge and its explicit premises

The RDF support, weighted RDF moment integrability, moment identification and
g-side OZ equation are premises. A BH root alone does not construct an RDF.
The concrete Baxter kernel's support, integrability and transform are proved.
Repeated rates are allowed. Exterior sum closure cannot identify individual
tail amplitudes at repeated rates; no converse of that kind is asserted here.
-/
noncomputable section
open MeasureTheory Set Real
open scoped BigOperators

namespace FMSA.ExactMSA.MultiTail

variable {ι : Type*} [Fintype ι]

def gsource (xi : ℝ) (z Dt G : ι → ℝ) (u : ℝ) : ℝ :=
  u * amplitudeA xi z Dt G + amplitudeQp xi z Dt G +
    ∑ t, z t * C xi z Dt G t * exp (-z t * u)

theorem gsource_laplace (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ t, 0 < z t)
    {s : ℝ} (hs : 0 < s) :
    (∫ u in Ioi (0 : ℝ), gsource xi z Dt G u * exp (-s * u)) =
      secondRHS xi z Dt G s := by
  have he : (fun u => gsource xi z Dt G u * exp (-s * u)) = fun u =>
      amplitudeA xi z Dt G * (u * exp (-s * u)) +
      amplitudeQp xi z Dt G * exp (-s * u) +
      ∑ t, (z t * C xi z Dt G t) * exp (-(s + z t) * u) := by
    funext u
    unfold gsource
    rw [add_mul, add_mul, Finset.sum_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro t _
      rw [show -(s + z t) * u = -z t * u + -s * u by ring, exp_add]
      ring
  have h1 : IntegrableOn (fun u => amplitudeA xi z Dt G * (u * exp (-s * u))) (Ioi 0) :=
    (integrableOn_Ioi_id_mul_exp_neg hs).const_mul _
  have h2 : IntegrableOn (fun u => amplitudeQp xi z Dt G * exp (-s * u)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -s < 0) 0).const_mul _
  have ht : ∀ t, IntegrableOn (fun u => (z t * C xi z Dt G t) * exp (-(s + z t) * u)) (Ioi 0) := by
    intro t
    exact (integrableOn_exp_mul_Ioi (by linarith [hz t] : -(s + z t) < 0) 0).const_mul _
  have ha : IntegrableOn (fun u => amplitudeA xi z Dt G * (u * exp (-s * u)) +
      amplitudeQp xi z Dt G * exp (-s * u)) (Ioi 0) := h1.add h2
  have hb : IntegrableOn (fun u => ∑ t, (z t * C xi z Dt G t) * exp (-(s + z t) * u))
      (Ioi 0) := integrable_finsetSum _ (fun t _ => ht t)
  rw [he, integral_add ha hb,
    integral_add h1 h2, integral_finsetSum _ (fun t _ => ht t)]
  simp only [integral_const_mul]
  rw [integral_Ioi_id_mul_exp_neg hs, integral_exp_mul_Ioi (by linarith : -s < 0)]
  simp only [mul_zero, exp_zero]
  have hp (t : ι) : (∫ u in Ioi (0 : ℝ), exp (-(s + z t) * u)) = 1 / (s + z t) := by
    rw [integral_exp_mul_Ioi (by linarith [hz t] : -(s + z t) < 0)]
    simp only [mul_zero, exp_zero]
    field_simp [show -(s + z t) ≠ 0 by linarith [hz t], (add_pos hs (hz t)).ne']
  simp_rw [hp]
  unfold secondRHS
  have hsum : (∑ t, s ^ 2 * z t / (s + z t) * C xi z Dt G t) =
      s ^ 2 * ∑ t, z t * C xi z Dt G t * (1 / (s + z t)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hsum]
  field_simp [hs.ne']

theorem q_nonneg_weighted_integrable (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ t, 0 < z t)
    {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun t => exp (-s * t) * q xi z Dt G t) := by
  have he : (fun t => exp (-s * t) * q xi z Dt G t) =
      (Ici (0 : ℝ)).indicator (fun t => exp (-s * t) * q xi z Dt G t) := by
    funext t
    by_cases ht : 0 ≤ t
    · simp [indicator_apply, ht]
    · simp [indicator_apply, ht, q, not_le.mp ht]
  rw [he, integrable_indicator_iff measurableSet_Ici,
    ← Icc_union_Ioi_eq_Ici (a := (0 : ℝ)) (b := 1) zero_le_one]
  apply IntegrableOn.union
  · have hi : IntegrableOn (fun t => exp (-s * t) * qCore xi z Dt G t) (Icc 0 1) := by
      apply Continuous.integrableOn_Icc
      unfold qCore
      fun_prop
    apply hi.congr_fun _ measurableSet_Icc
    intro t ht
    dsimp only
    rw [q, if_neg (not_lt.mpr ht.1), if_pos ht.2]
  · have et : (fun t => exp (-s * t) * qTail xi z Dt G t) = fun t =>
        ∑ u, (W xi z Dt G u + C xi z Dt G u * exp (z u)) * exp (-(s + z u) * t) := by
      funext t
      rw [qTail_decomposition, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      unfold tailQ
      rw [show -(s + z u) * t = -s * t + -z u * t by ring, exp_add]
      ring
    have hi : IntegrableOn (fun t => exp (-s * t) * qTail xi z Dt G t) (Ioi 1) := by
      rw [et]
      exact integrable_finsetSum _ (fun u _ =>
        (integrableOn_exp_mul_Ioi (by linarith [hz u] : -(s + z u) < 0) 1).const_mul _)
    apply hi.congr_fun _ measurableSet_Ioi
    intro t ht
    dsimp only
    change 1 < t at ht
    rw [q, if_neg (by linarith), if_neg (not_le.mpr ht)]

theorem q_weighted_integrable (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ t, 0 < z t)
    {s : ℝ} (hs : 0 < s) : Integrable (fun t => exp (-s * t) * q xi z Dt G t) :=
  q_nonneg_weighted_integrable xi z Dt G hz hs.le

/-- The actual supported finite-tail Baxter kernel belongs to L1 on the full line. -/
theorem q_integrable (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ t, 0 < z t) :
    Integrable (q xi z Dt G) := by
  simpa using q_nonneg_weighted_integrable xi z Dt G hz (s := 0) le_rfl

/-- The second BH equations follow from the actual g-side OZ moments.
The RDF hypotheses are retained explicitly; the Baxter L1/transform hypotheses are discharged. -/
theorem second_equations_of_gside (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ t, 0 < z t)
    (g : ℝ → ℝ) (hsupp : ∀ u, u < 0 → g u = 0)
    (hL1 : ∀ t, Integrable (fun u => exp (-z t * u) * (u * g u)))
    (hmoment : ∀ t, GSide.rdfLaplaceMoment g (z t) = G t)
    (hoz : ∀ t, 2 * π * GSide.rdfLaplaceMoment g (z t) =
      (∫ u in Ioi (0 : ℝ), gsource xi z Dt G u * exp (-z t * u)) +
      2 * π * rhoOf xi * (∫ r in Ioi (0 : ℝ), exp (-z t * r) *
        ∫ u in Ioi (0 : ℝ), (r - u) * g (r - u) * q xi z Dt G u)) :
    ∀ t, 2 * π * G t * factor xi z Dt G (z t) = secondRHS xi z Dt G (z t) := by
  intro t
  have he := hoz t
  rw [GSide.laplace_conv_eq_rdf_mul_qhat_of_integrable g (q xi z Dt G) (z t)
    hsupp (hL1 t) (q_weighted_integrable xi z Dt G hz (hz t)), hmoment t,
    gsource_laplace xi z Dt G hz (hz t)] at he
  have hq : (∫ u in Ioi (0 : ℝ), exp (-z t * u) * q xi z Dt G u) = Qhat xi z Dt G (z t) := by
    rw [← laplaceQ_eq_Qhat xi z Dt G hz (hz t), laplaceQ_eq_integral xi z Dt G hz (hz t)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    ring
  rw [hq] at he
  unfold factor
  linear_combination he

/-- The actual g-side OZ primitive at any positive Laplace rate, beyond the
finite set of tail rates. This is the interface needed by RDF reconstruction. -/
theorem moment_identity_of_gside (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ t, 0 < z t)
    (g : ℝ → ℝ) {s : ℝ} (hs : 0 < s)
    (hsupp : ∀ u, u < 0 → g u = 0)
    (hL1 : Integrable (fun u => exp (-s * u) * (u * g u)))
    (hoz : 2 * π * GSide.rdfLaplaceMoment g s =
      (∫ u in Ioi (0 : ℝ), gsource xi z Dt G u * exp (-s * u)) +
      2 * π * rhoOf xi * (∫ r in Ioi (0 : ℝ), exp (-s * r) *
        ∫ u in Ioi (0 : ℝ), (r - u) * g (r - u) * q xi z Dt G u)) :
    2 * π * GSide.rdfLaplaceMoment g s * factor xi z Dt G s = secondRHS xi z Dt G s := by
  rw [GSide.laplace_conv_eq_rdf_mul_qhat_of_integrable g (q xi z Dt G) s
    hsupp hL1 (q_weighted_integrable xi z Dt G hz hs),
    gsource_laplace xi z Dt G hz hs] at hoz
  have hq : (∫ u in Ioi (0 : ℝ), exp (-s * u) * q xi z Dt G u) = Qhat xi z Dt G s := by
    rw [← laplaceQ_eq_Qhat xi z Dt G hz hs, laplaceQ_eq_integral xi z Dt G hz hs]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    ring
  rw [hq] at hoz
  unfold factor
  linear_combination hoz

end FMSA.ExactMSA.MultiTail
