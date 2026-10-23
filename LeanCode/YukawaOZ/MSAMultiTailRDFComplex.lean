import LeanCode.YukawaOZ.MSAMultiTailRDFDecay
import LeanCode.YukawaOZ.MSAMultiTailRDFSpectral
import LeanCode.Analysis.CausalLaplaceComplex

/-! The actual global moment density's complex transfer and Abel boundary.
The actual RDF excess, rather than the linearly growing moment density, is
used for the boundary limit. -/
noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace FMSA.ExactMSA.MultiTail
variable {ι : Type*} [Fintype ι]

def sourceSymbol (xi : ℝ) (z Dt G : ι → ℝ) (s : ℂ) : ℂ :=
  RDFAlgebra.P (amplitudeA xi z Dt G : ℂ) (amplitudeQp xi z Dt G : ℂ)
    (fun u => (z u : ℂ)) (fun u => (C xi z Dt G u : ℂ)) s

def actualFactor (xi : ℝ) (z Dt G : ι → ℝ) (s : ℂ) : ℂ :=
  1 - (rhoOf xi : ℂ) * causalComplexLaplace (qRight xi z Dt G) s

theorem complexP_eq_sourceSymbol (xi : ℝ) (z Dt G : ι → ℝ) (s : ℂ) :
    complexP xi z Dt G s = (rhoOf xi : ℂ) * sourceSymbol xi z Dt G s := by
  unfold complexP sourceSymbol RDFAlgebra.P RDFAlgebra.polyP RDFAlgebra.tailP normA normQp normC
  push_cast
  simp only [mul_add, Finset.mul_sum, mul_div_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro u _; ring

theorem gsource_complex_laplace (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    {s : ℂ} (hs : 0 < s.re) :
    causalComplexLaplace (gsource xi z Dt G) s = sourceSymbol xi z Dt G s := by
  have he : (fun u : ℝ => (gsource xi z Dt G u : ℂ) * Complex.exp (-s * u)) = fun u : ℝ =>
      (amplitudeA xi z Dt G : ℂ) * ((u : ℂ) * Complex.exp (-s * u)) +
      (amplitudeQp xi z Dt G : ℂ) * Complex.exp (-s * u) +
      ∑ t, ((z t : ℂ) * (C xi z Dt G t : ℂ)) * Complex.exp (-(s + (z t : ℂ)) * u) := by
    funext u
    unfold gsource
    push_cast
    rw [add_mul, add_mul, Finset.sum_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro t _
      rw [show -(s + (z t : ℂ)) * u = (-(z t * u : ℝ) : ℂ) + -s * u by push_cast; ring,
        Complex.exp_add]
      push_cast
      ring
  have hi1 : IntegrableOn (fun u : ℝ => (amplitudeA xi z Dt G : ℂ) *
      ((u : ℂ) * Complex.exp (-s * u))) (Ioi 0) := (complex_first_integrable hs).const_mul _
  have hi2 : IntegrableOn (fun u : ℝ => (amplitudeQp xi z Dt G : ℂ) * Complex.exp (-s * u))
      (Ioi 0) := (integrableOn_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hs) 0).const_mul _
  have ht (t : ι) : IntegrableOn (fun u : ℝ => ((z t : ℂ) * (C xi z Dt G t : ℂ)) *
      Complex.exp (-(s + (z t : ℂ)) * u)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi (a := -(s + (z t : ℂ))) (by
      simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
      linarith [hz t]) 0).const_mul _
  unfold causalComplexLaplace
  have ha : IntegrableOn (fun u : ℝ => (amplitudeA xi z Dt G : ℂ) *
      ((u : ℂ) * Complex.exp (-s * u)) +
      (amplitudeQp xi z Dt G : ℂ) * Complex.exp (-s * u)) (Ioi 0) := hi1.add hi2
  have hb : IntegrableOn (fun u : ℝ => ∑ t, ((z t : ℂ) * (C xi z Dt G t : ℂ)) *
      Complex.exp (-(s + (z t : ℂ)) * u)) (Ioi 0) := integrable_finsetSum _ (fun t _ => ht t)
  rw [he, integral_add ha hb,
    integral_add hi1 hi2, integral_finsetSum _ (fun t _ => ht t)]
  simp only [integral_const_mul]
  rw [complex_first_Ioi hs, integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hs)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_neg]
  have hp (t : ι) : (∫ u : ℝ in Ioi 0, Complex.exp (-(s + (z t : ℂ)) * u)) =
      1 / (s + (z t : ℂ)) := by
    simpa only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_div, neg_neg] using
      integral_exp_mul_complex_Ioi (a := -(s + (z t : ℂ))) (by
      simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
      linarith [hz t]) 0
  simp_rw [hp]
  unfold sourceSymbol RDFAlgebra.P RDFAlgebra.polyP RDFAlgebra.tailP
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro t _; ring

theorem qRight_weighted_integrable (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun u => Real.exp (-a * u) * qRight xi z Dt G u) (Ioi 0) := by
  refine (q_nonneg_weighted_integrable xi z Dt G hz ha).integrableOn.congr_fun
    (fun u hu => ?_) measurableSet_Ioi
  dsimp only
  rw [qRight_eq_q xi z Dt G hu.le]

/-- Complex transfer of the actual globally constructed density. -/
theorem causalMoment_complex_transfer (xi : ℝ) (z Dt G : ι → ℝ)
    (hz : ∀ u, 0 < z u) (he : IntegrableOn (rdfExcess xi z Dt G) (Ioi 0))
    {s : ℂ} (hs : 0 < s.re) :
    (2 * Real.pi * rhoOf xi : ℂ) * causalComplexLaplace (causalMoment xi z Dt G) s *
      actualFactor xi z Dt G s = complexP xi z Dt G s := by
  have heq : ∀ r, 0 ≤ r → causalMoment xi z Dt G r = gsource xi z Dt G r / (2 * Real.pi) +
      ∫ t in (0 : ℝ)..r, (rhoOf xi * qRight xi z Dt G (r - t)) * causalMoment xi z Dt G t := by
    intro r hr
    rw [causalMoment_renewal xi z Dt G hr]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hr] at ht
    dsimp only
    rw [qRight_eq_q xi z Dt G (by linarith [ht.2])]
  have hiq : IntegrableOn (fun u => Real.exp (-s.re * u) * (rhoOf xi * qRight xi z Dt G u))
      (Ioi 0) := by
    have hi : IntegrableOn (fun u => rhoOf xi * (Real.exp (-s.re * u) * qRight xi z Dt G u))
        (Ioi 0) := (qRight_weighted_integrable xi z Dt G hz hs.le).const_mul (rhoOf xi)
    exact hi.congr_fun (fun u _ => by change rhoOf xi * (Real.exp (-s.re * u) * qRight xi z Dt G u) = _; ring)
      measurableSet_Ioi
  have hif : IntegrableOn (fun u => Real.exp (-s.re * u) * (gsource xi z Dt G u / (2 * Real.pi)))
      (Ioi 0) := by
    have hi : IntegrableOn (fun u => (Real.exp (-s.re * u) * gsource xi z Dt G u) / (2 * Real.pi))
        (Ioi 0) := (gsource_weighted_integrable xi z Dt G hz hs).div_const (2 * Real.pi)
    exact hi.congr_fun (fun u _ => by dsimp only; ring) measurableSet_Ioi
  have ht := causalComplexLaplace_renewal s
    ((qRight_continuous xi z Dt G).const_mul (rhoOf xi)).continuousOn
    ((gsource_continuous xi z Dt G).div_const (2 * Real.pi)).continuousOn
    (causalMoment_continuousOn xi z Dt G) hiq hif
    (causalMoment_weighted_integrable_of_excess xi z Dt G he hs) heq
  have hq : causalComplexLaplace (fun u => rhoOf xi * qRight xi z Dt G u) s =
      (rhoOf xi : ℂ) * causalComplexLaplace (qRight xi z Dt G) s := by
    unfold causalComplexLaplace
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _; dsimp only; push_cast; ring
  have hf : causalComplexLaplace (fun u => gsource xi z Dt G u / (2 * Real.pi)) s =
      sourceSymbol xi z Dt G s / (2 * Real.pi : ℂ) := by
    rw [← gsource_complex_laplace xi z Dt G hz hs]
    unfold causalComplexLaplace
    rw [← integral_div]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _; dsimp only; push_cast; ring
  rw [hq, hf] at ht
  rw [complexP_eq_sourceSymbol]
  unfold actualFactor
  push_cast
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hp] at ht
  linear_combination (rhoOf xi : ℂ) * ht

theorem complexP_continuousAt (xi : ℝ) (z Dt G : ι → ℝ) {s : ℂ}
    (hs : s ≠ 0) (hp : ∀ u, s + (z u : ℂ) ≠ 0) : ContinuousAt (complexP xi z Dt G) s := by
  unfold complexP RDFAlgebra.P RDFAlgebra.polyP RDFAlgebra.tailP
  apply ContinuousAt.add
  · exact (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hs)).add
      (continuousAt_const.div continuousAt_id hs)
  · fun_prop (disch := aesop)

/-- Actual Abel boundary transfer, derived from Volterra and L1 excess.
There is no assumed inverse-transform formula or assumed OZ equation. -/
theorem causalMoment_abel_transfer (xi : ℝ) (z Dt G : ι → ℝ)
    (hz : ∀ u, 0 < z u) (he : IntegrableOn (rdfExcess xi z Dt G) (Ioi 0))
    {s : ℂ} (hsre : s.re = 0) (hs : s ≠ 0) (hp : ∀ u, s + (z u : ℂ) ≠ 0) :
    (2 * Real.pi * rhoOf xi : ℂ) *
      (causalComplexLaplace (rdfExcess xi z Dt G) s + 1 / s ^ 2 + 1 / s) *
        actualFactor xi z Dt G s = complexP xi z Dt G s := by
  have hq0 : IntegrableOn (qRight xi z Dt G) (Ioi 0) := by
    simpa using qRight_weighted_integrable xi z Dt G hz (a := 0) (by rfl)
  have hLq := causalComplexLaplace_boundary (qRight xi z Dt G)
    (qRight_continuous xi z Dt G).continuousOn hq0 s hsre
  have hLe := causalComplexLaplace_boundary (rdfExcess xi z Dt G)
    (rdfExcess_continuousOn xi z Dt G) he s hsre
  have harg : ContinuousAt (fun a : ℝ => (a : ℂ) + s) 0 := by fun_prop
  have hd1 : ContinuousAt (fun a : ℝ => (1 : ℂ) / ((a : ℂ) + s) ^ 2) 0 :=
    continuousAt_const.div (harg.pow 2) (by simpa using pow_ne_zero 2 hs)
  have hd2 : ContinuousAt (fun a : ℝ => (1 : ℂ) / ((a : ℂ) + s)) 0 :=
    continuousAt_const.div harg (by simpa using hs)
  let L := fun a : ℝ => (2 * Real.pi * rhoOf xi : ℂ) *
    (causalComplexLaplace (rdfExcess xi z Dt G) ((a : ℂ) + s) +
      1 / ((a : ℂ) + s) ^ 2 + 1 / ((a : ℂ) + s)) * actualFactor xi z Dt G ((a : ℂ) + s)
  have hleft : ContinuousWithinAt L (Ici 0) 0 :=
    (continuousWithinAt_const.mul ((hLe.add hd1.continuousWithinAt).add hd2.continuousWithinAt)).mul
      (continuousWithinAt_const.sub (continuousWithinAt_const.mul hLq))
  have hright : ContinuousAt (fun a : ℝ => complexP xi z Dt G ((a : ℂ) + s)) 0 := by
    have hP : ContinuousAt (complexP xi z Dt G) (((0 : ℝ) : ℂ) + s) := by
      simpa using complexP_continuousAt xi z Dt G hs hp
    exact ContinuousAt.comp (f := fun a : ℝ => (a : ℂ) + s) (x := 0) hP harg
  have hlimit := (hleft.sub hright.continuousWithinAt).mono Ioi_subset_Ici_self
  have hezero : ∀ᶠ a : ℝ in 𝓝[>] 0, L a - complexP xi z Dt G ((a : ℂ) + s) = 0 := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have hsa : 0 < ((a : ℂ) + s).re := by simpa [hsre] using ha
    have ht := causalMoment_complex_transfer xi z Dt G hz he hsa
    rw [causalComplexLaplace_background (rdfExcess_continuousOn xi z Dt G) he
      (fun u _ => by unfold rdfExcess; ring) hsa] at ht
    exact sub_eq_zero.mpr ht
  have hzero : Tendsto (fun a => L a - complexP xi z Dt G ((a : ℂ) + s)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (hezero.mono (fun _ h => h.symm))
  have hval := tendsto_nhds_unique hlimit hzero
  simp only [L, Complex.ofReal_zero, zero_add] at hval
  exact sub_eq_zero.mp hval

end FMSA.ExactMSA.MultiTail
