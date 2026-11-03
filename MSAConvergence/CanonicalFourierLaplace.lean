import MSAConvergence.CanonicalContourShift
import Mathlib.Analysis.Fourier.Inversion

/-! Exact Fourier normalization and genuine Laplace transforms of canonical
causal inversion fields. Actual Volterra/RDF identification is separate. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped FourierTransform BigOperators

namespace FMSA.Convergence.CanonicalFourierLaplace
open FMSA.Convergence.CanonicalKernelEstimates FMSA.Convergence.CanonicalResolventAnalysis
open FMSA.Convergence.CanonicalContourShift
open FMSA.Paper FMSA.ExactMSA.MultiTailMixture MSAMixture

/-- Angular-to-standard Fourier measure normalization. -/
def fourierScale : ℂ := (((2*π : ℝ)⁻¹ : ℝ) : ℂ)

/-- The explicitly normalized vertical inversion, with no assumed transform
identity or identification with a time-domain RDF. -/
def normalizedInverse (F : ℂ → ℂ) (a t : ℝ) : ℂ := fourierScale*verticalIntegral F a t

/-- Real exponential damping, retained as a genuine complex time function. -/
def dampedField (u : ℝ → ℂ) (gamma t : ℝ) : ℂ := Complex.exp (-(gamma : ℂ)*(t : ℂ))*u t

/-- A vertical symbol sampled at the standard Fourier frequency. -/
def scaledSymbol (F : ℂ → ℂ) (gamma xi : ℝ) : ℂ := F (verticalPoint gamma (2*π*xi))

/-- The constant real phase splits from the actual vertical integral. -/
theorem vertical_integral_split_phase (F : ℂ → ℂ) (a t : ℝ) :
    verticalIntegral F a t = Complex.exp ((a : ℂ)*(t : ℂ))*
      ∫ k : ℝ, Complex.exp ((k : ℂ)*Complex.I*(t : ℂ))*F (verticalPoint a k) := by
  have he (k : ℝ) : Complex.exp (verticalPoint a k*(t : ℂ)) =
      Complex.exp ((a : ℂ)*(t : ℂ))*Complex.exp ((k : ℂ)*Complex.I*(t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    unfold verticalPoint
    ring
  unfold verticalIntegral
  simp_rw [he, mul_assoc]
  rw [integral_const_mul]

/-- The actual 2*pi substitution preserves absolute frequency integrability. -/
theorem scaled_symbol_integrable (F : ℂ → ℂ) (gamma : ℝ)
    (hi : Integrable (fun k : ℝ => F (verticalPoint gamma k))) :
    Integrable (scaledSymbol F gamma) :=
  hi.comp_mul_left' (R := 2*π) (by positivity)

/-- Mathlib's inverse theorem can use the genuine inverse-transform L1:
reflection supplies the stated forward-transform L1 without an extra assumption. -/
theorem fourier_inversion_of_inverse_integrable (f : ℝ → ℂ) (hc : Continuous f)
    (hf : Integrable f) (hInv : Integrable (𝓕⁻ f)) : 𝓕 (𝓕⁻ f) = f := by
  have he : (fun x : ℝ => (𝓕⁻ f) ((-1)*x)) = 𝓕 f := by
    funext x
    rw [neg_one_mul, Real.fourierInv_eq_fourier_neg, neg_neg]
  have hFFT : Integrable (𝓕 f) := by
    rw [← he]
    exact hInv.comp_mul_left' (R := -1) (by norm_num)
  exact hc.fourier_fourierInv_eq hf hFFT

/-- Exact standard inverse-Fourier normalization, by a real 2*pi change of
variables. This algebraic identity is used below with actual L1 supplied. -/
theorem scaled_symbol_fourierInv (F : ℂ → ℂ) (gamma t : ℝ) :
    (𝓕⁻ (scaledSymbol F gamma)) t = dampedField (normalizedInverse F gamma) gamma t := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  let g := fun k : ℝ => Complex.exp ((k : ℂ)*Complex.I*(t : ℂ))*F (verticalPoint gamma k)
  have he : (fun xi : ℝ => Complex.exp (((-2*π*xi*(-t) : ℝ) : ℂ)*Complex.I)*scaledSymbol F gamma xi) =
      fun xi : ℝ => g ((2*π)*xi) := by
    funext xi
    unfold g scaledSymbol
    congr 2
    push_cast
    ring
  rw [he, Measure.integral_comp_mul_left g (2*π),
    abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < 2*π)), Complex.real_smul]
  unfold dampedField normalizedInverse fourierScale
  rw [vertical_integral_split_phase]
  have hc : Complex.exp (-(gamma : ℂ)*(t : ℂ))*Complex.exp ((gamma : ℂ)*(t : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  change (((2*π : ℝ)⁻¹ : ℝ) : ℂ)*(∫ k : ℝ, g k) =
    Complex.exp (-(gamma : ℂ)*(t : ℂ))*((((2*π : ℝ)⁻¹ : ℝ) : ℂ)*
      (Complex.exp ((gamma : ℂ)*(t : ℂ))*(∫ k : ℝ, g k)))
  calc
    _ = (((2*π : ℝ)⁻¹ : ℝ) : ℂ)*(Complex.exp (-(gamma : ℂ)*(t : ℂ))*
        Complex.exp ((gamma : ℂ)*(t : ℂ)))*(∫ k : ℝ, g k) := by rw [hc, mul_one]
    _ = _ := by ring

/-- Cauchy line independence identifies the standard inverse transform with
the damped normalized inversion on a fixed reference line. -/
theorem shifted_fourierInv_eq_damped
    (F : ℂ → ℂ) (lower C : ℝ) (hF : AnalyticOnNhd ℂ F {s : ℂ | lower < s.re})
    (hmajor : ∀ a : ℝ, lower ≤ a → ∀ k : ℝ, (1+k^2)*‖F (verticalPoint a k)‖ ≤ C)
    (hL1 : ∀ a : ℝ, lower ≤ a → Integrable (fun k : ℝ => F (verticalPoint a k)))
    (a : ℝ) (ha : lower < a) (gamma : ℝ) (hg : a < gamma) :
    𝓕⁻ (scaledSymbol F gamma) = dampedField (normalizedInverse F a) gamma := by
  funext t
  rw [scaled_symbol_fourierInv]
  unfold dampedField normalizedInverse
  rw [vertical_integrals_eq F lower C hF hmajor hL1 gamma a (ha.trans hg) ha t]

/-- Genuine full-time weighted L1 of the normalized inverse field. -/
theorem normalized_inverse_damped_integrable
    (F : ℂ → ℂ) (lower C : ℝ) (hF : AnalyticOnNhd ℂ F {s : ℂ | lower < s.re})
    (hmajor : ∀ a : ℝ, lower ≤ a → ∀ k : ℝ, (1+k^2)*‖F (verticalPoint a k)‖ ≤ C)
    (hL1 : ∀ a : ℝ, lower ≤ a → Integrable (fun k : ℝ => F (verticalPoint a k)))
    (a : ℝ) (ha : lower < a) (gamma : ℝ) (hg : a < gamma) :
    Integrable (dampedField (normalizedInverse F a) gamma) := by
  have hi := (vertical_integral_weighted_integrable F lower C hF hmajor hL1 a ha gamma hg).const_mul fourierScale
  change Integrable (fun t : ℝ => Complex.exp (-(gamma : ℂ)*(t : ℂ))*
    (fourierScale*verticalIntegral F a t))
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hi

/-- Holomorphy supplies actual continuity of the standard frequency sample. -/
theorem scaled_symbol_continuous
    (F : ℂ → ℂ) (lower : ℝ) (hF : AnalyticOnNhd ℂ F {s : ℂ | lower < s.re})
    (gamma : ℝ) (hg : lower < gamma) : Continuous (scaledSymbol F gamma) := by
  apply continuous_iff_continuousAt.mpr
  intro xi
  have hp := hF (verticalPoint gamma (2*π*xi)) (by simpa [verticalPoint] using hg)
  have hm : ContinuousAt (fun x : ℝ => verticalPoint gamma (2*π*x)) xi := by
    unfold verticalPoint
    fun_prop
  exact hp.continuousAt.comp (f := fun x : ℝ => verticalPoint gamma (2*π*x)) hm

/-- The actual complex Laplace integrand factors into a unit-modulus
imaginary phase times the genuinely damped time field. -/
theorem damped_laplace_integrand_eq (u : ℝ → ℂ) (gamma k t : ℝ) :
    u t*Complex.exp (-verticalPoint gamma k*(t : ℂ)) =
      Complex.exp (-(k : ℂ)*Complex.I*(t : ℂ))*dampedField u gamma t := by
  have he : Complex.exp (-verticalPoint gamma k*(t : ℂ)) =
      Complex.exp (-(k : ℂ)*Complex.I*(t : ℂ))*Complex.exp (-(gamma : ℂ)*(t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    unfold verticalPoint
    ring
  rw [he]
  unfold dampedField
  ring

/-- Actual full-real-axis complex Laplace integrability follows from the
proved real damping L1, not a formal assignment to a divergent integral. -/
theorem complex_laplace_integrable_of_damped (u : ℝ → ℂ) (gamma k : ℝ)
    (hi : Integrable (dampedField u gamma)) :
    Integrable (fun t : ℝ => u t*Complex.exp (-verticalPoint gamma k*(t : ℂ))) := by
  have hm : AEStronglyMeasurable (fun t : ℝ => Complex.exp (-(k : ℂ)*Complex.I*(t : ℂ))) := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  have hh := hi.bdd_mul (c := 1) hm (Eventually.of_forall (fun t => by simp [Complex.norm_exp, Complex.mul_re]))
  have he : (fun t : ℝ => u t*Complex.exp (-verticalPoint gamma k*(t : ℂ))) =
      fun t : ℝ => Complex.exp (-(k : ℂ)*Complex.I*(t : ℂ))*dampedField u gamma t :=
    funext (fun t => damped_laplace_integrand_eq u gamma k t)
  rw [he]
  exact hh

/-- The standard Fourier transform of the damped actual time field equals
its full complex Laplace integral at the exactly scaled frequency. -/
theorem fourier_damped_eq_laplace (u : ℝ → ℂ) (gamma xi : ℝ) :
    𝓕 (dampedField u gamma) xi =
      ∫ t : ℝ, u t*Complex.exp (-verticalPoint gamma (2*π*xi)*(t : ℂ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  change Complex.exp (((-2*π*t*xi : ℝ) : ℂ)*Complex.I)*dampedField u gamma t =
    u t*Complex.exp (-verticalPoint gamma (2*π*xi)*(t : ℂ))
  rw [damped_laplace_integrand_eq]
  congr 2
  push_cast
  ring

/-- Genuine positive-axis Laplace inversion of the normalized causal field.
All full-time integrability is proved before Fourier inversion is applied,
and the positive-axis identity uses the proved nonpositive-time support. -/
theorem normalized_inverse_laplace
    (F : ℂ → ℂ) (lower C : ℝ) (hF : AnalyticOnNhd ℂ F {s : ℂ | lower < s.re})
    (hmajor : ∀ a : ℝ, lower ≤ a → ∀ k : ℝ, (1+k^2)*‖F (verticalPoint a k)‖ ≤ C)
    (hL1 : ∀ a : ℝ, lower ≤ a → Integrable (fun k : ℝ => F (verticalPoint a k)))
    (a : ℝ) (ha : lower < a) (gamma : ℝ) (hg : a < gamma) (k : ℝ) :
    Integrable (fun t : ℝ => normalizedInverse F a t*Complex.exp (-verticalPoint gamma k*(t : ℂ))) ∧
      (∫ t in Ioi (0 : ℝ), normalizedInverse F a t*Complex.exp (-verticalPoint gamma k*(t : ℂ))) =
        F (verticalPoint gamma k) := by
  have hInv := shifted_fourierInv_eq_damped F lower C hF hmajor hL1 a ha gamma hg
  have hDi := normalized_inverse_damped_integrable F lower C hF hmajor hL1 a ha gamma hg
  have hSi := scaled_symbol_integrable F gamma (hL1 gamma (ha.trans hg).le)
  have hIi : Integrable (𝓕⁻ (scaledSymbol F gamma)) := by rw [hInv]; exact hDi
  have hFFT := fourier_inversion_of_inverse_integrable (scaledSymbol F gamma)
    (scaled_symbol_continuous F lower hF gamma (ha.trans hg)) hSi hIi
  have hv := congrFun hFFT (k/(2*π))
  rw [hInv, fourier_damped_eq_laplace] at hv
  change (∫ t : ℝ, normalizedInverse F a t*
    Complex.exp (-verticalPoint gamma (2*π*(k/(2*π)))*(t : ℂ))) = F (verticalPoint gamma (2*π*(k/(2*π)))) at hv
  have hk : (2*π)*(k/(2*π)) = k := by field_simp
  rw [hk] at hv
  refine ⟨complex_laplace_integrable_of_damped (normalizedInverse F a) gamma k hDi, ?_⟩
  let f := fun t : ℝ => normalizedInverse F a t*Complex.exp (-verticalPoint gamma k*(t : ℂ))
  have hs : (Ioi (0 : ℝ)).indicator f = f := by
    funext t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · exact indicator_of_mem ht f
    · rw [indicator_of_notMem ht]
      have hz : normalizedInverse F a t = 0 := by
        unfold normalizedInverse
        rw [vertical_integral_eq_zero_of_nonpos F lower C hF hmajor hL1 a ha t (le_of_not_gt ht), mul_zero]
      simp only [f, hz, zero_mul]
  calc
    _ = ∫ t : ℝ, (Ioi (0 : ℝ)).indicator f t := (integral_indicator measurableSet_Ioi).symm
    _ = ∫ t : ℝ, f t := by rw [hs]
    _ = _ := hv

/-- The explicit causal exponential restores the leading kernel term.
Its value at zero is included, matching a continuous half-line solution. -/
def causalExponential (v : ℂ) (b t : ℝ) : ℂ :=
  (Ici (0 : ℝ)).indicator (fun t : ℝ => v*Complex.exp (-(b : ℂ)*(t : ℂ))) t

/-- The normalized causal inverse with its explicit leading term restored. -/
def restoredInverse (F : ℂ → ℂ) (v : ℂ) (b a t : ℝ) : ℂ :=
  causalExponential v b t+normalizedInverse F a t

/-- Actual whole-time integrability and the positive-axis transform of the
restored exponential are proved before using its rational transform. -/
theorem causal_exponential_laplace (v : ℂ) (b : ℝ) (s : ℂ) (hs : 0 < s.re+b) :
    Integrable (fun t : ℝ => causalExponential v b t*Complex.exp (-s*(t : ℂ))) ∧
      (∫ t in Ioi (0 : ℝ), causalExponential v b t*Complex.exp (-s*(t : ℂ))) = v/(s+(b : ℂ)) := by
  have hneg : (-(s+(b : ℂ))).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
    linarith
  have hbase : IntegrableOn (fun t : ℝ => v*Complex.exp (-(s+(b : ℂ))*(t : ℂ))) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hneg 0).const_mul v
  have hici : IntegrableOn (fun t : ℝ => v*Complex.exp (-(s+(b : ℂ))*(t : ℂ))) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hbase
  have hi := hici.integrable_indicator measurableSet_Ici
  have he (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
      causalExponential v b t*Complex.exp (-s*(t : ℂ)) = v*Complex.exp (-(s+(b : ℂ))*(t : ℂ)) := by
    unfold causalExponential
    rw [indicator_of_mem ht, mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hall : (fun t : ℝ => causalExponential v b t*Complex.exp (-s*(t : ℂ))) =
      (Ici (0 : ℝ)).indicator (fun t : ℝ => v*Complex.exp (-(s+(b : ℂ))*(t : ℂ))) := by
    funext t
    by_cases ht : t ∈ Ici (0 : ℝ)
    · rw [indicator_of_mem ht]
      exact he t ht
    · simp only [causalExponential, indicator_of_notMem ht, zero_mul]
  refine ⟨by rw [hall]; exact hi, ?_⟩
  calc
    _ = ∫ t in Ioi (0 : ℝ), v*Complex.exp (-(s+(b : ℂ))*(t : ℂ)) :=
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => he t (by
        change (0 : ℝ) ≤ t
        exact (show (0 : ℝ) < t from ht).le))
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_complex_Ioi hneg 0]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq]
      ring

/-- The restored leading term is continuous on the closed causal half-line. -/
theorem causal_exponential_continuousOn (v : ℂ) (b : ℝ) :
    ContinuousOn (causalExponential v b) (Ici (0 : ℝ)) := by
  have hc : ContinuousOn (fun t : ℝ => v*Complex.exp (-(b : ℂ)*(t : ℂ))) (Ici 0) := by fun_prop
  exact hc.congr (fun t ht => by simp only [causalExponential, indicator_of_mem ht])

/-- Honest Laplace transform of the restored causal inverse, with both
summands absolutely integrable before the sum is split. -/
theorem restored_inverse_laplace
    (F : ℂ → ℂ) (lower C : ℝ) (hF : AnalyticOnNhd ℂ F {s : ℂ | lower < s.re})
    (hmajor : ∀ a : ℝ, lower ≤ a → ∀ k : ℝ, (1+k^2)*‖F (verticalPoint a k)‖ ≤ C)
    (hL1 : ∀ a : ℝ, lower ≤ a → Integrable (fun k : ℝ => F (verticalPoint a k)))
    (v : ℂ) (b a : ℝ) (ha : lower < a) (gamma : ℝ) (hg : a < gamma)
    (hgb : 0 < gamma+b) (k : ℝ) :
    Integrable (fun t : ℝ => restoredInverse F v b a t*Complex.exp (-verticalPoint gamma k*(t : ℂ))) ∧
      (∫ t in Ioi (0 : ℝ), restoredInverse F v b a t*Complex.exp (-verticalPoint gamma k*(t : ℂ))) =
        F (verticalPoint gamma k)+v/(verticalPoint gamma k+(b : ℂ)) := by
  obtain ⟨hl, he⟩ := causal_exponential_laplace v b (verticalPoint gamma k) (by simpa [verticalPoint] using hgb)
  obtain ⟨hi, hv⟩ := normalized_inverse_laplace F lower C hF hmajor hL1 a ha gamma hg k
  have hsum : (fun t : ℝ => restoredInverse F v b a t*Complex.exp (-verticalPoint gamma k*(t : ℂ))) =
      fun t : ℝ => causalExponential v b t*Complex.exp (-verticalPoint gamma k*(t : ℂ))+
        normalizedInverse F a t*Complex.exp (-verticalPoint gamma k*(t : ℂ)) := by
    funext t
    exact add_mul _ _ _
  refine ⟨by rw [hsum]; exact hl.add hi, ?_⟩
  rw [hsum, integral_add hl.integrableOn hi.integrableOn, he, hv]
  exact add_comm _ _

/-- Restored inversion is continuous on the causal half-line and has the
true leading value at the origin; negative times vanish exactly. -/
theorem restored_inverse_causal_data
    (F : ℂ → ℂ) (lower C : ℝ) (hF : AnalyticOnNhd ℂ F {s : ℂ | lower < s.re})
    (hmajor : ∀ a : ℝ, lower ≤ a → ∀ k : ℝ, (1+k^2)*‖F (verticalPoint a k)‖ ≤ C)
    (hL1 : ∀ a : ℝ, lower ≤ a → Integrable (fun k : ℝ => F (verticalPoint a k)))
    (v : ℂ) (b a : ℝ) (ha : lower < a) :
    ContinuousOn (restoredInverse F v b a) (Ici (0 : ℝ)) ∧
      restoredInverse F v b a 0 = v ∧ ∀ t : ℝ, t < 0 → restoredInverse F v b a t = 0 := by
  have hc : Continuous (normalizedInverse F a) := by
    change Continuous (fun t : ℝ => fourierScale*verticalIntegral F a t)
    exact continuous_const.mul (vertical_integral_continuous F a (hL1 a ha.le))
  have hn (t : ℝ) (ht : t ≤ 0) : normalizedInverse F a t = 0 := by
    unfold normalizedInverse
    rw [vertical_integral_eq_zero_of_nonpos F lower C hF hmajor hL1 a ha t ht, mul_zero]
  refine ⟨(causal_exponential_continuousOn v b).add hc.continuousOn, ?_, ?_⟩
  · simp only [restoredInverse, hn 0 le_rfl, add_zero, causalExponential,
      indicator_of_mem (show (0 : ℝ) ∈ Ici 0 from by simp), Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, mul_one]
  · intro t ht
    simp only [restoredInverse, hn t ht.le, add_zero, causalExponential,
      indicator_of_notMem (show t ∉ Ici (0 : ℝ) from not_le.mpr ht)]

/-- The normalized restored field inherits a genuine exponential envelope,
including its exact leading time coefficient, on the causal half-line. -/
theorem restored_inverse_norm_bound
    (F : ℂ → ℂ) (lower C : ℝ)
    (hmajor : ∀ a : ℝ, lower ≤ a → ∀ k : ℝ, (1+k^2)*‖F (verticalPoint a k)‖ ≤ C)
    (hL1 : ∀ a : ℝ, lower ≤ a → Integrable (fun k : ℝ => F (verticalPoint a k)))
    (v : ℂ) (b a : ℝ) (ha : lower ≤ a) (hb : -b ≤ a) (t : ℝ) (ht : 0 ≤ t) :
    ‖restoredInverse F v b a t‖ ≤ (‖v‖+‖fourierScale‖*C*π)*exp (a*t) := by
  have hl : ‖causalExponential v b t‖ = ‖v‖*exp (-b*t) := by
    simp only [causalExponential, indicator_of_mem (show t ∈ Ici (0 : ℝ) from ht), norm_mul]
    congr 1
    simp [Complex.norm_exp, Complex.mul_re]
  have hi : ‖normalizedInverse F a t‖ ≤ ‖fourierScale‖*(exp (a*t)*C*π) := by
    unfold normalizedInverse
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (vertical_integral_integrable_bound F lower C hmajor hL1 a ha t).2 (norm_nonneg _)
  have he : exp (-b*t) ≤ exp (a*t) := exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb ht)
  calc
    _ ≤ ‖causalExponential v b t‖+‖normalizedInverse F a t‖ := norm_add_le _ _
    _ ≤ ‖v‖*exp (-b*t)+‖fourierScale‖*(exp (a*t)*C*π) := by rw [hl]; exact add_le_add le_rfl hi
    _ ≤ ‖v‖*exp (a*t)+‖fourierScale‖*(exp (a*t)*C*π) :=
      add_le_add (mul_le_mul_of_nonneg_left he (norm_nonneg _)) le_rfl
    _ = _ := by ring

/-- An actual canonical MSA kernel has an explicitly constructed causal,
exponentially decaying half-line inverse field. Its genuine Laplace transform
is the actual finite inverse minus I, throughout a negative half-plane,
including the Fourier axis and frequency zero. Identification with the
pre-existing Volterra/RDF constructors is not assumed here. -/
theorem actual_canonical_resolvent_field
    {N : ℕ} {T : Type*} [Fintype T]
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (p : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∃ delta b B : ℝ, 0 < delta ∧ (∀ u, delta < z u) ∧ delta < b ∧ 0 ≤ B ∧
      ∀ i j : Fin N,
        let F := fun s : ℂ => regularizedResolvent (nonlinearCausalKernel z rho sigma p.1 p.2) b s i j
        let r := restoredInverse F (nonlinearCausalKernel z rho sigma p.1 p.2 0 i j : ℂ) b (-delta/2)
        ContinuousOn r (Ici (0 : ℝ)) ∧ r 0 = (nonlinearCausalKernel z rho sigma p.1 p.2 0 i j : ℂ) ∧
        (∀ t : ℝ, t < 0 → r t = 0) ∧ Integrable r ∧
        (∀ t : ℝ, 0 ≤ t → ‖r t‖ ≤ B*exp ((-delta/2)*t)) ∧
        ∀ s : ℂ, -delta/2 < s.re →
          Integrable (fun t : ℝ => r t*Complex.exp (-s*(t : ℂ))) ∧
          (∫ t in Ioi (0 : ℝ), r t*Complex.exp (-s*(t : ℂ))) =
            ((1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹-1) i j := by
  obtain ⟨delta, b, _R, _B, C, hd, hdr, hb, _hR, _hB, hC, hAn, _hcont, _hfreq, hlines⟩ :=
    actual_canonical_regularized_resolvent_analysis z hz rho sigma hsigma p hcanon
  let q := nonlinearCausalKernel z rho sigma p.1 p.2
  let A := FMSA.matrixAbsSum (q 0)
  let D := ‖fourierScale‖*C*π
  have hA : 0 ≤ A := FMSA.matrixAbsSum_nonneg _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨delta, b, A+D, hd, hdr, hb, add_nonneg hA hD, ?_⟩
  intro i j
  let F := fun s : ℂ => regularizedResolvent q b s i j
  let v : ℂ := q 0 i j
  let a := -delta/2
  have ha : -delta < a := by dsimp [a]; linarith
  have hmajor (x : ℝ) (hx : -delta ≤ x) (k : ℝ) : (1+k^2)*‖F (verticalPoint x k)‖ ≤ C :=
    (mul_le_mul_of_nonneg_left (complexNormSum_entry_le _ i j) (by positivity)).trans ((hlines x hx).1 k)
  have hL1 (x : ℝ) (hx : -delta ≤ x) : Integrable (fun k : ℝ => F (verticalPoint x k)) :=
    ((hlines x hx).2.2 i j).1
  obtain ⟨hc, h0, hn⟩ := restored_inverse_causal_data F (-delta) C (hAn i j) hmajor hL1 v b a ha
  refine ⟨hc, h0, hn, ?_, ?_, ?_⟩
  · have hi := (restored_inverse_laplace F (-delta) C (hAn i j) hmajor hL1 v b a ha 0
      (by dsimp [a]; linarith) (by linarith) 0).1
    simpa only [verticalPoint, Complex.ofReal_zero, zero_mul, zero_add, neg_zero, Complex.exp_zero, mul_one] using hi
  · intro t ht
    have hv : ‖v‖ ≤ A := by
      simpa only [v, Complex.norm_real, Real.norm_eq_abs] using FMSA.matrixAbsSum_entry_le (q 0) i j
    have he := restored_inverse_norm_bound F (-delta) C hmajor hL1 v b a ha.le
      (by dsimp [a]; linarith) t ht
    exact he.trans (mul_le_mul_of_nonneg_right (add_le_add hv le_rfl) (exp_pos _).le)
  · intro s hs
    have hgb : 0 < s.re+b := by linarith
    obtain ⟨hi, he⟩ := restored_inverse_laplace F (-delta) C (hAn i j) hmajor hL1 v b a ha s.re hs hgb s.im
    have hp : verticalPoint s.re s.im = s := by apply Complex.ext <;> simp [verticalPoint]
    rw [hp] at hi he
    refine ⟨hi, ?_⟩
    calc
      _ = F s+v/(s+(b : ℂ)) := he
      _ = _ := by simp only [F, v, regularizedResolvent, Matrix.sub_apply, Matrix.of_apply]; ring

end FMSA.Convergence.CanonicalFourierLaplace

/-- info: 'FMSA.Convergence.CanonicalFourierLaplace.vertical_integral_split_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFourierLaplace.vertical_integral_split_phase

/-- info: 'FMSA.Convergence.CanonicalFourierLaplace.scaled_symbol_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFourierLaplace.scaled_symbol_integrable

/-- info: 'FMSA.Convergence.CanonicalFourierLaplace.fourier_inversion_of_inverse_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFourierLaplace.fourier_inversion_of_inverse_integrable

/-- info: 'FMSA.Convergence.CanonicalFourierLaplace.scaled_symbol_fourierInv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFourierLaplace.scaled_symbol_fourierInv

/-- info: 'FMSA.Convergence.CanonicalFourierLaplace.shifted_fourierInv_eq_damped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFourierLaplace.shifted_fourierInv_eq_damped

/-- info: 'FMSA.Convergence.CanonicalFourierLaplace.normalized_inverse_damped_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFourierLaplace.normalized_inverse_damped_integrable

/-- info: 'FMSA.Convergence.CanonicalFourierLaplace.scaled_symbol_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFourierLaplace.scaled_symbol_continuous

/-- info: 'FMSA.Convergence.CanonicalFourierLaplace.damped_laplace_integrand_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFourierLaplace.damped_laplace_integrand_eq

/-- info: 'FMSA.Convergence.CanonicalFourierLaplace.complex_laplace_integrable_of_damped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFourierLaplace.complex_laplace_integrable_of_damped

/-- info: 'FMSA.Convergence.CanonicalFourierLaplace.fourier_damped_eq_laplace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFourierLaplace.fourier_damped_eq_laplace

/-- info: 'FMSA.Convergence.CanonicalFourierLaplace.normalized_inverse_laplace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFourierLaplace.normalized_inverse_laplace

/-- info: 'FMSA.Convergence.CanonicalFourierLaplace.causal_exponential_laplace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFourierLaplace.causal_exponential_laplace

/-- info: 'FMSA.Convergence.CanonicalFourierLaplace.causal_exponential_continuousOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFourierLaplace.causal_exponential_continuousOn

/-- info: 'FMSA.Convergence.CanonicalFourierLaplace.restored_inverse_laplace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFourierLaplace.restored_inverse_laplace

/-- info: 'FMSA.Convergence.CanonicalFourierLaplace.restored_inverse_causal_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFourierLaplace.restored_inverse_causal_data

/-- info: 'FMSA.Convergence.CanonicalFourierLaplace.restored_inverse_norm_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFourierLaplace.restored_inverse_norm_bound

/-- info: 'FMSA.Convergence.CanonicalFourierLaplace.actual_canonical_resolvent_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalFourierLaplace.actual_canonical_resolvent_field
