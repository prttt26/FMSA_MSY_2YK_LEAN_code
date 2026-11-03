import MSAConvergence.ComplexWronskianJets
import FMSAPaper.BaxterWeakJetBasis

/-! Actual arbitrary-amplitude primitive variations, their full-line Fourier
transforms, and kernel reciprocity. No PY-seed or root-curve specialization. -/
noncomputable section
open MeasureTheory Real Filter Topology Set
open scoped BigOperators ContDiff FourierTransform RealInnerProductSpace

namespace FMSA.Convergence.ActualPrimitiveTangent
open FMSA.Paper FMSA.Paper.BaxterWeakJetBasis FMSA.Paper.FiniteBasis
open FMSA.Paper.JacobianExterior FMSA.Convergence.ComplexWronskianJets
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint FMSA.MatrixQ0 MSAMixture
open FMSA.Paper.BaxterSecondDerivative

section General
variable {I : Type*} [Fintype I]

/-- Multiplying a real L1 basis function by a unit Fourier phase remains L1. -/
theorem real_basis_phase_integrable (b : ℝ → ℝ) (hb : Integrable b) (k : ℝ) :
    Integrable (fun r : ℝ => (b r : ℂ) * Complex.exp (-(Complex.I * k) * r)) := by
  have hm : Continuous (fun r : ℝ => Complex.exp (-(Complex.I * k) * r)) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  apply hb.ofReal.mul_bdd hm.aestronglyMeasurable (c := 1)
  exact Eventually.of_forall (fun r => by simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im])

/-- Fixed finite real dictionaries can be integrated against the complete
Fourier phase; no truncation of exponential tails is used. -/
theorem finite_real_basis_phase_integral (a : I → ℝ) (b : I → ℝ → ℝ)
    (hb : ∀ n, Integrable (b n)) (k : ℝ) :
    (∫ r : ℝ, ((∑ n, a n * b n r : ℝ) : ℂ) * Complex.exp (-(Complex.I * k) * r)) =
      ∑ n, (a n : ℂ) * ∫ r : ℝ, (b n r : ℂ) * Complex.exp (-(Complex.I * k) * r) := by
  have he : (fun r : ℝ => ((∑ n, a n * b n r : ℝ) : ℂ) * Complex.exp (-(Complex.I * k) * r)) =
      fun r => ∑ n, (a n : ℂ) * ((b n r : ℂ) * Complex.exp (-(Complex.I * k) * r)) := by
    funext r
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, mul_assoc]
  rw [he, integral_finsetSum _ (fun n _ => (real_basis_phase_integrable (b n) (hb n) k).const_mul (a n : ℂ))]
  simp only [integral_const_mul]
end General

variable {N : ℕ} {T : Type*} [Fintype T]

def primitiveVariation (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) : ℝ :=
  fderiv ℝ (fun a => actualPrimitive z rho sigma a i j r) p v

/-- The actual real primitive's amplitude derivative exists at every r. -/
theorem actualPrimitive_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i) (i j : Fin N) (r : ℝ) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => actualPrimitive z rho sigma a i j r) := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => actualPrimitive z rho sigma a i j r) =
      fun a => ∑ b : Index T N, coefficients z rho sigma a i j b * primitiveBasis z sigma i j b r := by
    funext a
    exact primitive_eq_linear z hz rho sigma hsigma a i j r
  rw [he]
  exact ContDiff.sum fun b _ => (coefficients_contDiff z rho sigma i j b).mul contDiff_const

/-- The arbitrary-amplitude genuine primitive derivative retains the complete
fixed integrable basis, including every quadratic cross-correlation. -/
theorem primitiveVariation_eq_basis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    primitiveVariation z rho sigma p v i j r =
      ∑ b : Index T N, fderiv ℝ (fun a => coefficients z rho sigma a i j b) p v *
        primitiveBasis z sigma i j b r := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => actualPrimitive z rho sigma a i j r) =
      fun a => ∑ b : Index T N, coefficients z rho sigma a i j b * primitiveBasis z sigma i j b r := by
    funext a
    exact primitive_eq_linear z hz rho sigma hsigma a i j r
  rw [primitiveVariation, he, fderiv_fun_sum (fun b _ =>
    ((coefficients_contDiff z rho sigma i j b).differentiable (by simp) p).mul_const _)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro b _
  rw [(((coefficients_contDiff z rho sigma i j b).differentiable (by simp) p).hasFDerivAt.mul_const
    (primitiveBasis z sigma i j b r)).fderiv]
  simp [mul_comm]

/-- The actual arbitrary-amplitude primitive variation is globally L1. -/
theorem primitiveVariation_integrable (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    Integrable (primitiveVariation z rho sigma p v i j) := by
  change Integrable (fun r => primitiveVariation z rho sigma p v i j r)
  simp_rw [primitiveVariation_eq_basis z rho sigma hz hsigma p v i j]
  exact integrable_finsetSum _ (fun b _ => (primitiveBasis_integrable z hz sigma hsigma i j b).const_mul _)

/-- The real dictionary primitive is exactly the existing full reflected
complex Baxter primitive; this equality is off-root. -/
theorem actualPrimitive_complex_eq (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    (actualPrimitive z rho sigma p i j r : ℂ) =
      baxterPrimitive z rho sigma (amplitudeA z rho sigma p.1 p.2)
        (amplitudeQp z rho sigma p.1 p.2) (W z rho p.1 p.2) (C z rho sigma p.1 p.2) i j r := by
  classical
  simp only [actualPrimitive, realPrimitive_eq_re, baxterPrimitive_eq_basis z hz rho sigma hsigma p i j r,
    Complex.ofReal_re]

/-- The full Fourier transform has a finite amplitude-coordinate expansion. -/
theorem actualPrimitive_fourier_basis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (k : ℝ) (i j : Fin N) :
    nonlinearActualFourierC z rho sigma p.1 p.2 k i j =
      ∑ b : Index T N, (coefficients z rho sigma p i j b : ℂ) *
        ∫ r : ℝ, (primitiveBasis z sigma i j b r : ℂ) * Complex.exp (-(Complex.I * k) * r) := by
  classical
  rw [nonlinearActualFourierC, Matrix.of_apply,
    ← baxterPrimitive_fourier z hz rho sigma (amplitudeA z rho sigma p.1 p.2)
      (amplitudeQp z rho sigma p.1 p.2) (W z rho p.1 p.2) (C z rho sigma p.1 p.2) hsigma k i j]
  simp_rw [← actualPrimitive_complex_eq z rho sigma hz hsigma p i j,
    primitive_eq_linear z hz rho sigma hsigma p i j]
  exact finite_real_basis_phase_integral (coefficients z rho sigma p i j) (primitiveBasis z sigma i j)
    (primitiveBasis_integrable z hz sigma hsigma i j) k

/-- The genuine spectral Baxter C family is amplitude-smooth at every real
frequency, including zero, by the complete integrable primitive dictionary. -/
theorem actualFourierC_all_frequency_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i) (k : ℝ) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierC z rho sigma a.1 a.2 k i j) := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierC z rho sigma a.1 a.2 k i j) =
      fun a => ∑ b : Index T N, (coefficients z rho sigma a i j b : ℂ) *
        ∫ r : ℝ, (primitiveBasis z sigma i j b r : ℂ) * Complex.exp (-(Complex.I * k) * r) := by
    funext a
    exact actualPrimitive_fourier_basis z rho sigma hz hsigma a k i j
  rw [he]
  exact ContDiff.sum fun b _ => (complex_ofReal_contDiff _ (coefficients_contDiff z rho sigma i j b)).mul contDiff_const

/-- Full-line Fourier integration commutes with the genuine arbitrary-amplitude
primitive derivative. All basis integrability is discharged internally. -/
theorem primitiveVariation_fourier (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (k : ℝ) (i j : Fin N) :
    (∫ r : ℝ, (primitiveVariation z rho sigma p v i j r : ℂ) * Complex.exp (-(Complex.I * k) * r)) =
      fderiv ℝ (fun a => nonlinearActualFourierC z rho sigma a.1 a.2 k i j) p v := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierC z rho sigma a.1 a.2 k i j) =
      fun a => ∑ b : Index T N, (coefficients z rho sigma a i j b : ℂ) *
        ∫ r : ℝ, (primitiveBasis z sigma i j b r : ℂ) * Complex.exp (-(Complex.I * k) * r) := by
    funext a
    exact actualPrimitive_fourier_basis z rho sigma hz hsigma a k i j
  have hc (b : Index T N) : HasFDerivAt
      (fun a : TailMatrix T N × TailMatrix T N => (coefficients z rho sigma a i j b : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun a => coefficients z rho sigma a i j b) p)) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p
      ((coefficients_contDiff z rho sigma i j b).differentiable (by simp) p).hasFDerivAt
  simp_rw [primitiveVariation_eq_basis z rho sigma hz hsigma p v i j]
  rw [finite_real_basis_phase_integral _ _ (primitiveBasis_integrable z hz sigma hsigma i j) k,
    he, fderiv_fun_sum (fun b _ => (hc b).differentiableAt.mul_const _)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro b _
  rw [((hc b).mul_const (∫ r : ℝ, (primitiveBasis z sigma i j b r : ℂ) * Complex.exp (-(Complex.I * k) * r))).fderiv]
  simp [mul_comm]

/-- The Fourier convention k=2*pi*w is retained exactly for the actual
primitive variation and the existing spectral Baxter C. -/
theorem primitiveVariation_fourier_transform (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (w : ℝ) (i j : Fin N) :
    𝓕 (fun r : ℝ => (primitiveVariation z rho sigma p v i j r : ℂ)) w =
      fderiv ℝ (fun a => nonlinearActualFourierC z rho sigma a.1 a.2 (2 * π * w) i j) p v := by
  have he : FMSA.MixtureBaxter.zOfW w = Complex.I * (2 * π * w : ℝ) := by
    unfold FMSA.MixtureBaxter.zOfW
    push_cast
    ring
  rw [FMSA.MixtureBaxter.fourier_eq_zOfW, he]
  simpa only [neg_mul] using primitiveVariation_fourier z rho sigma hz hsigma p v (2 * π * w) i j

/-- Each fixed primitive basis function is continuous away from the one
possible lower-edge jump. Quadratic correlations are continuous everywhere. -/
theorem primitiveBasis_continuousAt (z : T → ℝ) (sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (i j : Fin N) (b : Index T N) (r : ℝ) (hr : r ≠ edgeLo sigma i j) :
    ContinuousAt (primitiveBasis z sigma i j b) r := by
  rcases b with b | (b | ⟨l, b, c⟩)
  · exact basisQ_continuousAt_off_lower_edge z hz sigma hsigma b i j r hr
  · have hn : -r ≠ edgeLo sigma j i := by
      intro he
      apply hr
      unfold edgeLo at he ⊢
      linarith
    exact (basisQ_continuousAt_off_lower_edge z hz sigma hsigma b j i (-r) hn).comp continuousAt_id.neg
  · exact (basisQQ_continuous z hz sigma hsigma b c i j l).continuousAt

/-- Actual primitive variation is continuous off its fixed lower edge. -/
theorem primitiveVariation_continuousAt (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) (hr : r ≠ edgeLo sigma i j) :
    ContinuousAt (primitiveVariation z rho sigma p v i j) r := by
  change ContinuousAt (fun x => primitiveVariation z rho sigma p v i j x) r
  simp_rw [primitiveVariation_eq_basis z rho sigma hz hsigma p v i j]
  exact tendsto_finsetSum _ (fun b _ => continuousAt_const.mul
    (primitiveBasis_continuousAt z sigma hz hsigma i j b r hr))

/-- The complex actual variation is almost everywhere continuous, supplying
the exact regularity needed by the frozen Fourier injectivity theorem. -/
theorem primitiveVariation_ae_continuous (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    ∀ᵐ r, ContinuousAt (fun x : ℝ => (primitiveVariation z rho sigma p v i j x : ℂ)) r := by
  filter_upwards [volume.ae_ne (edgeLo sigma i j)] with r hr
  exact Complex.continuous_ofReal.continuousAt.comp
    (primitiveVariation_continuousAt z rho sigma hz hsigma p v i j r hr)

/-- Genuine arbitrary-root primitive tangent reciprocity follows from the
actual spectral C tangent symmetry and full-line L1 Fourier uniqueness.
No kernel vector is assumed to integrate to a curve of roots. -/
theorem actual_kernel_primitiveVariation_reciprocity
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (hz : ∀ u, 0 < z u)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hkern : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    primitiveVariation z rho sigma p v i j =ᵐ[volume] primitiveVariation z rho sigma p v j i := by
  let P := fun a b r => (primitiveVariation z rho sigma p v a b r : ℂ)
  have hi (a b : Fin N) : Integrable (P a b) :=
    (primitiveVariation_integrable z rho sigma hz hsigma p v a b).ofReal
  have hF (a b : Fin N) (w : ℝ) :
      𝓕 (P a b) w = fderiv ℝ (fun q => nonlinearActualFourierC z rho sigma q.1 q.2 (2 * π * w) a b) p v := by
    exact primitiveVariation_fourier_transform z rho sigma hz hsigma p v w a b
  have hneq (w : ℝ) (hw : w ≠ 0) : 𝓕 (P i j) w = 𝓕 (P j i) w := by
    rw [hF, hF]
    exact actual_kernel_fourierC_fderiv_symmetric z rho sigma K hK hz hsigma hv t p v hroot hkern
      (2 * π * w) (mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hw) i j
  have hcont (a b : Fin N) : Continuous (𝓕 (P a b)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ (hi a b)
  have hzero : 𝓕 (P i j) 0 = 𝓕 (P j i) 0 :=
    nonlinear_boundary_eq_of_positive_eq _ _ (hcont i j).continuousAt.continuousWithinAt
      (hcont j i).continuousAt.continuousWithinAt (fun w hw => hneq w hw.ne')
  have hc : P i j =ᵐ[volume] P j i := by
    apply ae_eq_of_fourier_eq (hi i j) (hi j i) _
      (primitiveVariation_ae_continuous z rho sigma hz hsigma p v i j)
      (primitiveVariation_ae_continuous z rho sigma hz hsigma p v j i)
    funext w
    by_cases hw : w = 0
    · rw [hw]
      exact hzero
    · exact hneq w hw
  filter_upwards [hc] with r hr
  exact Complex.ofReal_injective hr

/-- The primitive bridge extends actual spectral C tangent symmetry to the
zero frequency as well, without evaluating the rational source at its pole. -/
theorem actual_kernel_fourierC_fderiv_symmetric_all
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (hz : ∀ u, 0 < z u)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hkern : amplitudeJacobian z rho sigma K t p v = 0) (k : ℝ) (i j : Fin N) :
    fderiv ℝ (fun a => nonlinearActualFourierC z rho sigma a.1 a.2 k i j) p v =
      fderiv ℝ (fun a => nonlinearActualFourierC z rho sigma a.1 a.2 k j i) p v := by
  rw [← primitiveVariation_fourier z rho sigma hz hsigma p v k i j,
    ← primitiveVariation_fourier z rho sigma hz hsigma p v k j i]
  apply integral_congr_ae
  filter_upwards [actual_kernel_primitiveVariation_reciprocity z rho sigma K hK hz hsigma hv t p v hroot hkern i j]
    with r hr
  rw [hr]

/-- The real primitive variation is exactly the genuine derivative of the
existing full complex Baxter primitive, not a new surrogate field. -/
theorem primitiveVariation_complex_fderiv (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    fderiv ℝ (fun a => baxterPrimitive z rho sigma (amplitudeA z rho sigma a.1 a.2)
      (amplitudeQp z rho sigma a.1 a.2) (W z rho a.1 a.2) (C z rho sigma a.1 a.2) i j r) p v =
      (primitiveVariation z rho sigma p v i j r : ℂ) := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => baxterPrimitive z rho sigma
      (amplitudeA z rho sigma a.1 a.2) (amplitudeQp z rho sigma a.1 a.2)
      (W z rho a.1 a.2) (C z rho sigma a.1 a.2) i j r) =
      fun a => (actualPrimitive z rho sigma a i j r : ℂ) := by
    funext a
    exact (actualPrimitive_complex_eq z rho sigma hz hsigma a i j r).symm
  rw [he]
  exact congrArg (fun L : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℂ => L v)
    (Complex.ofRealCLM.hasFDerivAt.comp p
      ((actualPrimitive_contDiff z rho sigma hz hsigma i j r).differentiable (by simp) p).hasFDerivAt).fderiv

/-- The full actual primitive's transpose/reflection relation holds off-root. -/
theorem actualPrimitive_reflection (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    actualPrimitive z rho sigma p i j (-r) = actualPrimitive z rho sigma p j i r := by
  simp only [actualPrimitive, realPrimitive_eq_re, baxterPrimitive_reflection]

/-- Actual coefficient differentiation preserves the off-root reflection law. -/
theorem primitiveVariation_reflection (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) :
    primitiveVariation z rho sigma p v i j (-r) = primitiveVariation z rho sigma p v j i r := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => actualPrimitive z rho sigma a i j (-r)) =
      fun a => actualPrimitive z rho sigma a j i r := by
    funext a
    exact actualPrimitive_reflection z rho sigma a i j r
  rw [primitiveVariation, primitiveVariation, he]

/-- The actual kernel primitive tangent is a.e. even as well as reciprocal. -/
theorem actual_kernel_primitiveVariation_even
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (hz : ∀ u, 0 < z u)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hkern : amplitudeJacobian z rho sigma K t p v = 0) (i j : Fin N) :
    (fun r => primitiveVariation z rho sigma p v i j (-r)) =ᵐ[volume]
      primitiveVariation z rho sigma p v i j := by
  simp_rw [primitiveVariation_reflection]
  exact actual_kernel_primitiveVariation_reciprocity z rho sigma K hK hz hsigma hv t p v hroot hkern j i

end FMSA.Convergence.ActualPrimitiveTangent

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.real_basis_phase_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.real_basis_phase_integrable

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.finite_real_basis_phase_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.finite_real_basis_phase_integral

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.actualPrimitive_contDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.actualPrimitive_contDiff

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.primitiveVariation_eq_basis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.primitiveVariation_eq_basis

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.primitiveVariation_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.primitiveVariation_integrable

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.actualPrimitive_complex_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.actualPrimitive_complex_eq

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.actualPrimitive_fourier_basis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.actualPrimitive_fourier_basis

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.actualFourierC_all_frequency_contDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.actualFourierC_all_frequency_contDiff

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.primitiveVariation_fourier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.primitiveVariation_fourier

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.primitiveVariation_fourier_transform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.primitiveVariation_fourier_transform

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.primitiveBasis_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.primitiveBasis_continuousAt

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.primitiveVariation_continuousAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.primitiveVariation_continuousAt

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.primitiveVariation_ae_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.primitiveVariation_ae_continuous

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.actual_kernel_primitiveVariation_reciprocity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.actual_kernel_primitiveVariation_reciprocity

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.actual_kernel_fourierC_fderiv_symmetric_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.actual_kernel_fourierC_fderiv_symmetric_all

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.primitiveVariation_complex_fderiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.primitiveVariation_complex_fderiv

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.actualPrimitive_reflection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.actualPrimitive_reflection

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.primitiveVariation_reflection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.primitiveVariation_reflection

/-- info: 'FMSA.Convergence.ActualPrimitiveTangent.actual_kernel_primitiveVariation_even' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualPrimitiveTangent.actual_kernel_primitiveVariation_even
