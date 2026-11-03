import MSAConvergence.ActualExcessTangentDecay

/-! Honest cancelled-source Laplace identities at the Fourier boundary.
The affine background is explicit algebra, not a separately asserted axis integral. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff

namespace FMSA.Convergence.ActualSourceBoundary
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open FMSA.Convergence.ComplexWronskianJets
open FMSA.Convergence.ActualRDFTangent FMSA.Convergence.RDFExponentialOrder
open FMSA.Convergence.ActualLaplaceJets FMSA.Convergence.CanonicalKernelEstimates
open FMSA.Convergence.CanonicalRenewalFormula FMSA.Convergence.ActualExcessDecay
open FMSA.Convergence.ActualExcessSourceTangent

variable {N : ℕ} {T : Type*} [Fintype T]

/-- Any genuine matrix exponential weight bound gives real damped entry
integrability, with no physical small-kernel-budget premise. -/
theorem weighted_matrix_real_damped_integrable
    (f : ℝ → Matrix (Fin N) (Fin N) ℝ) (hf : Continuous f) (delta B c : ℝ)
    (hb : ∀ t, 0 ≤ t → exp (delta*t)*FMSA.matrixAbsSum (f t) ≤ B)
    (hc : -delta < c) (i j : Fin N) : IntegrableOn (fun t : ℝ => exp (-c*t)*f t i j) (Ioi 0) := by
  apply entry_decay_weighted_integrable _ (hf.matrix_elem i j) delta B _ c hc
  intro t ht
  apply weighted_bound_to_decay
  exact (mul_le_mul_of_nonneg_left (FMSA.matrixAbsSum_entry_le (f t) i j) (exp_pos _).le).trans (hb t ht)

/-- Actual cancelled-source real weighted L1 at every nonnegative damping. -/
theorem actual_source_real_damped_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p : TailMatrix T N × TailMatrix T N) (c : ℝ) (hc : 0 ≤ c) (i j : Fin N) :
    IntegrableOn (fun t : ℝ => exp (-c*t)*nonlinearExcessSource z rho sigma p.1 p.2 t i j) (Ioi 0) := by
  obtain ⟨delta, hd, hdz⟩ := exists_positive_rate_margin z hz
  obtain ⟨B, _hB, hb⟩ := nonlinearExcessSource_weighted_bounded z rho sigma p.1 p.2 hz hsigma hv delta (fun u => (hdz u).le)
  exact weighted_matrix_real_damped_integrable _ (nonlinearExcessSource_continuous z rho sigma p.1 p.2)
    delta B c hb (by linarith) i j

/-- Genuine cancelled-source derivative real weighted L1 on the boundary. -/
theorem actual_source_variation_real_damped_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N) (c : ℝ) (hc : 0 ≤ c) (i j : Fin N) :
    IntegrableOn (fun t : ℝ => exp (-c*t)*excessSourceVariation z rho sigma p v i j t) (Ioi 0) := by
  obtain ⟨delta, hd, hdz⟩ := exists_positive_rate_margin z hz
  obtain ⟨B, _hB, hb⟩ := excess_source_variation_weighted_bounded z hz rho sigma hsigma hv p v delta (fun u => (hdz u).le)
  exact weighted_matrix_real_damped_integrable _
    (continuous_matrix (excess_source_variation_continuous z rho sigma p v)) delta B c hb (by linarith) i j

/-- Genuine kernel derivative real weighted L1 on the full closed right
half-plane, proved from its actual exponential tail. -/
theorem actual_kernel_variation_real_damped_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (c : ℝ) (hc : 0 ≤ c) (i j : Fin N) :
    IntegrableOn (fun t : ℝ => exp (-c*t)*kernelVariation z rho sigma p v i j t) (Ioi 0) := by
  obtain ⟨delta, hd, hdz⟩ := exists_positive_rate_margin z hz
  obtain ⟨B, _hB, hb⟩ := kernel_variation_weighted_bounded z rho sigma p v delta (fun u => (hdz u).le)
  exact weighted_matrix_real_damped_integrable _
    (continuous_matrix (kernel_variation_continuous z rho sigma p v)) delta B c hb (by linarith) i j

/-- Real actual kernel integrability includes the Fourier damping zero. -/
theorem actual_kernel_real_damped_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (c : ℝ) (hc : 0 ≤ c) (i j : Fin N) :
    IntegrableOn (fun t : ℝ => exp (-c*t)*nonlinearCausalKernel z rho sigma p.1 p.2 t i j) (Ioi 0) := by
  have h := (nonlinearRecenteredQ_weighted_integrable z rho sigma p.1 p.2 hsigma (-c)
    (fun u => by linarith [hz u]) i j).const_mul (rho i)
  change Integrable (fun t : ℝ => exp (-c*t)*nonlinearCausalKernel z rho sigma p.1 p.2 t i j) (volume.restrict (Ioi 0))
  simpa only [nonlinearCausalKernel, Matrix.of_apply, mul_assoc, mul_comm, mul_left_comm] using h

/-- An affine real envelope gives real weighted L1 at EVERY positive damping. -/
theorem real_affine_damped_integrable (f : ℝ → ℝ) (hf : Continuous f) (B c : ℝ)
    (hb : ∀ t, 0 ≤ t → |f t| ≤ B*(1+t)) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => exp (-c*t)*f t) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => B*(exp (-c*t)+t*exp (-c*t))) (Ioi 0) :=
    ((integrableOn_exp_mul_Ioi (by linarith : -c < 0) 0).add
      (FMSA.ExactMSA.integrableOn_Ioi_id_mul_exp_neg hc)).const_mul B
  apply hi.mono' ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hf).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖exp (-c*t)*f t‖ ≤ B*(exp (-c*t)+t*exp (-c*t))
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
  have h := mul_le_mul_of_nonneg_left (hb t ht.le) (exp_pos (-c*t)).le
  nlinarith

/-- The fixed amplitude-independent real affine background. -/
def affineBackground (sigma : Fin N → ℝ) (t : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => t+edgeHi sigma i j)

/-- Every background entry is truly real weighted L1 at positive damping. -/
theorem background_real_damped_integrable (sigma : Fin N → ℝ) (c : ℝ) (hc : 0 < c) (i j : Fin N) :
    IntegrableOn (fun t : ℝ => exp (-c*t)*affineBackground sigma t i j) (Ioi 0) := by
  apply real_affine_damped_integrable _ (by unfold affineBackground; fun_prop) (1+|edgeHi sigma i j|) c _ hc
  intro t ht
  change |t+edgeHi sigma i j| ≤ (1+|edgeHi sigma i j|)*(1+t)
  have h := abs_add_le t (edgeHi sigma i j)
  rw [abs_of_nonneg ht] at h
  nlinarith [abs_nonneg (edgeHi sigma i j)]

/-- The background transform is a genuine integral only at positive damping. -/
theorem background_laplace (sigma : Fin N → ℝ) (s : ℂ) (hs : 0 < s.re) :
    rdfMatrixLaplace (affineBackground sigma) s = nonlinearComplexBackground sigma s := by
  ext i j
  have hi := FMSA.complex_first_integrable hs
  have hc : IntegrableOn (fun t : ℝ => (edgeHi sigma i j : ℂ)*Complex.exp (-s*t)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hs) 0).const_mul _
  change (∫ t in Ioi (0 : ℝ), (affineBackground sigma t i j : ℂ)*Complex.exp (-s*t)) = _
  rw [show (fun t : ℝ => (affineBackground sigma t i j : ℂ)*Complex.exp (-s*t)) =
    fun t : ℝ => (t : ℂ)*Complex.exp (-s*t)+(edgeHi sigma i j : ℂ)*Complex.exp (-s*t) by
      funext t; simp only [affineBackground, Matrix.of_apply, Complex.ofReal_add]; ring,
    integral_add hi hc, FMSA.complex_first_Ioi hs, integral_const_mul,
    integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hs)]
  simp [nonlinearComplexBackground, div_eq_mul_inv]

/-- Correctly ordered affine-background-times-kernel convolution. -/
def backgroundConvolution (sigma : Fin N → ℝ) (q : ℝ → Matrix (Fin N) (Fin N) ℝ) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℝ := Matrix.of (fun i j =>
      ∑ m, causalIntervalConv (fun u => q u m j) (fun u => affineBackground sigma u i m) t)

/-- Its honest transform is Bhat*Qhat, whenever both actual inputs are
weighted L1. This theorem only assumes POSITIVE background damping. -/
theorem background_convolution_laplace (sigma : Fin N → ℝ)
    (q : ℝ → Matrix (Fin N) (Fin N) ℝ) (hq : Continuous q) (s : ℂ) (hs : 0 < s.re)
    (hiq : ∀ i j, IntegrableOn (fun t : ℝ => exp (-s.re*t)*q t i j) (Ioi 0)) :
    (∀ i j, IntegrableOn (fun t : ℝ => (backgroundConvolution sigma q t i j : ℂ)*Complex.exp (-s*t)) (Ioi 0)) ∧
    rdfMatrixLaplace (backgroundConvolution sigma q) s = nonlinearComplexBackground sigma s*rdfMatrixLaplace q s := by
  have hv (i j m : Fin N) := complexCausalLaplace_weighted_convolution (fun u => q u m j)
    (fun u => affineBackground sigma u i m) (hq.matrix_elem m j) (by unfold affineBackground; fun_prop) s (hiq m j)
    (background_real_damped_integrable sigma s.re hs i m)
  have he (i j : Fin N) : (fun t : ℝ => (backgroundConvolution sigma q t i j : ℂ)*Complex.exp (-s*t)) =
      fun t : ℝ => ∑ m, (causalIntervalConv (fun u => q u m j) (fun u => affineBackground sigma u i m) t : ℂ)*Complex.exp (-s*t) := by
    funext t
    simp only [backgroundConvolution, Matrix.of_apply, Complex.ofReal_sum, Finset.sum_mul]
  constructor
  · intro i j
    rw [he]
    exact integrable_finsetSum _ (fun m _ => (hv i j m).1)
  · rw [← background_laplace sigma s hs]
    ext i j
    change (∫ t in Ioi (0 : ℝ), (backgroundConvolution sigma q t i j : ℂ)*Complex.exp (-s*t)) = _
    rw [he, integral_finsetSum _ (fun m _ => (hv i j m).1)]
    change _ = ∑ m, rdfMatrixLaplace (affineBackground sigma) s i m*rdfMatrixLaplace q s m j
    exact Finset.sum_congr rfl (fun m _ => (hv i j m).2)

/-- The actual source definition has the explicit cancelled background
convolution, with its genuine row density placed inside the actual q. -/
theorem actual_source_background_identity (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (t : ℝ) :
    nonlinearExcessSource z rho sigma p.1 p.2 t = nonlinearGSource z rho sigma p.1 p.2 t-
      affineBackground sigma t+backgroundConvolution sigma (nonlinearCausalKernel z rho sigma p.1 p.2) t := by
  ext i j
  simp only [nonlinearExcessSource, affineBackground, backgroundConvolution, nonlinearCausalKernel,
    Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply, causalIntervalConv]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _hu
  ring

/-- Actual cancelled source transform at positive damping, before taking
any boundary value. Every affine/background integral here is genuinely L1. -/
theorem actual_source_laplace_positive (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) (hs : 0 < s.re) :
    rdfMatrixLaplace (nonlinearExcessSource z rho sigma p.1 p.2) s =
      (2*(π : ℂ))⁻¹ • nonlinearComplexJ z rho sigma p.1 p.2 s-nonlinearComplexBackground sigma s+
        nonlinearComplexBackground sigma s*rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s := by
  obtain ⟨hconv, hconvL⟩ := background_convolution_laplace sigma _
    (nonlinearCausalKernel_continuous z rho sigma p.1 p.2) s hs
    (actual_kernel_real_damped_integrable z hz rho sigma hsigma p s.re hs.le)
  have hback := background_laplace sigma s hs
  ext i j
  have hf := FMSA.complex_laplace_integrable _
    ((nonlinearGSource_continuous z rho sigma p.1 p.2).matrix_elem i j).continuousOn s
    (nonlinearGSource_laplace_integrable z rho sigma p.1 p.2 hz s.re hs i j)
  have hb := FMSA.complex_laplace_integrable _ (by unfold affineBackground; fun_prop) s
    (background_real_damped_integrable sigma s.re hs i j)
  have he : (fun t : ℝ => (nonlinearExcessSource z rho sigma p.1 p.2 t i j : ℂ)*Complex.exp (-s*t)) =
      fun t : ℝ => (nonlinearGSource z rho sigma p.1 p.2 t i j : ℂ)*Complex.exp (-s*t)-
        (affineBackground sigma t i j : ℂ)*Complex.exp (-s*t)+
        (backgroundConvolution sigma (nonlinearCausalKernel z rho sigma p.1 p.2) t i j : ℂ)*Complex.exp (-s*t) := by
    funext t
    rw [actual_source_background_identity]
    simp only [Matrix.add_apply, Matrix.sub_apply, Complex.ofReal_add, Complex.ofReal_sub, add_mul, sub_mul]
  change (∫ t in Ioi (0 : ℝ), (nonlinearExcessSource z rho sigma p.1 p.2 t i j : ℂ)*Complex.exp (-s*t)) = _
  have hsub : IntegrableOn (fun t : ℝ =>
      (nonlinearGSource z rho sigma p.1 p.2 t i j : ℂ)*Complex.exp (-s*t)-
      (affineBackground sigma t i j : ℂ)*Complex.exp (-s*t)) (Ioi 0) := hf.sub hb
  rw [he, integral_add hsub (hconv i j), integral_sub hf hb]
  change rdfMatrixLaplace (nonlinearGSource z rho sigma p.1 p.2) s i j-
    rdfMatrixLaplace (affineBackground sigma) s i j+
    rdfMatrixLaplace (backgroundConvolution sigma (nonlinearCausalKernel z rho sigma p.1 p.2)) s i j = _
  rw [hback, hconvL, nonlinearGSource_actual_complex_laplace z rho sigma p.1 p.2 hz s hs i j]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The actual uncancelled G-source derivative has a computed affine
bound; this is only used at strictly positive damping. -/
theorem source_variation_affine_bound (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (p v : TailMatrix T N × TailMatrix T N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, 0 ≤ t → ∀ i j, |sourceVariation z rho sigma p v i j t| ≤ B*(1+t) := by
  obtain ⟨B, hB, hb⟩ := sourceJet_affine_bound z hz rho sigma p v
  refine ⟨B, hB, ?_⟩
  intro t ht i j
  exact ((blockJet_entry_bound (nonlinearGSource z rho sigma p.1 p.2 t)
    (Matrix.of (fun i j => sourceVariation z rho sigma p v i j t)) i j).2).trans (hb t ht)

/-- Genuine finite J variation, defined by the existing amplitude Frechet derivative. -/
def jVariation (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexJ z rho sigma a.1 a.2 s i j) p v)

/-- The actual cancelled-source derivative transform at positive damping,
with an algebraically explicit affine background derivative contribution. -/
theorem actual_source_variation_laplace_positive (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (p v : TailMatrix T N × TailMatrix T N) (s : ℂ) (hs : 0 < s.re) :
    rdfMatrixLaplace (fun t => Matrix.of (fun i j => excessSourceVariation z rho sigma p v i j t)) s =
      (2*(π : ℂ))⁻¹ • jVariation z rho sigma p v s+nonlinearComplexBackground sigma s*
        rdfMatrixLaplace (fun t => Matrix.of (fun i j => kernelVariation z rho sigma p v i j t)) s := by
  obtain ⟨hconv, hconvL⟩ := background_convolution_laplace sigma
    (fun t => Matrix.of (fun i j => kernelVariation z rho sigma p v i j t))
    (continuous_matrix (kernel_variation_continuous z rho sigma p v)) s hs
    (actual_kernel_variation_real_damped_integrable z hz rho sigma p v s.re hs.le)
  obtain ⟨B, _hB, hb⟩ := source_variation_affine_bound z hz rho sigma p v
  ext i j
  have hf := affine_complex_laplace_integrable _ (sourceVariation_continuous z rho sigma p v i j) B
    (fun t ht => hb t ht i j) s hs
  have he : (fun t : ℝ => (excessSourceVariation z rho sigma p v i j t : ℂ)*Complex.exp (-s*t)) =
      fun t : ℝ => (sourceVariation z rho sigma p v i j t : ℂ)*Complex.exp (-s*t)+
        (backgroundConvolution sigma (fun u => Matrix.of (fun i j => kernelVariation z rho sigma p v i j u)) t i j : ℂ)*Complex.exp (-s*t) := by
    funext t
    simp only [excess_source_variation_eq_background, backgroundConvolution, affineBackground, Matrix.of_apply,
      Complex.ofReal_add, add_mul]
  change (∫ t in Ioi (0 : ℝ), (excessSourceVariation z rho sigma p v i j t : ℂ)*Complex.exp (-s*t)) = _
  rw [he, integral_add hf (hconv i j)]
  change rdfMatrixLaplace (fun t => Matrix.of (fun i j => sourceVariation z rho sigma p v i j t)) s i j+
    rdfMatrixLaplace (backgroundConvolution sigma (fun t => Matrix.of (fun i j => kernelVariation z rho sigma p v i j t))) s i j = _
  rw [hconvL, sourceVariation_laplace_eq_J_fderiv z hz rho sigma p v s hs i j]
  simp only [jVariation, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Fixed rational frequency dictionary for the actual J symbol. -/
def jBasis (z : T → ℝ) (b : BasisIndex T) (s : ℂ) : ℂ :=
  (basisA b : ℂ)/s^2+(basisQp b : ℂ)/s+
    (basisRate z b : ℂ)*(basisC b : ℂ)/(s+(basisRate z b : ℂ))

/-- Off-root actual J has a finite smooth-coefficient frequency dictionary. -/
theorem j_eq_basis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) (i j : Fin N) :
    nonlinearComplexJ z rho sigma p.1 p.2 s i j =
      ∑ b : BasisIndex T, (bhCoefficient z rho sigma p i j b : ℂ)*jBasis z b s := by
  simp [jBasis, nonlinearComplexJ, bhCoefficient, coefficient, basisRate, basisA, basisQp, basisC,
    Fintype.sum_sum_type, Fin.sum_univ_two]
  <;> simp only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]

/-- Genuine actual J variation with finite coefficient derivatives. -/
theorem j_variation_eq_basis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (s : ℂ) (i j : Fin N) :
    jVariation z rho sigma p v s i j = ∑ b : BasisIndex T,
      (fderiv ℝ (fun a => bhCoefficient z rho sigma a i j b) p v : ℂ)*jBasis z b s := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexJ z rho sigma a.1 a.2 s i j) =
      fun a => ∑ b : BasisIndex T, (bhCoefficient z rho sigma a i j b : ℂ)*jBasis z b s := by
    funext a
    exact j_eq_basis z rho sigma a s i j
  have hd (b : BasisIndex T) := (Complex.ofRealCLM.hasFDerivAt.comp p
    ((bhCoefficient_contDiff z rho sigma i j b).differentiable (by simp) p).hasFDerivAt).mul_const (jBasis z b s)
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ => hd b)
  change HasFDerivAt (fun a : TailMatrix T N × TailMatrix T N =>
    ∑ b : BasisIndex T, (bhCoefficient z rho sigma a i j b : ℂ)*jBasis z b s) _ p at hsum
  rw [jVariation, Matrix.of_apply, he, hsum.fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro b _
  simp [mul_comm]

/-- The genuine J variation is frequency-continuous at every nonzero
imaginary point; the finite coefficient derivative formula proves this. -/
theorem j_variation_continuousAt_axis (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (s : ℂ) (hs : s ≠ 0) (hsre : s.re = 0) :
    ContinuousAt (fun a : ℝ => jVariation z rho sigma p v ((a : ℂ)+s)) 0 := by
  have hbs (b : BasisIndex T) : s+(basisRate z b : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re, hsre, zero_add] at hre
    exact (FMSA.Convergence.RDFExponentialOrder.basisRate_pos z hz b).ne' hre
  have hphi (b : BasisIndex T) : ContinuousAt (fun a : ℝ => jBasis z b ((a : ℂ)+s)) 0 := by
    unfold jBasis
    fun_prop (disch := simp [hs, hbs b])
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  have he : (fun a : ℝ => jVariation z rho sigma p v ((a : ℂ)+s) i j) = fun a : ℝ =>
      ∑ b : BasisIndex T, (fderiv ℝ (fun p => bhCoefficient z rho sigma p i j b) p v : ℂ)*jBasis z b ((a : ℂ)+s) := by
    funext a
    exact j_variation_eq_basis z rho sigma p v ((a : ℂ)+s) i j
  rw [he]
  exact tendsto_finsetSum _ (fun b _ => continuousAt_const.mul (hphi b))

/-- Only the genuine L1 cancelled source is taken to the imaginary boundary. -/
theorem actual_source_laplace_continuousWithinAt_axis (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) (hsre : s.re = 0) :
    ContinuousWithinAt (fun a : ℝ => rdfMatrixLaplace (nonlinearExcessSource z rho sigma p.1 p.2) ((a : ℂ)+s)) (Ici 0) 0 := by
  apply continuousWithinAt_pi.mpr
  intro i
  apply continuousWithinAt_pi.mpr
  intro j
  have hi : IntegrableOn (fun t : ℝ => nonlinearExcessSource z rho sigma p.1 p.2 t i j) (Ioi 0) := by
    simpa only [neg_zero, zero_mul, exp_zero, one_mul] using
      actual_source_real_damped_integrable z hz rho sigma hsigma hv p 0 le_rfl i j
  exact FMSA.causalComplexLaplace_boundary _
    ((nonlinearExcessSource_continuous z rho sigma p.1 p.2).matrix_elem i j).continuousOn hi s hsre

/-- Boundary continuity of the actual cancelled-source Frechet tangent,
using its PROVED real L1, not boundary differentiation of an amplitude integral. -/
theorem actual_source_variation_laplace_continuousWithinAt_axis (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N) (s : ℂ) (hsre : s.re = 0) :
    ContinuousWithinAt (fun a : ℝ => rdfMatrixLaplace
      (fun t => Matrix.of (fun i j => excessSourceVariation z rho sigma p v i j t)) ((a : ℂ)+s)) (Ici 0) 0 := by
  apply continuousWithinAt_pi.mpr
  intro i
  apply continuousWithinAt_pi.mpr
  intro j
  have hi : IntegrableOn (excessSourceVariation z rho sigma p v i j) (Ioi 0) := by
    simpa only [neg_zero, zero_mul, exp_zero, one_mul] using
      actual_source_variation_real_damped_integrable z hz rho sigma hsigma hv p v 0 le_rfl i j
  exact FMSA.causalComplexLaplace_boundary _ (excess_source_variation_continuous z rho sigma p v i j).continuousOn hi s hsre

/-- Boundary continuity of the genuine actual kernel tangent integral. -/
theorem actual_kernel_variation_laplace_continuousWithinAt_axis (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (p v : TailMatrix T N × TailMatrix T N) (s : ℂ) (hsre : s.re = 0) :
    ContinuousWithinAt (fun a : ℝ => rdfMatrixLaplace
      (fun t => Matrix.of (fun i j => kernelVariation z rho sigma p v i j t)) ((a : ℂ)+s)) (Ici 0) 0 := by
  apply continuousWithinAt_pi.mpr
  intro i
  apply continuousWithinAt_pi.mpr
  intro j
  have hi : IntegrableOn (kernelVariation z rho sigma p v i j) (Ioi 0) := by
    simpa only [neg_zero, zero_mul, exp_zero, one_mul] using
      actual_kernel_variation_real_damped_integrable z hz rho sigma p v 0 le_rfl i j
  exact FMSA.causalComplexLaplace_boundary _ (kernel_variation_continuous z rho sigma p v i j).continuousOn hi s hsre

/-- Actual cancelled S has its honest finite J/background formula on
the entire closed right half-plane away from zero. Only S is an actual
axis integral; the background on that axis is explicit rational algebra. -/
theorem actual_source_laplace_closed_right (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) (hs : s ≠ 0) (hre : 0 ≤ s.re) :
    rdfMatrixLaplace (nonlinearExcessSource z rho sigma p.1 p.2) s =
      (2*(π : ℂ))⁻¹ • nonlinearComplexJ z rho sigma p.1 p.2 s-nonlinearComplexBackground sigma s+
        nonlinearComplexBackground sigma s*rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s := by
  rcases lt_or_eq_of_le hre with hp | hzre
  · exact actual_source_laplace_positive z hz rho sigma hsigma p s hp
  · have hsre : s.re = 0 := hzre.symm
    have hb := (nonlinearComplexBackground_continuousAt_axis sigma s hs).continuousWithinAt (s := Ici (0 : ℝ))
    have hj := ((nonlinearComplexJ_continuousAt_axis z rho sigma p.1 p.2 hz s hs hsre).continuousWithinAt (s := Ici (0 : ℝ))).const_smul (2*(π : ℂ))⁻¹
    have hq := nonlinearCausalKernel_complex_boundary z rho sigma p.1 p.2 hz hsigma s hsre
    have he := nonlinear_boundary_eq_of_positive_eq
      (fun a : ℝ => rdfMatrixLaplace (nonlinearExcessSource z rho sigma p.1 p.2) ((a : ℂ)+s))
      (fun a : ℝ => (2*(π : ℂ))⁻¹ • nonlinearComplexJ z rho sigma p.1 p.2 ((a : ℂ)+s)-
        nonlinearComplexBackground sigma ((a : ℂ)+s)+
          nonlinearComplexBackground sigma ((a : ℂ)+s)*rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) ((a : ℂ)+s))
      (actual_source_laplace_continuousWithinAt_axis z hz rho sigma hsigma hv p s hsre)
      ((hj.sub hb).add (hb.mul hq)) (fun a ha => actual_source_laplace_positive z hz rho sigma hsigma p _
        (by simpa [hsre] using ha))
    simpa only [Complex.ofReal_zero, zero_add] using he

/-- Actual cancelled-source Frechet tangent finite formula on the closed
right half-plane away from zero, with actual integrals and actual J
coefficient derivatives. No boundary amplitude-integral interchange. -/
theorem actual_source_variation_laplace_closed_right (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N) (s : ℂ) (hs : s ≠ 0) (hre : 0 ≤ s.re) :
    rdfMatrixLaplace (fun t => Matrix.of (fun i j => excessSourceVariation z rho sigma p v i j t)) s =
      (2*(π : ℂ))⁻¹ • jVariation z rho sigma p v s+nonlinearComplexBackground sigma s*
        rdfMatrixLaplace (fun t => Matrix.of (fun i j => kernelVariation z rho sigma p v i j t)) s := by
  rcases lt_or_eq_of_le hre with hp | hzre
  · exact actual_source_variation_laplace_positive z hz rho sigma p v s hp
  · have hsre : s.re = 0 := hzre.symm
    have hb := (nonlinearComplexBackground_continuousAt_axis sigma s hs).continuousWithinAt (s := Ici (0 : ℝ))
    have hj := ((j_variation_continuousAt_axis z hz rho sigma p v s hs hsre).continuousWithinAt (s := Ici (0 : ℝ))).const_smul (2*(π : ℂ))⁻¹
    have hq := actual_kernel_variation_laplace_continuousWithinAt_axis z hz rho sigma p v s hsre
    have he := nonlinear_boundary_eq_of_positive_eq
      (fun a : ℝ => rdfMatrixLaplace (fun t => Matrix.of (fun i j => excessSourceVariation z rho sigma p v i j t)) ((a : ℂ)+s))
      (fun a : ℝ => (2*(π : ℂ))⁻¹ • jVariation z rho sigma p v ((a : ℂ)+s)+
        nonlinearComplexBackground sigma ((a : ℂ)+s)*
          rdfMatrixLaplace (fun t => Matrix.of (fun i j => kernelVariation z rho sigma p v i j t)) ((a : ℂ)+s))
      (actual_source_variation_laplace_continuousWithinAt_axis z hz rho sigma hsigma hv p v s hsre)
      (hj.add (hb.mul hq)) (fun a ha => actual_source_variation_laplace_positive z hz rho sigma p v _
        (by simpa [hsre] using ha))
    simpa only [Complex.ofReal_zero, zero_add] using he

/-- Each fixed recentered kernel basis has a genuine exponential weight
bound, including its compact polynomial part. No amplitude is involved. -/
theorem kernel_basis_weighted_bound (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (sigma : Fin N → ℝ) (b : BasisIndex T) (i : Fin N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, 0 ≤ t →
      exp ((basisRate z b/2)*t)*|recenteredBasis z sigma b i t| ≤ B := by
  have hp := FMSA.Convergence.RDFExponentialOrder.basisRate_pos z hz b
  apply finite_exponential_tail_weighted_bound _ (recenteredBasis_continuous z sigma b i)
    (fun _ : Unit => basisRate z b)
    (fun _ : Unit => basisW b+basisC b*exp (basisRate z b*sigma i))
    (max 0 (sigma i)) (basisRate z b/2) (le_max_left _ _) (fun _ => by linarith)
  intro t ht
  have hti : sigma i ≤ t := (le_max_right 0 (sigma i)).trans ht
  have he : exp (-basisRate z b*(t-sigma i)) = exp (basisRate z b*sigma i)*exp (-basisRate z b*t) := by
    rw [← exp_add]
    congr 1
    ring
  simp only [Finset.univ_unique, Finset.sum_singleton, recenteredBasis, min_eq_right hti,
    max_eq_left hti, sub_self, mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add, he]
  ring

/-- Fixed actual kernel basis integrals are genuinely L1 even at zero
real damping. This permits actual amplitude differentiation on the axis. -/
theorem kernel_basis_laplace_closed_right (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (s : ℂ) (hs : 0 ≤ s.re) (b : BasisIndex T) (i : Fin N) :
    IntegrableOn (fun t : ℝ => ((rho i*recenteredBasis z sigma b i t : ℝ) : ℂ)*Complex.exp (-s*t)) (Ioi 0) := by
  obtain ⟨B, _hB, hb⟩ := kernel_basis_weighted_bound z hz sigma b i
  have hi := entry_decay_weighted_integrable _ (recenteredBasis_continuous z sigma b i)
    (basisRate z b/2) B (fun t ht => weighted_bound_to_decay _ _ _ _ (hb t ht)) s.re
    (by linarith [FMSA.Convergence.RDFExponentialOrder.basisRate_pos z hz b])
  have hreal : IntegrableOn (fun t : ℝ => exp (-s.re*t)*(rho i*recenteredBasis z sigma b i t)) (Ioi 0) := by
    change Integrable (fun t : ℝ => exp (-s.re*t)*(rho i*recenteredBasis z sigma b i t)) (volume.restrict (Ioi 0))
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hi.const_mul (rho i)
  exact FMSA.complex_laplace_integrable _ ((recenteredBasis_continuous z sigma b i).const_mul _).continuousOn s hreal

/-- The actual kernel's whole integral is genuinely amplitude C-infinity
at every fixed frequency in the closed right half-plane. Its fixed basis
has proved L1 there, independent of the amplitude coefficients. -/
theorem kernel_laplace_closed_right_contDiff (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (s : ℂ) (hs : 0 ≤ s.re) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N =>
      rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s i j) := by
  have he : (fun a : TailMatrix T N × TailMatrix T N =>
      rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s i j) =
      fun a => ∫ r in Ioi (0 : ℝ), ∑ b : BasisIndex T, (bhCoefficient z rho sigma a i j b : ℂ)*
        ((rho i*recenteredBasis z sigma b i r : ℝ)*Complex.exp (-s*r)) := by
    funext a
    exact kernel_laplace_basis z rho sigma a s i j
  rw [he]
  exact finite_complex_integral_contDiff _ _ (bhCoefficient_contDiff z rho sigma i j) _
    (fun b => kernel_basis_laplace_closed_right z hz rho sigma s hs b i)

/-- Genuine derivative/integral interchange for the actual kernel on the
closed right half-plane, including zero, is proved by its fixed L1 basis. -/
theorem kernel_variation_laplace_fderiv_closed_right (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (s : ℂ) (hs : 0 ≤ s.re) (i j : Fin N) :
    rdfMatrixLaplace (fun t => Matrix.of (fun i j => kernelVariation z rho sigma p v i j t)) s i j =
      fderiv ℝ (fun a => rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s i j) p v := by
  have he : (fun a : TailMatrix T N × TailMatrix T N =>
      rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s i j) =
      fun a => ∫ r in Ioi (0 : ℝ), ∑ b : BasisIndex T, (bhCoefficient z rho sigma a i j b : ℂ)*
        ((rho i*recenteredBasis z sigma b i r : ℝ)*Complex.exp (-s*r)) := by
    funext a
    exact kernel_laplace_basis z rho sigma a s i j
  rw [he, finite_complex_integral_fderiv _ _ (bhCoefficient_contDiff z rho sigma i j) _
    (fun b => kernel_basis_laplace_closed_right z hz rho sigma s hs b i) p v]
  unfold rdfMatrixLaplace FMSA.causalComplexLaplace
  simp only [Matrix.of_apply]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  dsimp only
  rw [kernelVariation_eq_basis z rho sigma p v i j t]
  simp only [Finset.mul_sum, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _hb
  ring

/-- The actual integrated kernel tangent has the finite genuine J/L
variation formula on the closed right half-plane away from zero. -/
theorem kernel_variation_rational_closed_right (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (s : ℂ) (hs : s ≠ 0) (hre : 0 ≤ s.re) (i j : Fin N) :
    s*rdfMatrixLaplace (fun t => Matrix.of (fun i j => kernelVariation z rho sigma p v i j t)) s i j =
      (rho i : ℂ)*(fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexL z rho sigma a.1 a.2 s i j) p v-
        Complex.exp (-s*(sigma i : ℂ))*jVariation z rho sigma p v s i j) := by
  have he : (fun a : TailMatrix T N × TailMatrix T N =>
      s*rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s i j) =
      fun a => (rho i : ℂ)*(nonlinearComplexL z rho sigma a.1 a.2 s i j-
        Complex.exp (-s*(sigma i : ℂ))*nonlinearComplexJ z rho sigma a.1 a.2 s i j) := by
    funext a
    exact kernel_rational_rate_domain z rho sigma hsigma a s hs (fun u => by linarith [hz u]) i j
  have hl := ((kernel_laplace_closed_right_contDiff z hz rho sigma s hre i j).differentiable (by simp) p).hasFDerivAt.const_mul s
  have hJ := ((complexJ_entry_contDiff z rho sigma s i j).differentiable (by simp) p).hasFDerivAt
  have hL := ((complexL_entry_contDiff z rho sigma s i j).differentiable (by simp) p).hasFDerivAt
  have hr := (hL.fun_sub (hJ.const_mul (Complex.exp (-s*(sigma i : ℂ))))).const_mul (rho i : ℂ)
  have hd := congrArg (fun L : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℂ => L v)
    ((congrArg (fun f : (TailMatrix T N × TailMatrix T N) → ℂ => fderiv ℝ f p) he).trans hr.fderiv)
  rw [hl.fderiv] at hd
  rw [kernel_variation_laplace_fderiv_closed_right z hz rho sigma p v s hre i j]
  simpa only [jVariation, Matrix.of_apply, smul_apply, smul_eq_mul, sub_apply] using hd

/-- Pure finite J/L formula for the actual causal-kernel transform. -/
def finiteKernelSymbol (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => (rho i : ℂ)*(nonlinearComplexL z rho sigma p.1 p.2 s i j-
    Complex.exp (-s*(sigma i : ℂ))*nonlinearComplexJ z rho sigma p.1 p.2 s i j)/s)

/-- Pure finite genuine J/L variation formula for the actual kernel tangent. -/
def finiteKernelVariationSymbol (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => (rho i : ℂ)*
    (fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexL z rho sigma a.1 a.2 s i j) p v-
      Complex.exp (-s*(sigma i : ℂ))*jVariation z rho sigma p v s i j)/s)

/-- The pure finite kernel symbol is the genuine actual integral on the
closed right half-plane away from zero. -/
theorem finite_kernel_symbol_eq_laplace (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) (hs : s ≠ 0) (hre : 0 ≤ s.re) :
    finiteKernelSymbol z rho sigma p s = rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s := by
  ext i j
  apply (div_eq_iff hs).mpr
  simpa only [mul_comm] using kernel_rational_rate_domain z rho sigma hsigma p s hs
    (fun u => by linarith [hz u]) i j |>.symm

/-- The pure finite kernel variation symbol is the actual integrated
Frechet kernel tangent, including the nonzero Fourier boundary. -/
theorem finite_kernel_variation_symbol_eq_laplace (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (s : ℂ) (hs : s ≠ 0) (hre : 0 ≤ s.re) :
    finiteKernelVariationSymbol z rho sigma p v s =
      rdfMatrixLaplace (fun t => Matrix.of (fun i j => kernelVariation z rho sigma p v i j t)) s := by
  ext i j
  apply (div_eq_iff hs).mpr
  simpa only [mul_comm] using (kernel_variation_rational_closed_right z hz rho sigma hsigma p v s hs hre i j).symm

end FMSA.Convergence.ActualSourceBoundary

/-- info: 'FMSA.Convergence.ActualSourceBoundary.weighted_matrix_real_damped_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.weighted_matrix_real_damped_integrable

/-- info: 'FMSA.Convergence.ActualSourceBoundary.actual_source_real_damped_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.actual_source_real_damped_integrable

/-- info: 'FMSA.Convergence.ActualSourceBoundary.actual_source_variation_real_damped_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.actual_source_variation_real_damped_integrable

/-- info: 'FMSA.Convergence.ActualSourceBoundary.actual_kernel_variation_real_damped_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.actual_kernel_variation_real_damped_integrable

/-- info: 'FMSA.Convergence.ActualSourceBoundary.actual_kernel_real_damped_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.actual_kernel_real_damped_integrable

/-- info: 'FMSA.Convergence.ActualSourceBoundary.real_affine_damped_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.real_affine_damped_integrable

/-- info: 'FMSA.Convergence.ActualSourceBoundary.background_real_damped_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.background_real_damped_integrable

/-- info: 'FMSA.Convergence.ActualSourceBoundary.background_laplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.background_laplace

/-- info: 'FMSA.Convergence.ActualSourceBoundary.background_convolution_laplace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.background_convolution_laplace

/-- info: 'FMSA.Convergence.ActualSourceBoundary.actual_source_background_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.actual_source_background_identity

/-- info: 'FMSA.Convergence.ActualSourceBoundary.actual_source_laplace_positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.actual_source_laplace_positive

/-- info: 'FMSA.Convergence.ActualSourceBoundary.source_variation_affine_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.source_variation_affine_bound

/-- info: 'FMSA.Convergence.ActualSourceBoundary.actual_source_variation_laplace_positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.actual_source_variation_laplace_positive

/-- info: 'FMSA.Convergence.ActualSourceBoundary.j_eq_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.j_eq_basis

/-- info: 'FMSA.Convergence.ActualSourceBoundary.j_variation_eq_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.j_variation_eq_basis

/-- info: 'FMSA.Convergence.ActualSourceBoundary.j_variation_continuousAt_axis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.j_variation_continuousAt_axis

/-- info: 'FMSA.Convergence.ActualSourceBoundary.actual_source_laplace_continuousWithinAt_axis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.actual_source_laplace_continuousWithinAt_axis

/-- info: 'FMSA.Convergence.ActualSourceBoundary.actual_source_variation_laplace_continuousWithinAt_axis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.actual_source_variation_laplace_continuousWithinAt_axis

/-- info: 'FMSA.Convergence.ActualSourceBoundary.actual_kernel_variation_laplace_continuousWithinAt_axis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.actual_kernel_variation_laplace_continuousWithinAt_axis

/-- info: 'FMSA.Convergence.ActualSourceBoundary.actual_source_laplace_closed_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.actual_source_laplace_closed_right

/-- info: 'FMSA.Convergence.ActualSourceBoundary.actual_source_variation_laplace_closed_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.actual_source_variation_laplace_closed_right

/-- info: 'FMSA.Convergence.ActualSourceBoundary.kernel_basis_weighted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.kernel_basis_weighted_bound

/-- info: 'FMSA.Convergence.ActualSourceBoundary.kernel_basis_laplace_closed_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.kernel_basis_laplace_closed_right

/-- info: 'FMSA.Convergence.ActualSourceBoundary.kernel_laplace_closed_right_contDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.kernel_laplace_closed_right_contDiff

/-- info: 'FMSA.Convergence.ActualSourceBoundary.kernel_variation_laplace_fderiv_closed_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.kernel_variation_laplace_fderiv_closed_right

/-- info: 'FMSA.Convergence.ActualSourceBoundary.kernel_variation_rational_closed_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.kernel_variation_rational_closed_right

/-- info: 'FMSA.Convergence.ActualSourceBoundary.finite_kernel_symbol_eq_laplace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.finite_kernel_symbol_eq_laplace

/-- info: 'FMSA.Convergence.ActualSourceBoundary.finite_kernel_variation_symbol_eq_laplace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualSourceBoundary.finite_kernel_variation_symbol_eq_laplace
