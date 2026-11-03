import MSAConvergence.ActualBHAmplitudeRecovery
import MSAConvergence.PolynomialExponentialSeparation

/-! Actual J/L polynomial tangent separation and second BH amplitude
recovery. Coefficient derivatives are genuine and no root curve is used. -/
noncomputable section
open MeasureTheory Set Real Filter Topology Polynomial
open scoped BigOperators ContDiff
namespace FMSA.Convergence.ActualBHSecondAmplitudeRecovery
open FMSA.Paper FMSA.Paper.JacobianExterior FMSA.ExactMSA.MultiTailMixture
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open FMSA.Convergence.SymplecticTangent FMSA.Convergence.ActualCanonicalKernelTangent
open FMSA.Convergence.ActualBHAmplitudeRecovery FMSA.Convergence.ActualSourceBoundary
open FMSA.Convergence.PolynomialJets FMSA.Convergence.WronskianJets
open FMSA.Convergence.PolynomialExponentialSeparation

variable {N : ℕ} {T : Type*} [Fintype T]

/-- Honest real-axis restriction of the actual finite complex J symbol. -/
theorem complex_J_real_axis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (c : ℝ) (i j : Fin N) :
    nonlinearComplexJ z rho sigma p.1 p.2 (c : ℂ) i j =
      (nonlinearRationalJ z rho sigma p.1 p.2 c i j : ℂ) := by
  simp only [nonlinearComplexJ, nonlinearRationalJ, Matrix.of_apply]
  push_cast
  rfl

/-- Honest real-axis restriction of the actual finite complex L symbol. -/
theorem complex_L_real_axis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (c : ℝ) (i j : Fin N) :
    nonlinearComplexL z rho sigma p.1 p.2 (c : ℂ) i j =
      (nonlinearRationalL z rho sigma p.1 p.2 c i j : ℂ) := by
  simp only [nonlinearComplexL, nonlinearRationalL, Matrix.of_apply]
  push_cast
  rfl

/-- The actual finite real J entry is amplitude-smooth. -/
theorem rational_J_entry_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (c : ℝ) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => nonlinearRationalJ z rho sigma a.1 a.2 c i j) := by
  simp only [nonlinearRationalJ, Matrix.of_apply]
  fun_prop

/-- The actual finite real L entry is amplitude-smooth. -/
theorem rational_L_entry_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (c : ℝ) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => nonlinearRationalL z rho sigma a.1 a.2 c i j) := by
  simp only [nonlinearRationalL, nonlinearLowerQValue, Matrix.of_apply]
  fun_prop

/-- Scalar complexification commutes with genuine real Frechet derivatives. -/
theorem ofReal_fderiv {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (f : P → ℝ) (p v : P) (hf : DifferentiableAt ℝ f p) :
    fderiv ℝ (fun a => (f a : ℂ)) p v = (fderiv ℝ f p v : ℂ) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp p hf.hasFDerivAt
  change HasFDerivAt (fun a => (f a : ℂ)) _ p at hd
  rw [hd.fderiv]
  rfl

/-- Actual finite J derivative on the positive real axis is the complex
lift of the genuine real J derivative, without a new polynomial norm. -/
theorem complex_J_real_fderiv (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (c : ℝ) (i j : Fin N) :
    jVariation z rho sigma p v (c : ℂ) i j =
      (fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearRationalJ z rho sigma a.1 a.2 c i j) p v : ℂ) := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexJ z rho sigma a.1 a.2 (c : ℂ) i j) =
      fun a => (nonlinearRationalJ z rho sigma a.1 a.2 c i j : ℂ) :=
    funext (fun a => complex_J_real_axis z rho sigma a c i j)
  change fderiv ℝ _ p v = _
  rw [he]
  exact ofReal_fderiv _ p v ((rational_J_entry_contDiff z rho sigma c i j).differentiable (by simp) p)

/-- Actual finite L derivative real-axis dictionary. -/
theorem complex_L_real_fderiv (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (c : ℝ) (i j : Fin N) :
    fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexL z rho sigma a.1 a.2 (c : ℂ) i j) p v =
      (fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearRationalL z rho sigma a.1 a.2 c i j) p v : ℂ) := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexL z rho sigma a.1 a.2 (c : ℂ) i j) =
      fun a => (nonlinearRationalL z rho sigma a.1 a.2 c i j : ℂ) :=
    funext (fun a => complex_L_real_axis z rho sigma a c i j)
  rw [he]
  exact ofReal_fderiv _ p v ((rational_L_entry_contDiff z rho sigma c i j).differentiable (by simp) p)

/-- Genuine coefficientwise J numerator variation with its proved degree cutoff. -/
def jTangentPolynomial (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) : Polynomial ℝ :=
  variation ((nonlinearDistinctRates z).card+1)
    (fun a : TailMatrix T N × TailMatrix T N => nonlinearDistinctJNumerator z rho sigma a.1 a.2 i j) p v

/-- Genuine coefficientwise L numerator variation. -/
def lTangentPolynomial (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) : Polynomial ℝ :=
  variation ((nonlinearDistinctRates z).card+2)
    (fun a : TailMatrix T N × TailMatrix T N => nonlinearDistinctLNumerator z rho sigma a.1 a.2 i j) p v

/-- Actual derivative evaluation commutes with clearing the true finite
J denominator. Repeated rates are grouped, not assumed distinct. -/
theorem j_tangent_polynomial_eval
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (c : ℝ) (hc : 0 < c) :
    (jTangentPolynomial z rho sigma p v i j).eval c = (nonlinearDistinctDenominator z).eval c*
      fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearRationalJ z rho sigma a.1 a.2 c i j) p v := by
  classical
  rw [jTangentPolynomial, variation_eval_fderiv _ _ p v
    (fun a => nonlinearDistinctJNumerator_degree_le z rho sigma a.1 a.2 i j)
    (fun n _ => (actual_JNumerator_coeffSmooth z rho sigma i j n).differentiable (by simp) p)]
  have he : (fun a : TailMatrix T N × TailMatrix T N => (nonlinearDistinctJNumerator z rho sigma a.1 a.2 i j).eval c) =
      fun a => (nonlinearDistinctDenominator z).eval c*nonlinearRationalJ z rho sigma a.1 a.2 c i j :=
    funext (fun a => nonlinearDistinctJNumerator_eval z rho sigma a.1 a.2 c hc.ne' (fun u => (add_pos hc (hz u)).ne') i j)
  have hd := ((rational_J_entry_contDiff z rho sigma c i j).differentiable (by simp) p).hasFDerivAt.const_mul ((nonlinearDistinctDenominator z).eval c)
  change HasFDerivAt (fun a : TailMatrix T N × TailMatrix T N => (nonlinearDistinctDenominator z).eval c*nonlinearRationalJ z rho sigma a.1 a.2 c i j) _ p at hd
  rw [he, hd.fderiv]
  rfl

/-- Actual L numerator variation evaluation with the true common denominator. -/
theorem l_tangent_polynomial_eval
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (c : ℝ) (hc : 0 < c) :
    (lTangentPolynomial z rho sigma p v i j).eval c = (nonlinearDistinctDenominator z).eval c*
      fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearRationalL z rho sigma a.1 a.2 c i j) p v := by
  classical
  rw [lTangentPolynomial, variation_eval_fderiv _ _ p v
    (fun a => nonlinearDistinctLNumerator_degree_le z rho sigma a.1 a.2 i j)
    (fun n _ => (actual_LNumerator_coeffSmooth z rho sigma i j n).differentiable (by simp) p)]
  have he : (fun a : TailMatrix T N × TailMatrix T N => (nonlinearDistinctLNumerator z rho sigma a.1 a.2 i j).eval c) =
      fun a => (nonlinearDistinctDenominator z).eval c*nonlinearRationalL z rho sigma a.1 a.2 c i j :=
    funext (fun a => nonlinearDistinctLNumerator_eval z rho sigma a.1 a.2 c hc.ne' (fun u => (add_pos hc (hz u)).ne') i j)
  have hd := ((rational_L_entry_contDiff z rho sigma c i j).differentiable (by simp) p).hasFDerivAt.const_mul ((nonlinearDistinctDenominator z).eval c)
  change HasFDerivAt (fun a : TailMatrix T N × TailMatrix T N => (nonlinearDistinctDenominator z).eval c*nonlinearRationalL z rho sigma a.1 a.2 c i j) _ p at hd
  rw [he, hd.fderiv]
  rfl

/-- Actual weighted kernel variation zero implies the actual weighted
J/L derivative relation on every positive real frequency. -/
theorem actual_weighted_JL_real_relation
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (i j : Fin N) (c : ℝ) (hc : 0 < c) :
    rho i*rho j*fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearRationalL z rho sigma a.1 a.2 c i j) p v =
      exp (-sigma i*c)*(rho i*rho j*fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearRationalJ z rho sigma a.1 a.2 c i j) p v) := by
  have hzK := congrFun (congrFun (actual_weighted_kernel_laplace_zero z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon (c : ℂ) (by simpa using hc.le)) i) j
  simp only [Matrix.mul_diagonal, Matrix.zero_apply] at hzK
  have hrat := kernel_variation_rational_closed_right z hz rho sigma (fun i => (hsigma i).le) p v (c : ℂ)
    (Complex.ofReal_ne_zero.mpr hc.ne') (by simpa using hc.le) i j
  have hzero : (rho i : ℂ)*(fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexL z rho sigma a.1 a.2 (c : ℂ) i j) p v-
      Complex.exp (-(c : ℂ)*(sigma i : ℂ))*jVariation z rho sigma p v (c : ℂ) i j)*(rho j : ℂ) = 0 := by
    rw [← hrat]
    calc
      _ = (c : ℂ)*(rdfMatrixLaplace (kernelVariationField z rho sigma p v) (c : ℂ) i j*(rho j : ℂ)) := by
        change (c : ℂ)*rdfMatrixLaplace (kernelVariationField z rho sigma p v) (c : ℂ) i j*(rho j : ℂ) = _
        ring
      _ = 0 := by rw [hzK, mul_zero]
  rw [complex_L_real_fderiv, complex_J_real_fderiv] at hzero
  have he : Complex.exp (-(c : ℂ)*(sigma i : ℂ)) = (exp (-sigma i*c) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [he] at hzero
  have hzR : rho i*rho j*(fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearRationalL z rho sigma a.1 a.2 c i j) p v-
      exp (-sigma i*c)*fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearRationalJ z rho sigma a.1 a.2 c i j) p v) = 0 := by
    apply Complex.ofReal_eq_zero.mp
    simp only [Complex.ofReal_mul, Complex.ofReal_sub]
    linear_combination hzero
  linear_combination hzR

/-- Genuine weighted J/L tangent numerator polynomials both vanish,
by positive-diameter exponential separation, without a root curve. -/
theorem actual_weighted_JL_polynomials_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) (i j : Fin N) :
    Polynomial.C (rho i*rho j)*lTangentPolynomial z rho sigma p v i j = 0 ∧
    Polynomial.C (rho i*rho j)*jTangentPolynomial z rho sigma p v i j = 0 := by
  apply polynomial_exp_separation _ _ (sigma i) (hsigma i)
  intro c hc
  rw [Polynomial.eval_mul, Polynomial.eval_C, l_tangent_polynomial_eval z hz rho sigma p v i j c hc,
    Polynomial.eval_mul, Polynomial.eval_C, j_tangent_polynomial_eval z hz rho sigma p v i j c hc]
  have hr := actual_weighted_JL_real_relation z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon i j c hc
  linear_combination (nonlinearDistinctDenominator z).eval c*hr

/-- Actual weighted J symbol derivative vanishes at every positive
frequency, after clearing and then cancelling the honest nonzero denominator. -/
theorem actual_weighted_J_derivative_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) (c : ℝ) (hc : 0 < c) :
    Matrix.diagonal (fun i => (rho i : ℂ))*jVariation z rho sigma p v (c : ℂ)*
      Matrix.diagonal (fun i => (rho i : ℂ)) = 0 := by
  classical
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply]
  rw [complex_J_real_fderiv]
  have hj := (actual_weighted_JL_polynomials_zero z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon i j).2
  have he := congrArg (Polynomial.eval c) hj
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_zero] at he
  rw [j_tangent_polynomial_eval z hz rho sigma p v i j c hc] at he
  have hd := nonlinearDistinctDenominator_eval_ne_zero z c hc.ne' (fun u => (add_pos hc (hz u)).ne')
  have hzero : rho i*rho j*fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearRationalJ z rho sigma a.1 a.2 c i j) p v = 0 := by
    apply (mul_eq_zero.mp (show (rho i*rho j*fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => nonlinearRationalJ z rho sigma a.1 a.2 c i j) p v)*(nonlinearDistinctDenominator z).eval c = 0 by linear_combination he)).resolve_right hd
  have hzC := congrArg Complex.ofReal hzero
  push_cast at hzC
  linear_combination hzC


/-- The second actual amplitude coordinates in the original norm. -/
def gSymbol (p : TailMatrix T N × TailMatrix T N) (u : T) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => (p.2 u i j : ℂ))

/-- Genuine second-coordinate derivative. -/
theorem g_symbol_matrix_derivative (p v : TailMatrix T N × TailMatrix T N) (u : T) :
    matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => gSymbol a u) p v =
      Matrix.of (fun i j => (v.2 u i j : ℂ)) := by
  ext i j
  let L : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp ((entry u i j).comp (ContinuousLinearMap.snd ℝ _ _))
  have hL : HasFDerivAt (fun a : TailMatrix T N × TailMatrix T N => (a.2 u i j : ℂ)) L p := L.hasFDerivAt
  change fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => (a.2 u i j : ℂ)) p v = (v.2 u i j : ℂ)
  rw [hL.fderiv]
  rfl

/-- Actual second amplitude entries are differentiable without a norm change. -/
theorem g_symbol_entry_diff (p : TailMatrix T N × TailMatrix T N) (u : T) :
    EntryDiff (fun a : TailMatrix T N × TailMatrix T N => gSymbol a u) p := by
  intro i j
  let L : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp ((entry u i j).comp (ContinuousLinearMap.snd ℝ _ _))
  exact L.differentiableAt

/-- The actual finite real J source at z_u equals the actual second BH
right-hand side at ALL amplitudes; no root equation is assumed. -/
theorem rational_J_at_rate_eq_second_rhs
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (u : T) (i j : Fin N) :
    nonlinearRationalJ z rho sigma p.1 p.2 (z u) i j = secondRHS z rho sigma p.1 p.2 u i j := by
  simp only [nonlinearRationalJ, Matrix.of_apply, secondRHS]
  rw [add_div, add_div, Finset.sum_div]
  congr 1
  · field_simp [(hz u).ne']
  · apply Finset.sum_congr rfl
    intro w _
    field_simp [(hz u).ne', (add_pos (hz u) (hz w)).ne'] <;> ring

/-- ALL-AMPLITUDE second BH matrix residual identity. This is the identity
that is differentiated, rather than a root-only G moment formula. -/
theorem second_residual_matrix_identity
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (K : TailMatrix T N) (t : ℝ) (p : TailMatrix T N × TailMatrix T N) (u : T) :
    ((2*(π : ℂ)) • gSymbol p u)*(1-Matrix.diagonal (fun i => (rho i : ℂ))*rootTransformSymbol z rho sigma p u)-
      nonlinearComplexJ z rho sigma p.1 p.2 (z u : ℂ) =
        Matrix.of (fun i j => ((FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K (t, p)).2 u i j : ℂ)) := by
  have hM : Matrix.of (secondLHS z rho sigma p.1 p.2 u) =
      ((2*π : ℝ) • Matrix.of (p.2 u))*(1-Matrix.diagonal rho*nonlinearRootRecenteredTransform z rho sigma p.1 p.2 u) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [secondLHS, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.sub_apply,
      Matrix.one_apply, Matrix.diagonal_mul, nonlinearRootRecenteredTransform]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  ext i j
  simp only [Matrix.sub_apply, Matrix.of_apply]
  rw [complex_J_real_axis, rational_J_at_rate_eq_second_rhs z hz rho sigma p u i j]
  change (((2*(π : ℂ)) • gSymbol p u)*(1-Matrix.diagonal (fun i => (rho i : ℂ))*rootTransformSymbol z rho sigma p u)) i j-
    (secondRHS z rho sigma p.1 p.2 u i j : ℂ) =
      ((secondLHS z rho sigma p.1 p.2 u i j-secondRHS z rho sigma p.1 p.2 u i j : ℝ) : ℂ)
  rw [Complex.ofReal_sub]
  congr 1
  have he := congrFun (congrFun hM i) j
  simp only [Matrix.of_apply] at he
  rw [Matrix.mul_apply] at he ⊢
  simp only [Matrix.smul_apply, smul_eq_mul, gSymbol, rootTransformSymbol, Matrix.of_apply,
    Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_mul] at he ⊢
  have heC := congrArg Complex.ofReal he
  push_cast at heC ⊢
  simp only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero] at heC
  exact heC.symm

/-- Actual second residual coordinate derivatives vanish along every
true fixed-coupling Jacobian kernel vector, with no root curve. -/
theorem actual_second_residual_derivative_zero
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0) (u : T) :
    matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => Matrix.of (fun i j =>
      ((FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K (t, a)).2 u i j : ℂ))) p v = 0 := by
  ext i j
  let L : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp ((entry u i j).comp (ContinuousLinearMap.snd ℝ _ _))
  have hd := L.hasFDerivAt.comp p (residual_amplitudes_hasFDerivAt z rho sigma K t p)
  change HasFDerivAt (fun a : TailMatrix T N × TailMatrix T N =>
    ((FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K (t, a)).2 u i j : ℂ)) _ p at hd
  change fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N =>
    ((FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K (t, a)).2 u i j : ℂ)) p v = 0
  rw [hd.fderiv]
  change L (amplitudeJacobian z rho sigma K t p v) = 0
  rw [hjac, map_zero]

/-- Pure second-BH weighted recovery. Sylvester's finite determinant
identity transfers the canonical unit without any inverse density. -/
theorem second_BH_weighted_recovery
    (H Q dH dQ dJ R : Matrix (Fin N) (Fin N) ℂ)
    (hu : IsUnit (1-R*Q)) (hq : R*dQ*R = 0) (hj : R*dJ*R = 0)
    (hsecond : dH*(1-R*Q)-H*R*dQ-dJ = 0) : R*dH*R = 0 := by
  have huB : IsUnit (1-Q*R) := (Matrix.isUnit_iff_isUnit_det _).mpr (by
    rw [Matrix.det_one_sub_mul_comm Q R]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hu)
  have he : (R*dH*R)*(1-Q*R) = 0 := by
    calc
      _ = R*(dH*(1-R*Q)-H*R*dQ-dJ)*R+R*H*(R*dQ*R)+R*dJ*R := by noncomm_ring
      _ = 0 := by rw [hsecond, hq, hj]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  apply huB.mul_left_injective
  simpa only [Matrix.zero_mul] using he

/-- Actual second BH amplitude recovery on the full active pair block.
Both zero-density rows and columns are retained as weighted statements. -/
theorem actual_second_amplitude_weighted_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∀ u : T, Matrix.diagonal rho*Matrix.of (v.2 u)*Matrix.diagonal rho = 0 := by
  classical
  intro u
  let R := Matrix.diagonal (fun i => (rho i : ℂ))
  let Q := fun a : TailMatrix T N × TailMatrix T N => rootTransformSymbol z rho sigma a u
  let G := fun a : TailMatrix T N × TailMatrix T N => gSymbol a u
  let H := fun a => (2*(π : ℂ)) • G a
  let A := fun a => 1-R*Q a
  let Jf := fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexJ z rho sigma a.1 a.2 (z u : ℂ)
  have hQ : EntryDiff Q p := fun i j => (root_transform_entry_contDiff z rho sigma u i j).differentiable (by simp) p
  have hG : EntryDiff G p := g_symbol_entry_diff p u
  have hH : EntryDiff H p := entry_diff_smul _ _ p hG
  have hRQ := entry_diff_mul (fun _ => R) Q p (entry_diff_const R p) hQ
  have hA : EntryDiff A p := entry_diff_sub _ _ p (entry_diff_const _ p) hRQ
  have hJ : EntryDiff Jf p := fun i j =>
    (FMSA.Convergence.ComplexWronskianJets.complexJ_entry_contDiff z rho sigma (z u : ℂ) i j).differentiable (by simp) p
  have he : (fun a => H a*A a-Jf a) = fun a : TailMatrix T N × TailMatrix T N =>
      Matrix.of (fun i j => ((FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K (t, a)).2 u i j : ℂ)) :=
    funext (fun a => second_residual_matrix_identity z hz rho sigma K t a u)
  have hd := congrArg (fun FF => matrixDerivative FF p v) he
  rw [matrix_derivative_sub _ _ p v (entry_diff_mul _ _ p hH hA) hJ,
    matrix_derivative_mul _ _ p v hH hA,
    matrix_derivative_sub _ _ p v (entry_diff_const _ p) hRQ, matrix_derivative_const,
    matrix_derivative_const_mul R Q p v hQ, zero_sub,
    actual_second_residual_derivative_zero z rho sigma K t p v hjac u] at hd
  have hsecond : matrixDerivative H p v*(1-R*Q p)-H p*R*matrixDerivative Q p v-matrixDerivative Jf p v = 0 := by
    change (matrixDerivative H p v*A p+H p*(-(R*matrixDerivative Q p v)))-matrixDerivative Jf p v = 0 at hd
    dsimp only [A] at hd
    linear_combination (norm := noncomm_ring) hd
  have hq : R*matrixDerivative Q p v*R = 0 := by
    rw [← actual_kernel_variation_root_dictionary z hz rho sigma (fun i => (hsigma i).le) p v u]
    exact actual_weighted_kernel_laplace_zero z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon (z u : ℂ) (by simpa using (hz u).le)
  have hj : R*matrixDerivative Jf p v*R = 0 :=
    actual_weighted_J_derivative_zero z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon (z u) (hz u)
  have hu : IsUnit (1-R*Q p) := by
    rw [← actual_kernel_root_dictionary z hz rho sigma (fun i => (hsigma i).le) p u]
    exact hcanon _ (by simpa using (hz u).le)
  have hzH := second_BH_weighted_recovery (H p) (Q p) (matrixDerivative H p v) (matrixDerivative Q p v) (matrixDerivative Jf p v) R hu hq hj hsecond
  rw [matrix_derivative_smul _ _ p v hG, g_symbol_matrix_derivative] at hzH
  simp only [Matrix.mul_smul, Matrix.smul_mul] at hzH
  have htwo : (2*(π : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr pi_ne_zero)
  have hzG := (smul_eq_zero.mp hzH).resolve_left htwo
  ext i j
  have hei := congrFun (congrFun hzG i) j
  simp only [R, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply, Matrix.zero_apply] at hei ⊢
  exact_mod_cast hei

/-- Every active pair of the actual G amplitude kernel vector vanishes. -/
theorem actual_second_amplitude_active_pair_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∀ u i j, 0 < rho i → 0 < rho j → v.2 u i j = 0 := by
  intro u i j hi hj
  have he := congrFun (congrFun (actual_second_amplitude_weighted_zero z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon u) i) j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply, Matrix.zero_apply] at he
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hj.ne')).resolve_left hi.ne'

/-- Positive species densities recover the entire G amplitude component. -/
theorem actual_second_amplitude_zero_of_positive_densities
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) : v.2 = 0 := by
  funext u i j
  exact actual_second_amplitude_active_pair_zero z hz rho sigma hsigma (fun i => (hrho i).le) K hK t p v hv hroot hjac hcanon u i j (hrho i) (hrho j)

/-- Complete actual BH amplitude-kernel recovery at every canonical root
with strictly positive species densities. Tracer directions are NOT
inferred to vanish from this positive-density theorem. -/
theorem actual_amplitude_kernel_zero_of_positive_densities
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) : v = 0 := by
  apply Prod.ext
  · exact actual_first_amplitude_zero_of_positive_densities z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon
  · exact actual_second_amplitude_zero_of_positive_densities z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon

/-- Actual amplitude Jacobian injectivity at strictly positive-density
canonical roots, without a supplied Jacobian inverse or root curve. -/
theorem actual_amplitude_jacobian_injective_of_positive_densities
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    Function.Injective (amplitudeJacobian z rho sigma K t p) := by
  intro v w he
  have hzero : amplitudeJacobian z rho sigma K t p (v-w) = 0 := by rw [map_sub, he, sub_self]
  exact sub_eq_zero.mp (actual_amplitude_kernel_zero_of_positive_densities z hz rho sigma hsigma hrho K hK t p (v-w) hv hroot hzero hcanon)

/-- Finite-dimensional actual Jacobian bijectivity at strictly positive
canonical densities. This is pointwise regularity, not stable-domain
continuation or any real-root/Taylor equivalence. -/
theorem actual_amplitude_jacobian_bijective_of_positive_densities
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    Function.Bijective (amplitudeJacobian z rho sigma K t p) := by
  have hi := actual_amplitude_jacobian_injective_of_positive_densities z hz rho sigma hsigma hrho K hK t p hv hroot hcanon
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

/-- The genuine residual partial derivative is continuously invertible,
in exactly the interface consumed by the frozen local-branch theorem. -/
theorem actual_residual_partial_isInvertible_of_positive_densities
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ((fderiv ℝ (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K) (t, p)).comp
      (ContinuousLinearMap.inr ℝ ℝ (TailMatrix T N × TailMatrix T N))).IsInvertible := by
  let L := amplitudeJacobian z rho sigma K t p
  have hb : Function.Bijective L :=
    actual_amplitude_jacobian_bijective_of_positive_densities z hz rho sigma hsigma hrho K hK t p hv hroot hcanon
  have hk : L.ker = ⊥ := LinearMap.ker_eq_bot.mpr hb.1
  have hr : L.range = ⊤ := LinearMap.range_eq_top.mpr hb.2
  exact ⟨ContinuousLinearEquiv.ofBijective L hk hr,
    ContinuousLinearEquiv.coe_ofBijective L hk hr⟩

end FMSA.Convergence.ActualBHSecondAmplitudeRecovery

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.complex_J_real_axis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.complex_J_real_axis

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.complex_L_real_axis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.complex_L_real_axis

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.rational_J_entry_contDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.rational_J_entry_contDiff

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.rational_L_entry_contDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.rational_L_entry_contDiff

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.ofReal_fderiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.ofReal_fderiv

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.complex_J_real_fderiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.complex_J_real_fderiv

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.complex_L_real_fderiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.complex_L_real_fderiv

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.j_tangent_polynomial_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.j_tangent_polynomial_eval

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.l_tangent_polynomial_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.l_tangent_polynomial_eval

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_weighted_JL_real_relation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_weighted_JL_real_relation

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_weighted_JL_polynomials_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_weighted_JL_polynomials_zero

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_weighted_J_derivative_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_weighted_J_derivative_zero

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.g_symbol_matrix_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.g_symbol_matrix_derivative

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.g_symbol_entry_diff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.g_symbol_entry_diff

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.rational_J_at_rate_eq_second_rhs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.rational_J_at_rate_eq_second_rhs

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.second_residual_matrix_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.second_residual_matrix_identity

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_second_residual_derivative_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_second_residual_derivative_zero

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.second_BH_weighted_recovery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.second_BH_weighted_recovery

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_second_amplitude_weighted_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_second_amplitude_weighted_zero

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_second_amplitude_active_pair_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_second_amplitude_active_pair_zero

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_second_amplitude_zero_of_positive_densities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_second_amplitude_zero_of_positive_densities

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_amplitude_kernel_zero_of_positive_densities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_amplitude_kernel_zero_of_positive_densities

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_amplitude_jacobian_injective_of_positive_densities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_amplitude_jacobian_injective_of_positive_densities

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_amplitude_jacobian_bijective_of_positive_densities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_amplitude_jacobian_bijective_of_positive_densities

/-- info: 'FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_residual_partial_isInvertible_of_positive_densities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHSecondAmplitudeRecovery.actual_residual_partial_isInvertible_of_positive_densities
