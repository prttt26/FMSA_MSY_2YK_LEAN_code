import MSAConvergence.CanonicalKernelEstimates
import Mathlib.Analysis.Complex.RemovableSingularity

/-! Actual frequency holomorphy and integrable regularized resolvent symbols.
No time-domain decay or contour shift is assumed in this module. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff

namespace FMSA.Convergence.CanonicalResolventAnalysis
open FMSA.Paper FMSA.Convergence.ActualRDFTangent FMSA.Convergence.RDFExponentialOrder
open FMSA.Convergence.ActualLaplaceJets FMSA.Convergence.CanonicalKernelEstimates
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture

variable {N : ℕ} {T : Type*} [Fintype T]

/-- A convergent tail denominator cannot vanish. -/
theorem rate_shift_ne_zero (s : ℂ) (z : ℝ) (h : 0 < s.re+z) : s+(z : ℂ) ≠ 0 := by
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hr
  linarith

/-- The existing finite J formula is genuinely complex differentiable off
its displayed poles, with no parameter derivative substituted for frequency. -/
theorem complexJ_frequency_differentiableAt
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (p : TailMatrix T N × TailMatrix T N)
    (s : ℂ) (hs : s ≠ 0) (hrate : ∀ u, 0 < s.re+z u) (i j : Fin N) :
    DifferentiableAt ℂ (fun w : ℂ => nonlinearComplexJ z rho sigma p.1 p.2 w i j) s := by
  have hzs (u : T) := rate_shift_ne_zero s (z u) (hrate u)
  simp only [nonlinearComplexJ, Matrix.of_apply]
  fun_prop (disch := aesop)

/-- The existing finite L formula is genuinely complex differentiable off
its displayed poles. -/
theorem complexL_frequency_differentiableAt
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (p : TailMatrix T N × TailMatrix T N)
    (s : ℂ) (hs : s ≠ 0) (hrate : ∀ u, 0 < s.re+z u) (i j : Fin N) :
    DifferentiableAt ℂ (fun w : ℂ => nonlinearComplexL z rho sigma p.1 p.2 w i j) s := by
  have hzs (u : T) := rate_shift_ne_zero s (z u) (hrate u)
  simp only [nonlinearComplexL, Matrix.of_apply]
  fun_prop (disch := aesop)

/-- The actual integral kernel symbol is complex differentiable off zero
inside the convergent half-plane, by a neighbourhood identity of honest
integrals with the exact J/L formula. -/
theorem actual_kernel_frequency_differentiableAt_off_zero
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (delta : ℝ) (hdelta : ∀ u, delta < z u)
    (s : ℂ) (hsre : -delta < s.re) (hs : s ≠ 0) (i j : Fin N) :
    DifferentiableAt ℂ (fun w : ℂ => rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) w i j) s := by
  have hrate (u : T) : 0 < s.re+z u := by linarith [hdelta u]
  have hJ := complexJ_frequency_differentiableAt z rho sigma p s hs hrate i j
  have hL := complexL_frequency_differentiableAt z rho sigma p s hs hrate i j
  have hright : DifferentiableAt ℂ (fun w : ℂ => (rho i : ℂ)*
      (nonlinearComplexL z rho sigma p.1 p.2 w i j-
        Complex.exp (-w*(sigma i : ℂ))*nonlinearComplexJ z rho sigma p.1 p.2 w i j)/w) s := by
    fun_prop
  apply hright.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsre,
    isOpen_ne.mem_nhds hs] with w hw hw0
  apply (eq_div_iff hw0).mpr
  simpa only [mul_comm] using kernel_rational_rate_domain z rho sigma hsigma p w hw0
    (fun u => by linarith [hdelta u]) i j

/-- The actual kernel integral is holomorphic throughout an open half-plane
extending left of the Fourier axis. Its frequency origin is removed using
proved integral continuity, not by redefining a rational expression there. -/
theorem actual_kernel_entry_analyticOnNhd
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (delta : ℝ) (hd : 0 < delta)
    (hdelta : ∀ u, delta < z u) (i j : Fin N) :
    AnalyticOnNhd ℂ (fun s : ℂ => rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j)
      {s : ℂ | -delta < s.re} := by
  let H := {s : ℂ | -delta < s.re}
  have hO : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hzero : H ∈ 𝓝 (0 : ℂ) := hO.mem_nhds (by change -delta < (0 : ℂ).re; simpa using hd)
  have hclosed : {s : ℂ | -delta ≤ s.re} ∈ 𝓝 (0 : ℂ) :=
    mem_of_superset hzero (fun s hs => by
      change -delta ≤ s.re
      change -delta < s.re at hs
      exact hs.le)
  have hc := (kernel_laplace_entry_continuous_halfplane z rho sigma hsigma p delta hdelta i j).continuousAt hclosed
  have hoff : DifferentiableOn ℂ (fun s : ℂ => rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s i j)
      (H \ {0}) := by
    intro s hs
    exact (actual_kernel_frequency_differentiableAt_off_zero z rho sigma hsigma p delta hdelta s hs.1 hs.2 i j).differentiableWithinAt
  have hh := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hzero).mp ⟨hoff, hc⟩
  exact hh.analyticOnNhd hO

/-- Finite determinant complex differentiability, with the actual matrix
entry topology and no change of amplitude or matrix norm. -/
theorem matrix_det_frequency_differentiableAt (A : ℂ → Matrix (Fin N) (Fin N) ℂ) (s : ℂ)
    (hA : ∀ i j, DifferentiableAt ℂ (fun w => A w i j) s) :
    DifferentiableAt ℂ (fun w => (A w).det) s := by
  simp only [Matrix.det_apply']
  exact DifferentiableAt.fun_sum fun perm _ => (differentiableAt_const _).mul
    (DifferentiableAt.fun_finsetProd fun i _ => hA (perm i) i)

/-- The genuine finite matrix inverse is complex differentiable at units,
proved directly from the finite adjugate and scalar reciprocal determinant. -/
theorem matrix_inverse_entry_frequency_differentiableAt
    (A : ℂ → Matrix (Fin N) (Fin N) ℂ) (s : ℂ)
    (hA : ∀ i j, DifferentiableAt ℂ (fun w => A w i j) s)
    (hu : IsUnit (A s)) (i j : Fin N) :
    DifferentiableAt ℂ (fun w => (A w)⁻¹ i j) s := by
  have hd : (A s).det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have hdet := matrix_det_frequency_differentiableAt A s hA
  have hadj : DifferentiableAt ℂ (fun w => (A w).adjugate i j) s := by
    simp only [Matrix.adjugate_apply]
    apply matrix_det_frequency_differentiableAt
    intro k l
    by_cases hk : k=j
    · subst k
      simp only [Matrix.updateRow_self]
      exact differentiableAt_const _
    · simpa only [Matrix.updateRow_ne hk] using hA k l
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact (hdet.inv hd).mul hadj

/-- Under actual unit control, the existing finite renewal inverse is
holomorphic on the open negative-real-part half-plane, including zero. -/
theorem actual_inverse_entry_analyticOnNhd
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (delta : ℝ) (hd : 0 < delta)
    (hdelta : ∀ u, delta < z u)
    (hu : ∀ s : ℂ, -delta ≤ s.re →
      IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) (i j : Fin N) :
    AnalyticOnNhd ℂ (fun s : ℂ =>
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹ i j)
      {s : ℂ | -delta < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  apply matrix_inverse_entry_frequency_differentiableAt
  · intro k l
    exact (differentiableAt_const ((1 : Matrix (Fin N) (Fin N) ℂ) k l)).sub
      ((actual_kernel_entry_analyticOnNhd z rho sigma hsigma p delta hd hdelta k l) s hs).differentiableAt
  · exact hu s hs.le

/-- The finite resolvent remainder with a harmless pole strictly to the
left of the chosen half-plane. This is a frequency symbol, not a new RDF. -/
def regularizedResolvent (q : ℝ → Matrix (Fin N) (Fin N) ℝ) (b : ℝ) (s : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (1-rdfMatrixLaplace q s)⁻¹-1-Matrix.of (fun i j => (q 0 i j : ℂ)/(s+(b : ℂ)))

/-- Replacing the leading 1/s term by 1/(s+b) retains inverse-square
high-frequency control and removes the origin pole. -/
theorem shifted_leading_difference_bound (s a : ℂ) (b : ℝ)
    (hs : 1 ≤ ‖s‖) (hb : 2 * |b| ≤ ‖s‖) :
    ‖s‖^2*‖a/s-a/(s+(b : ℂ))‖ ≤ 2 * |b| *‖a‖ := by
  have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hs
  have hshift : s+(b : ℂ) ≠ 0 := by
    intro h
    have hh := norm_add_real_lower_bound s b hb
    simp only [h, norm_zero, mul_zero] at hh
    linarith
  have he : a/s-a/(s+(b : ℂ)) = (a*(b : ℂ)/(s+(b : ℂ)))/s := by
    field_simp
    ring
  calc
    _ = ‖s‖*(‖s‖*‖(a*(b : ℂ)/(s+(b : ℂ)))/s‖) := by rw [he]; ring
    _ = ‖s‖*‖a*(b : ℂ)/(s+(b : ℂ))‖ := by rw [scaled_norm_div s _ hs0]
    _ ≤ 2*‖a*(b : ℂ)‖ := scaled_norm_div_shift s _ b hs hb
    _ = _ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; ring

/-- The actual regularized finite resolvent has a uniform inverse-square
remainder throughout a full convergent closed half-plane at high frequency. -/
theorem actual_regularized_resolvent_high_frequency
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (delta : ℝ) (hdelta : ∀ u, delta < z u) (b : ℝ) :
    ∃ R B : ℝ, 1 ≤ R ∧ 0 ≤ B ∧ ∀ s : ℂ, -delta ≤ s.re → R ≤ ‖s‖ →
      ‖s‖^2*complexNormSum (regularizedResolvent (nonlinearCausalKernel z rho sigma p.1 p.2) b s) ≤ B := by
  obtain ⟨R0, B0, hR0, hB0, hb0⟩ := actual_resolvent_halfplane_high_frequency z rho sigma hsigma p delta hdelta
  let A := FMSA.matrixAbsSum (nonlinearCausalKernel z rho sigma p.1 p.2 0)
  have hA : 0 ≤ A := FMSA.matrixAbsSum_nonneg _
  refine ⟨max R0 (2 * |b|), B0+2 * |b| *A, hR0.trans (le_max_left _ _), by positivity, ?_⟩
  intro s hsre hsR
  have hsR0 : R0 ≤ ‖s‖ := (le_max_left _ _).trans hsR
  have hs : 1 ≤ ‖s‖ := hR0.trans hsR0
  have hsb : 2 * |b| ≤ ‖s‖ := (le_max_right _ _).trans hsR
  let U := (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹
  let K0 := Matrix.of (fun i j => (nonlinearCausalKernel z rho sigma p.1 p.2 0 i j : ℂ)/s)
  let Kb := Matrix.of (fun i j => (nonlinearCausalKernel z rho sigma p.1 p.2 0 i j : ℂ)/(s+(b : ℂ)))
  have herr : ‖s‖^2*complexNormSum (U-1-K0) ≤ B0 := (hb0 s hsre hsR0).2.2
  have hshift : ‖s‖^2*complexNormSum (K0-Kb) ≤ 2 * |b| *A := by
    simpa only [complexNormSum, Matrix.sub_apply, Matrix.of_apply, K0, Kb, A,
      FMSA.matrixAbsSum, Finset.mul_sum, Complex.norm_real, Real.norm_eq_abs] using
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        shifted_leading_difference_bound s (nonlinearCausalKernel z rho sigma p.1 p.2 0 i j : ℂ) b hs hsb))
  have he : U-1-Kb = (U-1-K0)+(K0-Kb) := by abel
  change ‖s‖^2*complexNormSum (U-1-Kb) ≤ _
  rw [he]
  calc
    _ ≤ ‖s‖^2*(complexNormSum (U-1-K0)+complexNormSum (K0-Kb)) :=
      mul_le_mul_of_nonneg_left (complexNormSum_add_le _ _) (sq_nonneg _)
    _ = ‖s‖^2*complexNormSum (U-1-K0)+‖s‖^2*complexNormSum (K0-Kb) := by ring
    _ ≤ _ := add_le_add herr hshift

/-- The regularizer pole is outside the chosen closed half-plane. -/
theorem regularizer_denominator_ne_zero (delta b : ℝ) (hb : delta < b)
    (s : ℂ) (hs : -delta ≤ s.re) : s+(b : ℂ) ≠ 0 :=
  rate_shift_ne_zero s b (by linarith)

/-- The actual regularized resolvent is continuous, including frequency zero,
wherever its actual inverse is continuous and the regularizer pole is excluded. -/
theorem regularized_resolvent_continuousOn
    (q : ℝ → Matrix (Fin N) (Fin N) ℝ) (delta b : ℝ) (hb : delta < b)
    (hU : ContinuousOn (fun s : ℂ => (1-rdfMatrixLaplace q s)⁻¹) {s : ℂ | -delta ≤ s.re}) :
    ContinuousOn (regularizedResolvent q b) {s : ℂ | -delta ≤ s.re} := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  simp only [regularizedResolvent, Matrix.sub_apply, Matrix.of_apply]
  exact ((continuousOn_pi.mp (continuousOn_pi.mp hU i) j).sub continuousOn_const).sub
    (continuousOn_const.div (continuousOn_id.add continuousOn_const)
      (fun s hs => regularizer_denominator_ne_zero delta b hb s hs))

/-- The actual regularized finite resolvent is holomorphic across zero and
throughout the open negative-real-part half-plane under actual unit control. -/
theorem actual_regularized_resolvent_entry_analyticOnNhd
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (delta : ℝ) (hd : 0 < delta)
    (hdelta : ∀ u, delta < z u) (b : ℝ) (hb : delta < b)
    (hu : ∀ s : ℂ, -delta ≤ s.re →
      IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) (i j : Fin N) :
    AnalyticOnNhd ℂ (fun s : ℂ => regularizedResolvent (nonlinearCausalKernel z rho sigma p.1 p.2) b s i j)
      {s : ℂ | -delta < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  have hU := ((actual_inverse_entry_analyticOnNhd z rho sigma hsigma p delta hd hdelta hu i j) s hs).differentiableAt
  have hden := regularizer_denominator_ne_zero delta b hb s hs.le
  simp only [regularizedResolvent, Matrix.sub_apply, Matrix.of_apply]
  exact (hU.sub (differentiableAt_const _)).sub
    ((differentiableAt_const _).div (differentiableAt_id.add (differentiableAt_const _)) hden)

/-- Every entry norm is controlled by the full finite entry norm sum. -/
theorem complexNormSum_entry_le (A : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    ‖A i j‖ ≤ complexNormSum A := by
  calc
    _ ≤ ∑ k, ‖A i k‖ := Finset.single_le_sum (fun k _ => norm_nonneg (A i k)) (Finset.mem_univ j)
    _ ≤ ∑ k, ∑ l, ‖A k l‖ := Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg (fun l _ => norm_nonneg (A k l))) (Finset.mem_univ i)

theorem complexNormSum_neg (A : Matrix (Fin N) (Fin N) ℂ) : complexNormSum (-A) = complexNormSum A := by
  simp only [complexNormSum, Matrix.neg_apply, norm_neg]

theorem complexNormSum_sub_le (A B : Matrix (Fin N) (Fin N) ℂ) :
    complexNormSum (A-B) ≤ complexNormSum A+complexNormSum B := by
  simpa only [sub_eq_add_neg, complexNormSum_neg] using complexNormSum_add_le A (-B)

/-- A regularizer separated by at least one from the half-plane gives a
uniform actual remainder bound from the actual inverse bound. -/
theorem regularized_resolvent_normSum_bound
    (q : ℝ → Matrix (Fin N) (Fin N) ℝ) (delta b C : ℝ) (hb : delta+1 ≤ b)
    (s : ℂ) (hs : -delta ≤ s.re) (hU : complexNormSum ((1-rdfMatrixLaplace q s)⁻¹) ≤ C) :
    complexNormSum (regularizedResolvent q b s) ≤ C+(N : ℝ)+FMSA.matrixAbsSum (q 0) := by
  have hden : 1 ≤ ‖s+(b : ℂ)‖ := by
    have hr : 1 ≤ (s+(b : ℂ)).re := by simp only [Complex.add_re, Complex.ofReal_re]; linarith
    exact hr.trans (Complex.re_le_norm _)
  have hK : complexNormSum (Matrix.of (fun i j => (q 0 i j : ℂ)/(s+(b : ℂ)))) ≤ FMSA.matrixAbsSum (q 0) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    change ‖(q 0 i j : ℂ)/(s+(b : ℂ))‖ ≤ |q 0 i j|
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    exact div_le_self (abs_nonneg _) hden
  unfold regularizedResolvent
  calc
    _ ≤ complexNormSum ((1-rdfMatrixLaplace q s)⁻¹-1)+
        complexNormSum (Matrix.of (fun i j => (q 0 i j : ℂ)/(s+(b : ℂ)))) := complexNormSum_sub_le _ _
    _ ≤ (complexNormSum ((1-rdfMatrixLaplace q s)⁻¹)+complexNormSum 1)+FMSA.matrixAbsSum (q 0) :=
      add_le_add (complexNormSum_sub_le _ _) hK
    _ ≤ _ := by rw [complexNormSum_one]; exact add_le_add (add_le_add hU le_rfl) le_rfl

/-- A bounded nonnegative function with a quadratic high-frequency bound
has an explicit globally integrable inverse-quadratic majorant. -/
theorem quadratic_tail_global_majorant (g : ℝ → ℝ) (R M B : ℝ)
    (hR : 1 ≤ R) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hgn : ∀ k, 0 ≤ g k) (hgm : ∀ k, g k ≤ M)
    (htail : ∀ k, R ≤ |k| → k^2*g k ≤ B) (k : ℝ) :
    (1+k^2)*g k ≤ (1+R^2)*M+2*B := by
  by_cases hk : |k| ≤ R
  · have hsq : k^2 ≤ R^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg k) hk 2
    have hh : (1+k^2)*g k ≤ (1+R^2)*M :=
      mul_le_mul (by linarith) (hgm k) (hgn k) (by positivity)
    linarith
  · have hkR : R ≤ |k| := le_of_lt (lt_of_not_ge hk)
    have hk1 : 1 ≤ k^2 := by
      simpa only [one_pow, sq_abs] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (hR.trans hkR) 2
    have hh := htail k hkR
    have hm : (1+k^2)*g k ≤ (2*k^2)*g k := mul_le_mul_of_nonneg_right (by linarith) (hgn k)
    have hc : 0 ≤ (1+R^2)*M := mul_nonneg (by positivity) hM
    nlinarith

/-- Vertical-line parameter with the actual complex Fourier coordinate. -/
def verticalPoint (a k : ℝ) : ℂ := (a : ℂ)+(k : ℂ)*Complex.I

/-- The inverse-transform exponential has constant norm along a vertical
line. The coordinate is angular frequency, with no hidden 2*pi substitution. -/
theorem vertical_exponential_norm (a k t : ℝ) :
    ‖Complex.exp (verticalPoint a k*(t : ℂ))‖ = exp (a*t) := by
  simp [verticalPoint, Complex.norm_exp, Complex.mul_re]

/-- Absolute integrability of a vertical symbol persists under the actual
inverse-transform exponential, for every fixed real time. -/
theorem vertical_phase_integrable (F : ℂ → ℂ) (a t : ℝ)
    (hF : Integrable (fun k : ℝ => F (verticalPoint a k))) :
    Integrable (fun k : ℝ => Complex.exp (verticalPoint a k*(t : ℂ))*F (verticalPoint a k)) := by
  have he : AEStronglyMeasurable (fun k : ℝ => Complex.exp (verticalPoint a k*(t : ℂ))) := by
    apply Continuous.aestronglyMeasurable
    unfold verticalPoint
    fun_prop
  exact hF.bdd_mul (c := exp (a*t)) he
    (Eventually.of_forall (fun k => (vertical_exponential_norm a k t).le))

/-- Uniform half-plane bounds and the actual quadratic frequency tail give
one integrable vertical-line majorant, independent of the line's real part. -/
theorem matrix_symbol_vertical_integrable
    (F : ℂ → Matrix (Fin N) (Fin N) ℂ) (delta R B M : ℝ)
    (hR : 1 ≤ R) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hF : ContinuousOn F {s : ℂ | -delta ≤ s.re})
    (hglobal : ∀ s : ℂ, -delta ≤ s.re → complexNormSum (F s) ≤ M)
    (htail : ∀ s : ℂ, -delta ≤ s.re → R ≤ ‖s‖ → ‖s‖^2*complexNormSum (F s) ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, -delta ≤ a →
      (∀ k : ℝ, (1+k^2)*complexNormSum (F (verticalPoint a k)) ≤ C) ∧
      Integrable (fun k : ℝ => complexNormSum (F (verticalPoint a k))) ∧
      ∀ i j : Fin N, Integrable (fun k : ℝ => F (verticalPoint a k) i j) ∧
        ∀ t : ℝ, Integrable (fun k : ℝ => Complex.exp (verticalPoint a k*(t : ℂ))*F (verticalPoint a k) i j) := by
  let C := (1+R^2)*M+2*B
  refine ⟨C, by positivity, ?_⟩
  intro a ha
  have hv : Continuous (verticalPoint a) := by unfold verticalPoint; fun_prop
  have hmem (k : ℝ) : -delta ≤ (verticalPoint a k).re := by simpa [verticalPoint] using ha
  have hc : Continuous (fun k : ℝ => F (verticalPoint a k)) := hF.comp_continuous hv hmem
  let g := fun k : ℝ => complexNormSum (F (verticalPoint a k))
  have hgn (k : ℝ) : 0 ≤ g k := complexNormSum_nonneg _
  have hgc : Continuous g := by
    unfold g complexNormSum
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact ((continuous_apply j).comp ((continuous_apply i).comp hc)).norm
  have hquadratic (k : ℝ) (hk : R ≤ |k|) : k^2*g k ≤ B := by
    have hnorm : |k| ≤ ‖verticalPoint a k‖ := by
      simpa [verticalPoint] using Complex.abs_im_le_norm (verticalPoint a k)
    have hsq : k^2 ≤ ‖verticalPoint a k‖^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg k) hnorm 2
    exact (mul_le_mul_of_nonneg_right hsq (hgn k)).trans
      (htail _ (hmem k) (hk.trans hnorm))
  have hmajor (k : ℝ) : (1+k^2)*g k ≤ C := quadratic_tail_global_majorant g R M B hR hM hB
    hgn (fun k => hglobal _ (hmem k)) hquadratic k
  have hpoint (k : ℝ) : g k ≤ C*(1+k^2)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < 1+k^2)).mpr (by simpa only [mul_comm] using hmajor k)
  have hg : Integrable g := by
    apply (integrable_inv_one_add_sq.const_mul C).mono' hgc.aestronglyMeasurable
    exact Eventually.of_forall (fun k => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hgn k)] using hpoint k)
  refine ⟨hmajor, hg, ?_⟩
  intro i j
  have hentry : Continuous (fun k : ℝ => F (verticalPoint a k) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hc)
  have hi := hg.mono' hentry.aestronglyMeasurable
    (Eventually.of_forall (fun k => complexNormSum_entry_le (F (verticalPoint a k)) i j))
  exact ⟨hi, fun t => vertical_phase_integrable (fun s => F s i j) a t hi⟩

/-- Full actual canonicity gives a regularized holomorphic resolvent with
one inverse-quadratic majorant for every vertical line in a negative half-plane,
and genuine absolute integrability of all entries and their norm sum. -/
theorem actual_canonical_regularized_resolvent_analysis
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (p : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re →
      IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∃ delta b R B C : ℝ, 0 < delta ∧ (∀ u, delta < z u) ∧ delta < b ∧
      1 ≤ R ∧ 0 ≤ B ∧ 0 ≤ C ∧
      (∀ i j : Fin N, AnalyticOnNhd ℂ (fun s : ℂ =>
        regularizedResolvent (nonlinearCausalKernel z rho sigma p.1 p.2) b s i j)
        {s : ℂ | -delta < s.re}) ∧
      ContinuousOn (regularizedResolvent (nonlinearCausalKernel z rho sigma p.1 p.2) b)
        {s : ℂ | -delta ≤ s.re} ∧
      (∀ s : ℂ, -delta ≤ s.re → R ≤ ‖s‖ →
        ‖s‖^2*complexNormSum (regularizedResolvent (nonlinearCausalKernel z rho sigma p.1 p.2) b s) ≤ B) ∧
      ∀ a : ℝ, -delta ≤ a →
        (∀ k : ℝ, (1+k^2)*complexNormSum
          (regularizedResolvent (nonlinearCausalKernel z rho sigma p.1 p.2) b (verticalPoint a k)) ≤ C) ∧
        Integrable (fun k : ℝ => complexNormSum
          (regularizedResolvent (nonlinearCausalKernel z rho sigma p.1 p.2) b (verticalPoint a k))) ∧
        ∀ i j : Fin N, Integrable (fun k : ℝ =>
          regularizedResolvent (nonlinearCausalKernel z rho sigma p.1 p.2) b (verticalPoint a k) i j) ∧
          ∀ t : ℝ, Integrable (fun k : ℝ => Complex.exp (verticalPoint a k*(t : ℂ))*
            regularizedResolvent (nonlinearCausalKernel z rho sigma p.1 p.2) b (verticalPoint a k) i j) := by
  obtain ⟨delta, R0, B0, C0, hd, hdr, hR0, hB0, hC0, hU, hall⟩ :=
    actual_canonical_resolvent_control z hz rho sigma hsigma p hcanon
  let q := nonlinearCausalKernel z rho sigma p.1 p.2
  let b := delta+1
  have hb : delta < b := by dsimp [b]; linarith
  have hu (s : ℂ) (hs : -delta ≤ s.re) : IsUnit (1-rdfMatrixLaplace q s) := (hall s hs).1
  have hc : ContinuousOn (regularizedResolvent q b) {s : ℂ | -delta ≤ s.re} :=
    regularized_resolvent_continuousOn q delta b hb hU
  obtain ⟨R, B, hR, hB, hfreq⟩ := actual_regularized_resolvent_high_frequency z rho sigma hsigma p delta hdr b
  let M := C0+(N : ℝ)+FMSA.matrixAbsSum (q 0)
  have hA : 0 ≤ FMSA.matrixAbsSum (q 0) := FMSA.matrixAbsSum_nonneg _
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hglobal (s : ℂ) (hs : -delta ≤ s.re) : complexNormSum (regularizedResolvent q b s) ≤ M :=
    regularized_resolvent_normSum_bound q delta b C0 le_rfl s hs (hall s hs).2.1
  obtain ⟨C, hC, hvertical⟩ := matrix_symbol_vertical_integrable (regularizedResolvent q b) delta R B M hR hB hM hc hglobal hfreq
  exact ⟨delta, b, R, B, C, hd, hdr, hb, hR, hB, hC,
    fun i j => actual_regularized_resolvent_entry_analyticOnNhd z rho sigma hsigma p delta hd hdr b hb hu i j,
    hc, hfreq, hvertical⟩

end FMSA.Convergence.CanonicalResolventAnalysis

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.rate_shift_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.rate_shift_ne_zero

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.complexJ_frequency_differentiableAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.complexJ_frequency_differentiableAt

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.complexL_frequency_differentiableAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.complexL_frequency_differentiableAt

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.actual_kernel_frequency_differentiableAt_off_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.actual_kernel_frequency_differentiableAt_off_zero

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.actual_kernel_entry_analyticOnNhd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.actual_kernel_entry_analyticOnNhd

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.matrix_det_frequency_differentiableAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.matrix_det_frequency_differentiableAt

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.matrix_inverse_entry_frequency_differentiableAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.matrix_inverse_entry_frequency_differentiableAt

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.actual_inverse_entry_analyticOnNhd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.actual_inverse_entry_analyticOnNhd

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.shifted_leading_difference_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.shifted_leading_difference_bound

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.actual_regularized_resolvent_high_frequency' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.actual_regularized_resolvent_high_frequency

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.regularizer_denominator_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.regularizer_denominator_ne_zero

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.regularized_resolvent_continuousOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.regularized_resolvent_continuousOn

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.actual_regularized_resolvent_entry_analyticOnNhd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.actual_regularized_resolvent_entry_analyticOnNhd

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.complexNormSum_entry_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.complexNormSum_entry_le

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.complexNormSum_neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.complexNormSum_neg

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.complexNormSum_sub_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.complexNormSum_sub_le

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.regularized_resolvent_normSum_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.regularized_resolvent_normSum_bound

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.quadratic_tail_global_majorant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.quadratic_tail_global_majorant

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.vertical_exponential_norm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.vertical_exponential_norm

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.vertical_phase_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.vertical_phase_integrable

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.matrix_symbol_vertical_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.matrix_symbol_vertical_integrable

/-- info: 'FMSA.Convergence.CanonicalResolventAnalysis.actual_canonical_regularized_resolvent_analysis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.CanonicalResolventAnalysis.actual_canonical_regularized_resolvent_analysis
