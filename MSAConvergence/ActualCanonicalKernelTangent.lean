import MSAConvergence.ActualRadialTangentOZ
import MSAConvergence.CausalFactorTangent

/-! Actual canonical kernel-tangent recovery from active-pair DCF
cancellation, retaining zero-density species without inverse densities. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators FourierTransform ContDiff RealInnerProductSpace
namespace FMSA.Convergence.ActualCanonicalKernelTangent
open FMSA.Paper FMSA.Paper.JacobianExterior FMSA.Paper.RadialVariationL2
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open FMSA.Convergence.SymplecticTangent FMSA.Convergence.CausalFactorTangent
open FMSA.Convergence.ActualRDFTangent FMSA.Convergence.ActualSourceBoundary
open FMSA.Convergence.CanonicalVolterraResolvent FMSA.Convergence.CanonicalRenewalFormula
open FMSA.Convergence.ActualRadialTangentOZ FMSA.Convergence.ComplexWronskianJets
open FMSA.Convergence.ActualExcessSourceTangent

variable {N : ℕ} {T : Type*} [Fintype T]

/-- Actual row-density kernel Frechet variation as a real matrix field. -/
def kernelVariationField (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (t : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => kernelVariation z rho sigma p v i j t)

/-- Actual left logarithmic response dq+r*dq. One transpose of the
proved right source response preserves the correct species order. -/
def leftKernelResponse (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (t : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (sourceResolventResponse
    (fun r => (kernelVariationField z rho sigma p v r).transpose)
    (fun r => (actualKernelResolvent z rho sigma p r).transpose) t).transpose


/-- Actual physical Baxter factor as an amplitude-family symbol. -/
def factorSymbol (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (k : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fourierFactor z rho sigma (amplitudeA z rho sigma p.1 p.2)
    (amplitudeQp z rho sigma p.1 p.2) (W z rho p.1 p.2) (C z rho sigma p.1 p.2) k

/-- Genuine physical logarithmic amplitude response F^(-1)*dF. -/
def physicalLogVariation (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (k : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  (factorSymbol z rho sigma p k)⁻¹*
    matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => factorSymbol z rho sigma a k) p v

/-- Density-congruent physical response written with the honest actual
canonical left-response integral, not an assumed inverse-transform field. -/
def weightedLeftSymbol (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  rdfPhase sigma (-s)*rdfMatrixLaplace (leftKernelResponse z rho sigma p v) s*
    rdfPhase sigma s*Matrix.diagonal (fun i => (rho i : ℂ))

/-- Entrywise real-to-complex Laplace integration commutes with transpose. -/
theorem matrix_laplace_transpose (f : ℝ → Matrix (Fin N) (Fin N) ℝ) (s : ℂ) :
    rdfMatrixLaplace (fun t => (f t).transpose) s = (rdfMatrixLaplace f s).transpose := rfl

/-- The actual left response is a continuous real field. -/
theorem left_kernel_response_continuous (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) : Continuous (leftKernelResponse z rho sigma p v) := by
  have hf : Continuous (kernelVariationField z rho sigma p v) := continuous_matrix
    (kernel_variation_continuous z rho sigma p v)
  have hr : Continuous (actualKernelResolvent z rho sigma p) := kernel_resolvent_continuous _ _
  have hh := source_resolvent_response_continuous _ _
    (continuous_matrix (fun i j => hf.matrix_elem j i))
    (continuous_matrix (fun i j => hr.matrix_elem j i))
  exact continuous_matrix (fun i j => hh.matrix_elem j i)

/-- Honest actual canonical left-response Laplace identity on the full
closed right half-plane; only the fixed base point is canonical. -/
theorem actual_left_response_laplace
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (s : ℂ) (hre : 0 ≤ s.re) :
    (∀ i j, IntegrableOn (fun t : ℝ => (leftKernelResponse z rho sigma p v t i j : ℂ)*Complex.exp (-s*(t : ℂ))) (Ioi 0)) ∧
    rdfMatrixLaplace (leftKernelResponse z rho sigma p v) s =
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹*
        rdfMatrixLaplace (kernelVariationField z rho sigma p v) s := by
  obtain ⟨delta, b, B, hd, _hdz, _hdb, _hB, hrc⟩ :=
    actual_kernel_resolvent_canonical z hz rho sigma hsigma p hcanon
  have hf : Continuous (kernelVariationField z rho sigma p v) := continuous_matrix
    (kernel_variation_continuous z rho sigma p v)
  have hr : Continuous (actualKernelResolvent z rho sigma p) := kernel_resolvent_continuous _ _
  have hh := source_resolvent_response_laplace
    (fun t => (kernelVariationField z rho sigma p v t).transpose)
    (fun t => (actualKernelResolvent z rho sigma p t).transpose)
    (continuous_matrix (fun i j => hf.matrix_elem j i))
    (continuous_matrix (fun i j => hr.matrix_elem j i)) s
    (fun i j => actual_kernel_variation_real_damped_integrable z hz rho sigma p v s.re hre j i)
    (fun i j => (hrc j i).2.2.2.1 s.re (by linarith))
  have hR : rdfMatrixLaplace (actualKernelResolvent z rho sigma p) s =
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)⁻¹-1 := by
    ext i j
    exact ((hrc i j).2.2.2.2 s (by linarith)).2
  refine ⟨fun i j => hh.1 j i, ?_⟩
  have he := congrArg Matrix.transpose hh.2
  simp only [matrix_laplace_transpose, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose] at he
  change rdfMatrixLaplace (leftKernelResponse z rho sigma p v) s = _ at he
  rw [hR] at he
  rw [he]
  noncomm_ring

/-- Actual canonical left response has genuine positive-axis L1. -/
theorem actual_left_response_integrable
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) (i j : Fin N) :
    IntegrableOn (fun t => leftKernelResponse z rho sigma p v t i j) (Ioi (0 : ℝ)) := by
  have hi := (actual_left_response_laplace z hz rho sigma hsigma p v hcanon 0 (by simp)).1 i j
  change Integrable (fun t : ℝ => leftKernelResponse z rho sigma p v t i j) (volume.restrict (Ioi 0))
  simpa only [neg_zero, zero_mul, Complex.exp_zero, mul_one, RCLike.re_to_complex, Complex.ofReal_re] using hi.re

/-- Active-pair DCF cancellation gives a zero FULL density-weighted
actual spectral derivative. Tracer weights vanish without division. -/
theorem actual_weighted_C_derivative_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) (k : ℝ) (hk : k ≠ 0) :
    Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))*
      matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierC z rho sigma a.1 a.2 k) p v*
        Matrix.diagonal (fun i => (sqrt (rho i) : ℂ)) = 0 := by
  rw [actual_weighted_C_variation z hz rho sigma hsigma K hK hv t p v hroot hjac k hk]
  have hcf := actual_kernel_DCF_ae_zero z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon
  ext i j
  simp only [radialVariationMatrix, Matrix.of_apply, Matrix.zero_apply, densityWeight, Complex.ofReal_mul]
  by_cases hi : rho i = 0
  · simp only [hi, sqrt_zero, Complex.ofReal_zero, zero_mul]
  by_cases hj : rho j = 0
  · simp only [hj, sqrt_zero, Complex.ofReal_zero, mul_zero, zero_mul]
  have hp := hcf i j (lt_of_le_of_ne (hrho i) (Ne.symm hi)) (lt_of_le_of_ne (hrho j) (Ne.symm hj))
  have he : (∫ r in Ioi (0 : ℝ), r^2*orderedVariation z rho sigma K p v i j r*sinc (k*r)) = 0 := by
    calc
      _ = ∫ r in Ioi (0 : ℝ), (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [hp] with r hr
        simp only [hr, mul_zero, zero_mul, Pi.zero_apply]
      _ = 0 := by simp
  simp only [RadialZeroMode.radialSymbol, he, mul_zero, Complex.ofReal_zero]

/-- The actual physical Fourier factor in its exact weighted-Q form. -/
theorem physical_factor_eq_weighted_Q
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (p : TailMatrix T N × TailMatrix T N) (k : ℝ) :
    fourierFactor z rho sigma (amplitudeA z rho sigma p.1 p.2)
      (amplitudeQp z rho sigma p.1 p.2) (W z rho p.1 p.2) (C z rho sigma p.1 p.2) k =
      1-Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))*nonlinearActualFourierQ z rho sigma p.1 p.2 k*
        Matrix.diagonal (fun i => (sqrt (rho i) : ℂ)) := by
  classical
  unfold fourierFactor
  congr 1
  ext i j
  simp only [nonlinearActualFourierQ, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  ring

/-- Actual physical-factor entries have genuine amplitude derivatives. -/
theorem physical_factor_entry_diff
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (k : ℝ) (hk : k ≠ 0) :
    EntryDiff (fun a : TailMatrix T N × TailMatrix T N => fourierFactor z rho sigma
      (amplitudeA z rho sigma a.1 a.2) (amplitudeQp z rho sigma a.1 a.2)
        (W z rho a.1 a.2) (C z rho sigma a.1 a.2) k) p := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => fourierFactor z rho sigma
      (amplitudeA z rho sigma a.1 a.2) (amplitudeQp z rho sigma a.1 a.2)
        (W z rho a.1 a.2) (C z rho sigma a.1 a.2) k) =
      fun a => 1-Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))*nonlinearActualFourierQ z rho sigma a.1 a.2 k*
        Matrix.diagonal (fun i => (sqrt (rho i) : ℂ)) :=
    funext (fun a => physical_factor_eq_weighted_Q z rho sigma a k)
  rw [he]
  exact entry_diff_sub _ _ p (entry_diff_const _ p)
    (entry_diff_mul _ _ p (entry_diff_mul _ _ p (entry_diff_const _ p)
      (fun i j => (actualFourierQ_entry_contDiff z rho sigma hz hsigma k hk i j).differentiable (by simp) p)) (entry_diff_const _ p))


/-- Actual physical product factorization is an off-root identity. -/
theorem physical_factor_product (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hrho : ∀ i, 0 ≤ rho i) (p : TailMatrix T N × TailMatrix T N) (k : ℝ) :
    factorSymbol z rho sigma p k*(factorSymbol z rho sigma p (-k)).transpose =
      1-Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))*nonlinearActualFourierC z rho sigma p.1 p.2 k*
        Matrix.diagonal (fun i => (sqrt (rho i) : ℂ)) := by
  classical
  let S := Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))
  let R := Matrix.diagonal (fun i => (rho i : ℂ))
  have hSS : S*S = R := by
    rw [show S = Matrix.diagonal (fun i => (sqrt (rho i) : ℂ)) from rfl, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact_mod_cast mul_self_sqrt (hrho i)
  unfold factorSymbol
  rw [physical_factor_eq_weighted_Q, physical_factor_eq_weighted_Q]
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
    Matrix.diagonal_transpose, Matrix.transpose_transpose]
  simp only [← Matrix.mul_assoc]
  rw [nonlinearActualFourierC_eq_Q_product]
  change (1-S*nonlinearActualFourierQ z rho sigma p.1 p.2 k*S)*
      (1-S*(nonlinearActualFourierQ z rho sigma p.1 p.2 (-k)).transpose*S) = _
  change _ = 1-S*(nonlinearActualFourierQ z rho sigma p.1 p.2 k+
    (nonlinearActualFourierQ z rho sigma p.1 p.2 (-k)).transpose-
      nonlinearActualFourierQ z rho sigma p.1 p.2 k*R*(nonlinearActualFourierQ z rho sigma p.1 p.2 (-k)).transpose)*S
  rw [← hSS]
  noncomm_ring

/-- Opposite contact phases are genuine matrix inverses. -/
theorem phase_inverse (sigma : Fin N → ℝ) (s : ℂ) : (rdfPhase sigma s)⁻¹ = rdfPhase sigma (-s) := by
  have hmul : rdfPhase sigma s*rdfPhase sigma (-s) = 1 := by
    simp only [rdfPhase, Matrix.diagonal_mul_diagonal]
    change Matrix.diagonal (fun i => Complex.exp (-s*(sigma i : ℂ)/2)*Complex.exp (-(-s)*(sigma i : ℂ)/2)) =
      Matrix.diagonal (fun _ => (1 : ℂ))
    congr 1
    funext i
    rw [← Complex.exp_add, show -s*(sigma i : ℂ)/2+-(-s)*(sigma i : ℂ)/2 = 0 by ring, Complex.exp_zero]
  have hd := Matrix.isUnit_det_of_right_inverse hmul
  have he := congrArg (fun Z => (rdfPhase sigma s)⁻¹*Z) hmul
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_one] at he
  exact he.symm

/-- Source phase convention in a density congruence, valid off root.
Neither S nor the density matrix is assumed invertible. -/
theorem physical_factor_phase_congruence
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i)
    (p : TailMatrix T N × TailMatrix T N) (k : ℝ) :
    (factorSymbol z rho sigma p k).transpose*Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))*rdfPhase sigma (Complex.I*k) =
      Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))*rdfPhase sigma (Complex.I*k)*
        (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) (Complex.I*k)).transpose := by
  classical
  let S := Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))
  let R := Matrix.diagonal (fun i => (rho i : ℂ))
  have hSS : S*S = R := by
    rw [show S = Matrix.diagonal (fun i => (sqrt (rho i) : ℂ)) from rfl, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact_mod_cast mul_self_sqrt (hrho i)
  have hFS : (factorSymbol z rho sigma p k).transpose*S =
      S*(1-(nonlinearActualFourierQ z rho sigma p.1 p.2 k).transpose*R) := by
    rw [factorSymbol, physical_factor_eq_weighted_Q]
    simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, Matrix.diagonal_transpose]
    simp only [← Matrix.mul_assoc]
    change (1-S*(nonlinearActualFourierQ z rho sigma p.1 p.2 k).transpose*S)*S = _
    rw [← hSS]
    noncomm_ring
  change (factorSymbol z rho sigma p k).transpose*S*rdfPhase sigma (Complex.I*k) = _
  rw [hFS, Matrix.mul_assoc, nonlinear_actual_recentered_factor_phase]
  noncomm_ring

/-- Actual logarithmic physical factor variations are anti-transpose at
opposite nonzero frequencies, derived from the zero weighted C derivative. -/
theorem actual_physical_log_variation_anti
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) (k : ℝ) (hk : k ≠ 0) :
    physicalLogVariation z rho sigma p v k+(physicalLogVariation z rho sigma p v (-k)).transpose = 0 := by
  let S := Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))
  let F := fun a : TailMatrix T N × TailMatrix T N => factorSymbol z rho sigma a k
  let G := fun a : TailMatrix T N × TailMatrix T N => factorSymbol z rho sigma a (-k)
  let Cf := fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierC z rho sigma a.1 a.2 k
  have hF : EntryDiff F p := physical_factor_entry_diff z hz rho sigma (fun i => (hsigma i).le) p k hk
  have hG : EntryDiff G p := physical_factor_entry_diff z hz rho sigma (fun i => (hsigma i).le) p (-k) (neg_ne_zero.mpr hk)
  have hC : EntryDiff Cf p := fun i j => (actualFourierC_entry_contDiff z rho sigma hz (fun i => (hsigma i).le) k hk i j).differentiable (by simp) p
  have he : (fun a => F a*(G a).transpose) = fun a => 1-S*Cf a*S :=
    funext (fun a => physical_factor_product z rho sigma hrho a k)
  have hd := congrArg (fun FF => matrixDerivative FF p v) he
  have hSC := entry_diff_mul (fun _ => S) Cf p (entry_diff_const S p) hC
  rw [matrix_derivative_mul _ _ p v hF (entry_diff_transpose _ p hG), matrix_derivative_transpose,
    matrix_derivative_sub _ _ p v (entry_diff_const _ p) (entry_diff_mul _ _ p hSC (entry_diff_const _ p)),
    matrix_derivative_const, matrix_derivative_mul_const _ S p v hSC, matrix_derivative_const_mul S Cf p v hC] at hd
  have hzero : S*matrixDerivative Cf p v*S = 0 := actual_weighted_C_derivative_zero z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon k hk
  rw [hzero, sub_self] at hd
  exact logarithmic_response_anti (F p) (G p) (matrixDerivative F p v) (matrixDerivative G p v)
    (physical_fourier_factor_unit_of_kernel_unit z rho sigma hrho p k (hcanon _ (by simp)))
    (physical_fourier_factor_unit_of_kernel_unit z rho sigma hrho p (-k) (hcanon _ (by simp))) hd


/-- The actual recentered kernel factor's genuine derivative is minus
the honest actual kernel-variation transform, including zero frequency. -/
theorem kernel_factor_matrix_derivative
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (s : ℂ) (hre : 0 ≤ s.re) :
    matrixDerivative (fun a : TailMatrix T N × TailMatrix T N =>
      1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s) p v =
        -rdfMatrixLaplace (kernelVariationField z rho sigma p v) s := by
  have hq : EntryDiff (fun a : TailMatrix T N × TailMatrix T N =>
      rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s) p :=
    fun i j => (kernel_laplace_closed_right_contDiff z hz rho sigma s hre i j).differentiable (by simp) p
  rw [matrix_derivative_sub _ _ p v (entry_diff_const _ p) hq, matrix_derivative_const, zero_sub]
  congr 1
  ext i j
  exact (kernel_variation_laplace_fderiv_closed_right z hz rho sigma p v s hre i j).symm

/-- Actual logarithmic response transport by symmetric phase/density
congruences. No inverse density, root curve or new tangent field is used. -/
theorem actual_physical_log_transport
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) (k : ℝ) (hk : k ≠ 0) :
    weightedLeftSymbol z rho sigma p v (Complex.I*k) =
      -(Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))*physicalLogVariation z rho sigma p v k*
        Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))) := by
  classical
  let sp : ℂ := Complex.I*k
  let S := Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))
  let R := Matrix.diagonal (fun i => (rho i : ℂ))
  let P := rdfPhase sigma sp
  let F := fun a : TailMatrix T N × TailMatrix T N => factorSymbol z rho sigma a k
  let A := fun a : TailMatrix T N × TailMatrix T N => 1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) sp
  have hre : 0 ≤ sp.re := by simp [sp]
  have hF : EntryDiff F p := physical_factor_entry_diff z hz rho sigma hsigma p k hk
  have hA : EntryDiff A p := entry_diff_sub _ _ p (entry_diff_const _ p)
    (fun i j => (kernel_laplace_closed_right_contDiff z hz rho sigma sp hre i j).differentiable (by simp) p)
  have hFT := entry_diff_transpose F p hF
  have hAT := entry_diff_transpose A p hA
  have hS := entry_diff_const S p
  have hPS := entry_diff_const P p
  have he : (fun a => (F a).transpose*S*P) = fun a => S*P*(A a).transpose :=
    funext (fun a => physical_factor_phase_congruence z rho sigma hrho a k)
  have hdphase := congrArg (fun FF => matrixDerivative FF p v) he
  rw [matrix_derivative_mul_const _ P p v (entry_diff_mul _ _ p hFT hS),
    matrix_derivative_mul_const _ S p v hFT, matrix_derivative_transpose,
    matrix_derivative_const_mul (S*P) _ p v hAT, matrix_derivative_transpose] at hdphase
  have hSS : S*S = R := by
    rw [show S = Matrix.diagonal (fun i => (sqrt (rho i) : ℂ)) from rfl, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact_mod_cast mul_self_sqrt (hrho i)
  have huP : IsUnit P := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    dsimp only [P, rdfPhase]
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun _ _ => Complex.exp_ne_zero _))
  have ht := logarithmic_response_transport (F p) (A p) (matrixDerivative F p v) (matrixDerivative A p v) S P R
    (physical_fourier_factor_unit_of_kernel_unit z rho sigma hrho p k (hcanon _ (by simp)))
    (hcanon sp hre) huP (Matrix.diagonal_transpose _) (Matrix.diagonal_transpose _) hSS (congrFun he p) hdphase
  have hda : matrixDerivative A p v = -rdfMatrixLaplace (kernelVariationField z rho sigma p v) sp :=
    kernel_factor_matrix_derivative z hz rho sigma p v sp hre
  have hLap : rdfMatrixLaplace (leftKernelResponse z rho sigma p v) sp =
      (A p)⁻¹*rdfMatrixLaplace (kernelVariationField z rho sigma p v) sp :=
    (actual_left_response_laplace z hz rho sigma hsigma p v hcanon sp hre).2
  have hX : weightedLeftSymbol z rho sigma p v sp =
      P⁻¹*((A p)⁻¹*rdfMatrixLaplace (kernelVariationField z rho sigma p v) sp)*P*R := by
    unfold weightedLeftSymbol
    rw [hLap]
    change _ = (rdfPhase sigma sp)⁻¹*((A p)⁻¹*rdfMatrixLaplace (kernelVariationField z rho sigma p v) sp)*P*R
    rw [phase_inverse]
  rw [hda] at ht
  simp only [Matrix.mul_neg, Matrix.neg_mul] at ht
  rw [← hX] at ht
  have hn := congrArg Neg.neg ht
  simpa only [neg_neg, physicalLogVariation, F, S, sp] using hn.symm

/-- The honest actual left response, transported into physical contact
coordinates and weighted only by densities, is anti-transpose at opposite
nonzero frequencies. All zero-density species remain included. -/
theorem actual_weighted_left_response_anti
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) (k : ℝ) (hk : k ≠ 0) :
    weightedLeftSymbol z rho sigma p v (Complex.I*k)+
      (weightedLeftSymbol z rho sigma p v (-(Complex.I*k))).transpose = 0 := by
  let S := Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))
  have hp := actual_physical_log_transport z hz rho sigma (fun i => (hsigma i).le) hrho p v hcanon k hk
  have hm : weightedLeftSymbol z rho sigma p v (-(Complex.I*k)) =
      -(S*physicalLogVariation z rho sigma p v (-k)*S) := by
    simpa only [Complex.ofReal_neg, mul_neg] using
      actual_physical_log_transport z hz rho sigma (fun i => (hsigma i).le) hrho p v hcanon (-k) (neg_ne_zero.mpr hk)
  rw [hp, hm]
  have hanti := actual_physical_log_variation_anti z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon k hk
  change -(S*physicalLogVariation z rho sigma p v k*S)+(-(S*physicalLogVariation z rho sigma p v (-k)*S)).transpose = 0
  simp only [Matrix.transpose_neg, Matrix.transpose_mul, S, Matrix.diagonal_transpose]
  simp only [← Matrix.mul_assoc, ← sub_eq_add_neg]
  change -(S*physicalLogVariation z rho sigma p v k*S)-(S*(physicalLogVariation z rho sigma p v (-k)).transpose*S) = 0
  calc
    _ = -(S*(physicalLogVariation z rho sigma p v k+(physicalLogVariation z rho sigma p v (-k)).transpose)*S) := by noncomm_ring
    _ = 0 := by rw [hanti, Matrix.mul_zero, Matrix.zero_mul, neg_zero]

/-- Actual physical response entries are honest Fourier transforms of
causal L1 fields shifted by the SOURCE edgeLo, including unequal diameters. -/
theorem weighted_left_response_fourier
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (i j : Fin N) (w : ℝ) :
    𝓕 (fun r => (causalShift (fun t => rho j*leftKernelResponse z rho sigma p v t i j) (edgeLo sigma i j) r : ℂ)) w =
      weightedLeftSymbol z rho sigma p v (Complex.I*(2*π*w)) i j := by
  rw [causal_shift_fourier]
  have hL : FMSA.causalComplexLaplace (fun t => rho j*leftKernelResponse z rho sigma p v t i j) (Complex.I*(2*π*w)) =
      (rho j : ℂ)*rdfMatrixLaplace (leftKernelResponse z rho sigma p v) (Complex.I*(2*π*w)) i j := by
    change FMSA.causalComplexLaplace (fun t => rho j*leftKernelResponse z rho sigma p v t i j) (Complex.I*(2*π*w)) =
      (rho j : ℂ)*FMSA.causalComplexLaplace (fun t => leftKernelResponse z rho sigma p v t i j) (Complex.I*(2*π*w))
    unfold FMSA.causalComplexLaplace
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    simp only [Matrix.of_apply, Complex.ofReal_mul]
    ring
  rw [hL]
  simp only [weightedLeftSymbol, rdfPhase, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hphase : Complex.exp (-(Complex.I*(2*π*w))*(edgeLo sigma i j : ℂ)) =
      Complex.exp (-(-(Complex.I*(2*π*w)))*(sigma i : ℂ)/2)*Complex.exp (-(Complex.I*(2*π*w))*(sigma j : ℂ)/2) := by
    rw [← Complex.exp_add]
    congr 1
    unfold edgeLo
    push_cast
    ring
  rw [hphase]
  ring


/-- Causal support and reflected-transposed Fourier antisymmetry force
all density-weighted actual left responses to vanish on the CLOSED
causal half-line. The touching endpoint is recovered by continuity. -/
theorem actual_weighted_left_response_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∀ i j, EqOn (fun r => rho j*leftKernelResponse z rho sigma p v r i j) (fun _ => 0) (Ici (0 : ℝ)) := by
  intro i j
  apply touching_causal_pair_zero
    (fun r => rho j*leftKernelResponse z rho sigma p v r i j)
    (fun r => rho i*leftKernelResponse z rho sigma p v r j i) (edgeLo sigma i j)
    (continuous_const.mul ((left_kernel_response_continuous z rho sigma p v).matrix_elem i j))
    ((actual_left_response_integrable z hz rho sigma (fun i => (hsigma i).le) p v hcanon i j).const_mul (rho j))
    ((actual_left_response_integrable z hz rho sigma (fun i => (hsigma i).le) p v hcanon j i).const_mul (rho i))
  intro w hw
  rw [← edgeLo_reverse sigma i j, weighted_left_response_fourier, weighted_left_response_fourier]
  have hk : 2*π*w ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) pi_ne_zero) hw
  have hh := congrFun (congrFun (actual_weighted_left_response_anti z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon (2*π*w) hk) i) j
  simpa only [Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply, mul_neg, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat] using hh

/-- Actual weighted left-response transforms vanish at all frequencies;
this is an integral of a proved zero actual field, not a formal substitution. -/
theorem actual_weighted_left_laplace_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) (s : ℂ) :
    rdfMatrixLaplace (leftKernelResponse z rho sigma p v) s*Matrix.diagonal (fun i => (rho i : ℂ)) = 0 := by
  have hzero := actual_weighted_left_response_zero z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.zero_apply]
  change (∫ r in Ioi (0 : ℝ), (leftKernelResponse z rho sigma p v r i j : ℂ)*Complex.exp (-s*(r : ℂ)))*(rho j : ℂ) = 0
  rw [← integral_mul_const]
  calc
    _ = ∫ r in Ioi (0 : ℝ), (0 : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hr0 : 0 < r := hr
      have he : (rho j : ℂ)*(leftKernelResponse z rho sigma p v r i j : ℂ) = 0 := by
        exact_mod_cast hzero i j (show r ∈ Ici (0 : ℝ) from hr0.le)
      calc
        _ = ((rho j : ℂ)*(leftKernelResponse z rho sigma p v r i j : ℂ))*Complex.exp (-s*(r : ℂ)) := by ring
        _ = 0 := by rw [he, zero_mul]
    _ = 0 := by simp

/-- Canonical unit renewal recovers the actual weighted kernel tangent
transform from the now-zero actual left response. Includes zero frequency. -/
theorem actual_weighted_kernel_laplace_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) (s : ℂ) (hre : 0 ≤ s.re) :
    rdfMatrixLaplace (kernelVariationField z rho sigma p v) s*Matrix.diagonal (fun i => (rho i : ℂ)) = 0 := by
  let A := 1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s
  let R := Matrix.diagonal (fun i => (rho i : ℂ))
  have hLap := (actual_left_response_laplace z hz rho sigma (fun i => (hsigma i).le) p v hcanon s hre).2
  have he := congrArg (fun Z => A*Z*R) hLap
  have hleft : A*rdfMatrixLaplace (leftKernelResponse z rho sigma p v) s*R = 0 := by
    rw [Matrix.mul_assoc, actual_weighted_left_laplace_zero z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon s, Matrix.mul_zero]
  rw [hleft] at he
  change 0 = A*(A⁻¹*rdfMatrixLaplace (kernelVariationField z rho sigma p v) s)*R at he
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hcanon s hre)), Matrix.one_mul] at he
  exact he.symm

/-- Genuine actual kernel Frechet tangents, weighted only by the column
densities, vanish on the whole closed causal half-line. Honest Laplace
uniqueness supplies the time-domain conclusion, without a root curve. -/
theorem actual_weighted_kernel_variation_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∀ r : ℝ, 0 ≤ r → kernelVariationField z rho sigma p v r*Matrix.diagonal rho = 0 := by
  intro r hr
  ext i j
  simp only [kernelVariationField, Matrix.mul_diagonal, Matrix.of_apply, Matrix.zero_apply]
  let f := fun u : ℝ => ((rho j*kernelVariation z rho sigma p v i j u : ℝ) : ℂ)
  have hfc : Continuous f := Complex.continuous_ofReal.comp
    (continuous_const.mul (kernel_variation_continuous z rho sigma p v i j))
  have hifR : IntegrableOn (fun u => rho j*kernelVariation z rho sigma p v i j u) (Ioi (0 : ℝ)) := by
    have hh := (actual_kernel_variation_real_damped_integrable z hz rho sigma p v 0 (by simp) i j).const_mul (rho j)
    change Integrable (fun u : ℝ => rho j*kernelVariation z rho sigma p v i j u) (volume.restrict (Ioi 0))
    simpa only [neg_zero, zero_mul, exp_zero, one_mul] using hh
  have hif : IntegrableOn (FMSA.Convergence.CanonicalFourierLaplace.dampedField f 0) (Ioi (0 : ℝ)) := by
    change Integrable (fun u : ℝ => Complex.exp (-(0 : ℂ)*(u : ℂ))*((rho j*kernelVariation z rho sigma p v i j u : ℝ) : ℂ)) (volume.restrict (Ioi 0))
    simp only [neg_zero, zero_mul, Complex.exp_zero, one_mul]
    change Integrable f (volume.restrict (Ioi 0))
    apply hifR.norm.mono' hfc.aestronglyMeasurable
    exact ae_of_all _ (fun u => by simp only [f, Complex.norm_real, le_refl])
  have hg : IntegrableOn (FMSA.Convergence.CanonicalFourierLaplace.dampedField (fun _ : ℝ => (0 : ℂ)) 0) (Ioi (0 : ℝ)) := by
    change Integrable (fun u : ℝ => Complex.exp (-(0 : ℂ)*(u : ℂ))*(0 : ℂ)) (volume.restrict (Ioi 0))
    simp only [mul_zero]
    exact integrable_zero _ _ _
  have hEq := causal_laplace_injective f (fun _ => 0) 0 hfc.continuousOn continuousOn_const hif hg (fun w => by
    let s := FMSA.Convergence.CanonicalResolventAnalysis.verticalPoint 0 (2*π*w)
    have hs : 0 ≤ s.re := by simp [s, FMSA.Convergence.CanonicalResolventAnalysis.verticalPoint]
    have he := congrFun (congrFun (actual_weighted_kernel_laplace_zero z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon s hs) i) j
    simp only [Matrix.mul_diagonal, Matrix.zero_apply] at he
    change (∫ u in Ioi (0 : ℝ), f u*Complex.exp (-s*(u : ℂ))) = ∫ u in Ioi (0 : ℝ), (0 : ℂ)*Complex.exp (-s*(u : ℂ))
    simp only [zero_mul, integral_zero]
    have hf : (fun u : ℝ => f u*Complex.exp (-s*(u : ℂ))) =
        fun u => (rho j : ℂ)*((kernelVariation z rho sigma p v i j u : ℂ)*Complex.exp (-s*(u : ℂ))) := by
      funext u
      dsimp only [f]
      push_cast
      ring
    rw [hf, integral_const_mul]
    change (rho j : ℂ)*rdfMatrixLaplace (kernelVariationField z rho sigma p v) s i j = 0
    simpa only [mul_comm] using he)
  have hz := hEq (show r ∈ Ici (0 : ℝ) from hr)
  have hzC : ((rho j*kernelVariation z rho sigma p v i j r : ℝ) : ℂ) = 0 := hz
  have hzR := Complex.ofReal_eq_zero.mp hzC
  simpa only [mul_comm] using hzR

/-- Every actual kernel-tangent entry in a positive-density column
vanishes pointwise on t>=0. Zero-density columns are not divided. -/
theorem actual_kernel_variation_active_column_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∀ i j, 0 < rho j → ∀ r : ℝ, 0 ≤ r → kernelVariation z rho sigma p v i j r = 0 := by
  intro i j hj r hr
  have he := congrFun (congrFun (actual_weighted_kernel_variation_zero z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon r hr) i) j
  simp only [kernelVariationField, Matrix.mul_diagonal, Matrix.of_apply, Matrix.zero_apply] at he
  exact (mul_eq_zero.mp he).resolve_right (ne_of_gt hj)

end FMSA.Convergence.ActualCanonicalKernelTangent

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.matrix_laplace_transpose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.matrix_laplace_transpose

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.left_kernel_response_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.left_kernel_response_continuous

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.actual_left_response_laplace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.actual_left_response_laplace

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.actual_left_response_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.actual_left_response_integrable

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.actual_weighted_C_derivative_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.actual_weighted_C_derivative_zero

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.physical_factor_eq_weighted_Q' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.physical_factor_eq_weighted_Q

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.physical_factor_entry_diff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.physical_factor_entry_diff

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.physical_factor_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.physical_factor_product

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.phase_inverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.phase_inverse

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.physical_factor_phase_congruence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.physical_factor_phase_congruence

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.actual_physical_log_variation_anti' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.actual_physical_log_variation_anti

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.kernel_factor_matrix_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.kernel_factor_matrix_derivative

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.actual_physical_log_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.actual_physical_log_transport

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.actual_weighted_left_response_anti' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.actual_weighted_left_response_anti

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.weighted_left_response_fourier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.weighted_left_response_fourier

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.actual_weighted_left_response_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.actual_weighted_left_response_zero

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.actual_weighted_left_laplace_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.actual_weighted_left_laplace_zero

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.actual_weighted_kernel_laplace_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.actual_weighted_kernel_laplace_zero

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.actual_weighted_kernel_variation_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.actual_weighted_kernel_variation_zero

/-- info: 'FMSA.Convergence.ActualCanonicalKernelTangent.actual_kernel_variation_active_column_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualCanonicalKernelTangent.actual_kernel_variation_active_column_zero
