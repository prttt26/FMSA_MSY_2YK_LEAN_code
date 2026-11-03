import MSAConvergence.ActualCanonicalKernelTangent

/-! Actual BH amplitude recovery from the honest canonical kernel tangent.
The first residual identity is differentiated off root, in the original
amplitude norm and without inverting any density matrix. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.ActualBHAmplitudeRecovery
open FMSA.Paper FMSA.Paper.JacobianExterior
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open FMSA.Convergence.SymplecticTangent FMSA.Convergence.ActualSourceBoundary
open FMSA.Convergence.ActualCanonicalKernelTangent FMSA.Convergence.ActualRDFTangent

variable {N : ℕ} {T : Type*} [Fintype T]

/-- Complex scalar lift of the actual real BH recentered root transform. -/
def rootTransformSymbol (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (u : T) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => (nonlinearRootRecenteredTransform z rho sigma p.1 p.2 u i j : ℂ))

/-- The actual first amplitude coordinates, with no amplitude norm alias. -/
def dtSymbol (p : TailMatrix T N × TailMatrix T N) (u : T) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => (p.1 u i j : ℂ))

/-- The actual first BH left-hand side, lifted entrywise to complex scalars. -/
def firstSymbol (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (u : T) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => (firstLHS z rho sigma p.1 p.2 u i j : ℂ))

/-- Real-axis complex Laplace integrals are the complex lifts of the
actual real matrix integrals. No formal J/L substitution is used. -/
theorem matrix_laplace_real_axis (f : ℝ → Matrix (Fin N) (Fin N) ℝ) (s : ℝ) :
    rdfMatrixLaplace f (s : ℂ) = Matrix.of (fun i j => (realMatrixLaplace f s i j : ℂ)) := by
  ext i j
  change (∫ t in Ioi (0 : ℝ), (f t i j : ℂ)*Complex.exp (-(s : ℂ)*(t : ℂ))) =
    ((∫ t in Ioi (0 : ℝ), exp (-s*t)*f t i j : ℝ) : ℂ)
  rw [← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]
  ring

/-- The fixed-rate actual root transform is genuinely amplitude-smooth. -/
theorem root_transform_entry_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (u : T) (i j : Fin N) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => rootTransformSymbol z rho sigma a u i j) := by
  simp only [rootTransformSymbol, nonlinearRootRecenteredTransform, Matrix.of_apply]
  fun_prop

/-- Genuine first-coordinate differentiation recovers the actual vector,
using the frozen finite-tail coordinate CLM and the original norm. -/
theorem dt_symbol_matrix_derivative (p v : TailMatrix T N × TailMatrix T N) (u : T) :
    matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => dtSymbol a u) p v =
      Matrix.of (fun i j => (v.1 u i j : ℂ)) := by
  ext i j
  let L : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp ((entry u i j).comp (ContinuousLinearMap.fst ℝ _ _))
  have hL : HasFDerivAt (fun a : TailMatrix T N × TailMatrix T N => (a.1 u i j : ℂ)) L p := L.hasFDerivAt
  change fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => (a.1 u i j : ℂ)) p v = (v.1 u i j : ℂ)
  rw [hL.fderiv]
  rfl

/-- Actual first amplitude entries are differentiable in the given norm. -/
theorem dt_symbol_entry_diff (p : TailMatrix T N × TailMatrix T N) (u : T) :
    EntryDiff (fun a : TailMatrix T N × TailMatrix T N => dtSymbol a u) p := by
  intro i j
  change DifferentiableAt ℝ (fun a : TailMatrix T N × TailMatrix T N => (a.1 u i j : ℂ)) p
  let L : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp ((entry u i j).comp (ContinuousLinearMap.fst ℝ _ _))
  exact L.differentiableAt

/-- At each positive actual Yukawa rate the honest actual kernel integral
is row density times the actual BH root transform, at ALL amplitudes. -/
theorem actual_kernel_root_dictionary
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (p : TailMatrix T N × TailMatrix T N) (u : T) :
    rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) (z u : ℂ) =
      Matrix.diagonal (fun i => (rho i : ℂ))*rootTransformSymbol z rho sigma p u := by
  have hB := nonlinear_actual_secondBlock z rho sigma p.1 p.2 hz hsigma u
  have hBi : Matrix.of (secondBlock z rho sigma p.1 p.2 u) =
      1-Matrix.diagonal rho*nonlinearRootRecenteredTransform z rho sigma p.1 p.2 u := by
    ext i j
    simp only [secondBlock, nonlinearRootRecenteredTransform, Matrix.of_apply, Matrix.sub_apply,
      Matrix.one_apply, Matrix.diagonal_mul]
    ring
  have hL : realMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) (z u) =
      Matrix.diagonal rho*nonlinearRootRecenteredTransform z rho sigma p.1 p.2 u := by
    rw [hBi] at hB
    linear_combination (norm := noncomm_ring) hB
  rw [matrix_laplace_real_axis, hL]
  ext i j
  simp only [rootTransformSymbol, Matrix.of_apply, Matrix.diagonal_mul, Complex.ofReal_mul]

/-- Genuine whole-kernel derivative interchange identifies the actual
BH root-transform derivative at each positive rate, off root. -/
theorem actual_kernel_variation_root_dictionary
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (p v : TailMatrix T N × TailMatrix T N) (u : T) :
    rdfMatrixLaplace (kernelVariationField z rho sigma p v) (z u : ℂ) =
      Matrix.diagonal (fun i => (rho i : ℂ))*
        matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => rootTransformSymbol z rho sigma a u) p v := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) (z u : ℂ)) =
      fun a => Matrix.diagonal (fun i => (rho i : ℂ))*rootTransformSymbol z rho sigma a u :=
    funext (fun a => actual_kernel_root_dictionary z hz rho sigma hsigma a u)
  have hd := congrArg (fun FF => matrixDerivative FF p v) he
  have hQ : EntryDiff (fun a : TailMatrix T N × TailMatrix T N => rootTransformSymbol z rho sigma a u) p :=
    fun i j => (root_transform_entry_contDiff z rho sigma u i j).differentiable (by simp) p
  rw [matrix_derivative_const_mul _ _ p v hQ] at hd
  have hD : matrixDerivative (fun a : TailMatrix T N × TailMatrix T N =>
      rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) (z u : ℂ)) p v =
        rdfMatrixLaplace (kernelVariationField z rho sigma p v) (z u : ℂ) := by
    ext i j
    exact (kernel_variation_laplace_fderiv_closed_right z hz rho sigma p v (z u : ℂ) (by simpa using (hz u).le) i j).symm
  rw [hD] at hd
  exact hd

/-- All-amplitude first BH matrix identity, before any root restriction. -/
theorem first_symbol_matrix (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (u : T) :
    firstSymbol z rho sigma p u = dtSymbol p u*
      (1-Matrix.diagonal (fun i => (rho i : ℂ))*(rootTransformSymbol z rho sigma p u).transpose) := by
  have he := nonlinearRoot_first_matrix z rho sigma p.1 p.2 u
  ext i j
  have hei := congrFun (congrFun he i) j
  simp only [Matrix.of_apply, Matrix.mul_apply (M := Matrix.of (p.1 u)), Matrix.sub_apply,
    Matrix.one_apply, Matrix.diagonal_mul, Matrix.transpose_apply] at hei
  rw [Matrix.mul_apply]
  simp only [firstSymbol, dtSymbol, rootTransformSymbol, Matrix.of_apply,
    Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_mul, Matrix.transpose_apply]
  have heiC := congrArg Complex.ofReal hei
  push_cast at heiC ⊢
  simp only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero] at heiC
  exact heiC

/-- A true actual amplitude-Jacobian kernel vector fixes the first BH
left-hand side. No root value or root curve is needed for this implication. -/
theorem actual_kernel_first_symbol_derivative_zero
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0) (u : T) :
    matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => firstSymbol z rho sigma a u) p v = 0 := by
  ext i j
  let L : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp ((entry u i j).comp (ContinuousLinearMap.fst ℝ _ _))
  have hres := L.hasFDerivAt.comp p (residual_amplitudes_hasFDerivAt z rho sigma K t p)
  have hsum := hres.add_const ((2*π*t*K u i j/z u : ℝ) : ℂ)
  simp only [Function.comp_def] at hsum
  have he : (fun a : TailMatrix T N × TailMatrix T N => (firstLHS z rho sigma a.1 a.2 u i j : ℂ)) =
      fun a => L (residual z rho sigma K (t, a))+((2*π*t*K u i j/z u : ℝ) : ℂ) := by
    funext a
    change (firstLHS z rho sigma a.1 a.2 u i j : ℂ) =
      ((firstLHS z rho sigma a.1 a.2 u i j-2*π*t*K u i j/z u : ℝ) : ℂ)+((2*π*t*K u i j/z u : ℝ) : ℂ)
    push_cast
    ring
  change fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => (firstLHS z rho sigma a.1 a.2 u i j : ℂ)) p v = 0
  rw [he, hsum.fderiv]
  change L (amplitudeJacobian z rho sigma K t p v) = 0
  rw [hjac, map_zero]

/-- Pure first-BH recovery uses only the canonical unit and weighted
transform variation zero. No inverse density or symmetry of D is needed. -/
theorem first_BH_weighted_recovery
    (D Q dD dQ R : Matrix (Fin N) (Fin N) ℂ) (hR : R.transpose = R)
    (hu : IsUnit (1-R*Q)) (hq : R*dQ*R = 0)
    (hfirst : dD*(1-R*Q.transpose)-D*R*dQ.transpose = 0) : dD*R = 0 := by
  have hqt : R*dQ.transpose*R = 0 := by
    have h := congrArg Matrix.transpose hq
    simpa only [Matrix.transpose_mul, Matrix.transpose_zero, hR, Matrix.mul_assoc] using h
  have hAT : IsUnit (1-R*Q).transpose := (Matrix.isUnit_iff_isUnit_det _).mpr
    (by simpa only [Matrix.det_transpose] using (Matrix.isUnit_iff_isUnit_det _).mp hu)
  have he : (dD*R)*(1-R*Q).transpose = 0 := by
    calc
      _ = (dD*(1-R*Q.transpose)-D*R*dQ.transpose)*R+D*(R*dQ.transpose*R) := by
        simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hR]
        noncomm_ring
      _ = 0 := by rw [hfirst, hqt, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  apply hAT.mul_left_injective
  simpa only [Matrix.zero_mul] using he

/-- Actual first BH amplitude variations are recovered in density-weighted
columns, including tracer ROWS, from the already proved actual kernel
recovery and a true unit at each positive rate. -/
theorem actual_first_amplitude_weighted_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∀ u : T, Matrix.of (v.1 u)*Matrix.diagonal rho = 0 := by
  classical
  intro u
  let R := Matrix.diagonal (fun i => (rho i : ℂ))
  let Q := fun a : TailMatrix T N × TailMatrix T N => rootTransformSymbol z rho sigma a u
  let D := fun a : TailMatrix T N × TailMatrix T N => dtSymbol a u
  let B := fun a => 1-R*(Q a).transpose
  have hQ : EntryDiff Q p := fun i j => (root_transform_entry_contDiff z rho sigma u i j).differentiable (by simp) p
  have hD : EntryDiff D p := dt_symbol_entry_diff p u
  have hQT := entry_diff_transpose Q p hQ
  have hRQ := entry_diff_mul (fun _ => R) (fun a => (Q a).transpose) p (entry_diff_const R p) hQT
  have hB : EntryDiff B p := entry_diff_sub _ _ p (entry_diff_const _ p) hRQ
  have hFn : (fun a : TailMatrix T N × TailMatrix T N => firstSymbol z rho sigma a u) = fun a => D a*B a :=
    funext (fun a => first_symbol_matrix z rho sigma a u)
  have hd := actual_kernel_first_symbol_derivative_zero z rho sigma K t p v hjac u
  rw [hFn, matrix_derivative_mul D B p v hD hB,
    matrix_derivative_sub _ _ p v (entry_diff_const _ p) hRQ, matrix_derivative_const,
    matrix_derivative_const_mul _ _ p v hQT, matrix_derivative_transpose, zero_sub] at hd
  have hfirst : matrixDerivative D p v*(1-R*(Q p).transpose)-D p*R*(matrixDerivative Q p v).transpose = 0 := by
    change matrixDerivative D p v*B p+D p*(-(R*(matrixDerivative Q p v).transpose)) = 0 at hd
    dsimp only [B] at hd
    linear_combination (norm := noncomm_ring) hd
  have hq : R*matrixDerivative Q p v*R = 0 := by
    rw [← actual_kernel_variation_root_dictionary z hz rho sigma (fun i => (hsigma i).le) p v u]
    exact actual_weighted_kernel_laplace_zero z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon (z u : ℂ) (by simpa using (hz u).le)
  have hu : IsUnit (1-R*Q p) := by
    rw [← actual_kernel_root_dictionary z hz rho sigma (fun i => (hsigma i).le) p u]
    exact hcanon _ (by simpa using (hz u).le)
  have hzD := first_BH_weighted_recovery (D p) (Q p) (matrixDerivative D p v) (matrixDerivative Q p v) R
    (Matrix.diagonal_transpose _) hu hq hfirst
  rw [dt_symbol_matrix_derivative] at hzD
  ext i j
  have he := congrFun (congrFun hzD i) j
  simp only [R, Matrix.mul_diagonal, Matrix.of_apply, Matrix.zero_apply] at he ⊢
  exact_mod_cast he

/-- Positive-density first-amplitude columns vanish pointwise in every
row, including a row whose species density is zero. -/
theorem actual_first_amplitude_active_column_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∀ u i j, 0 < rho j → v.1 u i j = 0 := by
  intro u i j hj
  have he := congrFun (congrFun (actual_first_amplitude_weighted_zero z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon u) i) j
  simp only [Matrix.mul_diagonal, Matrix.of_apply, Matrix.zero_apply] at he
  exact (mul_eq_zero.mp he).resolve_right (ne_of_gt hj)

/-- Strictly positive species densities recover the entire FIRST actual
amplitude component. The G component is not inferred from this theorem. -/
theorem actual_first_amplitude_zero_of_positive_densities
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 < rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) : v.1 = 0 := by
  funext u i j
  exact actual_first_amplitude_active_column_zero z hz rho sigma hsigma (fun i => (hrho i).le) K hK t p v hv hroot hjac hcanon u i j (hrho j)

end FMSA.Convergence.ActualBHAmplitudeRecovery

/-- info: 'FMSA.Convergence.ActualBHAmplitudeRecovery.matrix_laplace_real_axis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHAmplitudeRecovery.matrix_laplace_real_axis

/-- info: 'FMSA.Convergence.ActualBHAmplitudeRecovery.root_transform_entry_contDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHAmplitudeRecovery.root_transform_entry_contDiff

/-- info: 'FMSA.Convergence.ActualBHAmplitudeRecovery.dt_symbol_matrix_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHAmplitudeRecovery.dt_symbol_matrix_derivative

/-- info: 'FMSA.Convergence.ActualBHAmplitudeRecovery.dt_symbol_entry_diff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHAmplitudeRecovery.dt_symbol_entry_diff

/-- info: 'FMSA.Convergence.ActualBHAmplitudeRecovery.actual_kernel_root_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHAmplitudeRecovery.actual_kernel_root_dictionary

/-- info: 'FMSA.Convergence.ActualBHAmplitudeRecovery.actual_kernel_variation_root_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHAmplitudeRecovery.actual_kernel_variation_root_dictionary

/-- info: 'FMSA.Convergence.ActualBHAmplitudeRecovery.first_symbol_matrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHAmplitudeRecovery.first_symbol_matrix

/-- info: 'FMSA.Convergence.ActualBHAmplitudeRecovery.actual_kernel_first_symbol_derivative_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHAmplitudeRecovery.actual_kernel_first_symbol_derivative_zero

/-- info: 'FMSA.Convergence.ActualBHAmplitudeRecovery.first_BH_weighted_recovery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHAmplitudeRecovery.first_BH_weighted_recovery

/-- info: 'FMSA.Convergence.ActualBHAmplitudeRecovery.actual_first_amplitude_weighted_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHAmplitudeRecovery.actual_first_amplitude_weighted_zero

/-- info: 'FMSA.Convergence.ActualBHAmplitudeRecovery.actual_first_amplitude_active_column_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHAmplitudeRecovery.actual_first_amplitude_active_column_zero

/-- info: 'FMSA.Convergence.ActualBHAmplitudeRecovery.actual_first_amplitude_zero_of_positive_densities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualBHAmplitudeRecovery.actual_first_amplitude_zero_of_positive_densities
