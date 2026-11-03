import MSAConvergence.ActualBHSecondAmplitudeRecovery
import MSAConvergence.ActualTracerDCFCancellation

/-! Actual tracer amplitude recovery from the vanishing genuine h tangent
and all-amplitude BH residuals. No root curve is assumed. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.ActualTracerAmplitudeRecovery
open FMSA.Paper FMSA.Paper.JacobianExterior FMSA.ExactMSA.MultiTailMixture
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open FMSA.Convergence.SymplecticTangent FMSA.Convergence.ActualRadialTangentOZ
open FMSA.Convergence.ActualBHAmplitudeRecovery FMSA.Convergence.ActualBHSecondAmplitudeRecovery
open FMSA.Convergence.ActualTracerDCFCancellation FMSA.Convergence.ActualSourceBoundary
open FMSA.Convergence.ActualReciprocityTangent FMSA.Convergence.ActualCanonicalKernelTangent
variable {N : ℕ} {T : Type*} [Fintype T]

/-- Zero genuine h-tangent integrals force the actual completed J derivative
zero; fixed contact phases and 2*pi are genuinely nonzero factors. -/
theorem actual_completed_J_derivative_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (s : ℂ) (hs : s ≠ 0) (hre : 0 ≤ s.re) :
    matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => completedJSymbol z rho sigma a s) p v = 0 := by
  have he := actual_h_laplace_phase_derivative z hz rho sigma hsigma hv p v hcanon s hs hre
  rw [actual_h_tangent_laplace_zero z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon s,
    completed_phase_matrix_derivative z hz rho sigma p v s hre (hcanon s hre)] at he
  have htwo : (2*(π : ℂ))⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr pi_ne_zero))
  have hp := (smul_eq_zero.mp he.symm).resolve_left htwo
  ext i j
  have hij := congrFun (congrFun hp i) j
  simp only [rdfPhase, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply] at hij ⊢
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hij).resolve_right (Complex.exp_ne_zero _))).resolve_left (Complex.exp_ne_zero _)

/-- A root value and genuine second BH derivative, together with zero
completed-symbol derivative, recover the entire second amplitude direction. -/
theorem second_BH_recovery_from_completed_derivative
    (A H J dH dq dJ : Matrix (Fin N) (Fin N) ℂ)
    (hu : IsUnit A) (hb : H*A = J)
    (hd : dH*A-H*dq-dJ = 0) (hc : (dJ+(J*A⁻¹)*dq)*A⁻¹ = 0) : dH = 0 := by
  have hud := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hy : J*A⁻¹ = H := by rw [← hb, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hud, Matrix.mul_one]
  rw [hy] at hc
  have hs := congrArg (fun M => M*A) hc
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hud, Matrix.mul_one, Matrix.zero_mul] at hs
  have hz : dH*A = 0 := by linear_combination (norm := noncomm_ring) hd+hs
  apply hu.mul_left_injective
  simpa only [Matrix.zero_mul] using hz

/-- Full actual G recovery for NONNEGATIVE densities, including every
zero-density tracer row/column, through the genuine actual h tangent. -/
theorem actual_second_amplitude_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    : v.2 = 0 := by
  classical
  funext u i j
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
  have hsecond : matrixDerivative H p v*A p-H p*(R*matrixDerivative Q p v)-matrixDerivative Jf p v = 0 := by
    change (matrixDerivative H p v*A p+H p*(-(R*matrixDerivative Q p v)))-matrixDerivative Jf p v = 0 at hd
    linear_combination (norm := noncomm_ring) hd
  have hbase : H p*A p = Jf p := by
    apply sub_eq_zero.mp
    change ((2*(π : ℂ)) • gSymbol p u)*(1-R*rootTransformSymbol z rho sigma p u)-Jf p = 0
    rw [second_residual_matrix_identity z hz rho sigma K t p u]
    ext k l
    change ((secondLHS z rho sigma p.1 p.2 u k l-secondRHS z rho sigma p.1 p.2 u k l : ℝ) : ℂ) = 0
    rw [hroot.2 u k l, sub_self, Complex.ofReal_zero]
  have hu : IsUnit (A p) := by
    change IsUnit (1-R*Q p)
    rw [← actual_kernel_root_dictionary z hz rho sigma (fun i => (hsigma i).le) p u]
    exact hcanon _ (by simpa using (hz u).le)
  have hcomp := actual_completed_J_derivative_zero z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon (z u : ℂ)
    (Complex.ofReal_ne_zero.mpr (hz u).ne') (by simpa using (hz u).le)
  rw [completed_symbol_matrix_derivative z hz rho sigma p v (z u : ℂ) (by simpa using (hz u).le)
    (hcanon _ (by simpa using (hz u).le))] at hcomp
  change (jVariation z rho sigma p v (z u : ℂ)+completedJSymbol z rho sigma p (z u : ℂ)*
    rdfMatrixLaplace (kernelVariationField z rho sigma p v) (z u : ℂ))*
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) (z u : ℂ))⁻¹ = 0 at hcomp
  simp only [completedJSymbol] at hcomp
  rw [actual_kernel_variation_root_dictionary z hz rho sigma (fun i => (hsigma i).le) p v u,
    actual_kernel_root_dictionary z hz rho sigma (fun i => (hsigma i).le) p u] at hcomp
  change (matrixDerivative Jf p v+(Jf p*(A p)⁻¹)*(R*matrixDerivative Q p v))*(A p)⁻¹ = 0 at hcomp
  have hzH := second_BH_recovery_from_completed_derivative (A p) (H p) (Jf p)
    (matrixDerivative H p v) (R*matrixDerivative Q p v) (matrixDerivative Jf p v) hu hbase hsecond hcomp
  rw [matrix_derivative_smul _ _ p v hG, g_symbol_matrix_derivative] at hzH
  have htwo : 2*(π : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr pi_ne_zero)
  have hzG := (smul_eq_zero.mp hzH).resolve_left htwo
  have hij := congrFun (congrFun hzG i) j
  exact Complex.ofReal_eq_zero.mp hij

/-- The actual root transform in column j depends on Dt only through
that same column when G is fixed. This identity holds at ALL amplitudes. -/
theorem root_transform_column_local (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (D E G : TailMatrix T N) (j : Fin N) (hcol : ∀ u i, D u i j = E u i j)
    (u : T) (i : Fin N) :
    rootTransformSymbol z rho sigma (D,G) u i j = rootTransformSymbol z rho sigma (E,G) u i j := by
  simp only [rootTransformSymbol, nonlinearRootRecenteredTransform, Matrix.of_apply,
    dressedQhat, Qhat, amplitudeA, amplitudeQp, W, C, mixDA, mixDqp, mixM, mixN, Wt, Ct]
  simp_rw [hcol]

/-- Honest continuous linear projection retaining G and repeating one Dt
column. The original amplitude-space norm is used. -/
def columnProjection (j : Fin N) :
    (TailMatrix T N × TailMatrix T N) →L[ℝ] (TailMatrix T N × TailMatrix T N) :=
  (ContinuousLinearMap.pi (fun u => ContinuousLinearMap.pi (fun i =>
    ContinuousLinearMap.pi (fun _ : Fin N => (entry u i j).comp
      (ContinuousLinearMap.fst ℝ (TailMatrix T N) (TailMatrix T N)))))).prod
    (ContinuousLinearMap.snd ℝ (TailMatrix T N) (TailMatrix T N))

/-- Exact projection value, with every unused Dt column replaced. -/
theorem column_projection_apply (j : Fin N) (p : TailMatrix T N × TailMatrix T N) :
    columnProjection j p = ((fun u i _ => p.1 u i j),p.2) := rfl

/-- The genuine all-amplitude root-transform entry factors through that
continuous linear projection; no root neighbourhood is assumed. -/
theorem root_transform_column_factorization (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (u : T) (i j : Fin N) :
    (fun p : TailMatrix T N × TailMatrix T N => rootTransformSymbol z rho sigma p u i j) =
      fun p => rootTransformSymbol z rho sigma (columnProjection j p) u i j := by
  funext p
  rw [column_projection_apply]
  apply root_transform_column_local
  intro u i
  rfl

/-- True Frechet derivative column locality, obtained by differentiating
the ALL-AMPLITUDE projection factorization, not a root-only identity. -/
theorem root_transform_column_derivative_zero (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (hG : v.2 = 0)
    (j : Fin N) (hD : ∀ u i, v.1 u i j = 0) (u : T) (i : Fin N) :
    matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => rootTransformSymbol z rho sigma a u) p v i j = 0 := by
  let L := columnProjection (T := T) j
  have hvL : L v = 0 := by
    rw [show L = columnProjection j from rfl, column_projection_apply, hG]
    apply Prod.ext
    · funext u i k
      exact hD u i
    · rfl
  have hd := ((root_transform_entry_contDiff z rho sigma u i j).differentiable (by simp) (L p)).hasFDerivAt.comp p L.hasFDerivAt
  change HasFDerivAt (fun a : TailMatrix T N × TailMatrix T N => rootTransformSymbol z rho sigma (L a) u i j) _ p at hd
  change fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => rootTransformSymbol z rho sigma a u i j) p v = 0
  rw [root_transform_column_factorization z rho sigma u i j, hd.fderiv]
  change (fderiv ℝ (fun a : TailMatrix T N × TailMatrix T N => rootTransformSymbol z rho sigma a u i j) (L p)) (L v) = 0
  rw [hvL, map_zero]

/-- Recovered G and active Dt columns force actual root-transform
derivatives to vanish in every active column, including tracer rows. -/
theorem actual_root_transform_active_columns_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (u : T) (i j : Fin N) (hj : 0 < rho j) :
    matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => rootTransformSymbol z rho sigma a u) p v i j = 0 := by
  exact root_transform_column_derivative_zero z rho sigma p v (actual_second_amplitude_zero z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon) j
    (fun u i => actual_first_amplitude_active_column_zero z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon u i j hj) u i

/-- One-sided actual root-transform derivative weighting now vanishes,
without the previously necessary row-density factor. -/
theorem actual_root_transform_weighted_columns_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (u : T) :
    matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => rootTransformSymbol z rho sigma a u) p v*
      Matrix.diagonal (fun i => (rho i : ℂ)) = 0 := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.zero_apply]
  by_cases hj : rho j = 0
  · simp [hj]
  · rw [actual_root_transform_active_columns_zero z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon u i j (lt_of_le_of_ne (hrho j) (Ne.symm hj)), zero_mul]

/-- Once both one-sided weights have been recovered, the first BH
residual eliminates all first-amplitude directions without density inverses. -/
theorem first_BH_recovery_from_one_sided_zero (D Q dD dQ R : Matrix (Fin N) (Fin N) ℂ)
    (hR : R.transpose = R) (hd : dD*R = 0) (hq : dQ*R = 0)
    (hf : dD*(1-R*Q.transpose)-D*R*dQ.transpose = 0) : dD = 0 := by
  have ht : R*dQ.transpose = 0 := by
    have he := congrArg Matrix.transpose hq
    simpa only [Matrix.transpose_mul, hR, Matrix.transpose_zero] using he
  calc
    _ = (dD*(1-R*Q.transpose)-D*R*dQ.transpose)+(dD*R)*Q.transpose+D*(R*dQ.transpose) := by noncomm_ring
    _ = 0 := by rw [hf, hd, ht]; simp

/-- Full actual Dt recovery at nonnegative-density canonical roots,
including both tracer rows and tracer columns. -/
theorem actual_first_amplitude_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    : v.1 = 0 := by
  classical
  funext u i j
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
  have hf : matrixDerivative D p v*(1-R*(Q p).transpose)-D p*R*(matrixDerivative Q p v).transpose = 0 := by
    change matrixDerivative D p v*B p+D p*(-(R*(matrixDerivative Q p v).transpose)) = 0 at hd
    dsimp only [B] at hd
    linear_combination (norm := noncomm_ring) hd
  have hdr : matrixDerivative D p v*R = 0 := by
    rw [dt_symbol_matrix_derivative]
    ext i j
    have he := congrFun (congrFun (actual_first_amplitude_weighted_zero z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon u) i) j
    simp only [R, Matrix.mul_diagonal, Matrix.of_apply, Matrix.zero_apply] at he ⊢
    exact_mod_cast he
  have hqr : matrixDerivative Q p v*R = 0 := actual_root_transform_weighted_columns_zero z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon u
  have hzD := first_BH_recovery_from_one_sided_zero (D p) (Q p) (matrixDerivative D p v) (matrixDerivative Q p v) R
    (Matrix.diagonal_transpose _) hdr hqr hf
  rw [dt_symbol_matrix_derivative] at hzD
  exact Complex.ofReal_eq_zero.mp (congrFun (congrFun hzD i) j)

/-- The COMPLETE actual BH amplitude Jacobian kernel is zero at a
canonical root with nonnegative densities, allowing arbitrary tracers. -/
theorem actual_amplitude_kernel_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    : v = 0 := Prod.ext (actual_first_amplitude_zero z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon) (actual_second_amplitude_zero z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon)

/-- Actual Jacobian injectivity for nonnegative densities; no positive
lower density bound or supplied inverse is required. -/
theorem actual_amplitude_jacobian_injective
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    : Function.Injective (amplitudeJacobian z rho sigma K t p) := by
  intro v w he
  have hzero : amplitudeJacobian z rho sigma K t p (v-w) = 0 := by rw [map_sub, he, sub_self]
  exact sub_eq_zero.mp (actual_amplitude_kernel_zero z hz rho sigma hsigma hrho K hK t p (v-w) hzero hv hroot hcanon)

/-- Finite-dimensional actual Jacobian bijectivity including all tracers. -/
theorem actual_amplitude_jacobian_bijective
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    : Function.Bijective (amplitudeJacobian z rho sigma K t p) := by
  have hi := actual_amplitude_jacobian_injective z hz rho sigma hsigma hrho K hK t p hv hroot hcanon
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

/-- General nonnegative-density canonical-to-Jacobian bridge, in the EXACT
frozen local-branch residual-partial interface, including zero-density species. -/
theorem actual_residual_partial_isInvertible
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p : TailMatrix T N × TailMatrix T N)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    : ((fderiv ℝ (FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K) (t,p)).comp
      (ContinuousLinearMap.inr ℝ ℝ (TailMatrix T N × TailMatrix T N))).IsInvertible := by
  let L := amplitudeJacobian z rho sigma K t p
  have hb : Function.Bijective L := actual_amplitude_jacobian_bijective z hz rho sigma hsigma hrho K hK t p hv hroot hcanon
  have hk : L.ker = ⊥ := LinearMap.ker_eq_bot.mpr hb.1
  have hr : L.range = ⊤ := LinearMap.range_eq_top.mpr hb.2
  exact ⟨ContinuousLinearEquiv.ofBijective L hk hr, ContinuousLinearEquiv.coe_ofBijective L hk hr⟩

end FMSA.Convergence.ActualTracerAmplitudeRecovery

/-- info: 'FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_completed_J_derivative_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_completed_J_derivative_zero

/-- info: 'FMSA.Convergence.ActualTracerAmplitudeRecovery.second_BH_recovery_from_completed_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerAmplitudeRecovery.second_BH_recovery_from_completed_derivative

/-- info: 'FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_second_amplitude_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_second_amplitude_zero

/-- info: 'FMSA.Convergence.ActualTracerAmplitudeRecovery.root_transform_column_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerAmplitudeRecovery.root_transform_column_local

/-- info: 'FMSA.Convergence.ActualTracerAmplitudeRecovery.column_projection_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerAmplitudeRecovery.column_projection_apply

/-- info: 'FMSA.Convergence.ActualTracerAmplitudeRecovery.root_transform_column_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerAmplitudeRecovery.root_transform_column_factorization

/-- info: 'FMSA.Convergence.ActualTracerAmplitudeRecovery.root_transform_column_derivative_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerAmplitudeRecovery.root_transform_column_derivative_zero

/-- info: 'FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_root_transform_active_columns_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_root_transform_active_columns_zero

/-- info: 'FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_root_transform_weighted_columns_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_root_transform_weighted_columns_zero

/-- info: 'FMSA.Convergence.ActualTracerAmplitudeRecovery.first_BH_recovery_from_one_sided_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerAmplitudeRecovery.first_BH_recovery_from_one_sided_zero

/-- info: 'FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_first_amplitude_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_first_amplitude_zero

/-- info: 'FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_amplitude_kernel_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_amplitude_kernel_zero

/-- info: 'FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_amplitude_jacobian_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_amplitude_jacobian_injective

/-- info: 'FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_amplitude_jacobian_bijective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_amplitude_jacobian_bijective

/-- info: 'FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_residual_partial_isInvertible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_residual_partial_isInvertible
