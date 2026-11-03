import MSAConvergence.ActualReciprocityTangent
import MSAConvergence.FiniteTangentOZ
import MSAConvergence.RadialDCFTangent

/-! Actual radial tangent OZ from genuine finite phase/source variations.
No derivative of a root-only OZ identity is assumed. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators ContDiff ComplexOrder
namespace FMSA.Convergence.ActualRadialTangentOZ
open FMSA.Paper FMSA.Paper.JacobianExterior FMSA.Paper.RadialVariationL2
open FMSA.ExactMSA.MultiTailMixture MSAMixture FMSA.MatrixQ0
open FMSA.Convergence.SymplecticTangent FMSA.Convergence.FiniteTangentOZ
open FMSA.Convergence.ActualReciprocityTangent FMSA.Convergence.ActualSourceBoundary
open FMSA.Convergence.ComplexWronskianJets FMSA.Convergence.ActualLaplaceJets
open FMSA.Convergence.ActualRDFTangent FMSA.Convergence.ActualHRadialL2

variable {N : ℕ} {T : Type*} [Fintype T]

/-- Finite completed source symbol with both actual contact phases. -/
def completedPhase (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  rdfPhase sigma s*completedJSymbol z rho sigma p s*rdfPhase sigma s

/-- The actual transposed finite J source with the fixed contact phases. -/
def sourcePhase (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  rdfPhase sigma s*(nonlinearComplexJ z rho sigma p.1 p.2 s).transpose*rdfPhase sigma s

/-- Finite radial completion; its actual derivative will be identified
with the honest radial h tangent integral, not postulated to equal it. -/
def completedRadial (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (k : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  (Complex.I*k)⁻¹ • (completedPhase z rho sigma p (-(Complex.I*k))-
    completedPhase z rho sigma p (Complex.I*k))

/-- Genuine local amplitude regularity of the finite phased completion. -/
theorem completed_phase_entry_diff
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (s : ℂ) (hre : 0 ≤ s.re)
    (hu : IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    EntryDiff (fun a : TailMatrix T N × TailMatrix T N => completedPhase z rho sigma a s) p :=
  entry_diff_mul _ _ p
    (entry_diff_mul _ _ p (entry_diff_const _ p) (fun i j =>
      (completed_symbol_entry_contDiffAt z hz rho sigma p s hre hu i j).differentiableAt (by simp)))
    (entry_diff_const _ p)

/-- Base and genuine first-order finite renewal at a fixed unit frequency. -/
theorem completed_renewal_first_variation
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (s : ℂ) (hre : 0 ≤ s.re)
    (hu : IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    let A := fun a : TailMatrix T N × TailMatrix T N => 1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s
    let Jf := fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexJ z rho sigma a.1 a.2 s
    let Y := fun a : TailMatrix T N × TailMatrix T N => completedJSymbol z rho sigma a s
    Y p*A p = Jf p ∧ matrixDerivative Y p v*A p+Y p*matrixDerivative A p v = matrixDerivative Jf p v := by
  dsimp only
  let q := fun a : TailMatrix T N × TailMatrix T N => rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s
  let A := fun a : TailMatrix T N × TailMatrix T N => 1-q a
  let Jf := fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexJ z rho sigma a.1 a.2 s
  let Y := fun a : TailMatrix T N × TailMatrix T N => completedJSymbol z rho sigma a s
  have hq : EntryDiff q p := fun i j =>
    (kernel_laplace_closed_right_contDiff z hz rho sigma s hre i j).differentiable (by simp) p
  have hdA : matrixDerivative A p v = -matrixDerivative q p v := by
    rw [show A = fun a => 1-q a from rfl, matrix_derivative_sub _ _ p v (entry_diff_const _ p) hq,
      matrix_derivative_const, zero_sub]
  have hdq : matrixDerivative q p v =
      rdfMatrixLaplace (fun r => Matrix.of (fun i j => kernelVariation z rho sigma p v i j r)) s := by
    ext i j
    exact (kernel_variation_laplace_fderiv_closed_right z hz rho sigma p v s hre i j).symm
  have hdJ : matrixDerivative Jf p v = jVariation z rho sigma p v s := rfl
  have hdY := completed_symbol_matrix_derivative z hz rho sigma p v s hre hu
  have huD : IsUnit (A p).det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  refine ⟨?_, ?_⟩
  · change (Jf p*(A p)⁻¹)*A p = Jf p
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ huD, Matrix.mul_one]
  · change matrixDerivative Y p v*A p+Y p*matrixDerivative A p v = matrixDerivative Jf p v
    change matrixDerivative Y p v = (jVariation z rho sigma p v s+Y p*
      rdfMatrixLaplace (fun r => Matrix.of (fun i j => kernelVariation z rho sigma p v i j r)) s)*(A p)⁻¹ at hdY
    rw [hdY, ← hdq, ← hdJ, hdA, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ huD, Matrix.mul_one]
    noncomm_ring

/-- Actual completed phase transfer has zero value and first variation
along a true BH kernel vector. Only the factor-phase identity is used
off root; completed-symbol reciprocity is used at the base and tangent. -/
theorem actual_kernel_phase_transfer_vanishing
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0) (k : ℝ) (hk : k ≠ 0)
    (hu : IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) (Complex.I*k))) :
    VanishingVariation (fun a : TailMatrix T N × TailMatrix T N =>
      (1-(nonlinearActualFourierQ z rho sigma a.1 a.2 k).transpose*Matrix.diagonal (fun i => (rho i : ℂ)))*
        completedPhase z rho sigma a (Complex.I*k)-sourcePhase z rho sigma a (Complex.I*k)) p v := by
  classical
  let s : ℂ := Complex.I*k
  have hs : s ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)
  have hre : 0 ≤ s.re := by simp [s]
  let A := fun a : TailMatrix T N × TailMatrix T N => 1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma a.1 a.2) s
  let Jf := fun a : TailMatrix T N × TailMatrix T N => nonlinearComplexJ z rho sigma a.1 a.2 s
  let Y := fun a : TailMatrix T N × TailMatrix T N => completedJSymbol z rho sigma a s
  have hA : EntryDiff A p := entry_diff_sub _ _ p (entry_diff_const _ p) (fun i j =>
    (kernel_laplace_closed_right_contDiff z hz rho sigma s hre i j).differentiable (by simp) p)
  have hJ : EntryDiff Jf p := fun i j => (complexJ_entry_contDiff z rho sigma s i j).differentiable (by simp) p
  have hY : EntryDiff Y p := fun i j =>
    (completed_symbol_entry_contDiffAt z hz rho sigma p s hre hu i j).differentiableAt (by simp)
  obtain ⟨hYA, hdYA⟩ := completed_renewal_first_variation z hz rho sigma p v s hre hu
  obtain ⟨hy, hdy⟩ := actual_kernel_completed_symbol_reciprocity z hz rho sigma hsigma K hK hv t p v hroot hjac s hs (by simp [s]) hu
  have inner : VanishingVariation (fun a => (A a).transpose*Y a-(Jf a).transpose) p v := by
    refine ⟨entry_diff_sub _ _ p (entry_diff_mul _ _ p (entry_diff_transpose _ p hA) hY) (entry_diff_transpose _ p hJ), ?_, ?_⟩
    · have he := congrArg Matrix.transpose hYA
      simp only [Matrix.transpose_mul, hy] at he
      exact sub_eq_zero.mpr he
    · rw [matrix_derivative_sub _ _ p v (entry_diff_mul _ _ p (entry_diff_transpose _ p hA) hY) (entry_diff_transpose _ p hJ),
        matrix_derivative_mul _ _ p v (entry_diff_transpose _ p hA) hY, matrix_derivative_transpose, matrix_derivative_transpose]
      have he := congrArg Matrix.transpose hdYA
      simp only [Matrix.transpose_add, Matrix.transpose_mul, hy, hdy] at he
      change (A p).transpose*matrixDerivative Y p v+(matrixDerivative A p v).transpose*Y p = (matrixDerivative Jf p v).transpose at he
      linear_combination (norm := noncomm_ring) he
  have he : (fun a : TailMatrix T N × TailMatrix T N =>
      (1-(nonlinearActualFourierQ z rho sigma a.1 a.2 k).transpose*Matrix.diagonal (fun i => (rho i : ℂ)))*
        completedPhase z rho sigma a s-sourcePhase z rho sigma a s) =
      fun a => rdfPhase sigma s*((A a).transpose*Y a-(Jf a).transpose)*rdfPhase sigma s := by
    funext a
    dsimp only [completedPhase, sourcePhase]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      nonlinear_actual_recentered_factor_phase z rho sigma a.1 a.2 k]
    change (rdfPhase sigma s*(A a).transpose)*Y a*rdfPhase sigma s-
      rdfPhase sigma s*(Jf a).transpose*rdfPhase sigma s = _
    noncomm_ring
  change VanishingVariation _ p v
  rw [he]
  exact vanishing_mul_right _ _ p v
    (vanishing_mul_left _ _ p v (entry_diff_const _ p) inner) (entry_diff_const _ p)

/-- Actual source defect has zero value and genuine kernel variation. -/
theorem actual_kernel_source_vanishing
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0) (k : ℝ) (hk : k ≠ 0) :
    VanishingVariation (fun a : TailMatrix T N × TailMatrix T N => actualSourceDefect z rho sigma a k) p v := by
  refine ⟨(fun i j => (actualSourceDefect_entry_contDiff z rho sigma hz hsigma k hk i j).differentiable (by simp) p), ?_, ?_⟩
  · rw [actualSourceDefect_factorization z rho sigma hz hsigma p k hk]
    obtain ⟨hU, hV⟩ := actual_root_wronskian_values_zero z hz rho sigma K hK hv t p hroot (Complex.I*k)
      (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)) (by simp)
    rw [hU, hV]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  · ext i j
    exact actual_kernel_sourceDefect_fderiv_zero z rho sigma K hK hz hsigma hv t p v hroot hjac k hk i j

/-- Actual C(k)-C(-k) has zero value and genuine kernel variation,
obtained from the all-amplitude sum of the two source defects. -/
theorem actual_kernel_fourierC_even_vanishing
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0) (k : ℝ) (hk : k ≠ 0) :
    VanishingVariation (fun a : TailMatrix T N × TailMatrix T N =>
      nonlinearActualFourierC z rho sigma a.1 a.2 k-nonlinearActualFourierC z rho sigma a.1 a.2 (-k)) p v := by
  classical
  have hs : Complex.I*(k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)
  have hp := actual_kernel_source_vanishing z hz rho sigma hsigma K hK hv t p v hroot hjac k hk
  have hm := actual_kernel_source_vanishing z hz rho sigma hsigma K hK hv t p v hroot hjac (-k) (neg_ne_zero.mpr hk)
  have he : (fun a : TailMatrix T N × TailMatrix T N =>
      nonlinearActualFourierC z rho sigma a.1 a.2 k-nonlinearActualFourierC z rho sigma a.1 a.2 (-k)) =
      fun a => -(Complex.I*(k : ℂ))⁻¹ • (actualSourceDefect z rho sigma a k+actualSourceDefect z rho sigma a (-k)) := by
    funext a
    rw [actualSourceDefect_sum, ← nonlinearActualFourierC_neg_transpose, smul_smul]
    simp only [neg_mul, inv_mul_cancel₀ hs, neg_smul, one_smul, neg_sub]
  rw [he]
  exact vanishing_smul _ _ p v (vanishing_add _ _ p v hp hm)


/-- The finite radial completion is genuinely locally differentiable
at the two canonical Fourier frequencies, with no nearby root family. -/
theorem completed_radial_entry_diff
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (k : ℝ)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    EntryDiff (fun a : TailMatrix T N × TailMatrix T N => completedRadial z rho sigma a k) p :=
  entry_diff_smul _ _ p (entry_diff_sub _ _ p
    (completed_phase_entry_diff z hz rho sigma p (-(Complex.I*k)) (by simp) (hcanon _ (by simp)))
    (completed_phase_entry_diff z hz rho sigma p (Complex.I*k) (by simp) (hcanon _ (by simp))))

/-- Actual source, reciprocity and evenness first variations imply BOTH
base finite OZ and its genuine ordered tangent equation. The finite h
completion is used here; actual radial integrals are identified below. -/
theorem actual_kernel_completed_OZ
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) (k : ℝ) (hk : k ≠ 0) :
    let Cf := fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierC z rho sigma a.1 a.2 k
    let H := fun a : TailMatrix T N × TailMatrix T N => completedRadial z rho sigma a k
    let R := Matrix.diagonal (fun i => (rho i : ℂ))
    (1-Cf p*R)*H p = Cf p ∧
    (1-Cf p*R)*matrixDerivative H p v = matrixDerivative Cf p v+matrixDerivative Cf p v*R*H p := by
  classical
  let s : ℂ := Complex.I*k
  let R := Matrix.diagonal (fun i => (rho i : ℂ))
  let Qp := fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierQ z rho sigma a.1 a.2 k
  let Qm := fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierQ z rho sigma a.1 a.2 (-k)
  let Cf := fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierC z rho sigma a.1 a.2 k
  let Cm := fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierC z rho sigma a.1 a.2 (-k)
  let Ep := fun a : TailMatrix T N × TailMatrix T N => completedPhase z rho sigma a s
  let Em := fun a : TailMatrix T N × TailMatrix T N => completedPhase z rho sigma a (-s)
  let Bp := fun a : TailMatrix T N × TailMatrix T N => sourcePhase z rho sigma a s
  let Bm := fun a : TailMatrix T N × TailMatrix T N => sourcePhase z rho sigma a (-s)
  let H := fun a : TailMatrix T N × TailMatrix T N => completedRadial z rho sigma a k
  have hQp : EntryDiff Qp p := fun i j => (actualFourierQ_entry_contDiff z rho sigma hz hsigma k hk i j).differentiable (by simp) p
  have hQm : EntryDiff Qm p := fun i j => (actualFourierQ_entry_contDiff z rho sigma hz hsigma (-k) (neg_ne_zero.mpr hk) i j).differentiable (by simp) p
  have hEp : EntryDiff Ep p := completed_phase_entry_diff z hz rho sigma p s (by simp [s]) (hcanon _ (by simp [s]))
  have hp : VanishingVariation (fun a => (1-(Qp a).transpose*R)*Ep a-Bp a) p v :=
    actual_kernel_phase_transfer_vanishing z hz rho sigma hsigma K hK hv t p v hroot hjac k hk (hcanon _ (by simp))
  have hm : VanishingVariation (fun a => (1-(Qm a).transpose*R)*Em a-Bm a) p v := by
    simpa only [Qm, Em, Bm, s, Complex.ofReal_neg, mul_neg] using
      actual_kernel_phase_transfer_vanishing z hz rho sigma hsigma K hK hv t p v hroot hjac (-k) (neg_ne_zero.mpr hk) (hcanon _ (by simp))
  have hsource : VanishingVariation (fun a => (1-Qp a*R)*Bm a-(1-Qm a*R)*Bp a-s • Cf a) p v :=
    actual_kernel_source_vanishing z hz rho sigma hsigma K hK hv t p v hroot hjac k hk
  have heven : VanishingVariation (fun a => Cf a-Cm a) p v :=
    actual_kernel_fourierC_even_vanishing z hz rho sigma hsigma K hK hv t p v hroot hjac k hk
  have hC (a : TailMatrix T N × TailMatrix T N) : Cf a = Qp a+(Qm a).transpose-Qp a*R*(Qm a).transpose :=
    nonlinearActualFourierC_eq_Q_product z rho sigma a.1 a.2 k
  have hCm (a : TailMatrix T N × TailMatrix T N) : Cm a = Qm a+(Qp a).transpose-Qm a*R*(Qp a).transpose := by
    simpa only [neg_neg] using nonlinearActualFourierC_eq_Q_product z rho sigma a.1 a.2 (-k)
  have hres := phase_source_OZ_vanishing Qp Qm Cf Cm Ep Em Bp Bm R s p v hQp hQm hEp hC hCm hp hm hsource heven
  have hn : VanishingVariation (fun a => (1-Cf a*R)*H a-Cf a) p v :=
    normalized_OZ_vanishing Cf (fun a => Em a-Ep a) R s
      (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)) p v hres
  exact OZ_value_and_variation Cf H R p v
    (fun i j => (actualFourierC_entry_contDiff z rho sigma hz hsigma k hk i j).differentiable (by simp) p)
    (completed_radial_entry_diff z hz rho sigma p k hcanon) hn


/-- The genuine finite phased-symbol derivative retains both fixed phases. -/
theorem completed_phase_matrix_derivative
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (s : ℂ) (hre : 0 ≤ s.re)
    (hu : IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => completedPhase z rho sigma a s) p v =
      rdfPhase sigma s*matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => completedJSymbol z rho sigma a s) p v*rdfPhase sigma s := by
  have hY : EntryDiff (fun a : TailMatrix T N × TailMatrix T N => completedJSymbol z rho sigma a s) p :=
    fun i j => (completed_symbol_entry_contDiffAt z hz rho sigma p s hre hu i j).differentiableAt (by simp)
  unfold completedPhase
  rw [matrix_derivative_mul_const _ _ p v (entry_diff_mul _ _ p (entry_diff_const _ p) hY),
    matrix_derivative_const_mul _ _ p v hY]

/-- The actual positive-radius h tangent integral is the real finite
phased-symbol derivative divided by 2*pi at each nonzero closed-right
frequency. No whole-h amplitude-integral derivative is assumed. -/
theorem actual_h_laplace_phase_derivative
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (s : ℂ) (hs : s ≠ 0) (hre : 0 ≤ s.re) :
    rdfMatrixLaplace (fun r => Matrix.of (fun i j => r*hVariation z rho sigma p v i j r)) s =
      (2*(π : ℂ))⁻¹ • matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => completedPhase z rho sigma a s) p v := by
  rw [completed_phase_matrix_derivative z hz rho sigma p v s hre (hcanon s hre)]
  exact actual_h_tangent_laplace_completed_derivative z hz rho sigma hsigma hv p v hcanon s hs hre

/-- Honest plus/minus-frequency h integrals have exactly the standard
radial sine normalization, before any finite-symbol substitution. -/
theorem actual_h_radial_laplace_difference
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (k : ℝ) (hk : k ≠ 0) (i j : Fin N) :
    (RadialZeroMode.radialSymbol (hVariation z rho sigma p v i j) k : ℂ) =
      (2*(π : ℂ)/(Complex.I*k))*(
        rdfMatrixLaplace (fun r => Matrix.of (fun a b => r*hVariation z rho sigma p v a b r)) (-(Complex.I*k)) i j-
        rdfMatrixLaplace (fun r => Matrix.of (fun a b => r*hVariation z rho sigma p v a b r)) (Complex.I*k) i j) := by
  let f := fun r : ℝ => r*hVariation z rho sigma p v i j r
  have hp := (FMSA.Convergence.ActualHBoundaryResponse.actual_h_tangent_boundary_phase
    z hz rho sigma hsigma hv p v hcanon (-(Complex.I*k)) (by simp)).1 i j
  have hm := (FMSA.Convergence.ActualHBoundaryResponse.actual_h_tangent_boundary_phase
    z hz rho sigma hsigma hv p v hcanon (Complex.I*k) (by simp)).1 i j
  simp only [neg_neg] at hp
  have he : (∫ r in Ioi (0 : ℝ), (f r : ℂ)*Complex.exp ((Complex.I*k)*r))-
      (∫ r in Ioi (0 : ℝ), (f r : ℂ)*Complex.exp (-(Complex.I*k)*r)) =
      2*Complex.I*Complex.ofReal (∫ r in Ioi (0 : ℝ), f r*sin (k*r)) := by
    rw [← integral_sub hp hm, ← integral_complex_ofReal, ← integral_const_mul]
    apply integral_congr_ae (Eventually.of_forall _)
    intro r
    rw [← mul_sub, complex_axis_exp_difference]
    dsimp only [f]
    push_cast
    ring
  rw [RadialZeroMode.radialSymbol_eq_radial_fourier _ k hk]
  unfold FMSA.HardSphere.radial_fourier
  simp only [rdfMatrixLaplace, Matrix.of_apply, FMSA.causalComplexLaplace, neg_neg]
  change _ = (2*(π : ℂ)/(Complex.I*k))*((∫ r in Ioi (0 : ℝ), (f r : ℂ)*Complex.exp ((Complex.I*k)*r))-
    (∫ r in Ioi (0 : ℝ), (f r : ℂ)*Complex.exp (-(Complex.I*k)*r)))
  rw [he]
  change ((4*π/k*∫ r in Ioi (0 : ℝ), f r*sin (k*r) : ℝ) : ℂ) = _
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hk, Complex.I_ne_zero]
  ring

/-- The honest actual radial h tangent is the genuine derivative of the
finite completion at every nonzero real wave number. This is the actual
spatial-to-finite bridge, not a supplied radial OZ premise. -/
theorem actual_h_radial_completed_derivative
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (k : ℝ) (hk : k ≠ 0) :
    Matrix.of (fun i j => (RadialZeroMode.radialSymbol (hVariation z rho sigma p v i j) k : ℂ)) =
      matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => completedRadial z rho sigma a k) p v := by
  have hs : Complex.I*(k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)
  have hEp := completed_phase_entry_diff z hz rho sigma p (Complex.I*k) (by simp) (hcanon _ (by simp))
  have hEm := completed_phase_entry_diff z hz rho sigma p (-(Complex.I*k)) (by simp) (hcanon _ (by simp))
  rw [show (fun a : TailMatrix T N × TailMatrix T N => completedRadial z rho sigma a k) =
    (fun a => (Complex.I*k)⁻¹ • (completedPhase z rho sigma a (-(Complex.I*k))-completedPhase z rho sigma a (Complex.I*k))) from rfl,
    matrix_derivative_smul _ _ p v (entry_diff_sub _ _ p hEm hEp), matrix_derivative_sub _ _ p v hEm hEp]
  ext i j
  rw [Matrix.of_apply, actual_h_radial_laplace_difference z hz rho sigma hsigma hv p v hcanon k hk i j,
    actual_h_laplace_phase_derivative z hz rho sigma hsigma hv p v hcanon (-(Complex.I*k)) (neg_ne_zero.mpr hs) (by simp),
    actual_h_laplace_phase_derivative z hz rho sigma hsigma hv p v hcanon (Complex.I*k) hs (by simp)]
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  field_simp [hs, Complex.ofReal_ne_zero.mpr pi_ne_zero] <;> ring

/-- The weighted actual base spectral denominator equals the actual
radial DCF denominator, using the root certificate only at its value. -/
theorem actual_weighted_source_denominator
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (p : TailMatrix T N × TailMatrix T N) (hroot : IsRoot z rho sigma K p.1 p.2)
    (k : ℝ) (hk : k ≠ 0) :
    1-Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))*nonlinearActualFourierC z rho sigma p.1 p.2 k*
      Matrix.diagonal (fun i => (sqrt (rho i) : ℂ)) = MatrixOZPairing.radialDenominator z rho sigma K p.1 p.2 k := by
  classical
  unfold MatrixOZPairing.radialDenominator
  congr 1
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  have hc := ActualRadialIdentification.root_radial_fourier z rho sigma K p.1 p.2 hz hsigma hv hroot hK k hk i j
  change nonlinearActualFourierC z rho sigma p.1 p.2 k i j = _ at hc
  rw [hc, RadialZeroMode.radialSymbol_eq_radial_fourier _ k hk]
  ring

/-- Actual density-weighted h tangent equals the weighted derivative of
the finite radial completion. No density is inverted. -/
theorem actual_weighted_h_variation
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (k : ℝ) (hk : k ≠ 0) :
    Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))*
      matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => completedRadial z rho sigma a k) p v*
        Matrix.diagonal (fun i => (sqrt (rho i) : ℂ)) = radialHTangentMatrix z rho sigma p v k := by
  rw [← actual_h_radial_completed_derivative z hz rho sigma hsigma hv p v hcanon k hk]
  ext i j
  simp only [radialHTangentMatrix, densityWeight, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply, Complex.ofReal_mul]
  ring

/-- The genuine actual spectral derivative is the actual ordered radial
DCF tangent symbol for every species pair, retaining the exact weights. -/
theorem actual_weighted_C_variation
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0) (k : ℝ) (hk : k ≠ 0) :
    Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))*
      matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierC z rho sigma a.1 a.2 k) p v*
        Matrix.diagonal (fun i => (sqrt (rho i) : ℂ)) = radialVariationMatrix z rho sigma K p v k := by
  classical
  ext i j
  simp only [radialVariationMatrix, densityWeight, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply, matrixDerivative, Complex.ofReal_mul]
  have hc := FMSA.Convergence.RadialDCFTangent.actual_kernel_fourierC_fderiv_eq_ordered_radial z rho sigma K hK hz hsigma hv t p v hroot hjac i j k hk
  have he : orderedVariation z rho sigma (t • K) p v i j = orderedVariation z rho sigma K p v i j := rfl
  rw [he] at hc
  rw [hc, RadialZeroMode.radialSymbol_eq_radial_fourier _ k hk]
  ring


/-- A unit actual recentered kernel factor gives a unit physical Baxter
factor by phase conjugacy and the finite determinant swap. No species
density is divided, so tracer rows are included. This needs no BH root. -/
theorem physical_fourier_factor_unit_of_kernel_unit
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (hrho : ∀ i, 0 ≤ rho i)
    (p : TailMatrix T N × TailMatrix T N) (k : ℝ)
    (hu : IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) (Complex.I*k))) :
    IsUnit (fourierFactor z rho sigma (amplitudeA z rho sigma p.1 p.2)
      (amplitudeQp z rho sigma p.1 p.2) (W z rho p.1 p.2) (C z rho sigma p.1 p.2) k) := by
  classical
  let S := Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))
  let R := Matrix.diagonal (fun i => (rho i : ℂ))
  let Q := nonlinearActualFourierQ z rho sigma p.1 p.2 k
  let P := rdfPhase sigma (Complex.I*k)
  let A := 1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) (Complex.I*k)
  let F := 1-Q.transpose*R
  have hR : S*S = R := by
    rw [show S = Matrix.diagonal (fun i => (sqrt (rho i) : ℂ)) from rfl, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact_mod_cast mul_self_sqrt (hrho i)
  have hp : IsUnit P := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    dsimp only [P, rdfPhase]
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun _ _ => Complex.exp_ne_zero _))
  have hAT : IsUnit A.transpose := (Matrix.isUnit_iff_isUnit_det _).mpr
    (by simpa only [Matrix.det_transpose] using (Matrix.isUnit_iff_isUnit_det _).mp hu)
  have hphase : F*P = P*A.transpose := nonlinear_actual_recentered_factor_phase z rho sigma p.1 p.2 k
  have hprod : IsUnit (F*P) := hphase.symm ▸ hp.mul hAT
  have hprodD : IsUnit (F.det*P.det) := by
    simpa only [Matrix.det_mul] using (Matrix.isUnit_iff_isUnit_det _).mp hprod
  have hF : IsUnit F := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_left hprodD)
  have hFT : IsUnit F.transpose := (Matrix.isUnit_iff_isUnit_det _).mpr
    (by simpa only [Matrix.det_transpose] using (Matrix.isUnit_iff_isUnit_det _).mp hF)
  have hRQ : IsUnit (1-R*Q) := by
    simpa only [F, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose, R, Matrix.diagonal_transpose] using hFT
  have heF : fourierFactor z rho sigma (amplitudeA z rho sigma p.1 p.2)
      (amplitudeQp z rho sigma p.1 p.2) (W z rho p.1 p.2) (C z rho sigma p.1 p.2) k = 1-S*Q*S := by
    unfold fourierFactor
    congr 1
    ext i j
    simp only [S, Q, nonlinearActualFourierQ, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
    ring
  rw [heF]
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_one_sub_mul_comm (S*Q) S, ← Matrix.mul_assoc, hR]
  exact (Matrix.isUnit_iff_isUnit_det _).mp hRQ

/-- Full actual radial tangent OZ at nonzero physical wave number. The
actual radial h/DCF integrals are the symbols in this equation, not
caller-supplied fields. Physical factor units are derived from the
base-point canonicity, including zero-density species. -/
theorem actual_radial_tangent_OZ
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hv : vacMix rho sigma ≠ 0) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (k : ℝ) (hk : k ≠ 0) :
    radialHTangentMatrix z rho sigma p v k =
      MatrixOZPairing.structureMatrix z rho sigma (t • K) p.1 p.2 k*
        radialVariationMatrix z rho sigma K p v k*
          MatrixOZPairing.structureMatrix z rho sigma (t • K) p.1 p.2 k := by
  classical
  let S := Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))
  let R := Matrix.diagonal (fun i => (rho i : ℂ))
  let Cf := fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierC z rho sigma a.1 a.2 k
  let H := fun a : TailMatrix T N × TailMatrix T N => completedRadial z rho sigma a k
  have hscaled : ∀ u i j, (t • K) u i j = (t • K) u j i := by
    intro u i j
    simp only [Pi.smul_apply, smul_eq_mul, hK u i j]
  have hR : S*S = R := by
    rw [show S = Matrix.diagonal (fun i => (sqrt (rho i) : ℂ)) from rfl, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact_mod_cast mul_self_sqrt (hrho i)
  have hden : 1-S*Cf p*S = MatrixOZPairing.radialDenominator z rho sigma (t • K) p.1 p.2 k :=
    actual_weighted_source_denominator z hz rho sigma hsigma hv (t • K) hscaled p hroot k hk
  have hF := physical_fourier_factor_unit_of_kernel_unit z rho sigma hrho p k (hcanon _ (by simp))
  have hu : IsUnit (1-S*Cf p*S) := by
    rw [hden]
    exact (MatrixOZPairing.actual_radial_denominator_posDef z hz rho sigma (t • K) p.1 p.2 hrho hsigma hv hroot hscaled k hF).isUnit
  obtain ⟨hb, hd⟩ := actual_kernel_completed_OZ z hz rho sigma (fun i => (hsigma i).le) K hK hv t p v hroot hjac hcanon k hk
  have ans := weighted_OZ_solution (Cf p) (H p) (matrixDerivative Cf p v) (matrixDerivative H p v) S R hR hu hb hd
  have hwH : S*matrixDerivative H p v*S = radialHTangentMatrix z rho sigma p v k :=
    actual_weighted_h_variation z hz rho sigma hsigma hv p v hcanon k hk
  have hwC : S*matrixDerivative Cf p v*S = radialVariationMatrix z rho sigma K p v k :=
    actual_weighted_C_variation z hz rho sigma hsigma K hK hv t p v hroot hjac k hk
  rw [hwH, hwC, hden] at ans
  exact ans

/-- Actual active-pair DCF cancellation with the radial tangent OZ
premise discharged internally. Full base canonicity supplies the
physical Fourier factor units; no independent factor-unit premise. -/
theorem actual_kernel_DCF_ae_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    ∀ i j, 0 < rho i → 0 < rho j → orderedVariation z rho sigma K p v i j =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  have hF := fun k => physical_fourier_factor_unit_of_kernel_unit z rho sigma hrho p k (hcanon _ (by simp))
  apply actual_kernel_DCF_ae_zero_of_radial_tangent_OZ z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon hF
  filter_upwards [show ∀ᵐ w : ℝ ∂volume, w ≠ 0 from volume.ae_ne 0] with w hw
  exact actual_radial_tangent_OZ z hz rho sigma hsigma hrho K hK hv t p v hroot hjac hcanon (2*π*w)
    (mul_ne_zero (mul_ne_zero (by norm_num) pi_ne_zero) hw)

end FMSA.Convergence.ActualRadialTangentOZ

/-- info: 'FMSA.Convergence.ActualRadialTangentOZ.completed_phase_entry_diff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRadialTangentOZ.completed_phase_entry_diff

/-- info: 'FMSA.Convergence.ActualRadialTangentOZ.completed_renewal_first_variation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRadialTangentOZ.completed_renewal_first_variation

/-- info: 'FMSA.Convergence.ActualRadialTangentOZ.actual_kernel_phase_transfer_vanishing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRadialTangentOZ.actual_kernel_phase_transfer_vanishing

/-- info: 'FMSA.Convergence.ActualRadialTangentOZ.actual_kernel_source_vanishing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRadialTangentOZ.actual_kernel_source_vanishing

/-- info: 'FMSA.Convergence.ActualRadialTangentOZ.actual_kernel_fourierC_even_vanishing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRadialTangentOZ.actual_kernel_fourierC_even_vanishing

/-- info: 'FMSA.Convergence.ActualRadialTangentOZ.completed_radial_entry_diff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRadialTangentOZ.completed_radial_entry_diff

/-- info: 'FMSA.Convergence.ActualRadialTangentOZ.actual_kernel_completed_OZ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRadialTangentOZ.actual_kernel_completed_OZ

/-- info: 'FMSA.Convergence.ActualRadialTangentOZ.completed_phase_matrix_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRadialTangentOZ.completed_phase_matrix_derivative

/-- info: 'FMSA.Convergence.ActualRadialTangentOZ.actual_h_laplace_phase_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRadialTangentOZ.actual_h_laplace_phase_derivative

/-- info: 'FMSA.Convergence.ActualRadialTangentOZ.actual_h_radial_laplace_difference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRadialTangentOZ.actual_h_radial_laplace_difference

/-- info: 'FMSA.Convergence.ActualRadialTangentOZ.actual_h_radial_completed_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRadialTangentOZ.actual_h_radial_completed_derivative

/-- info: 'FMSA.Convergence.ActualRadialTangentOZ.actual_weighted_source_denominator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRadialTangentOZ.actual_weighted_source_denominator

/-- info: 'FMSA.Convergence.ActualRadialTangentOZ.actual_weighted_h_variation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRadialTangentOZ.actual_weighted_h_variation

/-- info: 'FMSA.Convergence.ActualRadialTangentOZ.actual_weighted_C_variation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRadialTangentOZ.actual_weighted_C_variation

/-- info: 'FMSA.Convergence.ActualRadialTangentOZ.physical_fourier_factor_unit_of_kernel_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRadialTangentOZ.physical_fourier_factor_unit_of_kernel_unit

/-- info: 'FMSA.Convergence.ActualRadialTangentOZ.actual_radial_tangent_OZ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRadialTangentOZ.actual_radial_tangent_OZ

/-- info: 'FMSA.Convergence.ActualRadialTangentOZ.actual_kernel_DCF_ae_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualRadialTangentOZ.actual_kernel_DCF_ae_zero
