import MSAConvergence.ActualCanonicalKernelTangent
import MSAConvergence.AdditiveDensityTangentOZ

/-! Actual tracer DCF cancellation through additive density weights,
genuine odd radial L2 fields and two positive Parseval passes. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators FourierTransform ContDiff ComplexOrder
namespace FMSA.Convergence.ActualTracerDCFCancellation
open FMSA.Paper FMSA.Paper.JacobianExterior FMSA.Paper.RadialVariationL2
open FMSA.Paper.MatrixOZParseval
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open FMSA.Convergence.SymplecticTangent FMSA.Convergence.ActualCanonicalKernelTangent
open FMSA.Convergence.ActualRadialTangentOZ FMSA.Convergence.ActualHRadialL2
open FMSA.Convergence.ActualRDFTangent FMSA.Convergence.AdditiveDensityTangentOZ

variable {N : ℕ} {T : Type*} [Fintype T]

/-- Constant entry weights retain the actual DCF odd radial representative. -/
def cField
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (K : TailMatrix T N) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (w : Fin N → Fin N → ℝ) : MatrixL2 ℝ N := fun i j =>
  ((kernel_oddVariation_memLp z hz rho sigma (fun i => (hsigma i).le) K t p v hjac i j 2).const_mul
    (w i j : ℂ)).toLp (fun r => (w i j : ℂ)*oddVariation z rho sigma K p v i j r)

/-- Constant entry weights retain the genuine constructed h odd radial field. -/
def hField
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (w : Fin N → Fin N → ℝ) : MatrixL2 ℝ N := fun i j =>
  ((actual_odd_h_tangent_memLp_two z hz rho sigma (fun i => (hsigma i).le) hv p v hcanon i j
    (by unfold edgeHi; linarith [hsigma i, hsigma j])).const_mul (w i j : ℂ)).toLp
      (fun r => (w i j : ℂ)*oddHTangent z rho sigma p v i j r)

/-- Exact a.e. representative for the arbitrarily weighted actual c field. -/
theorem c_field_coe
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (K : TailMatrix T N) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (w : Fin N → Fin N → ℝ) (i j : Fin N) :
    (cField z hz rho sigma hsigma K t p v hjac w i j : ℝ → ℂ) =ᵐ[volume]
      fun r => (w i j : ℂ)*oddVariation z rho sigma K p v i j r := MemLp.coeFn_toLp _

/-- Exact a.e. representative for the arbitrarily weighted genuine h field. -/
theorem h_field_coe
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (w : Fin N → Fin N → ℝ) (i j : Fin N) :
    (hField z hz rho sigma hsigma hv p v hcanon w i j : ℝ → ℂ) =ᵐ[volume]
      fun r => (w i j : ℂ)*oddHTangent z rho sigma p v i j r := MemLp.coeFn_toLp _

/-- Honest Fourier integration commutes with any constant complex weight. -/
theorem fourier_constant_mul (f : ℝ → ℂ) (a : ℂ) (w : ℝ) :
    𝓕 (fun r => a*f r) w = a*𝓕 f w := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun r => by simp only [smul_eq_mul]; ring)

/-- Actual c Fourier representative with its unchanged physical normalization. -/
theorem c_field_fourier
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (K : TailMatrix T N) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (a : Fin N → Fin N → ℝ) (i j : Fin N) :
    ((𝓕 (cField z hz rho sigma hsigma K t p v hjac a i j) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] fun w => (a i j : ℂ)*(-(Complex.I*(w : ℂ))*
        (RadialZeroMode.radialSymbol (orderedVariation z rho sigma K p v i j) (2*π*w) : ℂ)) := by
  have he := FourierL1L2.L2_fourier_ae_integral
    (fun r => (a i j : ℂ)*oddVariation z rho sigma K p v i j r)
    ((kernel_oddVariation_integrable z hz rho sigma (fun i => (hsigma i).le) K t p v hjac i j).const_mul _)
    ((kernel_oddVariation_memLp z hz rho sigma (fun i => (hsigma i).le) K t p v hjac i j 2).const_mul _)
  apply he.trans
  exact ae_of_all _ (fun w => by rw [fourier_constant_mul,
    oddVariation_integral_fourier z hz rho sigma (fun i => (hsigma i).le) K t p v hjac i j w])

/-- Actual h Fourier representative; its L1/L2 hypotheses are internally proved. -/
theorem h_field_fourier
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (a : Fin N → Fin N → ℝ) (i j : Fin N) :
    ((𝓕 (hField z hz rho sigma hsigma hv p v hcanon a i j) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] fun w => (a i j : ℂ)*(-(Complex.I*(w : ℂ))*
        (RadialZeroMode.radialSymbol (hVariation z rho sigma p v i j) (2*π*w) : ℂ)) := by
  have hR : 0 < edgeHi sigma i j := by unfold edgeHi; linarith [hsigma i, hsigma j]
  have he := FourierL1L2.L2_fourier_ae_integral
    (fun r => (a i j : ℂ)*oddHTangent z rho sigma p v i j r)
    ((actual_odd_h_tangent_integrable z hz rho sigma (fun i => (hsigma i).le) hv p v hcanon i j hR).const_mul _)
    ((actual_odd_h_tangent_memLp_two z hz rho sigma (fun i => (hsigma i).le) hv p v hcanon i j hR).const_mul _)
  apply he.trans
  exact ae_of_all _ (fun w => by rw [fourier_constant_mul,
    actual_odd_h_tangent_integral_fourier z hz rho sigma (fun i => (hsigma i).le) hv p v hcanon i j hR w])

/-- Arbitrarily weighted actual radial DCF tangent symbol. -/
def cSymbol (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p v : TailMatrix T N × TailMatrix T N) (a : Fin N → Fin N → ℝ) (k : ℝ) :
    Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j => (a i j : ℂ)*
      (RadialZeroMode.radialSymbol (orderedVariation z rho sigma K p v i j) k : ℂ))

/-- Arbitrarily weighted actual radial h tangent symbol. -/
def hSymbol (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (a : Fin N → Fin N → ℝ) (k : ℝ) :
    Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j => (a i j : ℂ)*
      (RadialZeroMode.radialSymbol (hVariation z rho sigma p v i j) k : ℂ))

/-- The assembled actual c Fourier matrix has the genuine radial symbol. -/
theorem c_field_fourier_matrix
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (K : TailMatrix T N) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (a : Fin N → Fin N → ℝ) :
    fourierMatrix (cField z hz rho sigma hsigma K t p v hjac a) =ᵐ[volume]
      fun w => -(Complex.I*(w : ℂ)) • cSymbol z rho sigma K p v a (2*π*w) := by
  have he := eventually_all.mpr (fun i : Fin N => eventually_all.mpr (fun j : Fin N =>
    c_field_fourier z hz rho sigma hsigma K t p v hjac a i j))
  filter_upwards [he] with w hw
  ext i j
  change _ = -(Complex.I*(w : ℂ))*((a i j : ℂ)*_)
  rw [show fourierMatrix (cField z hz rho sigma hsigma K t p v hjac a) w i j = _ from hw i j]
  ring

/-- The assembled actual h Fourier matrix has the genuine radial symbol. -/
theorem h_field_fourier_matrix
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (a : Fin N → Fin N → ℝ) :
    fourierMatrix (hField z hz rho sigma hsigma hv p v hcanon a) =ᵐ[volume]
      fun w => -(Complex.I*(w : ℂ)) • hSymbol z rho sigma p v a (2*π*w) := by
  have he := eventually_all.mpr (fun i : Fin N => eventually_all.mpr (fun j : Fin N =>
    h_field_fourier z hz rho sigma hsigma hv p v hcanon a i j))
  filter_upwards [he] with w hw
  ext i j
  change _ = -(Complex.I*(w : ℂ))*((a i j : ℂ)*_)
  rw [show fourierMatrix (hField z hz rho sigma hsigma hv p v hcanon a) w i j = _ from hw i j]
  ring

/-- Actual spatial orthogonality holds for every constant entry weight. -/
theorem arbitrary_weight_spatial_pair_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (K : TailMatrix T N) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (a : Fin N → Fin N → ℝ) :
    spatialPair (cField z hz rho sigma hsigma K t p v hjac a)
      (hField z hz rho sigma hsigma hv p v hcanon a) = 0 := by
  apply spatialPair_zero_of_disjoint
  intro i j
  filter_upwards [c_field_coe z hz rho sigma hsigma K t p v hjac a i j,
    h_field_coe z hz rho sigma hsigma hv p v hcanon a i j,
    volume.ae_ne (edgeHi sigma i j), volume.ae_ne (-edgeHi sigma i j)] with r hc hh hr hp
  rw [hc, hh]
  by_cases hr0 : r = 0
  · simp [oddVariation, oddHTangent, FMSA.HardSphere.oddRadialMoment, hr0]
  · have hR : |r| ≠ edgeHi sigma i j := by
      intro he
      rcases le_or_gt 0 r with hpos | hneg
      · rw [abs_of_nonneg hpos] at he; exact hr he
      · rw [abs_of_neg hneg] at he; exact hp (by linarith)
    have hzprod := kernel_pairing_zero_off_contact z hz rho sigma (fun i => (hsigma i).le) K t p v hjac i j |r| (abs_pos.mpr hr0) hR
    have he : (a i j*(r*orderedVariation z rho sigma K p v i j |r|))*
        (a i j*(r*hVariation z rho sigma p v i j |r|)) = 0 := by
      calc
        _ = (a i j)^2*r^2*(orderedVariation z rho sigma K p v i j |r| *hVariation z rho sigma p v i j |r|) := by ring
        _ = 0 := by rw [hzprod, mul_zero]
    simpa only [oddVariation, oddHTangent, FMSA.HardSphere.oddRadialMoment,
      ← Complex.ofReal_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_zero, Pi.zero_apply] using congrArg Complex.ofReal he

/-- Zero of a truly weighted c L2 field recovers the actual radial variation
whenever that particular scalar weight is nonzero. -/
theorem variation_zero_of_field_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (K : TailMatrix T N) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (a : Fin N → Fin N → ℝ) (i j : Fin N) (ha : a i j ≠ 0)
    (hzero : cField z hz rho sigma hsigma K t p v hjac a i j = 0) :
    orderedVariation z rho sigma K p v i j =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  have hc := c_field_coe z hz rho sigma hsigma K t p v hjac a i j
  rw [hzero] at hc
  have he : (fun r => (a i j : ℂ)*oddVariation z rho sigma K p v i j r) =ᵐ[volume] 0 :=
    hc.symm.trans (Lp.coeFn_zero ℂ 2 volume)
  filter_upwards [ae_restrict_of_ae he, ae_restrict_mem measurableSet_Ioi] with r hr hs
  change 0 < r at hs
  change (a i j : ℂ)*oddVariation z rho sigma K p v i j r = 0 at hr
  simp only [oddVariation, FMSA.HardSphere.oddRadialMoment, abs_of_pos hs] at hr
  have heq : a i j*(r*orderedVariation z rho sigma K p v i j r) = 0 := by exact_mod_cast hr
  exact (mul_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left ha)).resolve_left hs.ne'

/-- Reusable actual Parseval cancellation with an arbitrary constant entry
weight and a genuinely proved positive radial OZ sandwich. -/
theorem field_zero_of_positive_radial_OZ
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (K : TailMatrix T N) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (a : Fin N → Fin N → ℝ) (A : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (hpos : ∀ k, (A k).PosDef)
    (hOZ : ∀ k : ℝ, k ≠ 0 → hSymbol z rho sigma p v a k = A k*cSymbol z rho sigma K p v a k*A k) :
    ∀ i j, cField z hz rho sigma hsigma K t p v hjac a i j = 0 := by
  apply positive_OZ_pairing_injective (fun w => A (2*π*w))
    (cField z hz rho sigma hsigma K t p v hjac a)
    (hField z hz rho sigma hsigma hv p v hcanon a)
    (ae_of_all _ (fun w => hpos (2*π*w))) _
    (arbitrary_weight_spatial_pair_zero z hz rho sigma hsigma K t p v hjac hv hcanon a)
  filter_upwards [c_field_fourier_matrix z hz rho sigma hsigma K t p v hjac a,
    h_field_fourier_matrix z hz rho sigma hsigma hv p v hcanon a, volume.ae_ne (0 : ℝ)] with w hc hh hw
  rw [hc, hh, hOZ (2*π*w) (mul_ne_zero (mul_ne_zero (by norm_num) pi_ne_zero) hw)]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- Additive square-root density weights retain all active/tracer cross pairs. -/
def additiveWeight (rho : Fin N → ℝ) (i j : Fin N) : ℝ := sqrt (rho i)+sqrt (rho j)

/-- Exact additive weighting for the actual radial c symbol. -/
theorem c_symbol_additive (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (p v : TailMatrix T N × TailMatrix T N) (k : ℝ) :
    cSymbol z rho sigma K p v (additiveWeight rho) k =
      cSymbol z rho sigma K p v (fun _ _ => 1) k*Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))+
        Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))*cSymbol z rho sigma K p v (fun _ _ => 1) k := by
  ext i j
  simp only [cSymbol, additiveWeight, Matrix.of_apply, Matrix.add_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Complex.ofReal_add, Complex.ofReal_one, one_mul]
  ring

/-- Exact additive weighting for the genuine radial h symbol. -/
theorem h_symbol_additive (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (k : ℝ) :
    hSymbol z rho sigma p v (additiveWeight rho) k =
      hSymbol z rho sigma p v (fun _ _ => 1) k*Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))+
        Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))*hSymbol z rho sigma p v (fun _ _ => 1) k := by
  ext i j
  simp only [hSymbol, additiveWeight, Matrix.of_apply, Matrix.add_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Complex.ofReal_add, Complex.ofReal_one, one_mul]
  ring

/-- The UNWEIGHTED true radial c symbol equals the actual spectral derivative. -/
theorem actual_c_symbol_derivative
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (k : ℝ) (hk : k ≠ 0) :
    cSymbol z rho sigma K p v (fun _ _ => 1) k =
      matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierC z rho sigma a.1 a.2 k) p v := by
  ext i j
  simp only [cSymbol, Matrix.of_apply, Complex.ofReal_one, one_mul, matrixDerivative]
  have he := FMSA.Convergence.RadialDCFTangent.actual_kernel_fourierC_fderiv_eq_ordered_radial
    z rho sigma K hK hz hsigma hv t p v hroot hjac i j k hk
  rw [RadialZeroMode.radialSymbol_eq_radial_fourier _ k hk]
  exact he.symm

/-- The UNWEIGHTED genuine radial h symbol equals the existing completion derivative. -/
theorem actual_h_symbol_derivative
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (k : ℝ) (hk : k ≠ 0) :
    hSymbol z rho sigma p v (fun _ _ => 1) k =
      matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => completedRadial z rho sigma a k) p v := by
  simpa only [hSymbol, Complex.ofReal_one, one_mul] using
    actual_h_radial_completed_derivative z hz rho sigma hsigma hv p v hcanon k hk

/-- Full base canonicity internally supplies the genuine positive physical denominator. -/
theorem actual_denominator_positive
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (k : ℝ) : (MatrixOZPairing.radialDenominator z rho sigma (t • K) p.1 p.2 k).PosDef := by
  have hscaled : ∀ u i j, (t • K) u i j = (t • K) u j i := by
    intro u i j
    simp only [Pi.smul_apply, smul_eq_mul, hK u i j]
  exact MatrixOZPairing.actual_radial_denominator_posDef z hz rho sigma (t • K) p.1 p.2
    hrho hsigma hv hroot hscaled k
    (physical_fourier_factor_unit_of_kernel_unit z rho sigma hrho p k (hcanon _ (by simp)))

/-- Actual additive-density radial tangent OZ, with the prior double-weight
cancellation discharged internally, including zero-density species. -/
theorem actual_additive_radial_tangent_OZ
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (k : ℝ) (hk : k ≠ 0) :
    hSymbol z rho sigma p v (additiveWeight rho) k =
      MatrixOZPairing.structureMatrix z rho sigma (t • K) p.1 p.2 k*
        cSymbol z rho sigma K p v (additiveWeight rho) k*
          MatrixOZPairing.structureMatrix z rho sigma (t • K) p.1 p.2 k := by
  let S := Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))
  let R := Matrix.diagonal (fun i => (rho i : ℂ))
  let Cf := fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierC z rho sigma a.1 a.2 k
  let H := fun a : TailMatrix T N × TailMatrix T N => completedRadial z rho sigma a k
  have hR : S*S = R := by
    rw [show S = Matrix.diagonal (fun i => (sqrt (rho i) : ℂ)) from rfl, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact_mod_cast mul_self_sqrt (hrho i)
  have hscaled : ∀ u i j, (t • K) u i j = (t • K) u j i := by
    intro u i j
    simp only [Pi.smul_apply, smul_eq_mul, hK u i j]
  have hden : 1-S*Cf p*S = MatrixOZPairing.radialDenominator z rho sigma (t • K) p.1 p.2 k :=
    actual_weighted_source_denominator z hz rho sigma hsigma hv (t • K) hscaled p hroot k hk
  have hu : IsUnit (1-S*Cf p*S) := by
    rw [hden]
    exact (actual_denominator_positive z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon k).isUnit
  obtain ⟨hb, hd⟩ := actual_kernel_completed_OZ z hz rho sigma (fun i => (hsigma i).le) K hK hv t p v hroot hjac hcanon k hk
  have hzC : S*matrixDerivative Cf p v*S = 0 :=
    actual_weighted_C_derivative_zero z hz rho sigma hsigma hrho K hK t p v hv hroot hjac hcanon k hk
  have he := additive_weighted_tangent_solution (Cf p) (H p) (matrixDerivative Cf p v) (matrixDerivative H p v) S R hR hu hb hd hzC
  rw [h_symbol_additive, c_symbol_additive,
    actual_c_symbol_derivative z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon k hk,
    actual_h_symbol_derivative z hz rho sigma hsigma hv p v hcanon k hk]
  rw [hden] at he
  exact he

/-- The genuine additive-weighted actual c L2 field is zero, recovering
all cross tracer/active pairs through the physical positive structure. -/
theorem actual_additive_c_field_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    : ∀ i j, cField z hz rho sigma hsigma K t p v hjac (additiveWeight rho) i j = 0 := by
  apply field_zero_of_positive_radial_OZ z hz rho sigma hsigma K t p v hjac hv hcanon
    (additiveWeight rho) (MatrixOZPairing.structureMatrix z rho sigma (t • K) p.1 p.2)
    (fun k => (actual_denominator_positive z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon k).inv)
  exact actual_additive_radial_tangent_OZ z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon

/-- All actual additive radial c symbols vanish, with no frequency restriction. -/
theorem actual_additive_c_symbol_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (k : ℝ) : cSymbol z rho sigma K p v (additiveWeight rho) k = 0 := by
  have hzero := actual_additive_c_field_zero z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon
  ext i j
  simp only [cSymbol, Matrix.of_apply, Matrix.zero_apply]
  by_cases ha : additiveWeight rho i j = 0
  · simp only [ha, Complex.ofReal_zero, zero_mul]
  · have hvz := variation_zero_of_field_zero z hz rho sigma hsigma K t p v hjac (additiveWeight rho) i j ha (hzero i j)
    rw [radialSymbol_zero_of_ae_zero _ hvz k, Complex.ofReal_zero, mul_zero]

/-- The two one-sided actual C derivative weights vanish SEPARATELY.
This is stronger than a formal cancellation of their sum. -/
theorem actual_C_one_sided_derivatives_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (k : ℝ) (hk : k ≠ 0) :
    let dC := matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierC z rho sigma a.1 a.2 k) p v
    let S := Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))
    dC*S = 0 ∧ S*dC = 0 := by
  have he := actual_additive_c_symbol_zero z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon k
  rw [c_symbol_additive, actual_c_symbol_derivative z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon k hk] at he
  exact additive_zero_split (fun i => sqrt (rho i)) (fun i => sqrt_nonneg _) _ he

/-- The remaining unweighted true radial tangent OZ is h=c, including
the double-tracer block, after separately vanishing both one-sided weights. -/
theorem actual_unweighted_radial_tangent_eq
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (k : ℝ) (hk : k ≠ 0) :
    hSymbol z rho sigma p v (fun _ _ => 1) k = cSymbol z rho sigma K p v (fun _ _ => 1) k := by
  let S := Matrix.diagonal (fun i => (sqrt (rho i) : ℂ))
  let R := Matrix.diagonal (fun i => (rho i : ℂ))
  let Cf := fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierC z rho sigma a.1 a.2 k
  let H := fun a : TailMatrix T N × TailMatrix T N => completedRadial z rho sigma a k
  have hR : S*S = R := by
    rw [show S = Matrix.diagonal (fun i => (sqrt (rho i) : ℂ)) from rfl, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact_mod_cast mul_self_sqrt (hrho i)
  have hscaled : ∀ u i j, (t • K) u i j = (t • K) u j i := by
    intro u i j
    simp only [Pi.smul_apply, smul_eq_mul, hK u i j]
  have hden : 1-S*Cf p*S = MatrixOZPairing.radialDenominator z rho sigma (t • K) p.1 p.2 k :=
    actual_weighted_source_denominator z hz rho sigma hsigma hv (t • K) hscaled p hroot k hk
  have hu : IsUnit (1-S*Cf p*S) := by
    rw [hden]
    exact (actual_denominator_positive z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon k).isUnit
  obtain ⟨hb, hd⟩ := actual_kernel_completed_OZ z hz rho sigma (fun i => (hsigma i).le) K hK hv t p v hroot hjac hcanon k hk
  obtain ⟨hr, hl⟩ := actual_C_one_sided_derivatives_zero z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon k hk
  rw [actual_c_symbol_derivative z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon k hk,
    actual_h_symbol_derivative z hz rho sigma hsigma hv p v hcanon k hk]
  exact tangent_eq_of_one_sided_zero (Cf p) (H p) (matrixDerivative Cf p v) (matrixDerivative H p v) S R hR hu hb hd hl hr

/-- A second positive Parseval pass, now with structure I and no density
weight, eliminates the genuine c L2 field including double-tracer pairs. -/
theorem actual_unweighted_c_field_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    : ∀ i j, cField z hz rho sigma hsigma K t p v hjac (fun _ _ => 1) i j = 0 := by
  apply field_zero_of_positive_radial_OZ z hz rho sigma hsigma K t p v hjac hv hcanon
    (fun _ _ => 1) (fun _ => 1) (fun _ => Matrix.PosDef.one)
  intro k hk
  simpa only [Matrix.one_mul, Matrix.mul_one] using actual_unweighted_radial_tangent_eq z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon k hk

/-- ALL-PAIR actual DCF tangent cancellation: neither species needs positive
density. Original root/canonical hypotheses remain, with rho>=0 only. -/
theorem actual_all_pair_DCF_ae_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    : ∀ i j, orderedVariation z rho sigma K p v i j =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  have he := actual_unweighted_c_field_zero z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon
  intro i j
  exact variation_zero_of_field_zero z hz rho sigma hsigma K t p v hjac (fun _ _ => 1) i j (by norm_num) (he i j)

/-- The genuine actual unweighted spectral C derivative vanishes on every
nonzero real wave number, including both tracer rows and tracer columns. -/
theorem actual_all_pair_C_derivative_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (k : ℝ) (hk : k ≠ 0) :
    matrixDerivative (fun a : TailMatrix T N × TailMatrix T N => nonlinearActualFourierC z rho sigma a.1 a.2 k) p v = 0 := by
  rw [← actual_c_symbol_derivative z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon k hk]
  have he := actual_all_pair_DCF_ae_zero z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon
  ext i j
  simp only [cSymbol, Matrix.of_apply, Complex.ofReal_one, one_mul, Matrix.zero_apply]
  rw [radialSymbol_zero_of_ae_zero _ (he i j) k, Complex.ofReal_zero]

/-- The actual unweighted h L2 field is zero too, by its honest Fourier
representative and the already proved all-pair c cancellation. -/
theorem actual_unweighted_h_field_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    : ∀ i j, hField z hz rho sigma hsigma hv p v hcanon (fun _ _ => 1) i j = 0 := by
  have hc := actual_all_pair_DCF_ae_zero z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon
  intro i j
  have hf : 𝓕 (hField z hz rho sigma hsigma hv p v hcanon (fun _ _ => 1) i j) = 0 := by
    apply Lp.ext
    filter_upwards [h_field_fourier z hz rho sigma hsigma hv p v hcanon (fun _ _ => 1) i j,
      volume.ae_ne (0 : ℝ), Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with w hh hw h0
    rw [h0, hh]
    have hk : 2*π*w ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) pi_ne_zero) hw
    have hs := congrFun (congrFun (actual_unweighted_radial_tangent_eq z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon (2*π*w) hk) i) j
    simp only [hSymbol, cSymbol, Matrix.of_apply, Complex.ofReal_one, one_mul] at hs ⊢
    rw [hs, radialSymbol_zero_of_ae_zero _ (hc i j) (2*π*w), Complex.ofReal_zero, mul_zero, Pi.zero_apply]
  apply norm_eq_zero.mp
  rw [← Lp.norm_fourier_eq (hField z hz rho sigma hsigma hv p v hcanon (fun _ _ => 1) i j), hf, norm_zero]

/-- Every actual h tangent vanishes a.e. on positive radii, including all
zero-density tracer pairs. No pointwise contact value is inferred. -/
theorem actual_all_pair_h_ae_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    : ∀ i j, hVariation z rho sigma p v i j =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  have hh := actual_unweighted_h_field_zero z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon
  intro i j
  have he := h_field_coe z hz rho sigma hsigma hv p v hcanon (fun _ _ => 1) i j
  rw [hh i j] at he
  have hzH : oddHTangent z rho sigma p v i j =ᵐ[volume] 0 := by
    simpa only [Complex.ofReal_one, one_mul] using he.symm.trans (Lp.coeFn_zero ℂ 2 volume)
  filter_upwards [ae_restrict_of_ae hzH, ae_restrict_mem measurableSet_Ioi] with r hr hs
  change 0 < r at hs
  change oddHTangent z rho sigma p v i j r = 0 at hr
  simp only [oddHTangent, FMSA.HardSphere.oddRadialMoment, abs_of_pos hs] at hr
  have heq : r*hVariation z rho sigma p v i j r = 0 := by exact_mod_cast hr
  exact (mul_eq_zero.mp heq).resolve_left hs.ne'

/-- Actual h tangent Laplace integrals are zero for every complex s, by
an a.e.-zero actual integrand. This does not integrate a nondecaying background. -/
theorem actual_h_tangent_laplace_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i) (t : ℝ)
    (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hv : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (s : ℂ) :
    rdfMatrixLaplace (fun r => Matrix.of (fun i j => r*hVariation z rho sigma p v i j r)) s = 0 := by
  have hh := actual_all_pair_h_ae_zero z hz rho sigma hsigma hrho K hK t p v hjac hv hroot hcanon
  ext i j
  simp only [rdfMatrixLaplace, Matrix.of_apply, Matrix.zero_apply, FMSA.causalComplexLaplace]
  calc
    _ = ∫ r in Ioi (0 : ℝ), (0 : ℂ) := by
      apply integral_congr_ae
      filter_upwards [hh i j] with r hr
      simp only [hr, Pi.zero_apply, mul_zero, Complex.ofReal_zero, zero_mul]
    _ = 0 := by simp

end FMSA.Convergence.ActualTracerDCFCancellation

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.c_field_coe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.c_field_coe

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.h_field_coe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.h_field_coe

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.fourier_constant_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.fourier_constant_mul

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.c_field_fourier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.c_field_fourier

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.h_field_fourier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.h_field_fourier

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.c_field_fourier_matrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.c_field_fourier_matrix

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.h_field_fourier_matrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.h_field_fourier_matrix

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.arbitrary_weight_spatial_pair_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.arbitrary_weight_spatial_pair_zero

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.variation_zero_of_field_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.variation_zero_of_field_zero

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.field_zero_of_positive_radial_OZ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.field_zero_of_positive_radial_OZ

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.c_symbol_additive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.c_symbol_additive

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.h_symbol_additive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.h_symbol_additive

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.actual_c_symbol_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.actual_c_symbol_derivative

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.actual_h_symbol_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.actual_h_symbol_derivative

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.actual_denominator_positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.actual_denominator_positive

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.actual_additive_radial_tangent_OZ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.actual_additive_radial_tangent_OZ

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.actual_additive_c_field_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.actual_additive_c_field_zero

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.actual_additive_c_symbol_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.actual_additive_c_symbol_zero

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.actual_C_one_sided_derivatives_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.actual_C_one_sided_derivatives_zero

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.actual_unweighted_radial_tangent_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.actual_unweighted_radial_tangent_eq

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.actual_unweighted_c_field_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.actual_unweighted_c_field_zero

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.actual_all_pair_DCF_ae_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.actual_all_pair_DCF_ae_zero

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.actual_all_pair_C_derivative_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.actual_all_pair_C_derivative_zero

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.actual_unweighted_h_field_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.actual_unweighted_h_field_zero

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.actual_all_pair_h_ae_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.actual_all_pair_h_ae_zero

/-- info: 'FMSA.Convergence.ActualTracerDCFCancellation.actual_h_tangent_laplace_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualTracerDCFCancellation.actual_h_tangent_laplace_zero
