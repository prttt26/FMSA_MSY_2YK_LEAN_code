import MSAConvergence.ActualPrimitiveTangent
import FMSAPaper.RadialIntegralJets
import FMSAPaper.BaxterNormalization

/-! Actual ordered radial DCF tangent identification. Every integrated
identity is established off-root before amplitude differentiation. -/
noncomputable section
open MeasureTheory Real Filter Topology Set
open scoped BigOperators ContDiff FourierTransform

namespace FMSA.Convergence.RadialDCFTangent
open FMSA.Convergence.ActualPrimitiveTangent FMSA.Convergence.ComplexWronskianJets
open FMSA.Paper FMSA.Paper.JacobianExterior FMSA.Paper.BaxterWeakJetBasis
open FMSA.Paper.RadialIntegralJets FMSA.Paper.PhysicalExteriorJets FMSA.Paper.FiniteBasis
open FMSA.Paper.BaxterSecondDerivative
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint FMSA.MatrixQ0 MSAMixture

variable {N : ℕ} {T : Type*} [Fintype T]

/-- The radius-weighted actual DCF is L1 on the positive axis at arbitrary
amplitudes, by its full-line integrable finite dictionary. -/
theorem correlation_radius_integrable_offroot (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    IntegrableOn (fun r => r * rootCorrelation z rho sigma p i j r) (Ioi 0) := by
  have hi : Integrable (fun r => (∑ b : Index T N, coefficients z rho sigma p i j b *
      radialBasis z sigma i j b r) / (2 * π)) :=
    (integrable_finsetSum _ (fun b _ => (radialBasis_integrable z hz sigma hsigma i j b).const_mul _)).div_const _
  apply hi.integrableOn.congr_fun _ measurableSet_Ioi
  intro r hr
  exact (correlation_radius_eq_linear z hz rho sigma hsigma p i j r hr.ne').symm

/-- The ordered right primitive decays without root equations: both its
spatial derivative and itself are integrable on the tail. -/
theorem rightPrimitive_tendsto_zero_offroot (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (horder : sigma j ≤ sigma i) :
    Tendsto (rightPrimitiveReal z rho sigma (amplitudeA z rho sigma p.1 p.2)
      (amplitudeQp z rho sigma p.1 p.2) (W z rho p.1 p.2) (C z rho sigma p.1 p.2) i j) atTop (𝓝 0) := by
  have hR : 0 ≤ edgeHi sigma i j := by unfold edgeHi; linarith [hsigma i, hsigma j]
  apply tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (a := edgeHi sigma i j) (f' := fun r => (-2 * π) * (r * rootCorrelation z rho sigma p i j r))
  · intro r hr
    convert! rightPrimitiveReal_hasDerivAt_positive z hz rho sigma
      (amplitudeA z rho sigma p.1 p.2) (amplitudeQp z rho sigma p.1 p.2)
      (W z rho p.1 p.2) (C z rho sigma p.1 p.2) hsigma i j horder r (hR.trans_lt hr) (ne_of_gt hr) using 1
    simp only [rootCorrelation]
    ring
  · have hi : IntegrableOn (fun r => (-2 * π) * (r * rootCorrelation z rho sigma p i j r)) (Ioi 0) :=
      (correlation_radius_integrable_offroot z rho sigma hz hsigma p i j).const_mul (-2 * π)
    exact hi.mono_set (Ioi_subset_Ioi hR)
  · exact (rightPrimitiveReal_integrable_positive z hz rho sigma _ _ _ _ hsigma i j horder).mono_set
      (Ioi_subset_Ioi hR)

/-- Root-free cosine/sine integration by parts for the actual ordered
primitive, with contact continuity and full tail decay discharged internally. -/
theorem rightPrimitive_cosine_offroot (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 < sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (horder : sigma j ≤ sigma i)
    (k : ℝ) (hk : k ≠ 0) :
    (∫ r in Ioi (0 : ℝ), rightPrimitiveReal z rho sigma (amplitudeA z rho sigma p.1 p.2)
      (amplitudeQp z rho sigma p.1 p.2) (W z rho p.1 p.2) (C z rho sigma p.1 p.2) i j r * cos (k*r)) =
      (2 * π / k) * ∫ r in Ioi (0 : ℝ), r * rootCorrelation z rho sigma p i j r * sin (k*r) := by
  have hs : ∀ i, 0 ≤ sigma i := fun i => (hsigma i).le
  let P := rightPrimitiveReal z rho sigma (amplitudeA z rho sigma p.1 p.2)
    (amplitudeQp z rho sigma p.1 p.2) (W z rho p.1 p.2) (C z rho sigma p.1 p.2) i j
  let c := rootCorrelation z rho sigma p i j
  obtain ⟨L, hL⟩ := rightPrimitiveReal_lipschitz z hz rho sigma
    (amplitudeA z rho sigma p.1 p.2) (amplitudeQp z rho sigma p.1 p.2)
    (W z rho p.1 p.2) (C z rho sigma p.1 p.2) hs i j
  have hpc : IntegrableOn (fun r => P r * cos (k*r)) (Ioi 0) :=
    (rightPrimitiveReal_integrable_positive z hz rho sigma _ _ _ _ hs i j horder).mul_bdd
      (by fun_prop) (Eventually.of_forall (fun r => by simpa only [Real.norm_eq_abs] using abs_cos_le_one (k*r)))
  have hcs : IntegrableOn (fun r => r * c r * sin (k*r)) (Ioi 0) :=
    (correlation_radius_integrable_offroot z rho sigma hz hs p i j).mul_bdd
      (by fun_prop) (Eventually.of_forall (fun r => by simpa only [Real.norm_eq_abs] using abs_sin_le_one (k*r)))
  have hR : 0 < edgeHi sigma i j := by unfold edgeHi; linarith [hsigma i, hsigma j]
  have h := FMSA.Analysis.cosine_of_one_contact P (fun r => 2 * π * r * c r) (edgeHi sigma i j) k hR hk
    hL.continuous (fun r hr hrR => by
      simpa only [P, c, rootCorrelation, neg_mul] using rightPrimitiveReal_hasDerivAt_positive z hz rho sigma
        (amplitudeA z rho sigma p.1 p.2) (amplitudeQp z rho sigma p.1 p.2)
        (W z rho p.1 p.2) (C z rho sigma p.1 p.2) hs i j horder r hr hrR)
    (rightPrimitive_tendsto_zero_offroot z rho sigma hz hs p i j horder) hpc
    (show IntegrableOn (fun r => (2 * π * r * c r) * sin (k*r)) (Ioi 0) by
      have he : (fun r => (2 * π * r * c r) * sin (k*r)) = fun r => (2 * π) * (r * c r * sin (k*r)) := by
        funext r
        ring
      rw [he]
      exact hcs.const_mul (2 * π))
  convert! h using 1
  have he : (fun r => (2 * π * r * c r) * sin (k*r)) = fun r => (2 * π) * (r * c r * sin (k*r)) := by
    funext r
    ring
  rw [he, integral_const_mul]
  ring

/-- The actual full reflected primitive selects the ordered right primitive
on positive radii, at arbitrary amplitudes. -/
theorem actualPrimitive_positive (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (horder : sigma j ≤ sigma i)
    (r : ℝ) (hr : 0 < r) :
    actualPrimitive z rho sigma p i j r = rightPrimitiveReal z rho sigma
      (amplitudeA z rho sigma p.1 p.2) (amplitudeQp z rho sigma p.1 p.2)
      (W z rho p.1 p.2) (C z rho sigma p.1 p.2) i j r := by
  rw [actualPrimitive, realPrimitive_eq_re, baxterPrimitive_positive_eq_ofReal z rho sigma _ _ _ _ i j horder r hr,
    Complex.ofReal_re, ← rightPrimitiveReal_eq_ordered_positive z rho sigma _ _ _ _ i j horder r hr]

/-- This all-amplitude cosine/radial-sine identity can safely be differentiated;
it does not require a neighboring family of BH roots. -/
theorem actualPrimitive_cosine_offroot (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 < sigma i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (horder : sigma j ≤ sigma i)
    (k : ℝ) (hk : k ≠ 0) :
    (∫ r in Ioi (0 : ℝ), actualPrimitive z rho sigma p i j r * cos (k*r)) =
      (2 * π / k) * ∫ r in Ioi (0 : ℝ), r * rootCorrelation z rho sigma p i j r * sin (k*r) := by
  have he : (∫ r in Ioi (0 : ℝ), actualPrimitive z rho sigma p i j r * cos (k*r)) =
      ∫ r in Ioi (0 : ℝ), rightPrimitiveReal z rho sigma (amplitudeA z rho sigma p.1 p.2)
        (amplitudeQp z rho sigma p.1 p.2) (W z rho p.1 p.2) (C z rho sigma p.1 p.2) i j r * cos (k*r) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [actualPrimitive_positive z rho sigma p i j horder r hr]
  rw [he]
  exact rightPrimitive_cosine_offroot z rho sigma hz hsigma p i j horder k hk

/-- A fixed finite integrable dictionary permits genuine amplitude
 differentiation under its integral, without a neighboring root curve. -/
theorem finite_integral_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type*} [Fintype I] (mu : Measure ℝ) (c : E → I → ℝ)
    (hc : ∀ b, ContDiff ℝ ∞ (fun a => c a b)) (phi : I → ℝ → ℝ)
    (hi : ∀ b, Integrable (phi b) mu) (p v : E) :
    fderiv ℝ (fun a => ∫ r, ∑ b, c a b * phi b r ∂mu) p v =
      ∫ r, ∑ b, fderiv ℝ (fun a => c a b) p v * phi b r ∂mu := by
  have he : (fun a => ∫ r, ∑ b, c a b * phi b r ∂mu) =
      fun a => ∑ b, c a b * ∫ r, phi b r ∂mu := by
    funext a
    rw [integral_finsetSum _ (fun b _ => (hi b).const_mul _)]
    simp only [integral_const_mul]
  rw [he, fderiv_fun_sum (fun b _ => ((hc b).differentiable (by simp) p).mul_const _),
    integral_finsetSum _ (fun b _ => (hi b).const_mul _)]
  simp only [sum_apply, integral_const_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [(((hc b).differentiable (by simp) p).hasFDerivAt.mul_const (∫ r, phi b r ∂mu)).fderiv]
  simp [mul_comm]

/-- The actual scalar DCF depends smoothly on amplitudes at every nonzero
radius, proved from the complete radial dictionary. -/
theorem rootCorrelation_contDiff (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i) (i j : Fin N) (r : ℝ) (hr : r ≠ 0) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N => rootCorrelation z rho sigma a i j r) := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => rootCorrelation z rho sigma a i j r) =
      fun a => (∑ b : Index T N, coefficients z rho sigma a i j b * radialBasis z sigma i j b r) / (2 * π) / r := by
    funext a
    apply (eq_div_iff hr).mpr
    simpa only [linear, mul_comm] using correlation_radius_eq_linear z hz rho sigma hsigma a i j r hr
  rw [he]
  exact (ContDiff.sum fun b _ => (coefficients_contDiff z rho sigma i j b).mul contDiff_const).div_const _ |>.div_const _

/-- The radius-weighted genuine DCF variation is the differentiated full
radial dictionary; this holds off-root and for every species pair. -/
theorem correlationVariation_radius_eq_basis (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) (hr : r ≠ 0) :
    r * correlationVariation z rho sigma p v i j r =
      (∑ b : Index T N, fderiv ℝ (fun a => coefficients z rho sigma a i j b) p v *
        radialBasis z sigma i j b r) / (2 * π) := by
  have he : (fun a : TailMatrix T N × TailMatrix T N => r * rootCorrelation z rho sigma a i j r) =
      fun a => (∑ b : Index T N, coefficients z rho sigma a i j b * radialBasis z sigma i j b r) / (2 * π) := by
    funext a
    exact correlation_radius_eq_linear z hz rho sigma hsigma a i j r hr
  have hc := ((rootCorrelation_contDiff z rho sigma hz hsigma i j r hr).differentiable (by simp) p).hasFDerivAt.const_mul r
  have hf (b : Index T N) :=
    ((coefficients_contDiff z rho sigma i j b).differentiable (by simp) p).hasFDerivAt.mul_const
      (radialBasis z sigma i j b r)
  have hd := congrArg (fun L : (TailMatrix T N × TailMatrix T N) →L[ℝ] ℝ => L v) hc.fderiv
  rw [he] at hd
  simp only [div_eq_mul_inv] at hd
  rw [((HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ => hf b)).mul_const (2 * π)⁻¹).fderiv] at hd
  simpa only [correlationVariation, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, div_eq_mul_inv, Finset.sum_mul, mul_comm] using hd.symm

/-- Smooth coefficients in a finite fixed integrable dictionary give a
smooth integral as a function of the actual amplitudes. -/
theorem finite_integral_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type*} [Fintype I] (mu : Measure ℝ) (c : E → I → ℝ)
    (hc : ∀ b, ContDiff ℝ ∞ (fun a => c a b)) (phi : I → ℝ → ℝ)
    (hi : ∀ b, Integrable (phi b) mu) :
    ContDiff ℝ ∞ (fun a => ∫ r, ∑ b, c a b * phi b r ∂mu) := by
  have he : (fun a => ∫ r, ∑ b, c a b * phi b r ∂mu) =
      fun a => ∑ b, c a b * ∫ r, phi b r ∂mu := by
    funext a
    rw [integral_finsetSum _ (fun b _ => (hi b).const_mul _)]
    simp only [integral_const_mul]
  rw [he]
  exact ContDiff.sum fun b _ => (hc b).mul contDiff_const

/-- The actual primitive cosine integral differentiates under the complete
positive-axis integral at arbitrary amplitudes. -/
theorem primitive_cosine_fderiv (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (k : ℝ) :
    fderiv ℝ (fun a => ∫ r in Ioi (0 : ℝ), actualPrimitive z rho sigma a i j r * cos (k*r)) p v =
      ∫ r in Ioi (0 : ℝ), primitiveVariation z rho sigma p v i j r * cos (k*r) := by
  let phi : Index T N → ℝ → ℝ := fun b r => primitiveBasis z sigma i j b r * cos (k*r)
  have hi (b : Index T N) : Integrable (phi b) (volume.restrict (Ioi 0)) := by
    exact (primitiveBasis_integrable z hz sigma hsigma i j b).integrableOn.mul_bdd
      (by fun_prop) (Eventually.of_forall (fun r => by simpa only [Real.norm_eq_abs] using abs_cos_le_one (k*r)))
  have he : (fun a : TailMatrix T N × TailMatrix T N =>
      ∫ r in Ioi (0 : ℝ), actualPrimitive z rho sigma a i j r * cos (k*r)) =
      fun a => ∫ r in Ioi (0 : ℝ), ∑ b : Index T N, coefficients z rho sigma a i j b * phi b r := by
    funext a
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    dsimp only
    rw [primitive_eq_linear z hz rho sigma hsigma a i j r]
    simp only [linear, phi, Finset.sum_mul, mul_assoc]
  rw [he, finite_integral_fderiv _ _ (coefficients_contDiff z rho sigma i j) _ hi p v]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  dsimp only
  rw [primitiveVariation_eq_basis z rho sigma hz hsigma p v i j r]
  simp only [phi, Finset.sum_mul, mul_assoc]

/-- The weighted DCF sine integral and its genuine amplitude derivative
are both given by the full integrable radial dictionary. -/
theorem correlation_sine_contDiff_and_fderiv (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (k : ℝ) :
    ContDiff ℝ ∞ (fun a : TailMatrix T N × TailMatrix T N =>
      ∫ r in Ioi (0 : ℝ), r * rootCorrelation z rho sigma a i j r * sin (k*r)) ∧
    fderiv ℝ (fun a => ∫ r in Ioi (0 : ℝ), r * rootCorrelation z rho sigma a i j r * sin (k*r)) p v =
      ∫ r in Ioi (0 : ℝ), r * correlationVariation z rho sigma p v i j r * sin (k*r) := by
  let phi : Index T N → ℝ → ℝ := fun b r => radialBasis z sigma i j b r * sin (k*r) / (2 * π)
  have hi (b : Index T N) : Integrable (phi b) (volume.restrict (Ioi 0)) := by
    exact ((radialBasis_integrable z hz sigma hsigma i j b).integrableOn.mul_bdd
      (by fun_prop) (Eventually.of_forall (fun r => by simpa only [Real.norm_eq_abs] using abs_sin_le_one (k*r)))).div_const _
  have he : (fun a : TailMatrix T N × TailMatrix T N =>
      ∫ r in Ioi (0 : ℝ), r * rootCorrelation z rho sigma a i j r * sin (k*r)) =
      fun a => ∫ r in Ioi (0 : ℝ), ∑ b : Index T N, coefficients z rho sigma a i j b * phi b r := by
    funext a
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [correlation_radius_eq_linear z hz rho sigma hsigma a i j r hr.ne']
    simp only [linear, phi, div_eq_mul_inv, Finset.sum_mul, mul_assoc]
    apply Finset.sum_congr rfl
    intro b _
    ring
  constructor
  · rw [he]
    exact finite_integral_contDiff _ _ (coefficients_contDiff z rho sigma i j) _ hi
  · rw [he, finite_integral_fderiv _ _ (coefficients_contDiff z rho sigma i j) _ hi p v]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [correlationVariation_radius_eq_basis z rho sigma hz hsigma p v i j r hr.ne']
    simp only [phi, div_eq_mul_inv, Finset.sum_mul, mul_assoc]
    apply Finset.sum_congr rfl
    intro b _
    ring

/-- The genuine primitive and DCF variations satisfy the radial cosine/sine
identity without a root hypothesis or a curve of roots. -/
theorem primitiveVariation_cosine (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 < sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (horder : sigma j ≤ sigma i)
    (k : ℝ) (hk : k ≠ 0) :
    (∫ r in Ioi (0 : ℝ), primitiveVariation z rho sigma p v i j r * cos (k*r)) =
      (2 * π / k) * ∫ r in Ioi (0 : ℝ), r * correlationVariation z rho sigma p v i j r * sin (k*r) := by
  have hs : ∀ i, 0 ≤ sigma i := fun i => (hsigma i).le
  have he : (fun a : TailMatrix T N × TailMatrix T N =>
      ∫ r in Ioi (0 : ℝ), actualPrimitive z rho sigma a i j r * cos (k*r)) =
      fun a => (2 * π / k) * ∫ r in Ioi (0 : ℝ), r * rootCorrelation z rho sigma a i j r * sin (k*r) := by
    funext a
    exact actualPrimitive_cosine_offroot z rho sigma hz hsigma a i j horder k hk
  obtain ⟨hc, hd⟩ := correlation_sine_contDiff_and_fderiv z rho sigma hz hs p v i j k
  rw [← primitive_cosine_fderiv z rho sigma hz hs p v i j k, he,
    ((hc.differentiable (by simp) p).hasFDerivAt.const_mul (2 * π / k)).fderiv]
  simpa only [smul_apply, smul_eq_mul] using congrArg (fun x : ℝ => (2 * π / k) * x) hd

/-- The genuine radius-weighted DCF variation is L1 on the positive axis
without any root or kernel assumption. -/
theorem correlationVariation_radius_integrable (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hsigma : ∀ i, 0 ≤ sigma i)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) :
    IntegrableOn (fun r => r * correlationVariation z rho sigma p v i j r) (Ioi 0) := by
  have hi : Integrable (fun r => (∑ b : Index T N,
      fderiv ℝ (fun a => coefficients z rho sigma a i j b) p v * radialBasis z sigma i j b r) / (2 * π)) :=
    (integrable_finsetSum _ (fun b _ => (radialBasis_integrable z hz sigma hsigma i j b).const_mul _)).div_const _
  apply hi.integrableOn.congr_fun _ measurableSet_Ioi
  intro r hr
  exact (correlationVariation_radius_eq_basis z rho sigma hz hsigma p v i j r hr.ne').symm

/-- At an actual symmetric-strength BH root along an actual Jacobian-kernel
direction, the spectral C derivative is the genuine radial DCF variation's
Fourier transform for an ordered species pair and every nonzero wave number. -/
theorem actual_kernel_fourierC_fderiv_eq_radial_ordered_pair
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (hz : ∀ u, 0 < z u)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hkern : amplitudeJacobian z rho sigma K t p v = 0)
    (i j : Fin N) (horder : sigma j ≤ sigma i) (k : ℝ) (hk : k ≠ 0) :
    fderiv ℝ (fun a => nonlinearActualFourierC z rho sigma a.1 a.2 k i j) p v =
      (FMSA.HardSphere.radial_fourier (correlationVariation z rho sigma p v i j) k : ℂ) := by
  have hs : ∀ i, 0 ≤ sigma i := fun i => (hsigma i).le
  let P : ℝ → ℂ := fun r => (primitiveVariation z rho sigma p v i j r : ℂ)
  have hi : Integrable P := (primitiveVariation_integrable z rho sigma hz hs p v i j).ofReal
  have heven : (fun r => P (-r)) =ᵐ[volume] P := by
    filter_upwards [actual_kernel_primitiveVariation_even z rho sigma K hK hz hs hv t p v hroot hkern i j]
      with r hr
    exact congrArg Complex.ofReal hr
  have hzW : FMSA.MixtureBaxter.zOfW (k/(2*π)) = Complex.I*k := by
    unfold FMSA.MixtureBaxter.zOfW
    push_cast
    field_simp
  have hf := fourier_of_ae_even P heven hi (k/(2*π))
  rw [FMSA.MixtureBaxter.fourier_eq_zOfW, hzW] at hf
  have hcos : (∫ r in Ioi (0 : ℝ), (cos (2*π*r*(k/(2*π))) : ℂ)*P r) =
      Complex.ofReal (∫ r in Ioi (0 : ℝ), primitiveVariation z rho sigma p v i j r * cos (k*r)) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    dsimp only
    have he : 2*π*r*(k/(2*π)) = k*r := by field_simp
    rw [he]
    dsimp only [P]
    push_cast
    ring
  rw [← primitiveVariation_fourier z rho sigma hz hs p v k i j]
  change (∫ r, P r * Complex.exp (-(Complex.I*k)*r)) = _
  have hneg : (fun r : ℝ => P r * Complex.exp (-(Complex.I*k)*r)) =
      (fun r => P r * Complex.exp (-(Complex.I*k*r))) := by
    funext r
    congr 2
    ring
  rw [hneg, hf, hcos, primitiveVariation_cosine z rho sigma hz hsigma p v i j horder k hk,
    FMSA.HardSphere.radial_fourier]
  push_cast
  ring

/-- The genuine derivative of the existing ordered radial DCF has the actual
spectral C derivative as its radial Fourier transform for every species pair.
No PY specialization, neighboring roots or Jacobian inverse is assumed. -/
theorem actual_kernel_fourierC_fderiv_eq_ordered_radial
    (z : T → ℝ) (rho sigma : Fin N → ℝ) (K : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (hz : ∀ u, 0 < z u)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hkern : amplitudeJacobian z rho sigma K t p v = 0)
    (i j : Fin N) (k : ℝ) (hk : k ≠ 0) :
    fderiv ℝ (fun a => nonlinearActualFourierC z rho sigma a.1 a.2 k i j) p v =
      (FMSA.HardSphere.radial_fourier (orderedVariation z rho sigma (t • K) p v i j) k : ℂ) := by
  by_cases horder : sigma j ≤ sigma i
  · have he : orderedVariation z rho sigma (t • K) p v i j = correlationVariation z rho sigma p v i j := by
      funext r
      unfold orderedVariation orderedRadialCorrelation
      simp only [if_pos horder]
      rfl
    rw [he]
    exact actual_kernel_fourierC_fderiv_eq_radial_ordered_pair
      z rho sigma K hK hz hsigma hv t p v hroot hkern i j horder k hk
  · have he : orderedVariation z rho sigma (t • K) p v i j = correlationVariation z rho sigma p v j i := by
      funext r
      unfold orderedVariation orderedRadialCorrelation
      simp only [if_neg horder]
      rfl
    rw [he, actual_kernel_fourierC_fderiv_symmetric_all z rho sigma K hK hz (fun i => (hsigma i).le)
      hv t p v hroot hkern k i j]
    exact actual_kernel_fourierC_fderiv_eq_radial_ordered_pair
      z rho sigma K hK hz hsigma hv t p v hroot hkern j i (le_of_not_ge horder) k hk

end FMSA.Convergence.RadialDCFTangent

/-- info: 'FMSA.Convergence.RadialDCFTangent.correlation_radius_integrable_offroot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RadialDCFTangent.correlation_radius_integrable_offroot

/-- info: 'FMSA.Convergence.RadialDCFTangent.rightPrimitive_tendsto_zero_offroot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RadialDCFTangent.rightPrimitive_tendsto_zero_offroot

/-- info: 'FMSA.Convergence.RadialDCFTangent.rightPrimitive_cosine_offroot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RadialDCFTangent.rightPrimitive_cosine_offroot

/-- info: 'FMSA.Convergence.RadialDCFTangent.actualPrimitive_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RadialDCFTangent.actualPrimitive_positive

/-- info: 'FMSA.Convergence.RadialDCFTangent.actualPrimitive_cosine_offroot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RadialDCFTangent.actualPrimitive_cosine_offroot

/-- info: 'FMSA.Convergence.RadialDCFTangent.finite_integral_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RadialDCFTangent.finite_integral_fderiv

/-- info: 'FMSA.Convergence.RadialDCFTangent.rootCorrelation_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RadialDCFTangent.rootCorrelation_contDiff

/-- info: 'FMSA.Convergence.RadialDCFTangent.correlationVariation_radius_eq_basis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RadialDCFTangent.correlationVariation_radius_eq_basis

/-- info: 'FMSA.Convergence.RadialDCFTangent.finite_integral_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RadialDCFTangent.finite_integral_contDiff

/-- info: 'FMSA.Convergence.RadialDCFTangent.primitive_cosine_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RadialDCFTangent.primitive_cosine_fderiv

/-- info: 'FMSA.Convergence.RadialDCFTangent.correlation_sine_contDiff_and_fderiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RadialDCFTangent.correlation_sine_contDiff_and_fderiv

/-- info: 'FMSA.Convergence.RadialDCFTangent.primitiveVariation_cosine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RadialDCFTangent.primitiveVariation_cosine

/-- info: 'FMSA.Convergence.RadialDCFTangent.correlationVariation_radius_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RadialDCFTangent.correlationVariation_radius_integrable

/-- info: 'FMSA.Convergence.RadialDCFTangent.actual_kernel_fourierC_fderiv_eq_radial_ordered_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RadialDCFTangent.actual_kernel_fourierC_fderiv_eq_radial_ordered_pair

/-- info: 'FMSA.Convergence.RadialDCFTangent.actual_kernel_fourierC_fderiv_eq_ordered_radial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.RadialDCFTangent.actual_kernel_fourierC_fderiv_eq_ordered_radial
