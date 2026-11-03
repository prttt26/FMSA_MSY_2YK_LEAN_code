import MSAConvergence.ActualExcessTangentDecay
import FMSAPaper.RadialVariationL2

/-! Actual h Frechet tangents in the global odd-radial L2 representation,
with their honest integral Fourier symbols and exact representatives. -/
noncomputable section
open MeasureTheory Set Real Filter Topology FourierTransform
open scoped BigOperators

namespace FMSA.Convergence.ActualHRadialL2
open FMSA.Paper FMSA.Paper.JacobianExterior FMSA.Paper.RadialVariationL2
open FMSA.Paper.MatrixOZParseval
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open FMSA.Convergence.ActualRDFTangent FMSA.Convergence.RDFExponentialOrder
open FMSA.Convergence.ActualExcessTangentDecay FMSA.Convergence.ActualExcessDecay

variable {N : ℕ} {T : Type*} [Fintype T]

/-- Measurability of the actual radius-weighted h tangent on positive
radius, proved from its actual contact/shift identity. -/
theorem actual_weighted_h_tangent_measurable (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (hR : 0 < edgeHi sigma i j) :
    AEStronglyMeasurable (fun r : ℝ => r*hVariation z rho sigma p v i j r) (volume.restrict (Ioi 0)) := by
  let f := (Ici (edgeHi sigma i j)).indicator
    (fun r : ℝ => causalVariation z rho sigma p v i j (r-edgeHi sigma i j))
  have hm : AEStronglyMeasurable f (volume.restrict (Ioi 0)) :=
    ((causalVariation_continuous z rho sigma p v i j).comp
      (continuous_id.sub continuous_const)).aestronglyMeasurable.indicator measurableSet_Ici
  apply hm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact (weighted_hVariation_positive_indicator z rho sigma p v i j hR r hr).symm

/-- Actual excess tangent decay transfers to the genuine radius-weighted
h tangent, with the contact phase retained in the computed constant. -/
theorem actual_weighted_h_tangent_decay
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (i j : Fin N) (hR : 0 < edgeHi sigma i j) :
    ∃ epsilon B : ℝ, 0 < epsilon ∧ 0 ≤ B ∧ ∀ r, 0 < r →
      |r*hVariation z rho sigma p v i j r| ≤ B*exp (-epsilon*r) := by
  obtain ⟨epsilon, D, he, hD, hdec⟩ := actual_excess_tangent_canonical_decay z hz rho sigma hsigma hv p v hcanon
  refine ⟨epsilon, D*exp (epsilon*edgeHi sigma i j), he, by positivity, ?_⟩
  intro r hr
  rw [actual_weighted_hVariation_positive z rho sigma p v i j hR r hr]
  split_ifs with hc
  · simp only [abs_zero]
    positivity
  · have hd := hdec (r-edgeHi sigma i j) (sub_nonneg.mpr (not_lt.mp hc)) i j
    rw [excessVariation_eq_causalVariation] at hd
    calc
      _ ≤ D*exp (-epsilon*(r-edgeHi sigma i j)) := hd
      _ = _ := by
        rw [mul_assoc, ← exp_add,
          show epsilon*edgeHi sigma i j+ -epsilon*r = -epsilon*(r-edgeHi sigma i j) by ring]

/-- The genuine positive radial moment is globally L1, not merely Lp on
finite intervals. Its input decay is proved internally. -/
theorem actual_weighted_h_tangent_integrable
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (i j : Fin N) (hR : 0 < edgeHi sigma i j) :
    IntegrableOn (fun r : ℝ => r*hVariation z rho sigma p v i j r) (Ioi 0) := by
  obtain ⟨epsilon, B, he, _hB, hb⟩ := actual_weighted_h_tangent_decay z hz rho sigma hsigma hv p v hcanon i j hR
  have hi : IntegrableOn (fun r : ℝ => B*exp (-epsilon*r)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -epsilon < 0) 0).const_mul B
  apply hi.mono' (actual_weighted_h_tangent_measurable z rho sigma p v i j hR)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  simpa only [Real.norm_eq_abs] using hb r hr

/-- The actual full-line odd radial h Frechet tangent. -/
def oddHTangent (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) : ℝ → ℂ :=
  FMSA.HardSphere.oddRadialMoment (hVariation z rho sigma p v i j)

/-- Actual whole-line L1 follows from the genuine positive radial moment. -/
theorem actual_odd_h_tangent_integrable
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (i j : Fin N) (hR : 0 < edgeHi sigma i j) : Integrable (oddHTangent z rho sigma p v i j) :=
  FMSA.HardSphere.oddRadialMoment_integrable
    (actual_weighted_h_tangent_integrable z hz rho sigma hsigma hv p v hcanon i j hR)

/-- The actual odd h tangent has a true global exponential envelope in
absolute radius, with zero and both time signs handled explicitly. -/
theorem actual_odd_h_tangent_decay
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (i j : Fin N) (hR : 0 < edgeHi sigma i j) :
    ∃ epsilon B : ℝ, 0 < epsilon ∧ 0 ≤ B ∧ ∀ r, ‖oddHTangent z rho sigma p v i j r‖ ≤ B*exp (-epsilon*|r|) := by
  obtain ⟨epsilon, B, he, hB, hb⟩ := actual_weighted_h_tangent_decay z hz rho sigma hsigma hv p v hcanon i j hR
  refine ⟨epsilon, B, he, hB, ?_⟩
  intro r
  by_cases hr : r = 0
  · subst r
    simp only [oddHTangent, FMSA.HardSphere.oddRadialMoment, zero_mul, Complex.ofReal_zero, norm_zero, abs_zero,
      mul_zero, exp_zero, mul_one]
    exact hB
  · have h := hb |r| (abs_pos.mpr hr)
    simpa only [oddHTangent, FMSA.HardSphere.oddRadialMoment, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_abs] using h

/-- A genuine L1 field with a proved global bound is L2, by an explicit
integrable bound on its squared norm. -/
theorem integrable_bounded_memLp_two {E : Type*} [NormedAddCommGroup E] {mu : Measure ℝ}
    (f : ℝ → E) (hf : Integrable f mu) (B : ℝ)
    (hb : ∀ᵐ r ∂mu, ‖f r‖ ≤ B) : MemLp f 2 mu := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  apply (hf.norm.const_mul B).mono' (hf.aestronglyMeasurable.norm.pow 2)
  filter_upwards [hb] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]
  exact mul_le_mul_of_nonneg_right hr (norm_nonneg _)

/-- Genuine global odd-radial L2 membership of the existing h Frechet
variation. No L2 field or unknown-tail bound is an input. -/
theorem actual_odd_h_tangent_memLp_two
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (i j : Fin N) (hR : 0 < edgeHi sigma i j) : MemLp (oddHTangent z rho sigma p v i j) 2 volume := by
  obtain ⟨epsilon, B, he, _hB, hb⟩ := actual_odd_h_tangent_decay z hz rho sigma hsigma hv p v hcanon i j hR
  apply integrable_bounded_memLp_two _ (actual_odd_h_tangent_integrable z hz rho sigma hsigma hv p v hcanon i j hR) B
  exact ae_of_all _ (fun r => (hb r).trans (by
    have h : exp (-epsilon*|r|) ≤ 1 := exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (abs_nonneg _))
    nlinarith))

/-- The actual positive-radius weighted h tangent is globally L2. -/
theorem actual_weighted_h_tangent_memLp_two
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (i j : Fin N) (hR : 0 < edgeHi sigma i j) :
    MemLp (fun r : ℝ => r*hVariation z rho sigma p v i j r) 2 (volume.restrict (Ioi 0)) := by
  obtain ⟨epsilon, B, he, hB, hb⟩ := actual_weighted_h_tangent_decay z hz rho sigma hsigma hv p v hcanon i j hR
  apply integrable_bounded_memLp_two _
    (actual_weighted_h_tangent_integrable z hz rho sigma hsigma hv p v hcanon i j hR) B
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have he1 : exp (-epsilon*r) ≤ 1 := exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hr.le)
  simpa only [Real.norm_eq_abs] using (hb r hr).trans (by nlinarith)

/-- Actual radial square integrability, with the physical radius-squared
weight, follows from the genuine global moment L2 bound. -/
theorem actual_h_tangent_radial_square_integrable
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (i j : Fin N) (hR : 0 < edgeHi sigma i j) :
    IntegrableOn (fun r : ℝ => r^2*(hVariation z rho sigma p v i j r)^2) (Ioi 0) := by
  have hi := (memLp_two_iff_integrable_sq
    (actual_weighted_h_tangent_measurable z rho sigma p v i j hR)).mp
    (actual_weighted_h_tangent_memLp_two z hz rho sigma hsigma hv p v hcanon i j hR)
  change Integrable (fun r : ℝ => r^2*(hVariation z rho sigma p v i j r)^2) (volume.restrict (Ioi 0))
  simpa only [mul_pow] using hi

/-- Actual density-weighted whole-line odd h tangent. -/
def weightedOddHTangent (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (i j : Fin N) (r : ℝ) : ℂ :=
  (densityWeight rho i j : ℂ)*oddHTangent z rho sigma p v i j r

/-- The actual density-weighted h L2 matrix, constructed from its genuine
representatives. Positive diameters supply every pair contact. -/
def actualHL2Field (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) : MatrixL2 ℝ N :=
  fun i j => ((actual_odd_h_tangent_memLp_two z hz rho sigma (fun i => (hsigma i).le) hv p v hcanon i j
    (by unfold edgeHi; linarith [hsigma i, hsigma j])).const_mul (densityWeight rho i j : ℂ)).toLp
      (weightedOddHTangent z rho sigma p v i j)

/-- Exact a.e. representative demanded by the existing actual DCF
cancellation theorem; there is no supplied unknown h-L2 field. -/
theorem actual_h_l2_field_coe (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) (i j : Fin N) :
    (actualHL2Field z hz rho sigma hsigma hv p v hcanon i j : ℝ → ℂ) =ᵐ[volume]
      fun r => (densityWeight rho i j : ℂ)*FMSA.HardSphere.oddRadialMoment (hVariation z rho sigma p v i j) r :=
  MemLp.coeFn_toLp _

/-- Honest full-line integral Fourier transform of the actual odd h
tangent, in the physical wave-number convention k=2*pi*w, including zero. -/
theorem actual_odd_h_tangent_integral_fourier
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (i j : Fin N) (hR : 0 < edgeHi sigma i j) (w : ℝ) :
    𝓕 (oddHTangent z rho sigma p v i j) w =
      -(Complex.I*(w : ℂ))*(RadialZeroMode.radialSymbol (hVariation z rho sigma p v i j) (2*π*w) : ℂ) := by
  have hodd : ∀ r : ℝ, oddHTangent z rho sigma p v i j (-r) = -oddHTangent z rho sigma p v i j r := by
    intro r
    simp only [oddHTangent, FMSA.HardSphere.oddRadialMoment, abs_neg, neg_mul, Complex.ofReal_neg]
  rw [fourier_of_odd _ hodd (actual_odd_h_tangent_integrable z hz rho sigma hsigma hv p v hcanon i j hR) w]
  have he : (∫ r in Ioi (0 : ℝ), (sin (2*π*r*w) : ℂ)*oddHTangent z rho sigma p v i j r) =
      ((∫ r in Ioi (0 : ℝ), r*hVariation z rho sigma p v i j r*sin ((2*π*w)*r) : ℝ) : ℂ) := by
    unfold oddHTangent FMSA.HardSphere.oddRadialMoment
    rw [FMSA.HardSphere.oddExt_fourier_integral_eq]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _hr
    dsimp only
    rw [show 2*π*r*w = (2*π*w)*r by ring]
  rw [he]
  by_cases hw : w = 0
  · simp only [hw, mul_zero, sin_zero, Complex.ofReal_zero, neg_zero, zero_mul, integral_zero]
  · rw [RadialZeroMode.radialSymbol_eq_radial_fourier _ _
      (mul_ne_zero (mul_ne_zero (by norm_num) pi_ne_zero) hw)]
    unfold FMSA.HardSphere.radial_fourier
    generalize hA : (∫ r in Ioi (0 : ℝ), r*hVariation z rho sigma p v i j r*sin ((2*π*w)*r)) = A
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hw, Complex.ofReal_ne_zero.mpr pi_ne_zero]
    ring

/-- The actual h L2 Fourier representative equals its genuine physical
radial integral symbol almost everywhere. -/
theorem actual_h_l2_field_fourier (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) (i j : Fin N) :
    ((𝓕 (actualHL2Field z hz rho sigma hsigma hv p v hcanon i j) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] fun w => (densityWeight rho i j : ℂ)*
        (-(Complex.I*(w : ℂ))*(RadialZeroMode.radialSymbol (hVariation z rho sigma p v i j) (2*π*w) : ℂ)) := by
  have hR : 0 < edgeHi sigma i j := by unfold edgeHi; linarith [hsigma i, hsigma j]
  have h := FourierL1L2.L2_fourier_ae_integral (weightedOddHTangent z rho sigma p v i j)
    ((actual_odd_h_tangent_integrable z hz rho sigma (fun i => (hsigma i).le) hv p v hcanon i j hR).const_mul _)
    ((actual_odd_h_tangent_memLp_two z hz rho sigma (fun i => (hsigma i).le) hv p v hcanon i j hR).const_mul _)
  apply h.trans
  exact ae_of_all _ (fun w => by
    have hm : 𝓕 (weightedOddHTangent z rho sigma p v i j) w =
        (densityWeight rho i j : ℂ)*𝓕 (oddHTangent z rho sigma p v i j) w := by
      rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun r => by simp only [weightedOddHTangent, smul_eq_mul]; ring)
    rw [hm, actual_odd_h_tangent_integral_fourier z hz rho sigma (fun i => (hsigma i).le) hv p v hcanon i j hR w])

/-- Actual density-weighted radial h tangent integral matrix. -/
def radialHTangentMatrix (z : T → ℝ) (rho sigma : Fin N → ℝ)
    (p v : TailMatrix T N × TailMatrix T N) (k : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => (densityWeight rho i j : ℂ)*
    (RadialZeroMode.radialSymbol (hVariation z rho sigma p v i j) k : ℂ))

/-- The complete actual h L2 Fourier matrix has its genuine radial
integral representative, retaining the physical 2*pi normalization. -/
theorem actual_h_fourier_matrix (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    fourierMatrix (actualHL2Field z hz rho sigma hsigma hv p v hcanon) =ᵐ[volume]
      fun w => -(Complex.I*(w : ℂ)) • radialHTangentMatrix z rho sigma p v (2*π*w) := by
  have he := eventually_all.mpr (fun i : Fin N => eventually_all.mpr (fun j : Fin N =>
    actual_h_l2_field_fourier z hz rho sigma hsigma hv p v hcanon i j))
  filter_upwards [he] with w hw
  ext i j
  change _ = -(Complex.I*(w : ℂ))*((densityWeight rho i j : ℂ)*_)
  rw [show fourierMatrix (actualHL2Field z hz rho sigma hsigma hv p v hcanon) w i j =
    (densityWeight rho i j : ℂ)*(-(Complex.I*(w : ℂ))*
      (RadialZeroMode.radialSymbol (hVariation z rho sigma p v i j) (2*π*w) : ℂ)) from hw i j]
  ring

/-- The actual second radial moment is L1 as well, so the zero-frequency
physical h tangent symbol is a genuine integral. -/
theorem actual_h_tangent_radial_moment_integrable
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (i j : Fin N) (hR : 0 < edgeHi sigma i j) :
    IntegrableOn (fun r : ℝ => r^2*hVariation z rho sigma p v i j r) (Ioi 0) := by
  obtain ⟨epsilon, B, he, hB, hb⟩ := actual_weighted_h_tangent_decay z hz rho sigma hsigma hv p v hcanon i j hR
  have hm : AEStronglyMeasurable (fun r : ℝ => r^2*hVariation z rho sigma p v i j r) (volume.restrict (Ioi 0)) := by
    have heq : (fun r : ℝ => r^2*hVariation z rho sigma p v i j r) =
        fun r : ℝ => r*(r*hVariation z rho sigma p v i j r) := by funext r; ring
    rw [heq]
    exact aestronglyMeasurable_id.mul (actual_weighted_h_tangent_measurable z rho sigma p v i j hR)
  have hi : IntegrableOn (fun r : ℝ => (B*(1+(epsilon/2)⁻¹))*exp (-(epsilon/2)*r)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(epsilon/2) < 0) 0).const_mul _
  apply hi.mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs, show r^2*hVariation z rho sigma p v i j r = r*(r*hVariation z rho sigma p v i j r) by ring,
    abs_mul, abs_of_pos hr]
  calc
    _ ≤ r*(B*exp (-epsilon*r)) := mul_le_mul_of_nonneg_left (hb r hr) hr.le
    _ = B*(r*exp (-epsilon*r)) := by ring
    _ ≤ B*((1+r)*exp (-epsilon*r)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le) hB
    _ ≤ B*((1+(epsilon/2)⁻¹)*exp (-(epsilon/2)*r)) :=
      mul_le_mul_of_nonneg_left (linear_exponential_absorption epsilon r he hr.le) hB
    _ = _ := by ring

/-- Every frequency of the actual physical sinc radial symbol, including
zero, has an honest absolutely integrable real integrand. -/
theorem actual_h_tangent_radial_symbol_integrable
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 ≤ sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (i j : Fin N) (hR : 0 < edgeHi sigma i j) (k : ℝ) :
    IntegrableOn (fun r : ℝ => r^2*hVariation z rho sigma p v i j r*sinc (k*r)) (Ioi 0) :=
  RadialZeroMode.weighted_sinc_integrable _
    (actual_h_tangent_radial_moment_integrable z hz rho sigma hsigma hv p v hcanon i j hR) k

/-- Genuine continuity of the actual radial h tangent matrix symbol at
all real physical frequencies, including the origin. -/
theorem actual_h_radial_matrix_continuous
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hv : vacMix rho sigma ≠ 0)
    (p v : TailMatrix T N × TailMatrix T N)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    Continuous (radialHTangentMatrix z rho sigma p v) := by
  apply continuous_matrix
  intro i j
  exact continuous_const.mul (Complex.continuous_ofReal.comp
    (RadialZeroMode.radialSymbol_continuous _
      (actual_h_tangent_radial_moment_integrable z hz rho sigma (fun i => (hsigma i).le) hv p v hcanon i j
        (by unfold edgeHi; linarith [hsigma i, hsigma j]))))

/-- The actual newly constructed h L2 field has the proved spatial
orthogonality to the actual DCF tangent along a BH-Jacobian kernel vector. -/
theorem actual_h_spatial_pair_zero
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hfree : vacMix rho sigma ≠ 0)
    (K : TailMatrix T N) (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s)) :
    spatialPair (weightedOddVariationLp z hz rho sigma (fun i => (hsigma i).le) K t p v hjac)
      (actualHL2Field z hz rho sigma hsigma hfree p v hcanon) = 0 :=
  actual_spatialPair_zero z hz rho sigma (fun i => (hsigma i).le) K t p v hjac
    (actualHL2Field z hz rho sigma hsigma hfree p v hcanon)
    (actual_h_l2_field_coe z hz rho sigma hsigma hfree p v hcanon)

/-- Actual DCF cancellation now needs no unknown h L2 representation.
The remaining radial tangent OZ premise is explicit and concerns the
actual integral symbols; deriving it from the residual is still separate. -/
theorem actual_kernel_DCF_ae_zero_of_radial_tangent_OZ
    (z : T → ℝ) (hz : ∀ u, 0 < z u) (rho sigma : Fin N → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hrho : ∀ i, 0 ≤ rho i)
    (K : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (t : ℝ) (p v : TailMatrix T N × TailMatrix T N)
    (hjac : amplitudeJacobian z rho sigma K t p v = 0)
    (hfree : vacMix rho sigma ≠ 0) (hroot : IsRoot z rho sigma (t • K) p.1 p.2)
    (hcanon : ∀ s : ℂ, 0 ≤ s.re → IsUnit
      (1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma p.1 p.2) s))
    (hF : ∀ k : ℝ, IsUnit (fourierFactor z rho sigma (amplitudeA z rho sigma p.1 p.2)
      (amplitudeQp z rho sigma p.1 p.2) (W z rho p.1 p.2) (C z rho sigma p.1 p.2) k))
    (hOZ : ∀ᵐ w ∂volume,
      radialHTangentMatrix z rho sigma p v (2*π*w) =
        MatrixOZPairing.structureMatrix z rho sigma (t • K) p.1 p.2 (2*π*w)*
          radialVariationMatrix z rho sigma K p v (2*π*w)*
          MatrixOZPairing.structureMatrix z rho sigma (t • K) p.1 p.2 (2*π*w)) :
    ∀ i j, 0 < rho i → 0 < rho j →
      orderedVariation z rho sigma K p v i j =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  apply actual_kernel_DCF_ae_zero_of_L2_OZ z hz rho sigma hsigma hrho K hK t p v hjac hfree hroot hF
    (actualHL2Field z hz rho sigma hsigma hfree p v hcanon)
    (actual_h_l2_field_coe z hz rho sigma hsigma hfree p v hcanon)
  filter_upwards [actual_h_fourier_matrix z hz rho sigma hsigma hfree p v hcanon,
    actual_fourier_matrix z hz rho sigma (fun i => (hsigma i).le) K t p v hjac, hOZ] with w hh hc ho
  rw [hh, hc, ho]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

end FMSA.Convergence.ActualHRadialL2

/-- info: 'FMSA.Convergence.ActualHRadialL2.actual_weighted_h_tangent_measurable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHRadialL2.actual_weighted_h_tangent_measurable

/-- info: 'FMSA.Convergence.ActualHRadialL2.actual_weighted_h_tangent_decay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHRadialL2.actual_weighted_h_tangent_decay

/-- info: 'FMSA.Convergence.ActualHRadialL2.actual_weighted_h_tangent_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHRadialL2.actual_weighted_h_tangent_integrable

/-- info: 'FMSA.Convergence.ActualHRadialL2.actual_odd_h_tangent_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHRadialL2.actual_odd_h_tangent_integrable

/-- info: 'FMSA.Convergence.ActualHRadialL2.actual_odd_h_tangent_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHRadialL2.actual_odd_h_tangent_decay

/-- info: 'FMSA.Convergence.ActualHRadialL2.integrable_bounded_memLp_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHRadialL2.integrable_bounded_memLp_two

/-- info: 'FMSA.Convergence.ActualHRadialL2.actual_odd_h_tangent_memLp_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHRadialL2.actual_odd_h_tangent_memLp_two

/-- info: 'FMSA.Convergence.ActualHRadialL2.actual_weighted_h_tangent_memLp_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHRadialL2.actual_weighted_h_tangent_memLp_two

/-- info: 'FMSA.Convergence.ActualHRadialL2.actual_h_tangent_radial_square_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHRadialL2.actual_h_tangent_radial_square_integrable

/-- info: 'FMSA.Convergence.ActualHRadialL2.actual_h_l2_field_coe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHRadialL2.actual_h_l2_field_coe

/-- info: 'FMSA.Convergence.ActualHRadialL2.actual_odd_h_tangent_integral_fourier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHRadialL2.actual_odd_h_tangent_integral_fourier

/-- info: 'FMSA.Convergence.ActualHRadialL2.actual_h_l2_field_fourier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHRadialL2.actual_h_l2_field_fourier

/-- info: 'FMSA.Convergence.ActualHRadialL2.actual_h_fourier_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHRadialL2.actual_h_fourier_matrix

/-- info: 'FMSA.Convergence.ActualHRadialL2.actual_h_tangent_radial_moment_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHRadialL2.actual_h_tangent_radial_moment_integrable

/-- info: 'FMSA.Convergence.ActualHRadialL2.actual_h_tangent_radial_symbol_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHRadialL2.actual_h_tangent_radial_symbol_integrable

/-- info: 'FMSA.Convergence.ActualHRadialL2.actual_h_radial_matrix_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHRadialL2.actual_h_radial_matrix_continuous

/-- info: 'FMSA.Convergence.ActualHRadialL2.actual_h_spatial_pair_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHRadialL2.actual_h_spatial_pair_zero

/-- info: 'FMSA.Convergence.ActualHRadialL2.actual_kernel_DCF_ae_zero_of_radial_tangent_OZ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FMSA.Convergence.ActualHRadialL2.actual_kernel_DCF_ae_zero_of_radial_tangent_OZ
