import MSAConvergence.ActualStructureCovariance
import MSAConvergence.CompactSpectralTest

/-! Actual odd-radial fields and honest Parseval pairing for covariance tests.
These identities precede the still-needed uniform matrix escape estimates. -/
noncomputable section
open MeasureTheory Set Real Filter Topology FourierTransform
open scoped BigOperators ComplexOrder
namespace FMSA.Convergence.RadialCovarianceBounds
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.Paper.FourierL1L2
open FMSA.ExactMSA.MultiTailMixture FMSA.ExactMSA.Breakpoint MSAMixture
open FMSA.Convergence.ActualStructureCovariance FMSA.Convergence.ActualExcessDecay
open FMSA.Convergence.ActualHRadialL2
open FMSA.HardSphere
variable {N : ℕ} {T : Type*} [Fintype T]

/-- Positive-radius moment L1 for the honest base h, without a small budget. -/
theorem actual_weighted_h_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (D G : TailMatrix T N)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ D G) s))
    (i j : Fin N) : IntegrableOn (fun r : ℝ => r*nonlinearH z ρ σ D G i j r) (Ioi 0) := by
  apply (actual_rdf_moment_integrable z hz ρ σ hσ hv D G hc i j).integrableOn.congr_fun _ measurableSet_Ioi
  intro r hr
  change 0 < r at hr
  dsimp only [nonlinearH]
  field_simp [hr.ne']

/-- The actual base odd h field is globally L1. -/
theorem actual_odd_h_integrable (z : T → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (D G : TailMatrix T N)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ D G) s))
    (i j : Fin N) : Integrable (oddRadialMoment (nonlinearH z ρ σ D G i j)) :=
  oddRadialMoment_integrable (actual_weighted_h_integrable z hz ρ σ hσ hv D G hc i j)

/-- Canonical excess decay makes the actual base odd h field globally L2.
The bound in this membership proof is per root, not a uniform escape bound. -/
theorem actual_odd_h_memLp_two (z : T → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 < σ i) (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (D G : TailMatrix T N)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ D G) s))
    (i j : Fin N) : MemLp (oddRadialMoment (nonlinearH z ρ σ D G i j)) 2 volume := by
  obtain ⟨epsilon,B,he,hB,hbound⟩ := actual_excess_canonical_decay z hz ρ σ
    (fun i => (hσ i).le) hv (D,G) hc
  let R := edgeHi σ i j
  have hR : 0 < R := by dsimp [R,edgeHi]; linarith [hσ i,hσ j]
  have hw (r : ℝ) (hr : 0 < r) : |r*nonlinearH z ρ σ D G i j r| ≤ R+B := by
    by_cases h : r < R
    · rw [nonlinearH_hardcore z ρ σ D G i j r hr h]
      simpa only [mul_neg_one,abs_neg,abs_of_pos hr] using (show r ≤ R+B by linarith)
    · have ht : 0 ≤ r-R := sub_nonneg.mpr (not_lt.mp h)
      have hd := hbound (r-R) ht i j
      have he1 : exp (-epsilon*(r-R)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
      have hsmall : |nonlinearRDFExcess z ρ σ D G (r-R) i j| ≤ B :=
        hd.trans (by nlinarith)
      rw [nonlinearH,nonlinearRDFMoment_outer z ρ σ D G i j hR r (not_lt.mp h)]
      have hcancel : r*(nonlinearRDFExcess z ρ σ D G (r-R) i j/r) =
          nonlinearRDFExcess z ρ σ D G (r-R) i j := by field_simp [hr.ne']
      rw [hcancel]
      linarith
  apply integrable_bounded_memLp_two _
    (actual_odd_h_integrable z hz ρ σ (fun i => (hσ i).le) hv D G hc i j) (R+B)
  apply ae_of_all
  intro r
  by_cases hr : r=0
  · subst r
    simp only [oddRadialMoment,zero_mul,Complex.ofReal_zero,norm_zero]
    linarith
  · have hh := hw |r| (abs_pos.mpr hr)
    simpa only [oddRadialMoment,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_abs] using hh

/-- Honest integral Fourier transform of any integrable odd radial moment,
with Mathlib frequency w and physical frequency k=2*pi*w. -/
theorem odd_radial_integral_fourier (f : ℝ → ℝ) (hi : Integrable (oddRadialMoment f)) (w : ℝ) :
    𝓕 (oddRadialMoment f) w = -(Complex.I*(w : ℂ))*(radial_fourier f (2*Real.pi*w) : ℂ) := by
  have hodd : ∀ r : ℝ, oddRadialMoment f (-r) = -oddRadialMoment f r := by
    intro r
    simp only [oddRadialMoment,abs_neg,neg_mul,Complex.ofReal_neg]
  rw [fourier_of_odd _ hodd hi w]
  have he : (∫ r in Ioi (0 : ℝ), (sin (2*Real.pi*r*w) : ℂ)*oddRadialMoment f r) =
      ((∫ r in Ioi (0 : ℝ), r*f r*sin ((2*Real.pi*w)*r) : ℝ) : ℂ) := by
    unfold oddRadialMoment
    rw [oddExt_fourier_integral_eq]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    dsimp only
    rw [show 2*Real.pi*r*w=(2*Real.pi*w)*r by ring]
  rw [he]
  by_cases hw : w=0
  · simp only [hw,mul_zero,sin_zero,Complex.ofReal_zero,neg_zero,zero_mul,integral_zero]
  · unfold radial_fourier
    generalize ha : (∫ r in Ioi (0 : ℝ), r*f r*sin ((2*Real.pi*w)*r)) = a
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hw,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring

private theorem fourier_product (f g : ℝ → ℝ) (w : ℝ) :
    star (-(Complex.I*(w : ℂ))*(radial_fourier f (2*Real.pi*w) : ℂ))*
      (-(Complex.I*(w : ℂ))*(radial_fourier g (2*Real.pi*w) : ℂ)) =
        ((w^2*radial_fourier f (2*Real.pi*w)*radial_fourier g (2*Real.pi*w) : ℝ) : ℂ) := by
  simp only [star_mul,star_neg,Complex.star_def,Complex.conj_I,Complex.conj_ofReal]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Genuine scalar radial Parseval with honest integral Fourier symbols.
The membership assumptions are analytic L1/L2, not amplitude bounds. -/
theorem radial_spectral_pairing (f g : ℝ → ℝ)
    (hfi : Integrable (oddRadialMoment f)) (hgi : Integrable (oddRadialMoment g))
    (hf₂ : MemLp (oddRadialMoment f) 2 volume) (hg₂ : MemLp (oddRadialMoment g) 2 volume) :
    Integrable (fun w : ℝ => w^2*radial_fourier f (2*Real.pi*w)*radial_fourier g (2*Real.pi*w)) ∧
    (∫ w : ℝ, w^2*radial_fourier f (2*Real.pi*w)*radial_fourier g (2*Real.pi*w)) =
      ∫ r : ℝ, r^2*f |r| *g |r| := by
  let F := hf₂.toLp (oddRadialMoment f)
  let G := hg₂.toLp (oddRadialMoment g)
  have hF := (L2_fourier_ae_integral _ hfi hf₂).trans (ae_of_all _ (odd_radial_integral_fourier f hfi))
  have hG := (L2_fourier_ae_integral _ hgi hg₂).trans (ae_of_all _ (odd_radial_integral_fourier g hgi))
  have hleft : (fun w : ℝ => star ((𝓕 F : Lp ℂ 2 volume) w)*((𝓕 G : Lp ℂ 2 volume) w)) =ᵐ[volume]
      fun w => ((w^2*radial_fourier f (2*Real.pi*w)*radial_fourier g (2*Real.pi*w) : ℝ) : ℂ) := by
    filter_upwards [hF,hG] with w hf hg
    rw [hf,hg]
    exact fourier_product f g w
  have hright : (fun r : ℝ => star (F r)*G r) =ᵐ[volume]
      fun r => ((r^2*f |r| *g |r| : ℝ) : ℂ) := by
    filter_upwards [hf₂.coeFn_toLp,hg₂.coeFn_toLp] with r hf hg
    change star ((hf₂.toLp (oddRadialMoment f)) r)*((hg₂.toLp (oddRadialMoment g)) r) = _
    rw [hf,hg]
    simp only [oddRadialMoment,Complex.star_def,Complex.conj_ofReal]
    push_cast
    ring
  have hi : Integrable (fun w : ℝ => star ((𝓕 F : Lp ℂ 2 volume) w)*((𝓕 G : Lp ℂ 2 volume) w)) := by
    simpa only [RCLike.inner_apply',Complex.star_def] using (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (𝓕 F) (𝓕 G))
  have he : (∫ w : ℝ, star ((𝓕 F : Lp ℂ 2 volume) w)*((𝓕 G : Lp ℂ 2 volume) w)) =
      ∫ r : ℝ, star (F r)*G r := by
    simpa only [MeasureTheory.L2.inner_def,RCLike.inner_apply',Complex.star_def] using Lp.inner_fourier_eq F G
  rw [integral_congr_ae hleft,integral_congr_ae hright] at he
  have hl := (hi.congr hleft).re
  refine ⟨hl,?_⟩
  have hre := congrArg Complex.re he
  simpa only [integral_complex_ofReal,Complex.ofReal_re] using hre

private theorem profile_scaled_zero (R : ℝ) (hR : 0 < R) (r : ℝ) (hr : R ≤ |r|) :
    CompactSpectralTest.profile (r/R) = 0 := by
  unfold CompactSpectralTest.profile
  rw [abs_div,abs_of_pos hR,max_eq_right]
  · norm_num
  · have h : 1 ≤ |r|/R := (le_div_iff₀ hR).mpr (by simpa using hr)
    linarith

/-- The actual scaled compact test supplies its own global L1/L2 premises. -/
theorem scaled_profile_odd_L1_L2 (R : ℝ) (hR : 0 < R) :
    Integrable (oddRadialMoment (fun r => CompactSpectralTest.profile (r/R))) ∧
      MemLp (oddRadialMoment (fun r => CompactSpectralTest.profile (r/R))) 2 volume := by
  let f := oddRadialMoment (fun r => CompactSpectralTest.profile (r/R))
  have hc : Continuous f := by
    change Continuous (fun r : ℝ => ((r*CompactSpectralTest.profile (|r|/R) : ℝ) : ℂ))
    unfold CompactSpectralTest.profile
    fun_prop
  have hs : Function.support f ⊆ Icc (-R) R := by
    intro r hr
    by_contra hn
    have hh : R ≤ |r| := (lt_of_not_ge (fun h => hn (abs_le.mp h))).le
    exact hr (by simp only [f,oddRadialMoment,profile_scaled_zero R hR |r| (by simpa only [abs_abs] using hh),mul_zero,Complex.ofReal_zero])
  have hcompact : HasCompactSupport f := isCompact_Icc.of_isClosed_subset isClosed_closure
    (closure_minimal hs isClosed_Icc)
  exact ⟨memLp_one_iff_integrable.mp (hc.memLp_of_hasCompactSupport hcompact),
    hc.memLp_of_hasCompactSupport hcompact⟩

/-- The ACTUAL h/test spectral pairing is a fixed negative core moment,
independent of amplitudes and strengths. -/
theorem actual_h_compact_test_pairing (z : T → ℝ) (hz : ∀ u, 0 < z u) (ρ σ : Fin N → ℝ)
    (hσ : ∀ i, 0 < σ i) (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (D G : TailMatrix T N)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ D G) s))
    (R : ℝ) (hR : 0 < R) (i j : Fin N) (hcontact : R < edgeHi σ i j) :
    Integrable (fun w : ℝ => w^2*radial_fourier (nonlinearH z ρ σ D G i j) (2*Real.pi*w)*
      radial_fourier (fun r => CompactSpectralTest.profile (r/R)) (2*Real.pi*w)) ∧
    (∫ w : ℝ, w^2*radial_fourier (nonlinearH z ρ σ D G i j) (2*Real.pi*w)*
      radial_fourier (fun r => CompactSpectralTest.profile (r/R)) (2*Real.pi*w)) =
        -(∫ r : ℝ, r^2*CompactSpectralTest.profile (r/R)) := by
  obtain ⟨hi,h₂⟩ := scaled_profile_odd_L1_L2 R hR
  obtain ⟨hpi,hpeq⟩ := radial_spectral_pairing (nonlinearH z ρ σ D G i j)
    (fun r => CompactSpectralTest.profile (r/R))
    (actual_odd_h_integrable z hz ρ σ (fun i => (hσ i).le) hv D G hc i j) hi
    (actual_odd_h_memLp_two z hz ρ σ hσ hv D G hc i j) h₂
  refine ⟨hpi,hpeq.trans ?_⟩
  rw [← integral_neg]
  apply integral_congr_ae
  apply ae_of_all
  intro r
  dsimp only
  by_cases hzero : r=0
  · simp [hzero]
  by_cases hr : |r| < R
  · rw [nonlinearH_hardcore z ρ σ D G i j |r| (abs_pos.mpr hzero) (hr.trans hcontact)]
    simp only [CompactSpectralTest.profile,abs_div,abs_abs]
    ring
  · have hz0 := profile_scaled_zero R hR r (not_lt.mp hr)
    have hza : CompactSpectralTest.profile (|r|/R) = 0 := by
      simpa only [CompactSpectralTest.profile,abs_div,abs_abs] using hz0
    rw [hz0,hza]
    ring

def testWeight (R w : ℝ) : ℝ := w^2*radial_fourier
  (fun r => CompactSpectralTest.profile (r/R)) (2*Real.pi*w)

private def unitWeight (w : ℝ) : ℝ := w^2*radial_fourier CompactSpectralTest.profile (2*Real.pi*w)

private theorem unitWeight_even (w : ℝ) : unitWeight (-w) = unitWeight w := by
  simp only [unitWeight,neg_sq,mul_neg,radial_fourier_neg]

private theorem unitWeight_nonneg (w : ℝ) : 0 ≤ unitWeight w := by
  by_cases hw : w=0
  · simp [unitWeight,hw]
  · exact mul_nonneg (sq_nonneg w) (CompactSpectralTest.profile_radial_fourier_pos _
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hw)).le

private theorem unitWeight_continuous : Continuous unitWeight := by
  have hi : Integrable (oddRadialMoment CompactSpectralTest.profile) := by
    simpa only [div_one] using (scaled_profile_odd_L1_L2 1 zero_lt_one).1
  have hf : Continuous (𝓕 (oddRadialMoment CompactSpectralTest.profile)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi
  have he : unitWeight = fun w : ℝ =>
      (Complex.I*(w : ℂ)*𝓕 (oddRadialMoment CompactSpectralTest.profile) w).re := by
    funext w
    rw [odd_radial_integral_fourier CompactSpectralTest.profile hi w]
    simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
      Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im]
    dsimp only [unitWeight]
    ring
  rw [he]
  exact Complex.continuous_re.comp ((continuous_const.mul Complex.continuous_ofReal).mul hf)

private theorem unitWeight_tail (w : ℝ) (hw : 1 ≤ |w|) : w^2*unitWeight w ≤ 48*Real.pi := by
  have hp (x : ℝ) (hx : 1 ≤ x) : x^2*unitWeight x ≤ 48*Real.pi := by
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    let k := 2*Real.pi*x
    have hk : 0 < k := by dsimp [k]; positivity
    have hxk : x ≤ k := by dsimp [k]; nlinarith [Real.pi_gt_three]
    have hk1 : 1 ≤ k := hx.trans hxk
    have hn : CompactSpectralTest.numerator k ≤ 6*k := by
      have hcos := mul_le_mul_of_nonneg_left (cos_le_one k) hk.le
      have hsin := neg_one_le_sin k
      dsimp only [CompactSpectralTest.numerator]
      nlinarith
    have hm : x^4*8*Real.pi*CompactSpectralTest.numerator k ≤ (48*Real.pi)*k^5 := by
      calc
        _ ≤ x^4*8*Real.pi*(6*k) := mul_le_mul_of_nonneg_left hn (by positivity)
        _ = x^4*(48*Real.pi*k) := by ring
        _ ≤ k^4*(48*Real.pi*k) := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hxpos.le hxk 4) (by positivity)
        _ = _ := by ring
    have he : x^2*unitWeight x = x^4*8*Real.pi*CompactSpectralTest.numerator k/k^5 := by
      rw [unitWeight,CompactSpectralTest.profile_radial_fourier (2*Real.pi*x) hk.ne']
      dsimp only [k]
      ring
    rw [he]
    exact (div_le_iff₀ (pow_pos hk 5)).mpr hm
  by_cases hsign : 0 ≤ w
  · exact hp w (by simpa only [abs_of_nonneg hsign] using hw)
  · have hneg : 0 ≤ -w := by linarith
    have h := hp (-w) (by simpa only [abs_of_nonpos (by linarith : w ≤ 0)] using hw)
    simpa only [neg_sq,unitWeight_even] using h

private theorem continuous_quadratic_tail_integrable (g : ℝ → ℝ) (hc : Continuous g)
    (hn : ∀ x, 0 ≤ g x) (B : ℝ) (hB : 0 ≤ B)
    (ht : ∀ x, 1 ≤ |x| → x ^ 2 * g x ≤ B) : Integrable g := by
  obtain ⟨m,hm,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (-1 : ℝ) 1).Nonempty by exact ⟨0,by norm_num⟩) hc.continuousOn
  let M := max (g m) B
  have hM : 0 ≤ M := (hn m).trans (le_max_left _ _)
  have hgm (x : ℝ) : g x ≤ M := by
    by_cases hx : |x| ≤ 1
    · exact (hmax (abs_le.mp hx)).trans (le_max_left _ _)
    · have hx1 : 1 ≤ |x| := (lt_of_not_ge hx).le
      have hsq : 1 ≤ x^2 := by simpa only [sq_abs,one_pow] using pow_le_pow_left₀ zero_le_one hx1 2
      exact ((le_mul_of_one_le_left (hn x) hsq).trans (ht x hx1)).trans (le_max_right _ _)
  apply (integrable_inv_one_add_sq.const_mul (2*M+2*B)).mono' hc.aestronglyMeasurable
  apply ae_of_all
  intro x
  have hmajor := CanonicalResolventAnalysis.quadratic_tail_global_majorant g 1 M B le_rfl hM hB hn hgm ht x
  norm_num only [one_pow,one_add_one_eq_two] at hmajor
  have hb : g x ≤ (2*M+2*B)*(1+x^2)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ (by positivity : 0 < 1+x^2)).mpr (by simpa only [mul_comm] using hmajor)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (hn x)] using hb

/-- The fixed unit test's spectral radial weight is genuinely L1. -/
theorem unit_test_weight_integrable : Integrable (testWeight 1) := by
  have h := continuous_quadratic_tail_integrable unitWeight unitWeight_continuous unitWeight_nonneg
    (48*Real.pi) (by positivity) unitWeight_tail
  convert h using 1
  funext w
  simp only [testWeight,unitWeight,div_one]

/-- Every scaled test's spectral radial weight is L1, with no root premise. -/
theorem scaled_test_weight_integrable (R : ℝ) (hR : 0 < R) : Integrable (testWeight R) := by
  have hunit : Integrable unitWeight := by
    convert unit_test_weight_integrable using 1
    funext w
    simp only [testWeight,unitWeight,div_one]
  have he : testWeight R = fun w : ℝ => R*unitWeight (R*w) := by
    funext w
    rw [testWeight,CompactSpectralTest.radial_fourier_dilate CompactSpectralTest.profile R hR]
    rw [show R*(2*Real.pi*w)=2*Real.pi*(R*w) by ring]
    dsimp only [unitWeight]
    ring
  rw [he]
  exact (hunit.comp_mul_left' hR.ne').const_mul R

/-- A UNIFORM actual covariance trace bound for all canonical roots at fixed
mixture data. The right side depends only on the test radius and species count;
it contains no tail strengths or amplitudes. No amplitude bound is supplied. -/
theorem actual_structure_weighted_trace_bound (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (R : ℝ) (hR : 0 < R) (hRσ : ∀ i, R < σ i)
    (K D G : TailMatrix T N) (hK : ∀ u i j, K u i j = K u j i)
    (hroot : IsRoot z ρ σ K D G)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ D G) s)) :
    Integrable (fun w : ℝ => testWeight R w*
      (FMSA.Paper.MatrixOZPairing.structureMatrix z ρ σ K D G (2*Real.pi*w)).trace.re) ∧
    (∫ w : ℝ, testWeight R w*
      (FMSA.Paper.MatrixOZPairing.structureMatrix z ρ σ K D G (2*Real.pi*w)).trace.re) ≤
        (N : ℝ)*(∫ w : ℝ, testWeight R w) := by
  classical
  let F : Fin N → ℝ → ℝ := fun i w => testWeight R w*radial_fourier (nonlinearH z ρ σ D G i i) (2*Real.pi*w)
  have hpair (i : Fin N) : Integrable (F i) ∧ (∫ w : ℝ, F i w) ≤ 0 := by
    have hcontact : R < edgeHi σ i i := by simpa only [edgeHi,add_self_div_two] using hRσ i
    obtain ⟨hi,he⟩ := actual_h_compact_test_pairing z hz ρ σ hσ hv D G hc R hR i i hcontact
    have heq : F i = fun w : ℝ => w^2*radial_fourier (nonlinearH z ρ σ D G i i) (2*Real.pi*w)*
        radial_fourier (fun r => CompactSpectralTest.profile (r/R)) (2*Real.pi*w) := by
      funext w
      dsimp only [F,testWeight]
      ring
    rw [heq]
    refine ⟨hi,?_⟩
    rw [he]
    apply neg_nonpos.mpr
    exact integral_nonneg (fun r => mul_nonneg (sq_nonneg r) (sq_nonneg _))
  have htrace (w : ℝ) (hw : w ≠ 0) :
      (FMSA.Paper.MatrixOZPairing.structureMatrix z ρ σ K D G (2*Real.pi*w)).trace.re =
        (N : ℝ)+∑ i, ρ i*radial_fourier (nonlinearH z ρ σ D G i i) (2*Real.pi*w) := by
    have hk : 2*Real.pi*w ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hw
    have hm := actual_structure_eq_covariance z hz ρ σ hρ hσ hv K D G hK hroot hc (2*Real.pi*w) hk
    have hd (i : Fin N) :
        (FMSA.Paper.MatrixOZPairing.structureMatrix z ρ σ K D G (2*Real.pi*w) i i).re =
          1+ρ i*radial_fourier (nonlinearH z ρ σ D G i i) (2*Real.pi*w) := by
      have hh := congrArg Complex.re (congrFun (congrFun hm i) i).symm
      simp only [Matrix.add_apply,Matrix.one_apply_eq,Matrix.diagonal_mul,Matrix.mul_diagonal,
        Matrix.of_apply,Complex.add_re,Complex.one_re,Complex.mul_re,Complex.mul_im,
        Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero] at hh
      rw [hh]
      rw [show sqrt (ρ i)*radial_fourier (nonlinearH z ρ σ D G i i) (2*Real.pi*w)*sqrt (ρ i) =
        (sqrt (ρ i)*sqrt (ρ i))*radial_fourier (nonlinearH z ρ σ D G i i) (2*Real.pi*w) by ring,
        Real.mul_self_sqrt (hρ i)]
    change Complex.reCLM (∑ i, FMSA.Paper.MatrixOZPairing.structureMatrix z ρ σ K D G (2*Real.pi*w) i i) = _
    rw [map_sum]
    change (∑ i, (FMSA.Paper.MatrixOZPairing.structureMatrix z ρ σ K D G (2*Real.pi*w) i i).re) = _
    simp_rw [hd]
    simp [Finset.sum_add_distrib]
  let V : ℝ → ℝ := fun w => (N : ℝ)*testWeight R w+∑ i, ρ i*F i w
  have hsum : Integrable (fun w : ℝ => ∑ i, ρ i*F i w) :=
    integrable_finsetSum _ (fun i _ => (hpair i).1.const_mul (ρ i))
  have hV : Integrable V := ((scaled_test_weight_integrable R hR).const_mul (N : ℝ)).add hsum
  have he : (fun w : ℝ => testWeight R w*
      (FMSA.Paper.MatrixOZPairing.structureMatrix z ρ σ K D G (2*Real.pi*w)).trace.re) =ᵐ[volume] V := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with w hw
    rw [htrace w hw]
    dsimp only [V,F]
    rw [mul_add,Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  refine ⟨hV.congr he.symm,?_⟩
  rw [integral_congr_ae he]
  change (∫ w : ℝ, (N : ℝ)*testWeight R w+∑ i, ρ i*F i w) ≤ _
  rw [integral_add ((scaled_test_weight_integrable R hR).const_mul (N : ℝ)) hsum,
    integral_const_mul,integral_finsetSum _ (fun i _ => (hpair i).1.const_mul (ρ i))]
  simp_rw [integral_const_mul]
  have hnonpos : (∑ i, ρ i*(∫ w : ℝ, F i w)) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hρ i) (hpair i).2)
  linarith

end FMSA.Convergence.RadialCovarianceBounds
/-- info: 'FMSA.Convergence.RadialCovarianceBounds.actual_weighted_h_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RadialCovarianceBounds.actual_weighted_h_integrable
/-- info: 'FMSA.Convergence.RadialCovarianceBounds.actual_odd_h_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RadialCovarianceBounds.actual_odd_h_integrable
/-- info: 'FMSA.Convergence.RadialCovarianceBounds.actual_odd_h_memLp_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RadialCovarianceBounds.actual_odd_h_memLp_two
/-- info: 'FMSA.Convergence.RadialCovarianceBounds.odd_radial_integral_fourier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RadialCovarianceBounds.odd_radial_integral_fourier
/-- info: 'FMSA.Convergence.RadialCovarianceBounds.radial_spectral_pairing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RadialCovarianceBounds.radial_spectral_pairing
/-- info: 'FMSA.Convergence.RadialCovarianceBounds.scaled_profile_odd_L1_L2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RadialCovarianceBounds.scaled_profile_odd_L1_L2
/-- info: 'FMSA.Convergence.RadialCovarianceBounds.actual_h_compact_test_pairing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RadialCovarianceBounds.actual_h_compact_test_pairing
/-- info: 'FMSA.Convergence.RadialCovarianceBounds.unit_test_weight_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RadialCovarianceBounds.unit_test_weight_integrable
/-- info: 'FMSA.Convergence.RadialCovarianceBounds.scaled_test_weight_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RadialCovarianceBounds.scaled_test_weight_integrable
/-- info: 'FMSA.Convergence.RadialCovarianceBounds.actual_structure_weighted_trace_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.RadialCovarianceBounds.actual_structure_weighted_trace_bound
