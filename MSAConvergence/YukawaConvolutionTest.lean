import MSAConvergence.RadialCovarianceBounds

/-! A compact odd radial test smoothed by the even exponential kernel.
Its exterior is exactly Yukawa, while Fourier convolution keeps the compact
positive spectral weight as a direct majorant. -/
noncomputable section
open MeasureTheory Set Real Filter Topology FourierTransform
open scoped BigOperators Convolution
namespace FMSA.Convergence.YukawaConvolutionTest
open FMSA.HardSphere FMSA.Convergence.CompactSpectralTest
open FMSA.Convergence.RadialCovarianceBounds FMSA.Convergence.ActualHRadialL2

def compactOdd (R t : ℝ) : ℝ := t*profile (t/R)
def exponential (s t : ℝ) : ℝ := exp (-s*|t|)
def smoothed (s R : ℝ) : ℝ → ℝ := compactOdd R ⋆[ContinuousLinearMap.mul ℝ ℝ] exponential s
def radialTest (s R r : ℝ) : ℝ := smoothed s R r/r

theorem compact_odd_continuous (R : ℝ) : Continuous (compactOdd R) := by
  unfold compactOdd profile
  fun_prop

private theorem profile_outside (R : ℝ) (hR : 0 < R) (t : ℝ) (ht : R ≤ |t|) : profile (t/R)=0 := by
  unfold profile
  rw [abs_div,abs_of_pos hR,max_eq_right]
  · norm_num
  · have h : 1 ≤ |t|/R := (le_div_iff₀ hR).mpr (by simpa using ht)
    linarith

theorem compact_odd_hasCompactSupport (R : ℝ) (hR : 0 < R) : HasCompactSupport (compactOdd R) := by
  have hs : Function.support (compactOdd R) ⊆ Icc (-R) R := by
    intro t ht
    by_contra hn
    have hh : R ≤ |t| := (lt_of_not_ge (fun h => hn (abs_le.mp h))).le
    exact ht (by simp only [compactOdd,profile_outside R hR t hh,mul_zero])
  exact isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc)

theorem compact_odd_integrable (R : ℝ) (hR : 0 < R) : Integrable (compactOdd R) :=
  (compact_odd_continuous R).integrable_of_hasCompactSupport (compact_odd_hasCompactSupport R hR)

private theorem compact_odd_neg (R t : ℝ) : compactOdd R (-t) = -compactOdd R t := by
  simp [compactOdd,profile,neg_div,abs_neg]

private theorem exponential_even (s t : ℝ) : exponential s (-t) = exponential s t := by
  simp only [exponential,abs_neg]

theorem exponential_integrable (s : ℝ) (hs : 0 < s) : Integrable (exponential s) := by
  let m := (Ioi (0 : ℝ)).indicator (fun t => exp (-s*t))
  have hi : Integrable m := (exp_neg_integrableOn_Ioi 0 hs).integrable_indicator measurableSet_Ioi
  apply (hi.add hi.comp_neg).congr
  filter_upwards [volume.ae_ne (0 : ℝ)] with t ht
  rcases lt_or_gt_of_ne ht with hn|hp
  · simp only [Pi.add_apply,m,indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from not_lt.mpr hn.le),
      indicator_of_mem (show -t ∈ Ioi (0 : ℝ) from neg_pos.mpr hn),zero_add,
      exponential,abs_of_neg hn]
  · simp only [Pi.add_apply,m,indicator_of_mem (show t ∈ Ioi (0 : ℝ) from hp),
      indicator_of_notMem (show -t ∉ Ioi (0 : ℝ) from not_lt.mpr (neg_nonpos.mpr hp.le)),
      add_zero,exponential,abs_of_pos hp]

private theorem exponential_le_one (s : ℝ) (hs : 0 ≤ s) (t : ℝ) : |exponential s t| ≤ 1 := by
  rw [exponential,abs_of_pos (exp_pos _)]
  exact exp_le_one_iff.mpr (by nlinarith [abs_nonneg t])

/-- The actual smoothed odd field supplies global L1, L2 and continuity. -/
theorem smoothed_L1_L2 (s R : ℝ) (hs : 0 < s) (hR : 0 < R) :
    Integrable (smoothed s R) ∧ MemLp (smoothed s R) 2 volume ∧ Continuous (smoothed s R) := by
  have hfi := compact_odd_integrable R hR
  have hgi := exponential_integrable s hs
  have hi : Integrable (smoothed s R) := hfi.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hgi
  have hb (r : ℝ) : |smoothed s R r| ≤ ∫ t : ℝ, |compactOdd R t| := by
    change ‖smoothed s R r‖ ≤ ∫ t : ℝ, ‖compactOdd R t‖
    rw [smoothed,convolution_def]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _)) hfi.norm
    apply ae_of_all
    intro t
    change |compactOdd R t*exponential s (r-t)| ≤ |compactOdd R t|
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (exponential_le_one s hs.le _) (abs_nonneg _)).trans_eq (mul_one _)
  exact ⟨hi,integrable_bounded_memLp_two _ hi _ (ae_of_all _ hb),
    (compact_odd_hasCompactSupport R hR).continuous_convolution_left
      (ContinuousLinearMap.mul ℝ ℝ) (compact_odd_continuous R) hgi.locallyIntegrable⟩

/-- Oddness is retained by the actual convolution, including its origin value. -/
theorem smoothed_neg (s R r : ℝ) : smoothed s R (-r) = -smoothed s R r := by
  rw [smoothed,convolution_def,← integral_neg_eq_self]
  simp only [ContinuousLinearMap.mul_apply',compact_odd_neg]
  have he (t : ℝ) : exponential s (-r- -t)=exponential s (r-t) := by
    rw [show -r- -t=-(r-t) by ring,exponential_even]
  simp_rw [he,neg_mul]
  rw [integral_neg]
  rfl

/-- The division at r=0 loses no field value because the smoothed field is odd. -/
theorem radial_test_odd_field (s R : ℝ) :
    oddRadialMoment (radialTest s R) = fun r => (smoothed s R r : ℂ) := by
  funext r
  have hzero : smoothed s R 0=0 := by
    have h := smoothed_neg s R 0
    simp only [neg_zero] at h
    linarith
  rcases lt_trichotomy r 0 with hn|rfl|hp
  · simp only [oddRadialMoment,radialTest,abs_of_neg hn,smoothed_neg]
    congr 1
    field_simp [hn.ne]
  · simp [oddRadialMoment,hzero]
  · simp only [oddRadialMoment,radialTest,abs_of_pos hp]
    congr 1
    field_simp [hp.ne']

private theorem complex_smoothed (s R : ℝ) :
    (fun r => (smoothed s R r : ℂ)) =
      (fun t => (compactOdd R t : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (fun t => (exponential s t : ℂ)) := by
  funext r
  simp only [smoothed,convolution_def,ContinuousLinearMap.mul_apply',← Complex.ofReal_mul,
    integral_complex_ofReal]

private theorem compact_odd_field (R : ℝ) :
    (fun t => (compactOdd R t : ℂ)) = oddRadialMoment (fun r => profile (r/R)) := by
  funext t
  simp only [compactOdd,oddRadialMoment,profile,abs_div,abs_abs]

/-- Exact honest Fourier convolution identity. No explicit transform of the
exponential is needed for the subsequent spectral domination. -/
theorem radial_test_fourier_identity (s R : ℝ) (hs : 0 < s) (hR : 0 < R) (w : ℝ) :
    𝓕 (oddRadialMoment (radialTest s R)) w =
      (-(Complex.I*(w : ℂ))*(radial_fourier (fun r => profile (r/R)) (2*Real.pi*w) : ℂ))*
        𝓕 (fun t : ℝ => (exponential s t : ℂ)) w := by
  rw [radial_test_odd_field,complex_smoothed]
  have he := Real.fourier_mul_convolution_eq (R := ℂ) (E := ℝ)
    (compact_odd_integrable R hR).ofReal (exponential_integrable s hs).ofReal
    (by unfold compactOdd profile; fun_prop) (by unfold exponential; fun_prop) w
  calc
    _ = 𝓕 (fun t : ℝ => (compactOdd R t : ℂ)) w *
        𝓕 (fun t : ℝ => (exponential s t : ℂ)) w := he
    _ = _ := by
      rw [compact_odd_field,odd_radial_integral_fourier _ (scaled_profile_odd_L1_L2 R hR).1]



/-- The actual radial test supplies the analytic premises needed by Parseval. -/
theorem radial_test_L1_L2 (s R : ℝ) (hs : 0 < s) (hR : 0 < R) :
    Integrable (oddRadialMoment (radialTest s R)) ∧
      MemLp (oddRadialMoment (radialTest s R)) 2 volume := by
  rw [radial_test_odd_field]
  obtain ⟨hi,h₂,_⟩ := smoothed_L1_L2 s R hs hR
  exact ⟨hi.ofReal,h₂.ofReal⟩

/-- Direct spectral domination by the SAME positive compact profile.
The constant is the actual L1 norm of the even exponential, independent of roots. -/
theorem radial_test_fourier_bound (s R : ℝ) (hs : 0 < s) (hR : 0 < R) (k : ℝ) (hk : k ≠ 0) :
    |radial_fourier (radialTest s R) k| ≤
      (∫ t : ℝ, exponential s t)*radial_fourier (fun r => profile (r/R)) k := by
  let w := k/(2*Real.pi)
  have hw : w ≠ 0 := div_ne_zero hk (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hkw : 2*Real.pi*w=k := by dsimp [w]; field_simp
  have hpositive : 0 ≤ radial_fourier (fun r => profile (r/R)) k := by
    rw [radial_fourier_dilate profile R hR]
    exact mul_nonneg (pow_nonneg hR.le 3)
      (profile_radial_fourier_pos _ (mul_ne_zero hR.ne' hk)).le
  have hE : ‖𝓕 (fun t : ℝ => (exponential s t : ℂ)) w‖ ≤ ∫ t : ℝ, exponential s t := by
    rw [Real.fourier_eq]
    apply (norm_integral_le_integral_norm _).trans_eq
    apply integral_congr_ae
    apply ae_of_all
    intro t
    dsimp only
    rw [Circle.norm_smul,Complex.norm_real,Real.norm_eq_abs]
    exact abs_of_pos (exp_pos _)
  have he := radial_test_fourier_identity s R hs hR w
  rw [odd_radial_integral_fourier _ (radial_test_L1_L2 s R hs hR).1 w,hkw] at he
  have hn := congrArg norm he
  simp only [norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs] at hn
  have hp := mul_le_mul_of_nonneg_left hE (mul_nonneg (abs_nonneg w) hpositive)
  rw [abs_of_nonneg hpositive] at hn
  rw [← hn] at hp
  apply (mul_le_mul_iff_right₀ (abs_pos.mpr hw)).mp
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hp

/-- Coefficient of the exact exterior Yukawa tail. -/
def exteriorCoefficient (s R : ℝ) : ℝ := ∫ t : ℝ, compactOdd R t*exp (s*t)

private theorem compact_exponential_integrable (s R : ℝ) (hR : 0 < R) :
    Integrable (fun t => compactOdd R t*exp (s*t)) :=
  ((compact_odd_continuous R).mul (by fun_prop)).integrable_of_hasCompactSupport
    ((compact_odd_hasCompactSupport R hR).mul_right)

/-- A positive fixed coefficient, derived by reflection rather than supplied. -/
theorem exterior_coefficient_pos (s R : ℝ) (hs : 0 < s) (hR : 0 < R) :
    0 < exteriorCoefficient s R := by
  let f : ℝ → ℝ := fun t => compactOdd R t*(exp (s*t)-exp (-s*t))
  have hc : Continuous f := (compact_odd_continuous R).mul (by fun_prop)
  have hi : Integrable f := hc.integrable_of_hasCompactSupport
    ((compact_odd_hasCompactSupport R hR).mul_right)
  have hnonneg (t : ℝ) : 0 ≤ f t := by
    by_cases ht : 0 ≤ t
    · exact mul_nonneg (mul_nonneg ht (sq_nonneg _))
        (sub_nonneg.mpr (exp_le_exp.mpr (by nlinarith)))
    · apply mul_nonneg_of_nonpos_of_nonpos
      · exact mul_nonpos_of_nonpos_of_nonneg (not_le.mp ht).le (sq_nonneg _)
      · exact sub_nonpos.mpr (exp_le_exp.mpr (by nlinarith [not_le.mp ht]))
  have hmid : 0 < compactOdd R (R/2) := by
    have he : (R/2)/R=1/2 := by field_simp
    rw [compactOdd,he,profile]
    norm_num
    linarith
  have hdiff : 0 < exp (s*(R/2))-exp (-s*(R/2)) :=
    sub_pos.mpr (exp_lt_exp.mpr (by nlinarith))
  have hpos : 0 < ∫ t : ℝ, f t := integral_pos_of_integrable_nonneg_nonzero hc hi hnonneg
    (ne_of_gt (mul_pos hmid hdiff))
  have he : (∫ t : ℝ, compactOdd R t*exp (-s*t)) = -exteriorCoefficient s R := by
    rw [← integral_neg_eq_self]
    simp only [compact_odd_neg,mul_neg,neg_mul,neg_neg]
    rw [integral_neg]
    rfl
  have heq : (∫ t : ℝ, f t)=2*exteriorCoefficient s R := by
    dsimp only [f]
    simp_rw [mul_sub]
    rw [integral_sub (compact_exponential_integrable s R hR)
      (by simpa only [neg_mul] using compact_exponential_integrable (-s) R hR),he]
    dsimp only [exteriorCoefficient]
    ring
  rw [heq] at hpos
  linarith

/-- Outside the fixed compact core the actual convolution is exactly an
exponential, with a strictly positive root-independent coefficient. -/
theorem smoothed_exterior (s R : ℝ) (hR : 0 < R) (r : ℝ) (hr : R ≤ r) :
    smoothed s R r=exp (-s*r)*exteriorCoefficient s R := by
  rw [smoothed,convolution_def,exteriorCoefficient,← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  simp only [ContinuousLinearMap.mul_apply']
  by_cases ht : |t| ≤ R
  · have htR : t ≤ R := (abs_le.mp ht).2
    rw [exponential,abs_of_nonneg (by linarith : 0 ≤ r-t)]
    rw [show -s*(r-t)= -s*r+s*t by ring,exp_add]
    ring
  · simp only [compactOdd,profile_outside R hR t (not_le.mp ht).le,mul_zero,zero_mul]

/-- The radial test is exactly a fixed positive multiple of Yukawa outside R. -/
theorem radial_test_exterior (s R : ℝ) (hR : 0 < R) (r : ℝ) (hr : R ≤ r) :
    radialTest s R r=exteriorCoefficient s R*exp (-s*r)/r := by
  rw [radialTest,smoothed_exterior s R hR r hr,mul_comm]

end FMSA.Convergence.YukawaConvolutionTest
/-- info: 'FMSA.Convergence.YukawaConvolutionTest.compact_odd_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.YukawaConvolutionTest.compact_odd_continuous
/-- info: 'FMSA.Convergence.YukawaConvolutionTest.compact_odd_hasCompactSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.YukawaConvolutionTest.compact_odd_hasCompactSupport
/-- info: 'FMSA.Convergence.YukawaConvolutionTest.compact_odd_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.YukawaConvolutionTest.compact_odd_integrable
/-- info: 'FMSA.Convergence.YukawaConvolutionTest.exponential_integrable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.YukawaConvolutionTest.exponential_integrable
/-- info: 'FMSA.Convergence.YukawaConvolutionTest.smoothed_L1_L2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.YukawaConvolutionTest.smoothed_L1_L2
/-- info: 'FMSA.Convergence.YukawaConvolutionTest.smoothed_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.YukawaConvolutionTest.smoothed_neg
/-- info: 'FMSA.Convergence.YukawaConvolutionTest.radial_test_odd_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.YukawaConvolutionTest.radial_test_odd_field
/-- info: 'FMSA.Convergence.YukawaConvolutionTest.radial_test_fourier_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.YukawaConvolutionTest.radial_test_fourier_identity
/-- info: 'FMSA.Convergence.YukawaConvolutionTest.radial_test_L1_L2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.YukawaConvolutionTest.radial_test_L1_L2
/-- info: 'FMSA.Convergence.YukawaConvolutionTest.radial_test_fourier_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.YukawaConvolutionTest.radial_test_fourier_bound
/-- info: 'FMSA.Convergence.YukawaConvolutionTest.exterior_coefficient_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.YukawaConvolutionTest.exterior_coefficient_pos
/-- info: 'FMSA.Convergence.YukawaConvolutionTest.smoothed_exterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.YukawaConvolutionTest.smoothed_exterior
/-- info: 'FMSA.Convergence.YukawaConvolutionTest.radial_test_exterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.YukawaConvolutionTest.radial_test_exterior
