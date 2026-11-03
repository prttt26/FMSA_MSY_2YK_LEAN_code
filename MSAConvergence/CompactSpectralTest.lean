import MSAConvergence.ScalarKernelResolventBounds

/-! The elementary numerator of the three-dimensional Fourier transform
of the compact radial function (1-r)_+^2. This module does not assume or
claim an actual mixture covariance identity. -/
noncomputable section
open Set Real MeasureTheory
namespace FMSA.Convergence.CompactSpectralTest

def numerator (x : ℝ) : ℝ := x*(2+cos x)-3*sin x
private def first (x : ℝ) : ℝ := 2-2*cos x-x*sin x
private def second (x : ℝ) : ℝ := sin x-x*cos x

private theorem deriv₀ (x : ℝ) : HasDerivAt numerator (first x) x := by
  convert! ((hasDerivAt_id x).mul ((hasDerivAt_cos x).const_add 2)).sub
    ((hasDerivAt_sin x).const_mul 3) using 1
  dsimp only [first,id]
  ring

private theorem deriv₁ (x : ℝ) : HasDerivAt first (second x) x := by
  convert! ((hasDerivAt_const x (2 : ℝ)).sub ((hasDerivAt_cos x).const_mul 2)).sub
    ((hasDerivAt_id x).mul (hasDerivAt_sin x)) using 1
  dsimp only [second,id]
  ring

private theorem deriv₂ (x : ℝ) : HasDerivAt second (x*sin x) x := by
  convert! (hasDerivAt_sin x).sub ((hasDerivAt_id x).mul (hasDerivAt_cos x)) using 1
  dsimp only [id]
  ring

private theorem positive_from_derivative (f g : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (hd : ∀ x, HasDerivAt f (g x) x) (h0 : f 0 = 0)
    (hg : ∀ x ∈ Ioo 0 b, 0 < g x) : ∀ x ∈ Ioc 0 b, 0 < f x := by
  have hm : StrictMonoOn f (Icc 0 b) := strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun x _ => (hd x).continuousAt.continuousWithinAt) (by
      intro x hx
      rw [interior_Icc] at hx
      rw [(hd x).deriv]
      exact hg x hx)
  intro x hx
  simpa only [h0] using hm ⟨le_rfl,hb.le⟩ ⟨hx.1.le,hx.2⟩ hx.1

/-- The compact radial test's spectral numerator is strictly positive
at every positive frequency, including frequencies beyond pi. -/
theorem numerator_pos (x : ℝ) (hx : 0 < x) : 0 < numerator x := by
  have h₂ : ∀ y ∈ Ioc 0 Real.pi, 0 < second y :=
    positive_from_derivative second (fun y => y*sin y) Real.pi Real.pi_pos deriv₂
      (by simp [second]) (fun y hy => mul_pos hy.1 (sin_pos_of_pos_of_lt_pi hy.1 hy.2))
  have h₁ : ∀ y ∈ Ioc 0 Real.pi, 0 < first y :=
    positive_from_derivative first second Real.pi Real.pi_pos deriv₁
      (by simp [first]) (fun y hy => h₂ y ⟨hy.1,hy.2.le⟩)
  have h₀ : ∀ y ∈ Ioc 0 Real.pi, 0 < numerator y :=
    positive_from_derivative numerator first Real.pi Real.pi_pos deriv₀
      (by simp [numerator]) (fun y hy => h₁ y ⟨hy.1,hy.2.le⟩)
  by_cases hp : x ≤ Real.pi
  · exact h₀ x ⟨hx,hp⟩
  · have hc := mul_le_mul_of_nonneg_left (neg_one_le_cos x) hx.le
    have hs := sin_le_one x
    have hpi := Real.pi_gt_three
    dsimp [numerator]
    nlinarith [lt_of_not_ge hp]

private theorem nonnegative_from_derivative (f g : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hd : ∀ x, HasDerivAt f (g x) x) (h0 : 0 ≤ f 0)
    (hg : ∀ x ∈ Icc 0 b, 0 ≤ g x) : ∀ x ∈ Icc 0 b, 0 ≤ f x := by
  have hm : MonotoneOn f (Icc 0 b) := monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt) (by
      intro x hx
      rw [interior_Icc] at hx
      rw [(hd x).deriv]
      exact hg x ⟨hx.1.le,hx.2.le⟩)
  intro x hx
  exact h0.trans (hm ⟨le_rfl,hb⟩ hx hx.1)

/-- A quantitative lower bound at the removable zero-frequency point. -/
theorem numerator_small_lower (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    x^5/120 ≤ numerator x := by
  have hs : ∀ y ∈ Icc (0 : ℝ) 1, y/2 ≤ sin y := by
    intro y hy
    by_cases hzero : y=0
    · simp [hzero]
    have hpos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hzero)
    have hcube : y^3 ≤ y := by
      calc
        y^3 = y*y^2 := by ring
        _ ≤ y*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hy.1 hy.2) hy.1
        _ = y := mul_one _
    linarith [sin_gt_sub_cube hpos hy.2]
  have h₂ : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ second y-y^3/6 :=
    nonnegative_from_derivative (fun y => second y-y^3/6)
      (fun y => y*sin y-y^2/2) 1 zero_le_one (fun y => by
        convert! (deriv₂ y).sub (((hasDerivAt_id y).pow 3).div_const 6) using 1
        dsimp only [id]
        ring)
      (by simp [second]) (fun y hy => by
        have h := mul_le_mul_of_nonneg_left (hs y hy) hy.1
        nlinarith)
  have h₁ : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ first y-y^4/24 :=
    nonnegative_from_derivative (fun y => first y-y^4/24)
      (fun y => second y-y^3/6) 1 zero_le_one (fun y => by
        convert! (deriv₁ y).sub (((hasDerivAt_id y).pow 4).div_const 24) using 1
        dsimp only [id]
        ring)
      (by simp [first]) h₂
  have h₀ : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ numerator y-y^5/120 :=
    nonnegative_from_derivative (fun y => numerator y-y^5/120)
      (fun y => first y-y^4/24) 1 zero_le_one (fun y => by
        convert! (deriv₀ y).sub (((hasDerivAt_id y).pow 5).div_const 120) using 1
        dsimp only [id]
        ring)
      (by simp [numerator]) h₁
  exact sub_nonneg.mp (h₀ x hx)

/-- At high frequency the positive numerator has a linear lower bound. -/
theorem numerator_large_lower (x : ℝ) (hx : 6 ≤ x) : x/2 ≤ numerator x := by
  have hpos : 0 ≤ x := by linarith
  have hc := mul_le_mul_of_nonneg_left (neg_one_le_cos x) hpos
  have hs := sin_le_one x
  dsimp [numerator]
  nlinarith

/-- A single positive lower constant controls the spectral weight at ALL
positive frequencies. No numerical grid or unproved sign premise is used. -/
theorem numerator_global_lower : ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 0 < x →
    c*x^5 ≤ numerator x*(1+x^2)^2 := by
  let q : ℝ → ℝ := fun x => numerator x*(1+x^2)^2/x^5
  have hq : ContinuousOn q (Icc 1 6) := by
    intro x hx
    have hpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
    apply ContinuousAt.continuousWithinAt
    dsimp [q,numerator]
    fun_prop (disch := positivity)
  obtain ⟨m,hm,hmin⟩ := isCompact_Icc.exists_isMinOn (show (Icc (1 : ℝ) 6).Nonempty by exact ⟨1,by norm_num⟩) hq
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm.1
  have hqm : 0 < q m := div_pos (mul_pos (numerator_pos m hmpos) (by positivity)) (pow_pos hmpos _)
  let c := min (1/120 : ℝ) (min (1/2 : ℝ) (q m))
  have hc : 0 < c := lt_min (by norm_num) (lt_min (by norm_num) hqm)
  have hcsmall : c ≤ 1/120 := min_le_left _ _
  have hclarge : c ≤ 1/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hcm : c ≤ q m := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c,hc,?_⟩
  intro x hx
  have hf : 0 ≤ numerator x := (numerator_pos x hx).le
  by_cases hs : x ≤ 1
  · calc
      c*x^5 ≤ x^5/120 := by nlinarith [mul_le_mul_of_nonneg_right hcsmall (pow_nonneg hx.le 5)]
      _ ≤ numerator x := numerator_small_lower x ⟨hx.le,hs⟩
      _ ≤ numerator x*(1+x^2)^2 := le_mul_of_one_le_right hf (by nlinarith [sq_nonneg x])
  · by_cases hl : 6 ≤ x
    · calc
        c*x^5 ≤ (1/2 : ℝ)*x^5 := mul_le_mul_of_nonneg_right hclarge (pow_nonneg hx.le 5)
        _ = (x/2)*(x^2)^2 := by ring
        _ ≤ numerator x*(1+x^2)^2 := mul_le_mul (numerator_large_lower x hl)
          (by nlinarith [sq_nonneg x]) (by positivity) hf
    · have hmid := hcm.trans (hmin ⟨(lt_of_not_ge hs).le,(lt_of_not_ge hl).le⟩)
      exact (le_div_iff₀ (pow_pos hx 5)).mp hmid

private def polynomial₀ (r : ℝ) := r*(1-r)^2
private def polynomial₁ (r : ℝ) := 1-4*r+3*r^2
private def polynomial₂ (r : ℝ) := -4+6*r
private def primitive (k r : ℝ) :=
  -polynomial₀ r*cos (k*r)/k+polynomial₁ r*sin (k*r)/k^2+
    polynomial₂ r*cos (k*r)/k^3-6*sin (k*r)/k^4

private theorem polynomial_deriv₀ (r : ℝ) : HasDerivAt polynomial₀ (polynomial₁ r) r := by
  convert! (hasDerivAt_id r).mul (((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).pow 2)
    using 1
  simp only [polynomial₁,id_eq,Pi.sub_apply,Pi.pow_apply]
  ring

private theorem polynomial_deriv₁ (r : ℝ) : HasDerivAt polynomial₁ (polynomial₂ r) r := by
  convert! ((hasDerivAt_const r (1 : ℝ)).sub ((hasDerivAt_id r).const_mul 4)).add
    (((hasDerivAt_id r).pow 2).const_mul 3) using 1
  dsimp only [polynomial₂,id]
  ring

private theorem polynomial_deriv₂ (r : ℝ) : HasDerivAt polynomial₂ 6 r := by
  convert! ((hasDerivAt_id r).const_mul 6).const_add (-4) using 1
  ring

private theorem primitive_deriv (k r : ℝ) (hk : k ≠ 0) :
    HasDerivAt (primitive k) (r*(1-r)^2*sin (k*r)) r := by
  have hc := ((hasDerivAt_id r).const_mul k).cos
  have hs := ((hasDerivAt_id r).const_mul k).sin
  convert! ((((polynomial_deriv₀ r).mul hc).neg.div_const k).add
    (((polynomial_deriv₁ r).mul hs).div_const (k^2))).add
    (((polynomial_deriv₂ r).mul hc).div_const (k^3)) |>.sub
    ((hs.const_mul 6).div_const (k^4)) using 1
  · funext x
    simp only [primitive,Pi.sub_apply,Pi.add_apply,Pi.mul_apply,Pi.neg_apply,id_eq,div_eq_mul_inv]
    ring
  · dsimp only [polynomial₀,polynomial₁,polynomial₂,id]
    field_simp [hk]
    ring

/-- The literal compact sine integral; no guessed Fourier surrogate. -/
theorem unit_sine_integral (k : ℝ) (hk : k ≠ 0) :
    (∫ r in (0 : ℝ)..1, r*(1-r)^2*sin (k*r)) = 2*numerator k/k^4 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => primitive_deriv k r hk)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [primitive,polynomial₀,polynomial₁,polynomial₂,numerator,mul_zero,sin_zero,cos_zero]
  field_simp
  ring

/-- An even, compact radial profile. Its contact radius is one before scaling. -/
def profile (r : ℝ) : ℝ := (max (1-|r|) 0)^2

/-- Identification with the honest radial Fourier integral away from zero. -/
theorem profile_radial_fourier (k : ℝ) (hk : k ≠ 0) :
    FMSA.HardSphere.radial_fourier profile k = 8*Real.pi*numerator k/k^5 := by
  unfold FMSA.HardSphere.radial_fourier
  have hi : (∫ r in Ioi (0 : ℝ), r*profile r*sin (k*r)) =
      ∫ r in (0 : ℝ)..1, r*(1-r)^2*sin (k*r) := by
    calc
      _ = ∫ r in Ioi (0 : ℝ), (Icc (0 : ℝ) 1).indicator
          (fun r => r*(1-r)^2*sin (k*r)) r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        change 0 < r at hr
        by_cases h : r ≤ 1
        · simp [profile,abs_of_pos hr,max_eq_left (by linarith : 0 ≤ 1-r),
            indicator_of_mem (show r ∈ Icc (0 : ℝ) 1 from ⟨hr.le,h⟩)]
        · simp [profile,abs_of_pos hr,max_eq_right (by linarith : 1-r ≤ 0),
            indicator_of_notMem (show r ∉ Icc (0 : ℝ) 1 from fun hh => h hh.2)]
      _ = ∫ r in Ioc (0 : ℝ) 1, r*(1-r)^2*sin (k*r) := by
        have hset : Ioi (0 : ℝ) ∩ Icc (0 : ℝ) 1 = Ioc (0 : ℝ) 1 := by
          ext r
          simp only [mem_inter_iff,mem_Ioi,mem_Icc,mem_Ioc]
          constructor
          · rintro ⟨h,_,h'⟩; exact ⟨h,h'⟩
          · rintro ⟨h,h'⟩; exact ⟨h,h.le,h'⟩
        rw [setIntegral_indicator measurableSet_Icc,hset]
      _ = _ := (intervalIntegral.integral_of_le zero_le_one).symm
  rw [hi,unit_sine_integral k hk]
  field_simp
  ring

/-- The honest transform is strictly positive at every nonzero frequency. -/
theorem profile_radial_fourier_pos (k : ℝ) (hk : k ≠ 0) :
    0 < FMSA.HardSphere.radial_fourier profile k := by
  rcases lt_or_gt_of_ne hk with hneg|hpos
  · rw [← FMSA.HardSphere.radial_fourier_neg profile k]
    rw [profile_radial_fourier (-k) (neg_ne_zero.mpr hk)]
    exact div_pos (mul_pos (by positivity) (numerator_pos _ (by linarith))) (pow_pos (by linarith) _)
  · rw [profile_radial_fourier k hk]
    exact div_pos (mul_pos (by positivity) (numerator_pos k hpos)) (pow_pos hpos _)

/-- A polynomially decaying lower bound for the ACTUAL test transform.
The radial integral convention assigns zero at k=0, so it is excluded. -/
theorem profile_radial_fourier_lower : ∃ c : ℝ, 0 < c ∧ ∀ k : ℝ, k ≠ 0 →
    c/(1+k^2)^2 ≤ FMSA.HardSphere.radial_fourier profile k := by
  obtain ⟨c,hc,hbound⟩ := numerator_global_lower
  refine ⟨8*Real.pi*c,by positivity,?_⟩
  have hp (k : ℝ) (hk : 0 < k) :
      8*Real.pi*c/(1+k^2)^2 ≤ FMSA.HardSphere.radial_fourier profile k := by
    rw [profile_radial_fourier k hk.ne']
    apply (div_le_div_iff₀ (by positivity : 0 < (1+k^2)^2) (pow_pos hk 5)).mpr
    have h := mul_le_mul_of_nonneg_left (hbound k hk) (by positivity : 0 ≤ 8*Real.pi)
    nlinarith [h]
  intro k hk
  rcases lt_or_gt_of_ne hk with hneg|hpos
  · have h := hp (-k) (by linarith)
    simpa only [neg_sq,FMSA.HardSphere.radial_fourier_neg] using h
  · exact hp k hpos

/-- Positive spatial dilation of the honest radial integral, with its exact
cubic volume factor. The identity does not assume Fourier integrability. -/
theorem radial_fourier_dilate (f : ℝ → ℝ) (R : ℝ) (hR : 0 < R) (k : ℝ) :
    FMSA.HardSphere.radial_fourier (fun r => f (r/R)) k =
      R^3*FMSA.HardSphere.radial_fourier f (R*k) := by
  by_cases hk : k=0
  · simp [hk,FMSA.HardSphere.radial_fourier]
  let g : ℝ → ℝ := fun r => r*f (r/R)*sin (k*r)
  have harg (r : ℝ) : g (R*r) = R*(r*f r*sin ((R*k)*r)) := by
    dsimp only [g]
    rw [mul_div_cancel_left₀ r hR.ne',show k*(R*r)=(R*k)*r by ring]
    ring
  have hi := integral_comp_mul_left_Ioi g 0 hR
  simp only [harg,mul_zero,smul_eq_mul,integral_const_mul] at hi
  have hm := congrArg (fun x : ℝ => R*x) hi
  have he : (∫ r in Ioi (0 : ℝ), g r) =
      R^2*(∫ r in Ioi (0 : ℝ), r*f r*sin ((R*k)*r)) := by
    simpa only [← mul_assoc,mul_inv_cancel₀ hR.ne',one_mul,pow_two] using hm.symm
  change (4*Real.pi/k)*(∫ r in Ioi (0 : ℝ), g r) = _
  rw [he]
  unfold FMSA.HardSphere.radial_fourier
  field_simp [hk,hR.ne']

/-- The compact positive-spectrum test fits inside ANY positive hard-core
radius and retains a uniform polynomial Fourier lower bound. -/
theorem scaled_profile_radial_fourier_lower (R : ℝ) (hR : 0 < R) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℝ, k ≠ 0 →
      c/(1+k^2)^2 ≤ FMSA.HardSphere.radial_fourier (fun r => profile (r/R)) k := by
  obtain ⟨c,hc,hbound⟩ := profile_radial_fourier_lower
  refine ⟨R^3*c/(1+R^2)^2,by positivity,?_⟩
  intro k hk
  rw [radial_fourier_dilate profile R hR k]
  have hbase := mul_le_mul_of_nonneg_left (hbound (R*k) (mul_ne_zero hR.ne' hk))
    (pow_nonneg hR.le 3)
  have hden : (1+(R*k)^2)^2 ≤ (1+R^2)^2*(1+k^2)^2 := by
    have h : 1+(R*k)^2 ≤ (1+R^2)*(1+k^2) := by nlinarith [sq_nonneg R,sq_nonneg k]
    nlinarith [sq_nonneg ((1+R^2)*(1+k^2)-(1+(R*k)^2))]
  calc
    R^3*c/(1+R^2)^2/(1+k^2)^2 = R^3*c/((1+R^2)^2*(1+k^2)^2) := by rw [div_div]
    _ ≤ R^3*c/(1+(R*k)^2)^2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ ≤ R^3*FMSA.HardSphere.radial_fourier profile (R*k) := by
      simpa only [mul_div_assoc] using hbase

/-- The compact radial profile has the exact mass needed in the covariance
test, before the usual 4*pi angular factor and cubic radius scaling. -/
theorem unit_profile_mass : (∫ r in (0 : ℝ)..1, r^2*(1-r)^2) = (1 : ℝ)/30 := by
  have hd (x : ℝ) : HasDerivAt (fun r : ℝ => r^3/3-r^4/2+r^5/5) (x^2*(1-x)^2) x := by
    convert! ((((hasDerivAt_id x).pow 3).div_const 3).sub
      (((hasDerivAt_id x).pow 4).div_const 2)).add
      (((hasDerivAt_id x).pow 5).div_const 5) using 1
    dsimp only [id]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  norm_num

end FMSA.Convergence.CompactSpectralTest
/-- info: 'FMSA.Convergence.CompactSpectralTest.numerator_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CompactSpectralTest.numerator_pos
/-- info: 'FMSA.Convergence.CompactSpectralTest.numerator_small_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CompactSpectralTest.numerator_small_lower
/-- info: 'FMSA.Convergence.CompactSpectralTest.numerator_large_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CompactSpectralTest.numerator_large_lower
/-- info: 'FMSA.Convergence.CompactSpectralTest.numerator_global_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CompactSpectralTest.numerator_global_lower
/-- info: 'FMSA.Convergence.CompactSpectralTest.unit_sine_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CompactSpectralTest.unit_sine_integral
/-- info: 'FMSA.Convergence.CompactSpectralTest.profile_radial_fourier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CompactSpectralTest.profile_radial_fourier
/-- info: 'FMSA.Convergence.CompactSpectralTest.profile_radial_fourier_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CompactSpectralTest.profile_radial_fourier_pos
/-- info: 'FMSA.Convergence.CompactSpectralTest.profile_radial_fourier_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CompactSpectralTest.profile_radial_fourier_lower
/-- info: 'FMSA.Convergence.CompactSpectralTest.radial_fourier_dilate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CompactSpectralTest.radial_fourier_dilate
/-- info: 'FMSA.Convergence.CompactSpectralTest.scaled_profile_radial_fourier_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CompactSpectralTest.scaled_profile_radial_fourier_lower
/-- info: 'FMSA.Convergence.CompactSpectralTest.unit_profile_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.CompactSpectralTest.unit_profile_mass
