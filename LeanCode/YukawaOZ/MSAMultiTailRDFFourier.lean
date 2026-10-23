import LeanCode.YukawaOZ.MSAMultiTailRDFComplex
import LeanCode.YukawaOZ.MSAMultiTailRDFAxis

/-! Actual Fourier identification for the globally constructed RDF. -/
noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTail
variable {ι : Type*} [Fintype ι]

theorem actualFactor_axis (xi : ℝ) (z Dt G : ι → ℝ) (hz : ∀ u, 0 < z u)
    {k : ℝ} (hk : k ≠ 0) :
    actualFactor xi z Dt G ((k : ℂ) * Complex.I) =
      reconstructedFactor xi z Dt G ((k : ℂ) * Complex.I) := by
  have hiq : IntegrableOn (qRight xi z Dt G) (Ioi 0) := by
    simpa using qRight_weighted_integrable xi z Dt G hz (a := 0) (by rfl)
  have hic := complex_laplace_integrable_of_L1 (qRight xi z Dt G)
    (qRight_continuous xi z Dt G).continuousOn hiq
    (s := (k : ℂ) * Complex.I) (by simp)
  have hQ : causalComplexLaplace (qRight xi z Dt G) ((k : ℂ) * Complex.I) =
      (Qre xi z Dt G k : ℂ) + (Qim xi z Dt G k : ℂ) * Complex.I := by
    have he (u : ℝ) : Complex.exp (-((k : ℂ) * Complex.I) * u) =
        (Real.cos (k * u) : ℂ) - (Real.sin (k * u) : ℂ) * Complex.I := by
      rw [show -((k : ℂ) * Complex.I) * u = -((k * u : ℝ) : ℂ) * Complex.I by push_cast; ring]
      simpa only [neg_mul] using axis_exp (k * u)
    unfold causalComplexLaplace
    apply Complex.ext
    · have hir := integral_re hic
      simp only [RCLike.re_to_complex] at hir
      rw [← hir, Qre_eq_integral xi z Dt G hz hk]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only
      rw [he, qRight_eq_q xi z Dt G hu.le]
      simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    · have hii := integral_im hic
      simp only [RCLike.im_to_complex] at hii
      rw [← hii, Qim_eq_neg_integral xi z Dt G hz hk, ← integral_neg]
      simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, zero_add, add_zero]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only
      rw [he, qRight_eq_q xi z Dt G hu.le]
      simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, zero_add]
      ring
  unfold actualFactor
  rw [hQ, reconstructedFactor_axis xi z Dt G hz hk]
  push_cast
  ring

theorem core_first_complex {s : ℂ} (hs : s ≠ 0) :
    (∫ u in (0 : ℝ)..1, (u : ℂ) * Complex.exp (-s * u)) =
      (1 - (s + 1) * Complex.exp (-s)) / s ^ 2 := by
  have hd : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun u : ℝ => (u : ℂ) * Complex.exp (-s * u))
      (Complex.exp (-s * u) - s * ((u : ℂ) * Complex.exp (-s * u))) u := by
    intro u _
    have h0 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    exact (h0.mul (h0.const_mul (-s)).cexp).congr_deriv (by ring)
  have hi0 : IntervalIntegrable (fun u : ℝ => Complex.exp (-s * u)) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have hi1 : IntervalIntegrable (fun u : ℝ => (u : ℂ) * Complex.exp (-s * u)) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hi0.sub (hi1.const_mul s))
  rw [intervalIntegral.integral_sub hi0 (hi1.const_mul s), intervalIntegral.integral_const_mul,
    integral_exp_mul_complex (neg_ne_zero.mpr hs)] at h
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero,
    zero_mul, sub_zero] at h
  field_simp [hs] at h ⊢
  linear_combination -h

def excessSupported (xi : ℝ) (z Dt G : ι → ℝ) : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator (rdfExcess xi z Dt G)

/-- The actual r*h moment. Its contact-point convention is immaterial to
integrals; on the open core it equals -r, and outside it equals y(r-1)-r. -/
def rdfRadialMoment (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun r => -r) r + excessSupported xi z Dt G (r - 1)

def reconstructedH (xi : ℝ) (z Dt G : ι → ℝ) (r : ℝ) : ℝ :=
  rdfRadialMoment xi z Dt G r / r

theorem reconstructedH_core (xi : ℝ) (z Dt G : ι → ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    reconstructedH xi z Dt G r = -1 := by
  simp [reconstructedH, rdfRadialMoment, excessSupported, indicator_apply,
    show r ∈ Ioc (0 : ℝ) 1 from ⟨hr, hr1.le⟩, show ¬ 0 < r - 1 by linarith]
  field_simp [hr.ne']

theorem reconstructedH_exterior (xi : ℝ) (z Dt G : ι → ℝ) {r : ℝ} (hr : 1 < r) :
    reconstructedH xi z Dt G r = candidateRDF xi z Dt G r - 1 := by
  simp only [reconstructedH, rdfRadialMoment, excessSupported, indicator_apply,
    if_neg (show r ∉ Ioc (0 : ℝ) 1 from fun h => (not_le_of_gt hr) h.2), zero_add,
    if_pos (show r - 1 ∈ Ioi (0 : ℝ) from sub_pos.mpr hr), rdfExcess,
    candidateRDF, if_neg (show ¬ r < 1 by linarith)]
  field_simp [show r ≠ 0 by linarith]
  ring

theorem rdfRadialMoment_integrable (xi : ℝ) (z Dt G : ι → ℝ)
    (he : IntegrableOn (rdfExcess xi z Dt G) (Ioi 0)) :
    Integrable (rdfRadialMoment xi z Dt G) := by
  have hep : Integrable (excessSupported xi z Dt G) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr he
  have hc : Integrable ((Ioc (0 : ℝ) 1).indicator (fun r : ℝ => -r)) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr
      (by apply Continuous.integrableOn_Ioc; fun_prop)
  have ht : Integrable (fun r => excessSupported xi z Dt G (r - 1)) := by
    simpa only [sub_eq_add_neg] using hep.comp_add_right (-1)
  exact hc.add ht

theorem rdfRadialMoment_zero (xi : ℝ) (z Dt G : ι → ℝ) {r : ℝ} (hr : r ≤ 0) :
    rdfRadialMoment xi z Dt G r = 0 := by
  have hc : r ∉ Ioc (0 : ℝ) 1 := fun h => (not_lt_of_ge hr) h.1
  have ht : r - 1 ∉ Ioi (0 : ℝ) := by
    intro h
    change 0 < r - 1 at h
    linarith
  simp only [rdfRadialMoment, excessSupported, indicator_of_notMem hc, indicator_of_notMem ht, add_zero]

theorem rdfRadialMoment_complex_integrable (xi : ℝ) (z Dt G : ι → ℝ)
    (he : IntegrableOn (rdfExcess xi z Dt G) (Ioi 0)) {s : ℂ} (hsre : s.re = 0) :
    Integrable (fun u => (rdfRadialMoment xi z Dt G u : ℂ) * Complex.exp (-s * u)) := by
  exact (rdfRadialMoment_integrable xi z Dt G he).ofReal.mul_bdd (c := 1)
    (by apply Continuous.aestronglyMeasurable; fun_prop)
    (Filter.Eventually.of_forall (fun u => by simp [Complex.norm_exp, hsre]))

/-- Actual integral of r*h, with its compact hard core and shifted excess.
The identity includes the baseline term that is lost by treating y as L1. -/
theorem rdfRadialMoment_complex_transform (xi : ℝ) (z Dt G : ι → ℝ)
    (he : IntegrableOn (rdfExcess xi z Dt G) (Ioi 0)) {s : ℂ} (hsre : s.re = 0) (hs : s ≠ 0) :
    (∫ u in Ioi (0 : ℝ), (rdfRadialMoment xi z Dt G u : ℂ) * Complex.exp (-s * u)) =
      Complex.exp (-s) * (causalComplexLaplace (rdfExcess xi z Dt G) s + 1 / s ^ 2 + 1 / s) -
        1 / s ^ 2 := by
  have hep : Integrable (excessSupported xi z Dt G) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr he
  have hc : Integrable ((Ioc (0 : ℝ) 1).indicator
      (fun u : ℝ => (-u : ℂ) * Complex.exp (-s * u))) := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    apply Continuous.integrableOn_Ioc
    fun_prop
  have hts : Integrable (fun u : ℝ => (excessSupported xi z Dt G (u - 1) : ℂ)) := by
    have hepc : Integrable (fun u : ℝ => (excessSupported xi z Dt G u : ℂ)) := hep.ofReal
    simpa only [sub_eq_add_neg] using hepc.comp_add_right (-1)
  have ht : Integrable (fun u : ℝ => (excessSupported xi z Dt G (u - 1) : ℂ) * Complex.exp (-s * u)) :=
    hts.mul_bdd (c := 1)
      (by apply Continuous.aestronglyMeasurable; fun_prop)
      (Filter.Eventually.of_forall (fun u => by simp [Complex.norm_exp, hsre]))
  have hwhole : (∫ u in Ioi (0 : ℝ), (rdfRadialMoment xi z Dt G u : ℂ) * Complex.exp (-s * u)) =
      ∫ u : ℝ, (rdfRadialMoment xi z Dt G u : ℂ) * Complex.exp (-s * u) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    rw [rdfRadialMoment_zero xi z Dt G (le_of_not_gt hu)]
    simp
  have hsplit : (fun u : ℝ => (rdfRadialMoment xi z Dt G u : ℂ) * Complex.exp (-s * u)) =
      fun u => (Ioc (0 : ℝ) 1).indicator (fun u : ℝ => (-u : ℂ) * Complex.exp (-s * u)) u +
        (excessSupported xi z Dt G (u - 1) : ℂ) * Complex.exp (-s * u) := by
    funext u
    unfold rdfRadialMoment
    by_cases hu : u ∈ Ioc (0 : ℝ) 1 <;> simp [indicator_apply, hu] <;> ring
  have hshift : (∫ u : ℝ, (excessSupported xi z Dt G (u - 1) : ℂ) * Complex.exp (-s * u)) =
      Complex.exp (-s) * causalComplexLaplace (rdfExcess xi z Dt G) s := by
    let F := fun u : ℝ => (excessSupported xi z Dt G u : ℂ) * Complex.exp (-s * u)
    have hx : (fun u : ℝ => (excessSupported xi z Dt G (u - 1) : ℂ) * Complex.exp (-s * u)) =
        fun u => Complex.exp (-s) * F (u - 1) := by
      funext u
      dsimp only [F]
      rw [show -s * (u : ℂ) = -s + -s * ((u - 1 : ℝ) : ℂ) by push_cast; ring, Complex.exp_add]
      ring
    rw [hx, integral_const_mul]
    have hcov : (∫ u : ℝ, F (u - 1)) = ∫ u : ℝ, F u := by
      simpa only [sub_eq_add_neg] using integral_add_right_eq_self F (-1)
    rw [hcov]
    congr 1
    have hF : F = (Ioi (0 : ℝ)).indicator
        (fun u : ℝ => (rdfExcess xi z Dt G u : ℂ) * Complex.exp (-s * u)) := by
      funext u
      by_cases hu : u ∈ Ioi (0 : ℝ)
      · simp only [F, excessSupported, indicator_of_mem hu]
      · simp only [F, excessSupported, indicator_of_notMem hu, Complex.ofReal_zero, zero_mul]
    rw [hF, integral_indicator measurableSet_Ioi]
    rfl
  rw [hwhole, hsplit, integral_add hc ht, integral_indicator measurableSet_Ioc, hshift,
    ← intervalIntegral.integral_of_le zero_le_one]
  have hcore : (∫ u in (0 : ℝ)..1, (-u : ℂ) * Complex.exp (-s * u)) =
      -((1 - (s + 1) * Complex.exp (-s)) / s ^ 2) := by
    have hx : (fun u : ℝ => (-u : ℂ) * Complex.exp (-s * u)) =
        fun u : ℝ => -((u : ℂ) * Complex.exp (-s * u)) := by funext u; push_cast; ring
    rw [hx, intervalIntegral.integral_neg, core_first_complex hs]
  rw [hcore]
  field_simp [hs]
  ring

def shiftedMomentSymbol (xi : ℝ) (z Dt G : ι → ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-s) * (causalComplexLaplace (rdfExcess xi z Dt G) s + 1 / s ^ 2 + 1 / s)

/-- Fourier transform of the actual constructed h(r), including its hard core. -/
theorem reconstructedH_fourier (xi : ℝ) (z Dt G : ι → ℝ)
    (he : IntegrableOn (rdfExcess xi z Dt G) (Ioi 0)) {k : ℝ} (hk : k ≠ 0) :
    FMSA.HardSphere.radial_fourier (reconstructedH xi z Dt G) k =
      -(4 * Real.pi / k) * (shiftedMomentSymbol xi z Dt G ((k : ℂ) * Complex.I)).im := by
  let s : ℂ := (k : ℂ) * Complex.I
  have hs : s ≠ 0 := imaginary_nonzero hk
  have hsre : s.re = 0 := by simp [s]
  have hic := (rdfRadialMoment_complex_integrable xi z Dt G he hsre).integrableOn (s := Ioi 0)
  have hm := rdfRadialMoment_complex_transform xi z Dt G he hsre hs
  change (∫ u in Ioi (0 : ℝ), (rdfRadialMoment xi z Dt G u : ℂ) * Complex.exp (-s * u)) =
    shiftedMomentSymbol xi z Dt G s - 1 / s ^ 2 at hm
  have hid : ((1 : ℂ) / s ^ 2).im = 0 := by
    simp [s, pow_two, Complex.div_im]
  have hmim := congrArg Complex.im hm
  simp only [Complex.sub_im, hid, sub_zero] at hmim
  have hiim := integral_im hic
  simp only [RCLike.im_to_complex] at hiim
  have hsin : (∫ u in Ioi (0 : ℝ), rdfRadialMoment xi z Dt G u * Real.sin (k * u)) =
      -(shiftedMomentSymbol xi z Dt G s).im := by
    rw [← hmim, ← hiim, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only
    have hex : Complex.exp (-s * u) =
        (Real.cos (k * u) : ℂ) - (Real.sin (k * u) : ℂ) * Complex.I := by
      rw [show -s * u = -((k * u : ℝ) : ℂ) * Complex.I by dsimp [s]; push_cast; ring]
      simpa only [neg_mul] using axis_exp (k * u)
    rw [hex]
    simp only [Complex.mul_im, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, zero_add]
    ring
  unfold FMSA.HardSphere.radial_fourier
  have hmoment : (∫ r in Ioi (0 : ℝ), r * reconstructedH xi z Dt G r * Real.sin (k * r)) =
      ∫ r in Ioi (0 : ℝ), rdfRadialMoment xi z Dt G r * Real.sin (k * r) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change 0 < r at hr
    dsimp only [reconstructedH]
    field_simp [hr.ne']
  rw [hmoment, hsin]
  ring

end FMSA.ExactMSA.MultiTail
