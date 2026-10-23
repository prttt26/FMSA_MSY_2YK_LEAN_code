import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearMoments
import LeanCode.YukawaOZ.MSAMultiTailRDFMoments
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Actual integrals of the nonlinear recentered mixture kernel. -/
noncomputable section
open MeasureTheory Set Real
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem nonlinear_compact_integrable (f : ℝ → ℝ) (hf : Continuous f)
    (x : ℝ) (hzero : ∀ t, x ≤ t → f t=0) : IntegrableOn f (Ioi 0) := by
  have hi := (hf.integrableOn_Icc (μ := volume) (a := 0) (b := x)).integrable_indicator measurableSet_Icc
  apply hi.integrableOn.congr_fun _ measurableSet_Ioi
  intro t ht
  by_cases hh : t ≤ x
  · exact indicator_of_mem (show t ∈ Icc (0 : ℝ) x from ⟨ht.le, hh⟩) _
  · rw [indicator_of_notMem (show t ∉ Icc (0 : ℝ) x from fun h => hh h.2)]
    rw [hzero t (not_le.mp hh).le]

theorem nonlinear_compact_integral (f : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ x)
    (hzero : ∀ t, x ≤ t → f t=0) :
    (∫ t in Ioi (0 : ℝ), f t) = ∫ t in (0 : ℝ)..x, f t := by
  have he : (∫ t in Ioi (0 : ℝ), f t) = ∫ t in Ioi (0 : ℝ), (Icc (0 : ℝ) x).indicator f t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    by_cases hh : t ≤ x
    · rw [indicator_of_mem (show t ∈ Icc (0 : ℝ) x from ⟨ht.le, hh⟩)]
    · rw [indicator_of_notMem (show t ∉ Icc (0 : ℝ) x from fun h => hh h.2), hzero t (not_le.mp hh).le]
  rw [he, setIntegral_indicator measurableSet_Icc]
  have hset : Ioi (0 : ℝ) ∩ Icc 0 x = Ioc 0 x := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨ht, _, htx⟩; exact ⟨ht, htx⟩
    · rintro ⟨ht, htx⟩; exact ⟨ht, ht.le, htx⟩
  rw [hset, intervalIntegral.integral_of_le hx]

def nonlinearClipExp (z x t : ℝ) : ℝ := exp (-z*(max t x-x))

theorem nonlinearClipExp_decomposition (z x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    nonlinearClipExp z x t = (Ioc (0 : ℝ) x).indicator (fun _ => (1 : ℝ)) t+
      (Ioi x).indicator (fun t => exp (z*x)*exp (-z*t)) t := by
  by_cases h : t ≤ x
  · simp [nonlinearClipExp, max_eq_right h, indicator_of_mem (show t ∈ Ioc (0 : ℝ) x from ⟨ht, h⟩),
      indicator_of_notMem (show t ∉ Ioi x from not_lt.mpr h)]
  · simp only [nonlinearClipExp, max_eq_left (not_le.mp h).le,
      indicator_of_notMem (show t ∉ Ioc (0 : ℝ) x from fun hh => h hh.2),
      indicator_of_mem (show t ∈ Ioi x from not_le.mp h), zero_add]
    rw [← exp_add]
    congr 1
    ring

theorem nonlinearClipExp_integrable (z x : ℝ) (hz : 0 < z) (hx : 0 ≤ x) :
    IntegrableOn (nonlinearClipExp z x) (Ioi 0) := by
  have hi0 : Integrable ((Ioc (0 : ℝ) x).indicator (fun _ => (1 : ℝ))) :=
    (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have hi1 : Integrable ((Ioi x).indicator (fun t => exp (z*x)*exp (-z*t))) :=
    IntegrableOn.integrable_indicator
      ((integrableOn_exp_mul_Ioi (by linarith : -z < 0) x).const_mul (exp (z*x))) measurableSet_Ioi
  exact (hi0.add hi1).integrableOn.congr_fun
    (fun t ht => (nonlinearClipExp_decomposition z x t hx ht).symm) measurableSet_Ioi

theorem nonlinearClipExp_first_integrable (z x : ℝ) (hz : 0 < z) (hx : 0 ≤ x) :
    IntegrableOn (fun t => t*nonlinearClipExp z x t) (Ioi 0) := by
  have hi0 : Integrable ((Ioc (0 : ℝ) x).indicator (fun t => t)) :=
    (continuous_id.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have hi1 : Integrable ((Ioi x).indicator (fun t => exp (z*x)*(t*exp (-z*t)))) :=
    IntegrableOn.integrable_indicator
      (((FMSA.ExactMSA.integrableOn_Ioi_id_mul_exp_neg hz).mono_set
        (Ioi_subset_Ioi hx)).const_mul (exp (z*x))) measurableSet_Ioi
  apply (hi0.add hi1).integrableOn.congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only [Pi.add_apply]
  rw [nonlinearClipExp_decomposition z x t hx ht]
  by_cases hh : t ≤ x
  · simp [indicator_of_mem (show t ∈ Ioc (0 : ℝ) x from ⟨ht, hh⟩),
      indicator_of_notMem (show t ∉ Ioi x from not_lt.mpr hh)]
  · simp [indicator_of_notMem (show t ∉ Ioc (0 : ℝ) x from fun h => hh h.2),
      indicator_of_mem (show t ∈ Ioi x from not_le.mp hh), mul_comm, mul_left_comm]

theorem nonlinearClipExp_integral (z x : ℝ) (hz : 0 < z) (hx : 0 ≤ x) :
    (∫ t in Ioi (0 : ℝ), nonlinearClipExp z x t) = x+1/z := by
  have hi0 : Integrable ((Ioc (0 : ℝ) x).indicator (fun _ => (1 : ℝ))) :=
    (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have hi1 : Integrable ((Ioi x).indicator (fun t => exp (z*x)*exp (-z*t))) :=
    IntegrableOn.integrable_indicator
      ((integrableOn_exp_mul_Ioi (by linarith : -z < 0) x).const_mul (exp (z*x))) measurableSet_Ioi
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => nonlinearClipExp_decomposition z x t hx ht),
    integral_add hi0.integrableOn hi1.integrableOn, setIntegral_indicator measurableSet_Ioc,
    setIntegral_indicator measurableSet_Ioi]
  have hs0 : Ioi (0 : ℝ) ∩ Ioc 0 x = Ioc 0 x := inter_eq_right.mpr Ioc_subset_Ioi_self
  have hs1 : Ioi (0 : ℝ) ∩ Ioi x = Ioi x := inter_eq_right.mpr (Ioi_subset_Ioi hx)
  rw [hs0, hs1, ← intervalIntegral.integral_of_le hx, intervalIntegral.integral_const,
    integral_const_mul, integral_exp_mul_Ioi (by linarith : -z < 0)]
  simp only [sub_zero, smul_eq_mul, mul_one]
  have he : exp (x*z)*exp (-(x*z))=1 := by rw [← exp_add]; simp
  field_simp [hz.ne']
  linear_combination he

theorem nonlinearClipExp_first_integral (z x : ℝ) (hz : 0 < z) (hx : 0 ≤ x) :
    (∫ t in Ioi (0 : ℝ), t*nonlinearClipExp z x t) = x^2/2+x/z+1/z^2 := by
  have hsplit : (fun t => t*nonlinearClipExp z x t) =ᵐ[volume.restrict (Ioi 0)]
      fun t => (Ioc (0 : ℝ) x).indicator (fun t => t) t+
        (Ioi x).indicator (fun t => exp (z*x)*(t*exp (-z*t))) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [nonlinearClipExp_decomposition z x t hx ht]
    by_cases hh : t ≤ x
    · simp [indicator_of_mem (show t ∈ Ioc (0 : ℝ) x from ⟨ht, hh⟩),
        indicator_of_notMem (show t ∉ Ioi x from not_lt.mpr hh)]
    · simp [indicator_of_notMem (show t ∉ Ioc (0 : ℝ) x from fun h => hh h.2),
        indicator_of_mem (show t ∈ Ioi x from not_le.mp hh), mul_comm, mul_left_comm]
  have hi0 : Integrable ((Ioc (0 : ℝ) x).indicator (fun t => t)) :=
    (continuous_id.integrableOn_Icc.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  have hi1 : Integrable ((Ioi x).indicator (fun t => exp (z*x)*(t*exp (-z*t)))) :=
    IntegrableOn.integrable_indicator
      (((FMSA.ExactMSA.integrableOn_Ioi_id_mul_exp_neg hz).mono_set
        (Ioi_subset_Ioi hx)).const_mul (exp (z*x))) measurableSet_Ioi
  rw [integral_congr_ae hsplit, integral_add hi0.integrableOn hi1.integrableOn,
    setIntegral_indicator measurableSet_Ioc, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr Ioc_subset_Ioi_self, inter_eq_right.mpr (Ioi_subset_Ioi hx),
    ← intervalIntegral.integral_of_le hx, integral_id,
    integral_const_mul, FMSA.ExactMSA.MultiTail.exp_first_Ioi z x hz]
  have he : exp (z*x)*exp (-z*x)=1 := by rw [← exp_add]; simp
  rw [← mul_assoc, he, one_mul]
  ring

def nonlinearClipPolynomial (a b x t : ℝ) : ℝ :=
  b*(min t x-x)+a/2*(min t x-x)^2

theorem nonlinearClipPolynomial_integrable (a b x : ℝ) :
    IntegrableOn (nonlinearClipPolynomial a b x) (Ioi 0) ∧
      IntegrableOn (fun t => t*nonlinearClipPolynomial a b x t) (Ioi 0) := by
  have hc : Continuous (nonlinearClipPolynomial a b x) := by unfold nonlinearClipPolynomial; fun_prop
  constructor
  · exact nonlinear_compact_integrable _ hc x (fun t ht => by simp [nonlinearClipPolynomial, min_eq_right ht])
  · exact nonlinear_compact_integrable _ (continuous_id.mul hc) x
      (fun t ht => by simp [nonlinearClipPolynomial, min_eq_right ht])

theorem nonlinearClipPolynomial_integrals (a b x : ℝ) (hx : 0 ≤ x) :
    (∫ t in Ioi (0 : ℝ), nonlinearClipPolynomial a b x t) = -b*x^2/2+a*x^3/6 ∧
      (∫ t in Ioi (0 : ℝ), t*nonlinearClipPolynomial a b x t) = -b*x^3/6+a*x^4/24 := by
  have hzero : ∀ t, x ≤ t → nonlinearClipPolynomial a b x t=0 :=
    fun t ht => by simp [nonlinearClipPolynomial, min_eq_right ht]
  have he : (∫ t in (0 : ℝ)..x, nonlinearClipPolynomial a b x t) =
      ∫ t in (0 : ℝ)..x, b*(t-x)+a*(t-x)^2/2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx] at ht
    simp only [nonlinearClipPolynomial, min_eq_left ht.2]
    ring
  have he1 : (∫ t in (0 : ℝ)..x, t*nonlinearClipPolynomial a b x t) =
      ∫ t in (0 : ℝ)..x, t*(b*(t-x)+a*(t-x)^2/2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx] at ht
    simp only [nonlinearClipPolynomial, min_eq_left ht.2]
    ring
  constructor
  · rw [nonlinear_compact_integral _ x hx hzero, he, FMSA.HSMix.baxterQuad_integral]
    ring
  · rw [nonlinear_compact_integral _ x hx (fun t ht => by rw [hzero t ht, mul_zero]),
      he1, FMSA.HSMix.baxterQuad1_integral]
    ring

theorem nonlinearRecenteredQ_decomposition (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) :
    nonlinearRecenteredQ z ρ σ Dt G i j = fun t =>
      nonlinearClipPolynomial (amplitudeA z ρ σ Dt G j) (amplitudeQp z ρ σ Dt G i j) (σ i) t+
        ∑ u, (W z ρ Dt G u i j*exp (-z u*t)+
          C z ρ σ Dt G u i j*nonlinearClipExp (z u) (σ i) t) := rfl

theorem nonlinearRecenteredQ_integrable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (i j : Fin N) : IntegrableOn (nonlinearRecenteredQ z ρ σ Dt G i j) (Ioi 0) := by
  rw [nonlinearRecenteredQ_decomposition]
  exact (nonlinearClipPolynomial_integrable _ _ _).1.add
    (integrable_finsetSum _ (fun u _ =>
      ((integrableOn_exp_mul_Ioi (by linarith [hz u] : -z u < 0) 0).const_mul _).add
        ((nonlinearClipExp_integrable (z u) (σ i) (hz u) (hσ i)).const_mul _)))

theorem nonlinearRecenteredQ_first_integrable (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (i j : Fin N) : IntegrableOn (fun t => t*nonlinearRecenteredQ z ρ σ Dt G i j t) (Ioi 0) := by
  have he : (fun t => t*nonlinearRecenteredQ z ρ σ Dt G i j t) = fun t =>
      t*nonlinearClipPolynomial (amplitudeA z ρ σ Dt G j) (amplitudeQp z ρ σ Dt G i j) (σ i) t+
        ∑ u, (W z ρ Dt G u i j*(t*exp (-z u*t))+
          C z ρ σ Dt G u i j*(t*nonlinearClipExp (z u) (σ i) t)) := by
    funext t
    rw [nonlinearRecenteredQ_decomposition, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [he]
  exact (nonlinearClipPolynomial_integrable _ _ _).2.add
    (integrable_finsetSum _ (fun u _ =>
      ((FMSA.ExactMSA.integrableOn_Ioi_id_mul_exp_neg (hz u)).const_mul _).add
        ((nonlinearClipExp_first_integrable (z u) (σ i) (hz u) (hσ i)).const_mul _)))

/-- The closed zeroth moment is the integral of the actual recentered Q. -/
theorem nonlinearQMoment0_eq_integral (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (i j : Fin N) : nonlinearQMoment0 z ρ σ Dt G i j =
      ∫ t in Ioi (0 : ℝ), nonlinearRecenteredQ z ρ σ Dt G i j t := by
  have hi (u : ι) : IntegrableOn (fun t => W z ρ Dt G u i j*exp (-z u*t)+
      C z ρ σ Dt G u i j*nonlinearClipExp (z u) (σ i) t) (Ioi 0) :=
    ((integrableOn_exp_mul_Ioi (by linarith [hz u] : -z u < 0) 0).const_mul _).add
      ((nonlinearClipExp_integrable (z u) (σ i) (hz u) (hσ i)).const_mul _)
  have hsum : IntegrableOn (fun t => ∑ u, (W z ρ Dt G u i j*exp (-z u*t)+
      C z ρ σ Dt G u i j*nonlinearClipExp (z u) (σ i) t)) (Ioi 0) :=
    integrable_finsetSum _ (fun u _ => hi u)
  have hp : IntegrableOn (nonlinearClipPolynomial (amplitudeA z ρ σ Dt G j)
      (amplitudeQp z ρ σ Dt G i j) (σ i)) (Ioi 0) := (nonlinearClipPolynomial_integrable _ _ _).1
  rw [nonlinearRecenteredQ_decomposition]
  dsimp only
  rw [integral_add hp hsum,
    (nonlinearClipPolynomial_integrals _ _ _ (hσ i)).1,
    integral_finsetSum _ (fun u _ => hi u)]
  unfold nonlinearQMoment0
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [integral_add ((integrableOn_exp_mul_Ioi (by linarith [hz u] : -z u < 0) 0).const_mul _)
    ((nonlinearClipExp_integrable (z u) (σ i) (hz u) (hσ i)).const_mul _),
    integral_const_mul, integral_const_mul,
    nonlinearClipExp_integral (z u) (σ i) (hz u) (hσ i),
    integral_exp_mul_Ioi (by linarith [hz u] : -z u < 0)]
  simp [div_eq_mul_inv]

theorem nonlinearQMoment1_eq_integral (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (i j : Fin N) : nonlinearQMoment1 z ρ σ Dt G i j =
      ∫ t in Ioi (0 : ℝ), t*nonlinearRecenteredQ z ρ σ Dt G i j t := by
  have hi (u : ι) : IntegrableOn (fun t => W z ρ Dt G u i j*(t*exp (-z u*t))+
      C z ρ σ Dt G u i j*(t*nonlinearClipExp (z u) (σ i) t)) (Ioi 0) :=
    ((FMSA.ExactMSA.integrableOn_Ioi_id_mul_exp_neg (hz u)).const_mul _).add
      ((nonlinearClipExp_first_integrable (z u) (σ i) (hz u) (hσ i)).const_mul _)
  have hsum : IntegrableOn (fun t => ∑ u, (W z ρ Dt G u i j*(t*exp (-z u*t))+
      C z ρ σ Dt G u i j*(t*nonlinearClipExp (z u) (σ i) t))) (Ioi 0) :=
    integrable_finsetSum _ (fun u _ => hi u)
  have hp : IntegrableOn (fun t => t*nonlinearClipPolynomial (amplitudeA z ρ σ Dt G j)
      (amplitudeQp z ρ σ Dt G i j) (σ i) t) (Ioi 0) := (nonlinearClipPolynomial_integrable _ _ _).2
  have he : (fun t => t*nonlinearRecenteredQ z ρ σ Dt G i j t) = fun t =>
      t*nonlinearClipPolynomial (amplitudeA z ρ σ Dt G j) (amplitudeQp z ρ σ Dt G i j) (σ i) t+
        ∑ u, (W z ρ Dt G u i j*(t*exp (-z u*t))+
          C z ρ σ Dt G u i j*(t*nonlinearClipExp (z u) (σ i) t)) := by
    funext t
    rw [nonlinearRecenteredQ_decomposition, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [he, integral_add hp hsum, (nonlinearClipPolynomial_integrals _ _ _ (hσ i)).2,
    integral_finsetSum _ (fun u _ => hi u)]
  unfold nonlinearQMoment1
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [integral_add ((FMSA.ExactMSA.integrableOn_Ioi_id_mul_exp_neg (hz u)).const_mul _)
    ((nonlinearClipExp_first_integrable (z u) (σ i) (hz u) (hσ i)).const_mul _),
    integral_const_mul, integral_const_mul,
    nonlinearClipExp_first_integral (z u) (σ i) (hz u) (hσ i),
    FMSA.ExactMSA.MultiTail.exp_first_Ioi (z u) 0 (hz u)]
  simp [div_eq_mul_inv]

theorem nonlinear_actual_background_normalization (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) :
    (∀ j, 1-(∑ m, ρ m*∫ t in Ioi (0 : ℝ), nonlinearRecenteredQ z ρ σ Dt G m j t) =
      amplitudeA z ρ σ Dt G j/(2*π)) ∧
    (∀ i j, edgeHi σ i j+(∑ m, ρ m*((∫ t in Ioi (0 : ℝ),
      t*nonlinearRecenteredQ z ρ σ Dt G m j t)-
      edgeHi σ i m*(∫ t in Ioi (0 : ℝ), nonlinearRecenteredQ z ρ σ Dt G m j t))) =
        amplitudeQp z ρ σ Dt G i j/(2*π)) := by
  constructor
  · intro j
    simp_rw [← nonlinearQMoment0_eq_integral z ρ σ Dt G hz hσ]
    exact nonlinear_background_mass_normalization z ρ σ Dt G (fun u => (hz u).ne') hv j
  · intro i j
    simp_rw [← nonlinearQMoment0_eq_integral z ρ σ Dt G hz hσ,
      ← nonlinearQMoment1_eq_integral z ρ σ Dt G hz hσ]
    exact nonlinear_background_contact_normalization z ρ σ Dt G (fun u => (hz u).ne') hv i j

end FMSA.ExactMSA.MultiTailMixture
