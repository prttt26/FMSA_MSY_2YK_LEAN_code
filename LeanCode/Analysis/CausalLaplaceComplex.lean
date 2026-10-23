import Mathlib
import LeanCode.YukawaOZ.MSABlumHoyeDerivation

/-! Actual complex half-line transforms for real causal renewal. -/
noncomputable section
open MeasureTheory Set Filter Topology

namespace FMSA

def causalComplexLaplace (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), (f u : ℂ) * Complex.exp (-s * u)

theorem complex_laplace_integrable (f : ℝ → ℝ) (hf : ContinuousOn f (Ici 0)) (s : ℂ)
    (hi : IntegrableOn (fun u => Real.exp (-s.re * u) * f u) (Ioi 0)) :
    IntegrableOn (fun u => (f u : ℂ) * Complex.exp (-s * u)) (Ioi 0) := by
  apply (integrable_norm_iff ?_).mp
  · simpa only [norm_mul, Complex.norm_real, Complex.norm_exp, Complex.mul_re,
      Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm] using hi.norm
  · exact ((Complex.continuous_ofReal.comp_continuousOn (hf.mono Ioi_subset_Ici_self)).mul
      (by fun_prop : Continuous (fun u : ℝ => Complex.exp (-s * u))).continuousOn).aestronglyMeasurable
      measurableSet_Ioi

theorem complex_first_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) * Complex.exp (-s * u)) (Ioi 0) :=
  complex_laplace_integrable _ continuous_id.continuousOn s
    (by simpa only [mul_comm, id_eq] using ExactMSA.integrableOn_Ioi_id_mul_exp_neg hs)

theorem complex_laplace_integrable_of_L1 (f : ℝ → ℝ) (hf : ContinuousOn f (Ici 0))
    (hi : IntegrableOn f (Ioi 0)) {s : ℂ} (hs : 0 ≤ s.re) :
    IntegrableOn (fun u => (f u : ℂ) * Complex.exp (-s * u)) (Ioi 0) := by
  have hw : IntegrableOn (fun u => f u * Real.exp (-s.re * u)) (Ioi 0) :=
    hi.mul_bdd (by apply Continuous.aestronglyMeasurable; fun_prop)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          change 0 < u at hu
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_one_iff.mpr (by nlinarith))
  apply complex_laplace_integrable f hf s
  exact hw.congr_fun (fun u _ => by dsimp only; ring) measurableSet_Ioi

theorem complex_first_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun u : ℝ => (u : ℂ) * Complex.exp (-s * u)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 s.re hs
  simp only [Real.rpow_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  simp [norm_mul, Complex.norm_real, Complex.norm_exp, abs_of_nonneg hu]

theorem complex_first_Ioi {s : ℂ} (hs : 0 < s.re) :
    (∫ u in Ioi (0 : ℝ), (u : ℂ) * Complex.exp (-s * u)) = 1 / s ^ 2 := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have he : IntegrableOn (fun u : ℝ => Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hs) 0
  have hi := complex_first_integrable hs
  have hd : ∀ u ∈ Ici (0 : ℝ), HasDerivAt
      (fun u : ℝ => (u : ℂ) * Complex.exp (-s * u))
      (Complex.exp (-s * u) - s * ((u : ℂ) * Complex.exp (-s * u))) u := by
    intro u _
    have h0 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    exact (h0.mul (h0.const_mul (-s)).cexp).congr_deriv (by ring)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd (he.sub (hi.const_mul s))
    (complex_first_tendsto hs)
  rw [integral_sub he (hi.const_mul s), integral_const_mul,
    integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hs)] at h
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, zero_mul, sub_zero] at h
  field_simp [hs0] at h ⊢
  linear_combination -h

theorem causalComplexLaplace_background {e y : ℝ → ℝ}
    (he : ContinuousOn e (Ici 0)) (hi : IntegrableOn e (Ioi 0))
    (hy : ∀ u, 0 < u → y u = e u + (u + 1)) {s : ℂ} (hs : 0 < s.re) :
    causalComplexLaplace y s = causalComplexLaplace e s + 1 / s ^ 2 + 1 / s := by
  have hec := complex_laplace_integrable_of_L1 e he hi hs.le
  have hi1 := complex_first_integrable hs
  have hi0 : IntegrableOn (fun u : ℝ => Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (a := -s) (by simpa using neg_neg_of_pos hs) 0
  have ha : IntegrableOn (fun u : ℝ => (e u : ℂ) * Complex.exp (-s * u) +
      (u : ℂ) * Complex.exp (-s * u)) (Ioi 0) := hec.add hi1
  unfold causalComplexLaplace
  calc
    _ = ∫ u in Ioi (0 : ℝ), (e u : ℂ) * Complex.exp (-s * u) +
        (u : ℂ) * Complex.exp (-s * u) + Complex.exp (-s * u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only
      rw [hy u hu]
      push_cast
      ring
    _ = _ := by
      rw [integral_add ha hi0, integral_add hec hi1, complex_first_Ioi hs,
        integral_exp_mul_complex_Ioi (a := -s) (by simpa using neg_neg_of_pos hs)]
      simp

/-- The transfer equation follows from actual interval convolution and its
Fubini theorem. It is valid at every complex point where the three weighted
functions are integrable. -/
theorem causalComplexLaplace_renewal {q f y : ℝ → ℝ} (s : ℂ)
    (hq : ContinuousOn q (Ici 0)) (hf : ContinuousOn f (Ici 0)) (hy : ContinuousOn y (Ici 0))
    (hiq : IntegrableOn (fun u => Real.exp (-s.re * u) * q u) (Ioi 0))
    (hif : IntegrableOn (fun u => Real.exp (-s.re * u) * f u) (Ioi 0))
    (hiy : IntegrableOn (fun u => Real.exp (-s.re * u) * y u) (Ioi 0))
    (heq : ∀ r, 0 ≤ r → y r = f r + ∫ t in (0 : ℝ)..r, q (r - t) * y t) :
    causalComplexLaplace y s * (1 - causalComplexLaplace q s) = causalComplexLaplace f s := by
  let yw := fun u => (y u : ℂ) * Complex.exp (-s * u)
  let qw := fun u => (q u : ℂ) * Complex.exp (-s * u)
  have hiyc : IntegrableOn yw (Ioi 0) := complex_laplace_integrable y hy s hiy
  have hiqc : IntegrableOn qw (Ioi 0) := complex_laplace_integrable q hq s hiq
  have hifc := complex_laplace_integrable f hf s hif
  have hw (r : ℝ) : ((∫ t in (0 : ℝ)..r, q (r - t) * y t : ℝ) : ℂ) * Complex.exp (-s * r) =
      ∫ t in (0 : ℝ)..r, yw t * qw (r - t) := by
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [yw, qw]
    push_cast
    have he : Complex.exp (-s * (t : ℂ)) * Complex.exp (-s * ((r - t : ℝ) : ℂ)) =
        Complex.exp (-s * r) := by rw [← Complex.exp_add]; push_cast; congr 1; ring
    push_cast at he
    linear_combination -(y t : ℂ) * (q (r - t) : ℂ) * he
  have hiv : IntegrableOn (fun r =>
      ((∫ t in (0 : ℝ)..r, q (r - t) * y t : ℝ) : ℂ) * Complex.exp (-s * r)) (Ioi 0) := by
    refine (integrable_posConvolution hiyc hiqc (ContinuousLinearMap.mul ℝ ℂ)).integrableOn.congr_fun
      (fun r hr => ?_) measurableSet_Ioi
    simp only [posConvolution, indicator_of_mem hr, ContinuousLinearMap.mul_apply']
    exact (hw r).symm
  have ht : causalComplexLaplace y s = causalComplexLaplace f s +
      causalComplexLaplace y s * causalComplexLaplace q s := by
    unfold causalComplexLaplace
    calc
      _ = ∫ r in Ioi (0 : ℝ), (f r : ℂ) * Complex.exp (-s * r) +
          ((∫ t in (0 : ℝ)..r, q (r - t) * y t : ℝ) : ℂ) * Complex.exp (-s * r) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        dsimp only
        rw [heq r hr.le]
        push_cast
        ring
      _ = _ := by
        rw [integral_add hifc hiv]
        simp_rw [hw]
        have hp := integral_posConvolution hiyc hiqc (ContinuousLinearMap.mul ℝ ℂ)
        simp only [ContinuousLinearMap.mul_apply'] at hp
        rw [hp]
  linear_combination ht

/-- Abel boundary continuity of an actual L1 transform. The dominant function
is |f|; no Fourier boundary formula is assumed. -/
theorem causalComplexLaplace_boundary (f : ℝ → ℝ) (hf : ContinuousOn f (Ici 0))
    (hi : IntegrableOn f (Ioi 0)) (s : ℂ) (hs : s.re = 0) :
    ContinuousWithinAt (fun a : ℝ => causalComplexLaplace f ((a : ℂ) + s)) (Ici 0) 0 := by
  unfold causalComplexLaplace
  apply continuousWithinAt_of_dominated (bound := fun u => |f u|)
  · exact Filter.Eventually.of_forall (fun a =>
      ((Complex.continuous_ofReal.comp_continuousOn (hf.mono Ioi_subset_Ici_self)).mul
        (by fun_prop : Continuous (fun u : ℝ => Complex.exp (-((a : ℂ) + s) * u))).continuousOn
        ).aestronglyMeasurable measurableSet_Ioi)
  · filter_upwards [self_mem_nhdsWithin] with a ha
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 0 ≤ a at ha
    change 0 < u at hu
    simp only [norm_mul, Complex.norm_real, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
      Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hs, add_zero]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by nlinarith)) (abs_nonneg _)
      |>.trans_eq (mul_one _)
  · exact hi.abs
  · exact Filter.Eventually.of_forall (fun u => by fun_prop)

end FMSA
