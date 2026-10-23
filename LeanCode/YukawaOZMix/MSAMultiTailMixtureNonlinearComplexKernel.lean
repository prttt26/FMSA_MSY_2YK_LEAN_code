import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearComplex

/-! Actual recentered Q complex dictionary and nonlinear kernel norm budget. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem nonlinearActualQ_eq_causalShift (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) :
    q z σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) i j=
      causalShift (nonlinearRecenteredQ z ρ σ Dt G i j) (edgeLo σ i j) := by
  funext r
  by_cases hr : r < edgeLo σ i j
  · rw [causalShift_eq_zero_below _ _ _ hr]
    simp only [q, if_pos hr]
  · have hu : 0 ≤ r-edgeLo σ i j := sub_nonneg.mpr (not_lt.mp hr)
    unfold causalShift causalFull
    rw [indicator_of_mem (show r-edgeLo σ i j ∈ Ici (0 : ℝ) from hu),
      nonlinearRecenteredQ_eq_actual z ρ σ Dt G i j _ hu, sub_add_cancel]

theorem nonlinearRecenteredQ_actual_complex_laplace (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (s : ℂ) (hs : s ≠ 0) (hsre : 0 ≤ s.re) (i j : Fin N) :
    FMSA.causalComplexLaplace (nonlinearRecenteredQ z ρ σ Dt G i j) s=
      Complex.exp (s*(edgeLo σ i j : ℂ))*QhatComplex z σ
        (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) s i j := by
  have hshift := causalShift_complex_laplace (nonlinearRecenteredQ z ρ σ Dt G i j) (edgeLo σ i j) s
  rw [← nonlinearActualQ_eq_causalShift,
    complexQ_integral_eq_Qhat z hz σ _ _ _ _ hσ s hs hsre] at hshift
  rw [hshift]
  have he : Complex.exp (s*(edgeLo σ i j : ℂ))*Complex.exp (-s*(edgeLo σ i j : ℂ))=1 := by
    rw [← Complex.exp_add]; simp
  rw [← mul_assoc, he, one_mul]

def nonlinearComplexL (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (s : ℂ) : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j =>
      (amplitudeA z ρ σ Dt G j : ℂ)/s^2+
        ((amplitudeQp z ρ σ Dt G i j : ℂ)-(σ i : ℂ)*(amplitudeA z ρ σ Dt G j : ℂ))/s+
        (nonlinearLowerQValue z ρ σ Dt G i j : ℂ)-
        ∑ u, (z u : ℂ)*(W z ρ Dt G u i j : ℂ)/(s+(z u : ℂ)))

theorem nonlinear_complex_recenter_identity (A qp x e s : ℂ) (z W C : ι → ℂ)
    (hs : s ≠ 0) (hzs : ∀ u, s+z u ≠ 0) :
    s*((1-s*x-e)/s^2*qp+(1-s*x+(s*x)^2/2-e)/s^3*A+
      (∑ u, (W u/(s+z u)+C u*(1-e)/s))+(∑ u, e*C u/(s+z u)))=
    A/s^2+(qp-x*A)/s-x*qp+A*x^2/2+(∑ u, (W u+C u))-(∑ u, z u*W u/(s+z u))-
      e*(A/s^2+qp/s+∑ u, z u*C u/(s+z u)) := by
  have hp : s*((1-s*x-e)/s^2*qp+(1-s*x+(s*x)^2/2-e)/s^3*A)=
      A/s^2+(qp-x*A)/s-x*qp+A*x^2/2-e*(A/s^2+qp/s) := by field_simp [hs]; ring
  have ht : s*((∑ u, (W u/(s+z u)+C u*(1-e)/s))+(∑ u, e*C u/(s+z u)))=
      (∑ u, (W u+C u))-(∑ u, z u*W u/(s+z u))-e*∑ u, z u*C u/(s+z u) := by
    simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    field_simp [hs, hzs u]
    ring
  linear_combination hp+ht

theorem nonlinearRecenteredQ_complex_laplace_rational (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (s : ℂ) (hs : s ≠ 0) (hsre : 0 ≤ s.re) (i j : Fin N) :
    s*FMSA.causalComplexLaplace (nonlinearRecenteredQ z ρ σ Dt G i j) s=
      nonlinearComplexL z ρ σ Dt G s i j-
        Complex.exp (-s*(σ i : ℂ))*nonlinearComplexJ z ρ σ Dt G s i j := by
  rw [nonlinearRecenteredQ_actual_complex_laplace z ρ σ Dt G hz hσ s hs hsre]
  have he0 : Complex.exp (s*(edgeLo σ i j : ℂ))*Complex.exp (-s*(edgeLo σ i j : ℂ))=1 := by
    rw [← Complex.exp_add]; simp
  have he1 : Complex.exp (s*(edgeLo σ i j : ℂ))*Complex.exp (-s*(edgeHi σ i j : ℂ))=
      Complex.exp (-s*(σ i : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; unfold edgeLo edgeHi; push_cast; ring
  have he : Complex.exp (s*(edgeLo σ i j : ℂ))*QhatComplex z σ
      (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) s i j=
      (1-s*(σ i : ℂ)-Complex.exp (-s*(σ i : ℂ)))/s^2*(amplitudeQp z ρ σ Dt G i j : ℂ)+
      (1-s*(σ i : ℂ)+(s*(σ i : ℂ))^2/2-Complex.exp (-s*(σ i : ℂ)))/s^3*(amplitudeA z ρ σ Dt G j : ℂ)+
      (∑ u, ((W z ρ Dt G u i j : ℂ)/(s+(z u : ℂ))+
        (C z ρ σ Dt G u i j : ℂ)*(1-Complex.exp (-s*(σ i : ℂ)))/s))+
      (∑ u, Complex.exp (-s*(σ i : ℂ))*(C z ρ σ Dt G u i j : ℂ)/(s+(z u : ℂ))) := by
    unfold QhatComplex
    rw [mul_add, ← mul_assoc, he0, one_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    calc
      _ = (Complex.exp (s*(edgeLo σ i j : ℂ))*Complex.exp (-s*(edgeHi σ i j : ℂ)))*
          (C z ρ σ Dt G u i j : ℂ)/(s+(z u : ℂ)) := by ring
      _ = _ := by rw [he1]
  rw [he]
  have hzs : ∀ u, s+(z u : ℂ) ≠ 0 := by
    intro u h
    have hRe := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hRe
    linarith [hz u]
  have hc := nonlinear_complex_recenter_identity (amplitudeA z ρ σ Dt G j)
    (amplitudeQp z ρ σ Dt G i j) (σ i) (Complex.exp (-s*(σ i : ℂ))) s
    (fun u => (z u : ℂ)) (fun u => (W z ρ Dt G u i j : ℂ)) (fun u => (C z ρ σ Dt G u i j : ℂ)) hs hzs
  simpa only [nonlinearComplexL, nonlinearComplexJ, Matrix.of_apply, nonlinearLowerQValue,
    Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_sum,
    sub_eq_add_neg, add_assoc, neg_mul] using hc

theorem complex_matrix_one_sub_isUnit_of_normSum (M : Matrix (Fin N) (Fin N) ℂ)
    (hM : (∑ i, ∑ j, ‖M i j‖) < 1) : IsUnit (1-M) := by
  letI := Matrix.linftyOpNormedRing (n := Fin N) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℂ) (n := Fin N) (α := ℂ)
  have hnn : ‖M‖₊ ≤ (∑ i, ∑ j, ‖M i j‖₊) := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.sup_le (fun i _ => Finset.single_le_sum
      (f := fun i : Fin N => ∑ j, ‖M i j‖₊) (fun _ _ => by positivity) (Finset.mem_univ i))
  have hn : ‖M‖ ≤ ∑ i, ∑ j, ‖M i j‖ := by
    have hre : (‖M‖₊ : ℝ) ≤ ((∑ i, ∑ j, ‖M i j‖₊ : NNReal) : ℝ) :=
      NNReal.coe_le_coe.mpr hnn
    simpa only [NNReal.coe_sum, coe_nnnorm] using hre
  exact isUnit_one_sub_of_norm_lt_one (hn.trans_lt hM)

theorem nonlinearCausalKernel_complex_laplace_budget (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδz : ∀ u, δ < z u) (s : ℂ) (hs : 0 ≤ s.re) :
    (∑ i, ∑ j, ‖rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s i j‖) ≤
      nonlinearWeightedKernelBudget z ρ σ Dt G δ := by
  have hiw := nonlinearCausalKernel_weighted_entry_integrable z ρ σ Dt G hσ δ hδz
  have hw (i j : Fin N) : ‖rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s i j‖ ≤
      ∫ t in Ioi (0 : ℝ), exp (δ*t)*|nonlinearCausalKernel z ρ σ Dt G t i j| := by
    have hiq : IntegrableOn (fun t => nonlinearCausalKernel z ρ σ Dt G t i j) (Ioi 0) := by
      change Integrable (fun t => ρ i*nonlinearRecenteredQ z ρ σ Dt G i j t) (volume.restrict (Ioi 0))
      simpa only [nonlinearCausalKernel, Matrix.of_apply, zero_mul, exp_zero, one_mul] using
        (nonlinearRecenteredQ_weighted_integrable z ρ σ Dt G hσ 0 hz i j).const_mul (ρ i)
    have hi := FMSA.complex_laplace_integrable_of_L1 _
      ((nonlinearCausalKernel_continuous z ρ σ Dt G).matrix_elem i j).continuousOn hiq hs
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono_ae hi.norm (hiw i j)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [norm_mul, Complex.norm_real, Complex.norm_exp, Complex.mul_re,
      Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Real.norm_eq_abs]
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith : -s.re ≤ δ) ht.le)
  calc
    _ ≤ ∑ i, ∑ j, ∫ t in Ioi (0 : ℝ), exp (δ*t)*|nonlinearCausalKernel z ρ σ Dt G t i j| :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hw i j))
    _ = _ := by
      unfold nonlinearWeightedKernelBudget
      simp only [FMSA.matrixAbsSum, Finset.mul_sum]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hiw i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hiw i j)]

/-- The actual complex renewal block is a unit throughout the closed right
half-plane, including every Fourier frequency. This is a sufficient kernel
budget condition, not a statement about the full BH amplitude Jacobian. -/
theorem nonlinear_complex_block_isUnit_of_weighted_budget (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (s : ℂ) (hs : 0 ≤ s.re) :
    IsUnit (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s) :=
  complex_matrix_one_sub_isUnit_of_normSum _
    ((nonlinearCausalKernel_complex_laplace_budget z ρ σ Dt G hz hσ δ hδ hδz s hs).trans_lt hb)

end FMSA.ExactMSA.MultiTailMixture
