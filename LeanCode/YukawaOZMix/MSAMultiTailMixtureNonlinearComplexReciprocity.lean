import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearComplexFinite

/-! Actual complex Laplace reciprocity from the finite coefficient test. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem nonlinearComplexReciprocityResidual_actual_factor (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (s : ℂ) (hs : s ≠ 0) (hsre : 0 ≤ s.re) :
    nonlinearComplexReciprocityResidual z ρ σ Dt G s=
      (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s).transpose*
        nonlinearComplexJ z ρ σ Dt G s-
      (nonlinearComplexJ z ρ σ Dt G s).transpose*
        (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s) := by
  have hk (m j : Fin N) : rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s m j=
      (ρ m : ℂ)*FMSA.causalComplexLaplace (nonlinearRecenteredQ z ρ σ Dt G m j) s := by
    unfold rdfMatrixLaplace FMSA.causalComplexLaplace nonlinearCausalKernel
    simp only [Matrix.of_apply]
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    push_cast
    ring
  ext i j
  simp only [nonlinearComplexReciprocityResidual, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, inv_mul_eq_div, Matrix.transpose_apply,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.mul_one,
    Matrix.mul_apply (M := (nonlinearComplexJ z ρ σ Dt G s).transpose*Matrix.diagonal (fun i => (ρ i : ℂ))),
    Matrix.mul_apply (M := (nonlinearComplexL z ρ σ Dt G s).transpose*Matrix.diagonal (fun i => (ρ i : ℂ)))]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hk]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  have he (m : Fin N) :
      (nonlinearComplexJ z ρ σ Dt G s m i*(ρ m : ℂ)*nonlinearComplexL z ρ σ Dt G s m j-
        nonlinearComplexL z ρ σ Dt G s m i*(ρ m : ℂ)*nonlinearComplexJ z ρ σ Dt G s m j)/s=
      nonlinearComplexJ z ρ σ Dt G s m i*((ρ m : ℂ)*FMSA.causalComplexLaplace
        (nonlinearRecenteredQ z ρ σ Dt G m j) s)-
        ((ρ m : ℂ)*FMSA.causalComplexLaplace (nonlinearRecenteredQ z ρ σ Dt G m i) s)*
          nonlinearComplexJ z ρ σ Dt G s m j := by
    apply (div_eq_iff hs).mpr
    linear_combination -(ρ m : ℂ)*nonlinearComplexJ z ρ σ Dt G s m i*
        nonlinearRecenteredQ_complex_laplace_rational z ρ σ Dt G hz hσ s hs hsre m j-
      -(ρ m : ℂ)*nonlinearComplexJ z ρ σ Dt G s m j*
        nonlinearRecenteredQ_complex_laplace_rational z ρ σ Dt G hz hσ s hs hsre m i
  simp only [nonlinearComplexJ, nonlinearComplexL, Matrix.of_apply] at he ⊢
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  ring

theorem complex_matrix_source_reciprocity_iff (F J Y : Matrix (Fin N) (Fin N) ℂ)
    (hF : IsUnit F) (c : ℂ) (hc : c ≠ 0) (hJ : J=c • (Y*F)) :
    F.transpose*J-J.transpose*F=0 ↔ Y.transpose=Y := by
  have he : F.transpose*J-J.transpose*F=c • (F.transpose*(Y-Y.transpose)*F) := by
    rw [hJ, Matrix.transpose_smul, Matrix.transpose_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
      smul_sub, Matrix.mul_assoc]
  rw [he]
  constructor
  · intro h
    have hz : F.transpose*(Y-Y.transpose)*F=0 := by
      ext i j
      have hi := congrFun (congrFun h i) j
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at hi
      exact (mul_eq_zero.mp hi).resolve_left hc
    have hz1 : F.transpose*(Y-Y.transpose)=0 :=
      (IsUnit.mul_left_injective hF) (by simpa using hz)
    have hz2 : Y-Y.transpose=0 :=
      (IsUnit.mul_right_injective ((Matrix.isUnit_transpose F).mpr hF)) (by simpa using hz1)
    exact (sub_eq_zero.mp hz2).symm
  · intro h
    rw [h, sub_self, Matrix.mul_zero, Matrix.zero_mul, smul_zero]

theorem nonlinear_actual_complex_laplace_reciprocity_iff (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (s : ℂ) (hs : 0 < s.re) :
    nonlinearComplexReciprocityResidual z ρ σ Dt G s=0 ↔
      (rdfMatrixLaplace (nonlinearCausalG z ρ σ Dt G) s).transpose=
        rdfMatrixLaplace (nonlinearCausalG z ρ σ Dt G) s := by
  have hs0 : s ≠ 0 := by intro h; simpa [h] using hs
  let F := 1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s
  let Y := rdfMatrixLaplace (nonlinearCausalG z ρ σ Dt G) s
  have hu : IsUnit F := nonlinear_complex_block_isUnit_of_weighted_budget
    z ρ σ Dt G hz hσ δ hδ.le hδz hb s hs.le
  have hc : (2*(π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr pi_ne_zero)
  have hJ : nonlinearComplexJ z ρ σ Dt G s=(2*(π : ℂ)) • (Y*F) := by
    have hr := nonlinearCausalG_actual_complex_laplace_renewal z ρ σ Dt G hz hσ hv δ hδ hδz hb s hs
    change Y*F=rdfMatrixLaplace (nonlinearGSource z ρ σ Dt G) s at hr
    rw [hr]
    ext i j
    rw [Matrix.smul_apply, nonlinearGSource_actual_complex_laplace z ρ σ Dt G hz s hs i j]
    simp only [smul_eq_mul]
    field_simp
  rw [nonlinearComplexReciprocityResidual_actual_factor z ρ σ Dt G hz hσ s hs0 hs.le]
  exact complex_matrix_source_reciprocity_iff F _ Y hu _ hc hJ

theorem nonlinear_finite_certificate_actual_complex_laplace_reciprocity
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i) (hv : vacMix ρ σ ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1)
    (hcert : NonlinearFiniteReciprocityCertificate z ρ σ Dt G) (s : ℂ) (hs : 0 < s.re) :
    (rdfMatrixLaplace (nonlinearCausalG z ρ σ Dt G) s).transpose=
      rdfMatrixLaplace (nonlinearCausalG z ρ σ Dt G) s := by
  apply (nonlinear_actual_complex_laplace_reciprocity_iff z ρ σ Dt G hz hσ hv δ hδ hδz hb s hs).mp
  exact nonlinear_finite_certificate_complex_residual_zero z ρ σ Dt G hz hcert s
    (by intro h; simpa [h] using hs) hs.le

end FMSA.ExactMSA.MultiTailMixture
