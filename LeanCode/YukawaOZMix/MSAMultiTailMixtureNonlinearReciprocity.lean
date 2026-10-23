import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearGIdentification

/-! A finite rational diagnostic for the actual nonlinear RDF Laplace reciprocity.
The row contact exponential cancels exactly. This is a test, not a proof that
every BH root obeys reciprocity or full radial OZ. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def nonlinearRationalJ (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (s : ℝ) : Matrix (Fin N) (Fin N) ℝ := Matrix.of (fun i j =>
      amplitudeA z ρ σ Dt G j/s^2+amplitudeQp z ρ σ Dt G i j/s+
        ∑ u, z u*C z ρ σ Dt G u i j/(s+z u))

def nonlinearLowerQValue (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (i j : Fin N) : ℝ := -σ i*amplitudeQp z ρ σ Dt G i j+
      amplitudeA z ρ σ Dt G j*σ i^2/2+(∑ u, (W z ρ Dt G u i j+C z ρ σ Dt G u i j))

def nonlinearRationalL (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (s : ℝ) : Matrix (Fin N) (Fin N) ℝ := Matrix.of (fun i j =>
      amplitudeA z ρ σ Dt G j/s^2+
        (amplitudeQp z ρ σ Dt G i j-σ i*amplitudeA z ρ σ Dt G j)/s+
        nonlinearLowerQValue z ρ σ Dt G i j-∑ u, z u*W z ρ Dt G u i j/(s+z u))

theorem nonlinear_recentered_dictionary_rational (z : ι → ℝ) (σ A : Fin N → ℝ)
    (qp : Fin N → Fin N → ℝ) (W C : TailMatrix ι N) (s : ℝ) (hs : s ≠ 0)
    (hzs : ∀ u, s+z u ≠ 0) (i j : Fin N) :
    s*exp (s*edgeLo σ i j)*Qhat z σ A qp W C s i j=
      (A j/s^2+(qp i j-σ i*A j)/s-σ i*qp i j+A j*σ i^2/2+
        (∑ u, (W u i j+C u i j))-(∑ u, z u*W u i j/(s+z u)))-
      exp (-s*σ i)*(A j/s^2+qp i j/s+∑ u, z u*C u i j/(s+z u)) := by
  have he0 : exp (s*edgeLo σ i j)*exp (-s*edgeLo σ i j)=1 := by rw [← exp_add]; simp
  have he1 : exp (s*edgeLo σ i j)*exp (-s*edgeHi σ i j)=exp (-s*σ i) := by
    rw [← exp_add]; congr 1; unfold edgeLo edgeHi; ring
  have he : exp (s*edgeLo σ i j)*Qhat z σ A qp W C s i j=
      (1-s*σ i-exp (-s*σ i))/s^2*qp i j+
      (1-s*σ i+(s*σ i)^2/2-exp (-s*σ i))/s^3*A j+
      (∑ u, (W u i j/(s+z u)+C u i j*(1-exp (-s*σ i))/s))+
      (∑ u, exp (-s*σ i)*C u i j/(s+z u)) := by
    unfold Qhat
    rw [mul_add, ← mul_assoc, he0, one_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    calc
      _ = (exp (s*edgeLo σ i j)*exp (-s*edgeHi σ i j))*C u i j/(s+z u) := by ring
      _ = _ := by rw [he1]
  rw [mul_assoc, he]
  have hpoly : s*((1-s*σ i-exp (-s*σ i))/s^2*qp i j+
      (1-s*σ i+(s*σ i)^2/2-exp (-s*σ i))/s^3*A j)=
      A j/s^2+(qp i j-σ i*A j)/s-σ i*qp i j+A j*σ i^2/2-
        exp (-s*σ i)*(A j/s^2+qp i j/s) := by field_simp [hs]; ring
  have htail : s*((∑ u, (W u i j/(s+z u)+C u i j*(1-exp (-s*σ i))/s))+
      ∑ u, exp (-s*σ i)*C u i j/(s+z u))=
      (∑ u, (W u i j+C u i j))-(∑ u, z u*W u i j/(s+z u))-
        exp (-s*σ i)*∑ u, z u*C u i j/(s+z u) := by
    simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    field_simp [hs, hzs u]
    ring
  linear_combination hpoly+htail

theorem nonlinearRecenteredQ_laplace_rational (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (s : ℝ) (hs : 0 < s) (i j : Fin N) :
    s*realCausalLaplace (nonlinearRecenteredQ z ρ σ Dt G i j) s=
      nonlinearRationalL z ρ σ Dt G s i j-exp (-s*σ i)*nonlinearRationalJ z ρ σ Dt G s i j := by
  rw [nonlinearRecenteredQ_actual_laplace z ρ σ Dt G hz hσ s hs]
  simpa only [nonlinearRationalL, nonlinearRationalJ, nonlinearLowerQValue,
    Matrix.of_apply, dressedQhat, mul_assoc, sub_eq_add_neg, add_assoc, neg_mul] using
    nonlinear_recentered_dictionary_rational z σ (amplitudeA z ρ σ Dt G)
      (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) s hs.ne'
    (fun u => (add_pos hs (hz u)).ne') i j

def nonlinearRationalReciprocityResidual (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (s : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  nonlinearRationalJ z ρ σ Dt G s-(nonlinearRationalJ z ρ σ Dt G s).transpose+
    s⁻¹ • ((nonlinearRationalJ z ρ σ Dt G s).transpose*Matrix.diagonal ρ*nonlinearRationalL z ρ σ Dt G s-
      (nonlinearRationalL z ρ σ Dt G s).transpose*Matrix.diagonal ρ*nonlinearRationalJ z ρ σ Dt G s)

theorem nonlinearReciprocityResidual_actual_factor (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (s : ℝ) (hs : 0 < s) :
    nonlinearRationalReciprocityResidual z ρ σ Dt G s=
      (1-realMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s).transpose*
        nonlinearRationalJ z ρ σ Dt G s-
      (nonlinearRationalJ z ρ σ Dt G s).transpose*
        (1-realMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s) := by
  have hk (m j : Fin N) : realMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s m j=
      ρ m*realCausalLaplace (nonlinearRecenteredQ z ρ σ Dt G m j) s := by
    unfold realMatrixLaplace realCausalLaplace nonlinearCausalKernel
    simp only [Matrix.of_apply]
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring
  ext i j
  simp only [nonlinearRationalReciprocityResidual, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, inv_mul_eq_div, Matrix.transpose_apply, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul,
    Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_one,
    Matrix.mul_apply (M := (nonlinearRationalJ z ρ σ Dt G s).transpose*Matrix.diagonal ρ),
    Matrix.mul_apply (M := (nonlinearRationalL z ρ σ Dt G s).transpose*Matrix.diagonal ρ)]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hk]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  have he (m : Fin N) :
      (nonlinearRationalJ z ρ σ Dt G s m i*ρ m*nonlinearRationalL z ρ σ Dt G s m j-
        nonlinearRationalL z ρ σ Dt G s m i*ρ m*nonlinearRationalJ z ρ σ Dt G s m j)/s=
      nonlinearRationalJ z ρ σ Dt G s m i*(ρ m*realCausalLaplace (nonlinearRecenteredQ z ρ σ Dt G m j) s)-
        (ρ m*realCausalLaplace (nonlinearRecenteredQ z ρ σ Dt G m i) s)*nonlinearRationalJ z ρ σ Dt G s m j := by
    apply (div_eq_iff hs.ne').mpr
    linear_combination -ρ m*nonlinearRationalJ z ρ σ Dt G s m i*
        nonlinearRecenteredQ_laplace_rational z ρ σ Dt G hz hσ s hs m j-
      -ρ m*nonlinearRationalJ z ρ σ Dt G s m j*
        nonlinearRecenteredQ_laplace_rational z ρ σ Dt G hz hσ s hs m i
  simp only [nonlinearRationalJ, nonlinearRationalL, Matrix.of_apply] at he ⊢
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  ring

theorem matrix_source_reciprocity_iff (F J Y : Matrix (Fin N) (Fin N) ℝ)
    (hF : IsUnit F) (c : ℝ) (hc : c ≠ 0) (hJ : J=c • (Y*F)) :
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
    have hz1 : F.transpose*(Y-Y.transpose)=0 := (IsUnit.mul_left_injective hF) (by simpa using hz)
    have hz2 : Y-Y.transpose=0 := (IsUnit.mul_right_injective ((Matrix.isUnit_transpose F).mpr hF))
      (by simpa using hz1)
    exact (sub_eq_zero.mp hz2).symm
  · intro h
    rw [h, sub_self, Matrix.mul_zero, Matrix.zero_mul, smul_zero]

/-- Actual positive-real Laplace reciprocity is equivalent to a finite rational
matrix residual. A nonzero residual is a precise failure condition; zero alone
does not certify radial OZ, g positivity, or thermodynamic stability. -/
theorem nonlinear_actual_laplace_reciprocity_iff (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (s : ℝ) (hs : 0 < s) :
    nonlinearRationalReciprocityResidual z ρ σ Dt G s=0 ↔
      (realMatrixLaplace (nonlinearCausalG z ρ σ Dt G) s).transpose=
        realMatrixLaplace (nonlinearCausalG z ρ σ Dt G) s := by
  let F := 1-realMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s
  let Y := realMatrixLaplace (nonlinearCausalG z ρ σ Dt G) s
  have hu : IsUnit F := matrix_one_sub_isUnit_of_absSum _
    ((nonlinearCausalKernel_laplace_budget z ρ σ Dt G hz hσ δ hδ.le hδz s hs).trans_lt hb)
  have hJ : nonlinearRationalJ z ρ σ Dt G s=(2*π) • (Y*F) := by
    have hr := nonlinearCausalG_actual_laplace_renewal z ρ σ Dt G hz hσ hv δ hδ hδz hb s hs
    change Y*F=realMatrixLaplace (nonlinearGSource z ρ σ Dt G) s at hr
    rw [hr]
    ext i j
    rw [Matrix.smul_apply, nonlinearGSource_actual_laplace z ρ σ Dt G hz s hs i j]
    simp only [nonlinearRationalJ, Matrix.of_apply, smul_eq_mul]
    field_simp [pi_ne_zero]
  rw [nonlinearReciprocityResidual_actual_factor z ρ σ Dt G hz hσ s hs]
  exact matrix_source_reciprocity_iff F _ Y hu (2*π) (mul_ne_zero two_ne_zero pi_ne_zero) hJ

theorem nonlinear_nonzero_residual_excludes_pair_reciprocity (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 < σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (s : ℝ) (hs : 0 < s)
    (hres : nonlinearRationalReciprocityResidual z ρ σ Dt G s ≠ 0) :
    ¬∀ i j r, 0 < r → nonlinearG z ρ σ Dt G i j r=nonlinearG z ρ σ Dt G j i r := by
  intro hsym
  apply hres
  apply (nonlinear_actual_laplace_reciprocity_iff z ρ σ Dt G hz (fun i => (hσ i).le)
    hv δ hδ hδz hb s hs).mpr
  ext i j
  have hR : 0 < edgeHi σ i j := by unfold edgeHi; linarith [hσ i, hσ j]
  have hRs : edgeHi σ j i=edgeHi σ i j := by unfold edgeHi; ring
  have he : (∫ r in Ioi (0 : ℝ), exp (-s*r)*(r*nonlinearG z ρ σ Dt G j i r))=
      ∫ r in Ioi (0 : ℝ), exp (-s*r)*(r*nonlinearG z ρ σ Dt G i j r) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [hsym i j r hr]
  rw [nonlinearG_radial_laplace_shift z ρ σ Dt G j i (by rw [hRs]; exact hR) s,
    nonlinearG_radial_laplace_shift z ρ σ Dt G i j hR s, hRs] at he
  simpa only [Matrix.transpose_apply, realMatrixLaplace, Matrix.of_apply] using
    mul_left_cancel₀ (exp_ne_zero _) he

end FMSA.ExactMSA.MultiTailMixture
