import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearRegularity

/-! Actual nonlinear Fourier OZ from finite coefficient admissibility tests.
No supplied Fourier OZ, radial OZ, or primitive core reciprocity is a premise. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0 FMSA.HardSphere
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem nonlinearCompletedZ_reciprocity (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1)
    (hc : NonlinearFiniteReciprocityCertificate z ρ σ Dt G) (s : ℂ) :
    (nonlinearCompletedZ z ρ σ Dt G s).transpose=nonlinearCompletedZ z ρ σ Dt G s := by
  ext i j
  simp only [nonlinearCompletedZ, Matrix.transpose_apply, Matrix.add_apply,
    rdfMatrixLaplace, Matrix.of_apply, nonlinearComplexBackground]
  have hR : edgeHi σ j i=edgeHi σ i j := by unfold edgeHi; ring
  rw [hR]
  congr 1
  unfold FMSA.causalComplexLaplace
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have he := nonlinear_finite_certificate_actual_causal_reciprocity z ρ σ Dt G hz hσ hv δ hδ hδz hb hc j i t ht.le
  simp only [nonlinearCausalG, Matrix.of_apply, hR] at he
  dsimp only
  rw [add_right_cancel (add_right_cancel he)]

theorem nonlinearCausalKernel_actual_fourier_entry (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (k : ℝ) (i j : Fin N) :
    rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) (Complex.I*k) i j=
      (ρ i : ℂ)*Complex.exp ((Complex.I*k)*(edgeLo σ i j : ℂ))*
        nonlinearActualFourierQ z ρ σ Dt G k i j := by
  have he : rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) (Complex.I*k) i j=
      (ρ i : ℂ)*FMSA.causalComplexLaplace (nonlinearRecenteredQ z ρ σ Dt G i j) (Complex.I*k) := by
    unfold rdfMatrixLaplace FMSA.causalComplexLaplace nonlinearCausalKernel
    simp only [Matrix.of_apply]
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _; push_cast; ring
  rw [he, nonlinearRecenteredQ_actual_fourier, ← mul_assoc]
  rfl

theorem nonlinear_actual_recentered_factor_phase (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (k : ℝ) :
    (1-(nonlinearActualFourierQ z ρ σ Dt G k).transpose*Matrix.diagonal (fun i => (ρ i : ℂ)))*
        rdfPhase σ (Complex.I*k)=
      rdfPhase σ (Complex.I*k)*(1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) (Complex.I*k)).transpose := by
  ext i j
  simp only [rdfPhase, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sub_apply,
    Matrix.transpose_apply, Matrix.one_apply, nonlinearCausalKernel_actual_fourier_entry]
  have hp := rdfPhase_edge_product σ (Complex.I*k) j i
  by_cases h : i=j
  · subst j; simp only [if_pos rfl, edgeLo, sub_self, zero_div, Complex.ofReal_zero,
      mul_zero, Complex.exp_zero, mul_one]; ring
  · simp only [if_neg h, if_neg (Ne.symm h), zero_sub]
    linear_combination (ρ j : ℂ)*nonlinearActualFourierQ z ρ σ Dt G k j i*hp

theorem nonlinear_completed_phase_transfer (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1)
    (hc : NonlinearFiniteReciprocityCertificate z ρ σ Dt G) (k : ℝ) (hk : k ≠ 0) :
    (1-(nonlinearActualFourierQ z ρ σ Dt G k).transpose*Matrix.diagonal (fun i => (ρ i : ℂ)))*
      rdfPhase σ (Complex.I*k)*nonlinearCompletedZ z ρ σ Dt G (Complex.I*k)*rdfPhase σ (Complex.I*k)=
      (2*(π : ℂ))⁻¹ • (rdfPhase σ (Complex.I*k)*(nonlinearComplexJ z ρ σ Dt G (Complex.I*k)).transpose*
        rdfPhase σ (Complex.I*k)) := by
  have hs : Complex.I*(k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)
  have he := congrArg Matrix.transpose (nonlinearCompletedZ_actual_axis_renewal
    z ρ σ Dt G hz hσ hv δ hδ hδz hb (Complex.I*k) hs (by simp))
  simp only [Matrix.transpose_mul, Matrix.transpose_smul,
    nonlinearCompletedZ_reciprocity z ρ σ Dt G hz hσ hv δ hδ hδz hb hc] at he
  rw [nonlinear_actual_recentered_factor_phase]
  rw [Matrix.mul_assoc (rdfPhase σ (Complex.I*k)), he]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem nonlinear_actual_OZ_factorization (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hw : NonlinearFiniteWronskianCertificate z ρ σ Dt G) (k : ℝ) (hk : k ≠ 0) :
    1-nonlinearActualFourierC z ρ σ Dt G k*Matrix.diagonal (fun i => (ρ i : ℂ))=
      (1-nonlinearActualFourierQ z ρ σ Dt G (-k)*Matrix.diagonal (fun i => (ρ i : ℂ)))*
      (1-(nonlinearActualFourierQ z ρ σ Dt G k).transpose*Matrix.diagonal (fun i => (ρ i : ℂ))) := by
  have he : nonlinearActualFourierC z ρ σ Dt G (-k)=nonlinearActualFourierC z ρ σ Dt G k := by
    rw [nonlinearActualFourierC_neg_transpose, ← nonlinear_finite_wronskian_actual_spectral_reciprocity z ρ σ Dt G hz hσ hw k hk]
  rw [← he, nonlinearActualFourierC_eq_Q_product]
  simp only [neg_neg, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, Matrix.add_mul, Matrix.mul_assoc]
  abel

theorem nonlinearH_actual_phase_difference (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 < σ i)
    (hv : vacMix ρ σ ≠ 0) (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (k : ℝ) (hk : k ≠ 0) :
    radialMatrixFourier (nonlinearH z ρ σ Dt G) k=(2*(π : ℂ)/(Complex.I*k)) •
      (rdfPhase σ (-(Complex.I*k))*nonlinearCompletedZ z ρ σ Dt G (-(Complex.I*k))*rdfPhase σ (-(Complex.I*k))-
        rdfPhase σ (Complex.I*k)*nonlinearCompletedZ z ρ σ Dt G (Complex.I*k)*rdfPhase σ (Complex.I*k)) := by
  ext i j
  have hR : 0 < edgeHi σ i j := by unfold edgeHi; linarith [hσ i,hσ j]
  have hm := nonlinearRDFMoment_positive_laplace z ρ σ Dt G i j hR hz (fun i => (hσ i).le) hv δ hδ hδz hb (-k) (neg_ne_zero.mpr hk)
  simp only [Complex.ofReal_neg, mul_neg, neg_neg] at hm
  simp only [radialMatrixFourier, Matrix.of_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  rw [nonlinearH_radial_fourier z ρ σ Dt G i j hz (fun i => (hσ i).le) hv δ hδ hδz hb k hk,
    nonlinearRDFMoment_positive_laplace z ρ σ Dt G i j hR hz (fun i => (hσ i).le) hv δ hδ hδz hb k hk, hm]
  simp only [rdfPhase, Matrix.diagonal_mul, Matrix.mul_diagonal, nonlinearCompletedZ,
    nonlinearComplexBackground, hsPairBackground, Matrix.of_apply, Matrix.add_apply]
  have hp := rdfPhase_contact_product σ (-(Complex.I*k)) i j
  have hn := rdfPhase_contact_product σ (Complex.I*k) i j
  simp only [neg_neg] at hp
  rw [← hp, ← hn]
  field_simp [Complex.ofReal_ne_zero.mpr hk, Complex.I_ne_zero]
  <;> ring

theorem nonlinearH_actual_Fourier_OZ_of_finite_certificates
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 < σ i) (hv : vacMix ρ σ ≠ 0)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j=K u j i)
    (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1)
    (hr : NonlinearFiniteReciprocityCertificate z ρ σ Dt G)
    (hw : NonlinearFiniteWronskianCertificate z ρ σ Dt G) (k : ℝ) (hk : k ≠ 0) :
    radialMatrixFourier (nonlinearH z ρ σ Dt G) k=
      radialMatrixFourier (orderedRadialCorrelation z ρ σ K Dt G) k+
      radialMatrixFourier (orderedRadialCorrelation z ρ σ K Dt G) k*Matrix.diagonal (fun i => (ρ i : ℂ))*
        radialMatrixFourier (nonlinearH z ρ σ Dt G) k := by
  let D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun i => (ρ i : ℂ))
  let T := 1-nonlinearActualFourierC z ρ σ Dt G k*D
  have hc : nonlinearActualFourierC z ρ σ Dt G k=radialMatrixFourier (orderedRadialCorrelation z ρ σ K Dt G) k := by
    ext i j
    exact spectralBaxterC_eq_ordered_radial_of_ae_core_reciprocity z hz ρ σ K Dt G hσ hroot hK
      (nonlinear_finite_wronskian_actual_core_reciprocity z ρ σ Dt G hz (fun i => (hσ i).le) hw) k hk i j
  have hTminus : 1-nonlinearActualFourierC z ρ σ Dt G (-k)*D=T := by
    rw [nonlinearActualFourierC_neg_transpose,
      ← nonlinear_finite_wronskian_actual_spectral_reciprocity z ρ σ Dt G hz (fun i => (hσ i).le) hw k hk]
  have hphase (w : ℝ) (hw0 : w ≠ 0) :
      (1-nonlinearActualFourierC z ρ σ Dt G w*D)*rdfPhase σ (Complex.I*w)*
          nonlinearCompletedZ z ρ σ Dt G (Complex.I*w)*rdfPhase σ (Complex.I*w)=
        (2*(π : ℂ))⁻¹ • ((1-nonlinearActualFourierQ z ρ σ Dt G (-w)*D)*
          (rdfPhase σ (Complex.I*w)*(nonlinearComplexJ z ρ σ Dt G (Complex.I*w)).transpose*rdfPhase σ (Complex.I*w))) := by
    rw [nonlinear_actual_OZ_factorization z ρ σ Dt G hz (fun i => (hσ i).le) hw w hw0]
    have he := congrArg (fun X => (1-nonlinearActualFourierQ z ρ σ Dt G (-w)*D)*X)
      (nonlinear_completed_phase_transfer z ρ σ Dt G hz (fun i => (hσ i).le) hv δ hδ hδz hb hr w hw0)
    simpa only [D, Matrix.mul_assoc, Matrix.mul_smul] using he
  have hm := hphase (-k) (neg_ne_zero.mpr hk)
  rw [hTminus] at hm
  simp only [Complex.ofReal_neg, mul_neg, neg_neg] at hm
  have hprod : T*radialMatrixFourier (nonlinearH z ρ σ Dt G) k=nonlinearActualFourierC z ρ σ Dt G k := by
    rw [nonlinearH_actual_phase_difference z ρ σ Dt G hz hσ hv δ hδ hδz hb k hk,
      Matrix.mul_smul, Matrix.mul_sub]
    simp only [← Matrix.mul_assoc]
    rw [hm, hphase k hk, ← smul_sub,
      nonlinear_actual_source_wronskian_of_finite_certificate z ρ σ Dt G hz (fun i => (hσ i).le) hw k hk,
      smul_smul, smul_smul]
    have hs : Complex.I*(k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)
    have he : (2*(π : ℂ)/(Complex.I*k))*(2*(π : ℂ))⁻¹*(Complex.I*k)=1 := by
      field_simp [Complex.ofReal_ne_zero.mpr hk, Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr pi_ne_zero]
    rw [he, one_smul]
  dsimp only [T] at hprod
  rw [Matrix.sub_mul, Matrix.one_mul, hc] at hprod
  exact sub_eq_iff_eq_add.mp hprod

end FMSA.ExactMSA.MultiTailMixture
