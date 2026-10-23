import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearPointwise

/-! Actual finite-frequency factor invertibility from the integral budget.
Strict radial positivity additionally retains the primitive core condition. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators ComplexOrder
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem nonlinearRecenteredQ_actual_fourier (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (k : ℝ) (i j : Fin N) :
    FMSA.causalComplexLaplace (nonlinearRecenteredQ z ρ σ Dt G i j) (Complex.I*k)=
      Complex.exp ((Complex.I*k)*(edgeLo σ i j : ℂ))*fourierQ z σ
        (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) k i j := by
  have he := causalShift_complex_laplace (nonlinearRecenteredQ z ρ σ Dt G i j)
    (edgeLo σ i j) (Complex.I*k)
  rw [← nonlinearActualQ_eq_causalShift] at he
  change fourierQ z σ _ _ _ _ k i j=Complex.exp (-(Complex.I*k)*(edgeLo σ i j : ℂ))*_ at he
  rw [he, ← mul_assoc, ← Complex.exp_add]
  simp

theorem nonlinear_fourierFactor_isUnit_of_weighted_budget
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i) (hρ : ∀ i, 0 ≤ ρ i)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (k : ℝ) :
    IsUnit (fourierFactor z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) k) := by
  let Q : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fourierQ z σ
    (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) k)
  let D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun i => (ρ i : ℂ))
  let S : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun i => (sqrt (ρ i) : ℂ))
  let E : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun i => Complex.exp ((Complex.I*k)*(σ i : ℂ)/2))
  let V : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun i => Complex.exp (-(Complex.I*k)*(σ i : ℂ)/2))
  have hEV : E*V=1 := by
    ext i j
    simp only [E, V, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs
    · rw [← Complex.exp_add, show (Complex.I*k)*(σ i : ℂ)/2+
        -(Complex.I*k)*(σ i : ℂ)/2=0 by ring, Complex.exp_zero]
    · rfl
  have hSS : S*S=D := by
    dsimp only [S, D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact_mod_cast mul_self_sqrt (hρ i)
  have hk : rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) (Complex.I*k)=V*(D*Q)*E := by
    ext i j
    simp only [rdfMatrixLaplace, Matrix.of_apply, FMSA.causalComplexLaplace,
      nonlinearCausalKernel, Matrix.of_apply, V, E, D, Matrix.diagonal_mul, Matrix.mul_diagonal]
    have hi : (∫ t in Ioi (0 : ℝ), ((ρ i*nonlinearRecenteredQ z ρ σ Dt G i j t : ℝ) : ℂ)*
        Complex.exp (-(Complex.I*k)*t))=
        (ρ i : ℂ)*FMSA.causalComplexLaplace (nonlinearRecenteredQ z ρ σ Dt G i j) (Complex.I*k) := by
      unfold FMSA.causalComplexLaplace
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _; push_cast; ring
    rw [hi, nonlinearRecenteredQ_actual_fourier]
    have he : Complex.exp ((Complex.I*k)*(edgeLo σ i j : ℂ))=
        Complex.exp (-(Complex.I*k)*(σ i : ℂ)/2)*Complex.exp ((Complex.I*k)*(σ j : ℂ)/2) := by
      rw [← Complex.exp_add]; congr 1; unfold edgeLo; push_cast; ring
    rw [he]
    simp only [Q, Matrix.of_apply]
    ring
  have hdet : (1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) (Complex.I*k)).det=(1-D*Q).det := by
    rw [hk, Matrix.det_one_sub_mul_comm]
    rw [← Matrix.mul_assoc E V, hEV, Matrix.one_mul]
  have hf : fourierFactor z ρ σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G)
      (W z ρ Dt G) (C z ρ σ Dt G) k=1-S*Q*S := by
    ext i j
    simp only [fourierFactor, Matrix.sub_apply, Matrix.of_apply, S, Q,
      Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  have hfd : (1-S*Q*S).det=(1-D*Q).det := by
    rw [Matrix.det_one_sub_mul_comm, ← Matrix.mul_assoc, hSS]
  rw [hf, Matrix.isUnit_iff_isUnit_det, hfd, ← hdet, ← Matrix.isUnit_iff_isUnit_det]
  exact nonlinear_complex_block_isUnit_of_weighted_budget z ρ σ Dt G hz hσ δ hδ hδz hb
    (Complex.I*k) (by simp)

/-- Strict positivity at every nonzero k for the actual radial DCF. The core
primitive reciprocity condition is explicit; it is not supplied RDF/OZ data. -/
theorem nonlinear_actualRadial_posDef_of_core_and_budget
    (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K Dt G : TailMatrix ι N)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 < σ i) (hρ : ∀ i, 0 ≤ ρ i)
    (hroot : IsRoot z ρ σ K Dt G) (hK : ∀ u i j, K u i j=K u j i)
    (hcore : AECorePrimitiveReciprocity z ρ σ Dt G)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (k : ℝ) (hk : k ≠ 0) :
    Matrix.PosDef (1-Matrix.of (fun i j => (sqrt (ρ i) : ℂ)*(sqrt (ρ j) : ℂ)*
      (FMSA.HardSphere.radial_fourier (orderedRadialCorrelation z ρ σ K Dt G i j) k : ℂ))) := by
  rw [← actualRadial_matrix_gram_of_ae_core_reciprocity z hz ρ σ K Dt G hσ hρ hroot hK hcore k hk]
  exact fourierFactor_gram_posDef_of_isUnit z ρ σ _ _ _ _ k
    (nonlinear_fourierFactor_isUnit_of_weighted_budget z ρ σ Dt G hz
      (fun i => (hσ i).le) hρ δ hδ hδz hb k)

end FMSA.ExactMSA.MultiTailMixture
