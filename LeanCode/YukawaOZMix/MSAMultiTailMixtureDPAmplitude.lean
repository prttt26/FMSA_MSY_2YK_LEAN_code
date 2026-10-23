import LeanCode.YukawaOZMix.MSAMultiTailMixtureEdgePropagator

/-! Independent HS resolvent amplitudes and their density normalization.
K here is the unweighted coefficient in c1=K exp(-z(r-R))/r. The paper's
weighted source is 2*pi*sqrt(rho_i*rho_j)*K. No division by density is used.
This is an amplitude dictionary, not the full DP core DCF identity. -/
noncomputable section
open Real MSAMixture FMSA.MatrixQ0 FMSA.ExactMSA.Breakpoint
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

def reducedHSPropagation (z : ι → ℝ) (ρ σ : Fin N → ℝ) (u : ι) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (hsMoment ρ σ (z u)) * (Matrix.of (baseSecond z ρ σ u))⁻¹

def dpHSLeft (z : ι → ℝ) (ρ σ : Fin N → ℝ) (u : ι) : Matrix (Fin N) (Fin N) ℝ :=
  1 + reducedHSPropagation z ρ σ u * Matrix.diagonal ρ

theorem dpHSLeft_eq_inverse_transpose (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hvac : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) :
    dpHSLeft z ρ σ u = ((Matrix.of (baseFirst z ρ σ u))⁻¹).transpose := by
  have hdet : IsUnit (1-Matrix.diagonal ρ*Matrix.of (hsMoment ρ σ (z u))).det := by
    rw [← baseSecond_matrix_moment]
    convert! baseSecond_isUnit_det z ρ σ hz hvac hρ hσ u using 1
  have hright : dpHSLeft z ρ σ u * (Matrix.of (baseFirst z ρ σ u)).transpose = 1 := by
    rw [dpHSLeft, reducedHSPropagation, baseSecond_matrix_moment, baseFirst_transpose_matrix_moment]
    exact dual_resolvent_right_inverse _ _ hdet
  simpa only [Matrix.transpose_nonsing_inv] using (Matrix.inv_eq_left_inv hright).symm

def dpBareAmplitude (z : ι → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix ι N) (u : ι) :
    Matrix (Fin N) (Fin N) ℝ :=
  (2*π) • (dpHSLeft z ρ σ u * Matrix.of (K u) * (dpHSLeft z ρ σ u).transpose)

theorem dpBareAmplitude_eq_dressedEdgeSlope (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hvac : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) :
    dpBareAmplitude z ρ σ K u = (z u) • dressedEdgeSlope z ρ σ K u := by
  rw [dpBareAmplitude, dpHSLeft_eq_inverse_transpose z ρ σ hz hvac hρ hσ u,
    Matrix.transpose_transpose, dressedEdgeSlope, smul_smul]
  congr 1
  field_simp [(hz u).ne']

theorem dpHSLeft_entry (z : ι → ℝ) (ρ σ : Fin N → ℝ) (u : ι) (i j : Fin N) :
    dpHSLeft z ρ σ u i j = (if i=j then 1 else 0) + reducedHSPropagation z ρ σ u i j*ρ j := by
  simp only [dpHSLeft, Matrix.add_apply, Matrix.one_apply, Matrix.mul_diagonal]

theorem dpBareAmplitude_fourterms (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (u : ι) (i j : Fin N) :
    dpBareAmplitude z ρ σ K u i j = 2*π*(K u i j +
      (∑ n, K u i n * reducedHSPropagation z ρ σ u j n * ρ n) +
      (∑ m, reducedHSPropagation z ρ σ u i m * K u m j * ρ m) +
      ∑ m, ∑ n, reducedHSPropagation z ρ σ u i m * K u m n *
        reducedHSPropagation z ρ σ u j n * ρ m * ρ n) := by
  unfold dpBareAmplitude
  rw [Matrix.mul_assoc]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply,
    dpHSLeft_entry, Matrix.of_apply, add_mul, mul_add, Finset.sum_add_distrib,
    mul_ite, ite_mul, zero_mul, mul_zero, one_mul, mul_one,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.mul_sum]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  ring

def densitySqrtMatrix (ρ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => sqrt (ρ i))

theorem densitySqrtMatrix_sq (ρ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i) :
    densitySqrtMatrix ρ * densitySqrtMatrix ρ = Matrix.diagonal ρ := by
  rw [densitySqrtMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_self_sqrt (hρ i)

def recenteredHSFactor (z : ι → ℝ) (ρ σ : Fin N → ℝ) (u : ι) :
    Matrix (Fin N) (Fin N) ℝ :=
  1-densitySqrtMatrix ρ * Matrix.of (hsMoment ρ σ (z u)) * densitySqrtMatrix ρ

def weightedHSLeft (z : ι → ℝ) (ρ σ : Fin N → ℝ) (u : ι) :
    Matrix (Fin N) (Fin N) ℝ :=
  1+densitySqrtMatrix ρ * reducedHSPropagation z ρ σ u * densitySqrtMatrix ρ

theorem weightedHSLeft_eq_inverse (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hvac : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) :
    weightedHSLeft z ρ σ u = (recenteredHSFactor z ρ σ u)⁻¹ := by
  have hdet : IsUnit (1-Matrix.diagonal ρ*Matrix.of (hsMoment ρ σ (z u))).det := by
    rw [← baseSecond_matrix_moment]
    convert! baseSecond_isUnit_det z ρ σ hz hvac hρ hσ u using 1
  have hdetS : IsUnit (1-densitySqrtMatrix ρ*(densitySqrtMatrix ρ*Matrix.of (hsMoment ρ σ (z u)))).det := by
    rw [← Matrix.mul_assoc, densitySqrtMatrix_sq ρ hρ]
    exact hdet
  have h := dual_resolvent_right_inverse
    (densitySqrtMatrix ρ*Matrix.of (hsMoment ρ σ (z u))) (densitySqrtMatrix ρ) hdetS
  have he : weightedHSLeft z ρ σ u * recenteredHSFactor z ρ σ u = 1 := by
    simpa only [weightedHSLeft, reducedHSPropagation, recenteredHSFactor,
      ← Matrix.mul_assoc, densitySqrtMatrix_sq ρ hρ, ← baseSecond_matrix_moment] using h
  exact (Matrix.inv_eq_left_inv he).symm

theorem weightedHSLeft_density_intertwining (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (u : ι) :
    weightedHSLeft z ρ σ u * densitySqrtMatrix ρ = densitySqrtMatrix ρ * dpHSLeft z ρ σ u := by
  unfold weightedHSLeft dpHSLeft
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one]
  rw [Matrix.mul_assoc (densitySqrtMatrix ρ * reducedHSPropagation z ρ σ u),
    densitySqrtMatrix_sq ρ hρ, Matrix.mul_assoc]

def paperWeightedK (ρ : Fin N → ℝ) (K : TailMatrix ι N) (u : ι) : Matrix (Fin N) (Fin N) ℝ :=
  (2*π) • (densitySqrtMatrix ρ * Matrix.of (K u) * densitySqrtMatrix ρ)

theorem paperWeightedK_entry (ρ : Fin N → ℝ) (K : TailMatrix ι N) (u : ι) (i j : Fin N) :
    paperWeightedK ρ K u i j = 2*π*sqrt (ρ i)*sqrt (ρ j)*K u i j := by
  simp only [paperWeightedK, densitySqrtMatrix, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  ring

theorem weighted_DP_amplitude_dictionary (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hρ : ∀ i, 0 ≤ ρ i) (u : ι) :
    weightedHSLeft z ρ σ u * paperWeightedK ρ K u * (weightedHSLeft z ρ σ u).transpose =
      densitySqrtMatrix ρ * dpBareAmplitude z ρ σ K u * densitySqrtMatrix ρ := by
  have ht : densitySqrtMatrix ρ * (weightedHSLeft z ρ σ u).transpose =
      (dpHSLeft z ρ σ u).transpose * densitySqrtMatrix ρ := by
    have h := congrArg Matrix.transpose (weightedHSLeft_density_intertwining z ρ σ hρ u)
    simpa only [Matrix.transpose_mul, densitySqrtMatrix, Matrix.diagonal_transpose] using h
  unfold paperWeightedK dpBareAmplitude
  simp only [mul_smul_comm, smul_mul_assoc]
  congr 1
  calc
    _ = (weightedHSLeft z ρ σ u*densitySqrtMatrix ρ) * Matrix.of (K u) *
        (densitySqrtMatrix ρ*(weightedHSLeft z ρ σ u).transpose) := by noncomm_ring
    _ = _ := by rw [weightedHSLeft_density_intertwining z ρ σ hρ u, ht]; noncomm_ring

def hsPhaseMatrix (σ : Fin N → ℝ) (s : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => exp (s*σ i/2))

theorem hsPhaseMatrix_mul_neg (σ : Fin N → ℝ) (s : ℝ) :
    hsPhaseMatrix σ s * hsPhaseMatrix σ (-s) = 1 := by
  unfold hsPhaseMatrix
  rw [Matrix.diagonal_mul_diagonal]
  have he : (fun i => exp (s*σ i/2)*exp ((-s)*σ i/2)) = (fun _ => (1 : ℝ)) := by
    funext i
    rw [← exp_add]
    convert exp_zero using 1 <;> ring
  rw [he, Matrix.diagonal_one]

def actualHSFactor (z : ι → ℝ) (ρ σ : Fin N → ℝ) (u : ι) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of (fun i j => (if i=j then 1 else 0) - sqrt (ρ i)*sqrt (ρ j)*hsTransform ρ σ (z u) i j)

theorem hsTransform_eq_phase_moment (ρ σ : Fin N → ℝ) (s : ℝ) (i j : Fin N) :
    hsTransform ρ σ s i j = exp (-s*edgeLo σ i j)*hsMoment ρ σ s i j := by
  rfl

theorem actualHSFactor_phase (z : ι → ℝ) (ρ σ : Fin N → ℝ) (u : ι) :
    actualHSFactor z ρ σ u = hsPhaseMatrix σ (z u) * recenteredHSFactor z ρ σ u * hsPhaseMatrix σ (-z u) := by
  ext i j
  have he : exp (z u*σ i/2)*exp ((-z u)*σ j/2) = exp (-z u*edgeLo σ i j) := by
    rw [← exp_add]
    congr 1
    unfold edgeLo
    ring
  simp only [actualHSFactor, Matrix.of_apply, hsPhaseMatrix, Matrix.diagonal_mul,
    Matrix.mul_diagonal, recenteredHSFactor, Matrix.sub_apply, densitySqrtMatrix,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.one_apply, hsTransform_eq_phase_moment]
  by_cases hij : i=j
  · subst j
    simp only [if_true, edgeLo, sub_self, zero_div, mul_zero, neg_zero, exp_zero, mul_one] at he ⊢
    linear_combination -(1-sqrt (ρ i)*hsMoment ρ σ (z u) i i*sqrt (ρ i))*he
  · simp only [if_neg hij]
    calc
      _ = -(sqrt (ρ i)*sqrt (ρ j)*hsMoment ρ σ (z u) i j) * exp (-z u*edgeLo σ i j) := by ring
      _ = _ := by rw [← he]; ring

theorem actualHSFactor_inverse_phase (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hvac : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) :
    (actualHSFactor z ρ σ u)⁻¹ =
      hsPhaseMatrix σ (z u)*weightedHSLeft z ρ σ u*hsPhaseMatrix σ (-z u) := by
  have hdet : IsUnit (1-densitySqrtMatrix ρ*(densitySqrtMatrix ρ*Matrix.of (hsMoment ρ σ (z u)))).det := by
    rw [← Matrix.mul_assoc, densitySqrtMatrix_sq ρ hρ, ← baseSecond_matrix_moment]
    convert! baseSecond_isUnit_det z ρ σ hz hvac hρ hσ u using 1
  have hdual := dual_resolvent_right_inverse
    (densitySqrtMatrix ρ*Matrix.of (hsMoment ρ σ (z u))) (densitySqrtMatrix ρ) hdet
  have hright : weightedHSLeft z ρ σ u * recenteredHSFactor z ρ σ u = 1 := by
    simpa only [weightedHSLeft, reducedHSPropagation, recenteredHSFactor,
      ← Matrix.mul_assoc, densitySqrtMatrix_sq ρ hρ, ← baseSecond_matrix_moment] using hdual
  apply Matrix.inv_eq_left_inv
  rw [actualHSFactor_phase]
  calc
    _ = hsPhaseMatrix σ (z u) * weightedHSLeft z ρ σ u *
        (hsPhaseMatrix σ (-z u)*hsPhaseMatrix σ (z u)) *
        recenteredHSFactor z ρ σ u * hsPhaseMatrix σ (-z u) := by noncomm_ring
    _ = 1 := by rw [show hsPhaseMatrix σ (-z u)*hsPhaseMatrix σ (z u) = 1 by
      simpa only [neg_neg] using hsPhaseMatrix_mul_neg σ (-z u)]
                rw [Matrix.mul_one, Matrix.mul_assoc (hsPhaseMatrix σ (z u)), hright, Matrix.mul_one,
                  hsPhaseMatrix_mul_neg]

theorem actualHSFactor_eq_actual_laplace (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i) (G0 : TailMatrix ι N) (u : ι) :
    actualHSFactor z ρ σ u = Matrix.of (fun i j => (if i=j then 1 else 0) -
      sqrt (ρ i)*sqrt (ρ j)*(∫ r : ℝ, q z σ (amplitudeA z ρ σ 0 G0)
        (amplitudeQp z ρ σ 0 G0) (W z ρ 0 G0) (C z ρ σ 0 G0) i j r * exp (-z u*r))) := by
  ext i j
  simp only [actualHSFactor, Matrix.of_apply, laplaceQ_eq_Qhat z hz σ _ _ _ _ hσ _ _ _ (hz u)]
  rw [← dressedQhat_zero z ρ σ G0]
  rfl

/-- The precise phase-removed inverse used by the bare HS propagator in
the paper/Python DP formulas. All actual HS inverse conditions are internal. -/
theorem actualHSFactor_inverse_recentered_entry (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (hz : ∀ u, 0 < z u) (hvac : 0 < vacMix ρ σ)
    (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i) (u : ι) (i j : Fin N) :
    (actualHSFactor z ρ σ u)⁻¹ i j * exp (z u*edgeLo σ i j) = weightedHSLeft z ρ σ u i j := by
  rw [actualHSFactor_inverse_phase z ρ σ hz hvac hρ hσ u]
  simp only [hsPhaseMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have he : exp (z u*σ i/2)*exp ((-z u)*σ j/2)*exp (z u*edgeLo σ i j) = 1 := by
    rw [← exp_add, ← exp_add]
    convert exp_zero using 1 <;> unfold edgeLo <;> ring
  calc
    _ = weightedHSLeft z ρ σ u i j *
      (exp (z u*σ i/2)*exp ((-z u)*σ j/2)*exp (z u*edgeLo σ i j)) := by ring
    _ = _ := by rw [he, mul_one]

theorem dpBareAmplitude_symmetric (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K : TailMatrix ι N) (hK : ∀ u i j, K u i j=K u j i) (u : ι) :
    (dpBareAmplitude z ρ σ K u).transpose = dpBareAmplitude z ρ σ K u := by
  have hKM : (Matrix.of (K u)).transpose = Matrix.of (K u) := by ext i j; exact hK u j i
  rw [dpBareAmplitude, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, hKM, Matrix.mul_assoc]

end FMSA.ExactMSA.MultiTailMixture
