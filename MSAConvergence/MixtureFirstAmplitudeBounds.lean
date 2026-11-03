import MSAConvergence.CanonicalInteriorInverseBounds

/-! Uniform control of the ORIGINAL first BH amplitudes over bounded
strengths, for general positive-density canonical mixtures. G is not bounded here. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open scoped BigOperators
namespace FMSA.Convergence.MixtureFirstAmplitudeBounds
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.ActualBHAmplitudeRecovery FMSA.Convergence.CanonicalInverseCovariance
open FMSA.Convergence.CanonicalInteriorInverseBounds
variable {N : ℕ} {T : Type*} [Fintype T]

private theorem density_intertwine (R Q : Matrix (Fin N) (Fin N) ℂ) (hR : R.transpose = R) :
    (1-R*Q.transpose)*R=R*(1-R*Q).transpose := by
  simp only [Matrix.transpose_sub,Matrix.transpose_one,Matrix.transpose_mul,hR]
  noncomm_ring

/-- Exact weighted recovery from the TRANSPOSED ORIGINAL first equation.
The density matrix is not inverted in this identity. -/
theorem first_weighted_inverse_identity (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hσ : ∀ i, 0 ≤ σ i) (K D G : TailMatrix T N)
    (hroot : IsRoot z ρ σ K D G)
    (hc : ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) (u : T) :
    dtSymbol (D,G) u*Matrix.diagonal (fun i => (ρ i : ℂ)) =
      (((2*Real.pi/z u : ℝ) : ℂ) • Matrix.of (fun i j => (K u i j : ℂ)))*
        Matrix.diagonal (fun i => (ρ i : ℂ))*((causalFactor z ρ σ D G (z u : ℂ))⁻¹).transpose := by
  classical
  let R := Matrix.diagonal (fun i => (ρ i : ℂ))
  let Q := rootTransformSymbol z ρ σ (D,G) u
  let A := causalFactor z ρ σ D G (z u : ℂ)
  let B := 1-R*Q.transpose
  let M := dtSymbol (D,G) u
  let F := (((2*Real.pi/z u : ℝ) : ℂ) • Matrix.of (fun i j => (K u i j : ℂ)))
  have hA : A=1-R*Q := by
    change 1-rdfMatrixLaplace (nonlinearCausalKernel z ρ σ D G) (z u : ℂ)=1-R*Q
    rw [actual_kernel_root_dictionary z hz ρ σ hσ (D,G) u]
  have hBR : B*R=R*A.transpose := by
    rw [hA]
    exact density_intertwine R Q (Matrix.diagonal_transpose _)
  have hfirst : M*B=F := by
    change dtSymbol (D,G) u*(1-Matrix.diagonal (fun i => (ρ i : ℂ))*(rootTransformSymbol z ρ σ (D,G) u).transpose) = _
    rw [← first_symbol_matrix]
    ext i j
    simp only [F,firstSymbol,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,hroot.1]
    push_cast
    ring
  have hweighted : (M*R)*A.transpose=F*R := by
    calc
      _ = M*(R*A.transpose) := Matrix.mul_assoc _ _ _
      _ = M*(B*R) := by rw [← hBR]
      _ = (M*B)*R := (Matrix.mul_assoc _ _ _).symm
      _ = _ := by rw [hfirst]
  have hu : IsUnit A := hc _ (by simpa using (hz u).le)
  have hut : IsUnit (A.transpose).det := by
    simpa only [Matrix.det_transpose] using (Matrix.isUnit_iff_isUnit_det A).mp hu
  change M*R=(F*R)*(A⁻¹).transpose
  calc
    _ = ((M*R)*A.transpose)*(A.transpose)⁻¹ := (Matrix.mul_nonsing_inv_cancel_right _ _ hut).symm
    _ = _ := by rw [hweighted,← Matrix.transpose_nonsing_inv]

private theorem strength_entry_bound (K : TailMatrix T N) (B : ℝ) (hB : ‖K‖ ≤ B)
    (u : T) (i j : Fin N) : |K u i j| ≤ max B 0 := by
  exact (((norm_le_pi_norm (K u i) j).trans
    ((norm_le_pi_norm (K u) i).trans (norm_le_pi_norm K u))).trans hB).trans (le_max_left _ _)

/-- A fixed tail's ORIGINAL first amplitudes are uniformly bounded over
all canonical reciprocal roots at bounded strengths. The inverse bound is DERIVED. -/
theorem first_rate_uniform_bound (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (B : ℝ) (u : T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ t i j, K t i j = K t j i) → IsRoot z ρ σ K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) → ∀ i j : Fin N, |D u i j| ≤ C := by
  classical
  obtain ⟨C₀,hC₀,hbound⟩ := actual_inverse_positive_point_uniformly_bounded z hz ρ σ hρ hσ hv (z u) (hz u)
  let Q := |2*Real.pi/z u| *max B 0*(∑ l, ρ l)*C₀
  have hρsum : 0 ≤ ∑ l, ρ l := Finset.sum_nonneg (fun l _ => (hρ l).le)
  have hQ : 0 ≤ Q := mul_nonneg (mul_nonneg
    (mul_nonneg (abs_nonneg _) (le_max_right B 0)) hρsum) hC₀
  let C := Q*(∑ l, (ρ l)⁻¹)
  have hC : 0 ≤ C := mul_nonneg hQ (Finset.sum_nonneg (fun l _ => (inv_pos.mpr (hρ l)).le))
  refine ⟨C,hC,?_⟩
  intro K D G hKnorm hK hroot hcanon i j
  have hmatrix := first_weighted_inverse_identity z hz ρ σ (fun i => (hσ i).le) K D G hroot hcanon u
  have he := congrFun (congrFun hmatrix i) j
  simp only [Matrix.mul_diagonal,Matrix.of_apply,dtSymbol] at he
  rw [Matrix.mul_apply] at he
  simp only [Matrix.transpose_apply,Matrix.mul_diagonal,Matrix.smul_apply,Matrix.of_apply,smul_eq_mul] at he
  have hsum : ‖∑ l, (((2*Real.pi/z u : ℝ) : ℂ)*(K u i l : ℂ)*(ρ l : ℂ))*
      (causalFactor z ρ σ D G (z u : ℂ))⁻¹ j l‖ ≤ Q := by
    calc
      _ ≤ ∑ l, ‖(((2*Real.pi/z u : ℝ) : ℂ)*(K u i l : ℂ)*(ρ l : ℂ))*
          (causalFactor z ρ σ D G (z u : ℂ))⁻¹ j l‖ := norm_sum_le _ _
      _ ≤ ∑ l, |2*Real.pi/z u| *max B 0*ρ l*C₀ := by
        apply Finset.sum_le_sum
        intro l _
        rw [norm_mul,norm_mul,norm_mul]
        simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hρ l)]
        exact mul_le_mul (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (strength_entry_bound K B hKnorm u i l) (abs_nonneg _)) (hρ l).le)
          (hbound K D G hK hroot hcanon j l) (norm_nonneg _)
          (mul_nonneg (mul_nonneg (abs_nonneg _) (le_max_right B 0)) (hρ l).le)
      _ = Q := by
        dsimp only [Q]
        rw [Finset.mul_sum,Finset.sum_mul]
  have hn : |D u i j| *ρ j ≤ Q := by
    have h := (congrArg norm he).le.trans hsum
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hρ j)] using h
  have hentry : |D u i j| ≤ Q/ρ j := (le_div_iff₀ (hρ j)).mpr hn
  calc
    _ ≤ Q/ρ j := hentry
    _ = Q*(ρ j)⁻¹ := div_eq_mul_inv _ _
    _ ≤ C := mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun l _ => (inv_pos.mpr (hρ l)).le) (Finset.mem_univ j)) hQ

/-- Uniform first-amplitude bound in the ORIGINAL entrywise Pi norm, over
bounded strengths and arbitrary signs/repeated finite positive rates. -/
theorem first_amplitudes_uniformly_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ t i j, K t i j = K t j i) → IsRoot z ρ σ K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) → ‖D‖ ≤ C := by
  classical
  choose C hC hbound using first_rate_uniform_bound z hz ρ σ hρ hσ hv B
  refine ⟨∑ u, C u,Finset.sum_nonneg (fun u _ => hC u),?_⟩
  intro K D G hnorm hK hroot hcanon
  have hsum : 0 ≤ ∑ u, C u := Finset.sum_nonneg (fun u _ => hC u)
  apply (pi_norm_le_iff_of_nonneg hsum).mpr
  intro u
  apply (pi_norm_le_iff_of_nonneg hsum).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hsum).mpr
  intro j
  exact (hbound u K D G hnorm hK hroot hcanon i j).trans
    (Finset.single_le_sum (fun u _ => hC u) (Finset.mem_univ u))

/-- A finite canonical prefix cannot escape through its FIRST amplitudes.
This does not yet exclude escape of the pair: G still needs its own bound. -/
theorem no_finite_first_amplitude_escape (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (K : TailMatrix T N)
    (hK : ∀ u i j, K u i j = K u j i) (p : ℝ → TailMatrix T N × TailMatrix T N)
    (b : ℝ) (hb : 0 < b)
    (hroot : ∀ t ∈ Ico 0 b, IsRoot z ρ σ (t • K) (p t).1 (p t).2)
    (hcanon : ∀ t ∈ Ico 0 b, ∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ (p t).1 (p t).2 s)) :
    ¬∀ B c : ℝ, c < b → ∃ t ∈ Ico 0 b, c < t ∧ B < ‖(p t).1‖ := by
  obtain ⟨C,hC,hbound⟩ := first_amplitudes_uniformly_bounded z hz ρ σ hρ hσ hv (b*‖K‖)
  intro hescape
  obtain ⟨t,ht,_hc,hlarge⟩ := hescape C 0 hb
  apply (not_lt_of_ge (hbound (t • K) (p t).1 (p t).2 _ _ (hroot t ht) (hcanon t ht))) hlarge
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg _)
  · intro u i j
    simp only [Pi.smul_apply,smul_eq_mul,hK u i j]

end FMSA.Convergence.MixtureFirstAmplitudeBounds
/-- info: 'FMSA.Convergence.MixtureFirstAmplitudeBounds.first_weighted_inverse_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureFirstAmplitudeBounds.first_weighted_inverse_identity
/-- info: 'FMSA.Convergence.MixtureFirstAmplitudeBounds.first_rate_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureFirstAmplitudeBounds.first_rate_uniform_bound
/-- info: 'FMSA.Convergence.MixtureFirstAmplitudeBounds.first_amplitudes_uniformly_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureFirstAmplitudeBounds.first_amplitudes_uniformly_bounded
/-- info: 'FMSA.Convergence.MixtureFirstAmplitudeBounds.no_finite_first_amplitude_escape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.MixtureFirstAmplitudeBounds.no_finite_first_amplitude_escape
