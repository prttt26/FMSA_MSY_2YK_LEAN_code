import MSAConvergence.ActiveMixtureAmplitudeBounds
import MSAConvergence.FiniteKernelLaplace

/-! The active bath's ACTUAL finite kernel coefficients stay bounded even
when zero-density tracer amplitudes have not yet been bounded. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators
namespace FMSA.Convergence.ActiveBathKernelBounds
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Convergence.CanonicalInverseCovariance FMSA.Convergence.ActiveMixtureAmplitudeBounds
variable {N : ℕ} {T : Type*} [Fintype T]

def activeProjection (ρ : Fin N → ℝ) (p : TailMatrix T N × TailMatrix T N) :
    TailMatrix T N × TailMatrix T N :=
  ((fun u i j => if 0 < ρ i ∧ 0 < ρ j then p.1 u i j else 0),
   (fun u i j => if 0 < ρ i ∧ 0 < ρ j then p.2 u i j else 0))

omit [Fintype T] in
private theorem project_D (ρ : Fin N → ℝ) (p : TailMatrix T N × TailMatrix T N)
    (u : T) (i j : Fin N) (hi : 0 < ρ i) (hj : 0 < ρ j) :
    (activeProjection ρ p).1 u i j = p.1 u i j := by simp only [activeProjection,if_pos (show 0 < ρ i ∧ 0 < ρ j from ⟨hi,hj⟩)]

omit [Fintype T] in
private theorem project_G (ρ : Fin N → ℝ) (p : TailMatrix T N × TailMatrix T N)
    (u : T) (i j : Fin N) (hi : 0 < ρ i) (hj : 0 < ρ j) :
    (activeProjection ρ p).2 u i j = p.2 u i j := by simp only [activeProjection,if_pos (show 0 < ρ i ∧ 0 < ρ j from ⟨hi,hj⟩)]

omit [Fintype T] in
private theorem project_W (z : T → ℝ) (ρ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (p : TailMatrix T N × TailMatrix T N) (u : T) (i j : Fin N) (hi : 0 < ρ i) (hj : 0 < ρ j) :
    W z ρ (activeProjection ρ p).1 (activeProjection ρ p).2 u i j = W z ρ p.1 p.2 u i j := by
  unfold W Wt
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : ρ l = 0
  · simp only [hl,zero_mul]
  · have hp : 0 < ρ l := lt_of_le_of_ne (hρ l) (Ne.symm hl)
    rw [project_G ρ p u i l hi hp,project_D ρ p u l j hp hj]

omit [Fintype T] in
private theorem project_C (z : T → ℝ) (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (p : TailMatrix T N × TailMatrix T N) (u : T) (i j : Fin N) (hi : 0 < ρ i) (hj : 0 < ρ j) :
    C z ρ σ (activeProjection ρ p).1 (activeProjection ρ p).2 u i j = C z ρ σ p.1 p.2 u i j := by
  have h := cancellation_star (z u) ρ σ (p.2 u) (p.1 u) i j
  have hp := cancellation_star (z u) ρ σ ((activeProjection ρ p).2 u) ((activeProjection ρ p).1 u) i j
  change (activeProjection ρ p).1 u i j-C z ρ σ (activeProjection ρ p).1 (activeProjection ρ p).2 u i j =
    exp (-z u*σ i)*W z ρ (activeProjection ρ p).1 (activeProjection ρ p).2 u i j at hp
  rw [project_D ρ p u i j hi hj,project_W z ρ hρ p u i j hi hj] at hp
  change p.1 u i j-C z ρ σ p.1 p.2 u i j = exp (-z u*σ i)*W z ρ p.1 p.2 u i j at h
  linarith

omit [Fintype T] in
private theorem project_M_entry (z : T → ℝ) (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (p : TailMatrix T N × TailMatrix T N) (u : T) (j : Fin N) (hj : 0 < ρ j) :
    mixM (z u) ρ σ ((activeProjection ρ p).2 u) ((activeProjection ρ p).1 u) j = 
      mixM (z u) ρ σ (p.2 u) (p.1 u) j := by
  unfold mixM
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : ρ l = 0
  · simp only [hl,zero_mul]
  · have hp : 0 < ρ l := lt_of_le_of_ne (hρ l) (Ne.symm hl)
    change ρ l*(W z ρ (activeProjection ρ p).1 (activeProjection ρ p).2 u l j+
      (1+z u*σ l)*C z ρ σ (activeProjection ρ p).1 (activeProjection ρ p).2 u l j)=_
    rw [project_W z ρ hρ p u l j hp hj,project_C z ρ σ hρ p u l j hp hj]
    rfl

omit [Fintype T] in
private theorem project_N_entry (z : T → ℝ) (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (p : TailMatrix T N × TailMatrix T N) (u : T) (j : Fin N) (hj : 0 < ρ j) :
    mixN (z u) ρ σ ((activeProjection ρ p).2 u) ((activeProjection ρ p).1 u) j = 
      mixN (z u) ρ σ (p.2 u) (p.1 u) j := by
  unfold mixN
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : ρ l = 0
  · simp only [hl,zero_mul]
  · have hp : 0 < ρ l := lt_of_le_of_ne (hρ l) (Ne.symm hl)
    change ρ l*((1+z u*((σ j-σ l)/2))/(z u)^2*W z ρ (activeProjection ρ p).1 (activeProjection ρ p).2 u l j+
      (((1+z u*σ l+(z u*σ l)^2/2)/(z u)^2)+((σ j-σ l)/2)*(1+z u*σ l)/z u)*
        C z ρ σ (activeProjection ρ p).1 (activeProjection ρ p).2 u l j)=_
    rw [project_W z ρ hρ p u l j hp hj,project_C z ρ σ hρ p u l j hp hj]
    rfl

private theorem project_A (z : T → ℝ) (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (p : TailMatrix T N × TailMatrix T N) (j : Fin N) (hj : 0 < ρ j) :
    amplitudeA z ρ σ (activeProjection ρ p).1 (activeProjection ρ p).2 j = amplitudeA z ρ σ p.1 p.2 j := by
  simp only [amplitudeA,mixDA,project_M_entry z ρ σ hρ p _ j hj,project_N_entry z ρ σ hρ p _ j hj]

private theorem project_Qp (z : T → ℝ) (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (hj : 0 < ρ j) :
    amplitudeQp z ρ σ (activeProjection ρ p).1 (activeProjection ρ p).2 i j = amplitudeQp z ρ σ p.1 p.2 i j := by
  simp only [amplitudeQp,mixDqp,project_M_entry z ρ σ hρ p _ j hj,project_N_entry z ρ σ hρ p _ j hj]

/-- Exact active-bath coefficient identity at ALL amplitudes. No root or
canonicity is used: retained tracer amplitudes cannot alter this bath block. -/
theorem active_coefficient_projection (z : T → ℝ) (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i)
    (p : TailMatrix T N × TailMatrix T N) (i j : Fin N) (hi : 0 < ρ i) (hj : 0 < ρ j) :
    bhCoefficient z ρ σ (activeProjection ρ p) i j = bhCoefficient z ρ σ p i j := by
  funext b
  rcases b with b|(u|u)
  · fin_cases b <;> simp only [bhCoefficient,coefficient,Fin.isValue,
      project_A z ρ σ hρ p j hj,project_Qp z ρ σ hρ p i j hj]
  · exact project_W z ρ hρ p u i j hi hj
  · exact project_C z ρ σ hρ p u i j hi hj

/-- The ACTUAL active-bath finite coefficient block is uniformly bounded
over bounded strengths, even when unweighted tracer amplitudes remain open. -/
theorem active_coefficients_uniformly_bounded (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ t i j, K t i j = K t j i) → IsRoot z ρ σ K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) →
      ∀ i j, 0 < ρ i → 0 < ρ j → ‖bhCoefficient z ρ σ (D,G) i j‖ ≤ C := by
  classical
  obtain ⟨CD,hCD,hD⟩ := first_active_columns_uniformly_bounded z hz ρ σ hρ hσ hv B
  obtain ⟨CG,hCG,hG⟩ := second_active_block_uniformly_bounded z hz ρ σ hρ hσ hv
  let P := max CD CG
  have hP : 0 ≤ P := hCD.trans (le_max_left _ _)
  let F := fun p : TailMatrix T N × TailMatrix T N => fun i j => bhCoefficient z ρ σ p i j
  have hF : Continuous F := continuous_pi (fun i => continuous_pi (fun j =>
    continuous_pi (fun b => (bhCoefficient_contDiff z ρ σ i j b).continuous)))
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : TailMatrix T N × TailMatrix T N) P).exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro K D G hn hK hr hc i j hi hj
  have hp : ‖activeProjection ρ (D,G)‖ ≤ P := by
    rw [Prod.norm_def,max_le_iff]
    constructor
    all_goals
      apply (pi_norm_le_iff_of_nonneg hP).mpr
      intro u
      apply (pi_norm_le_iff_of_nonneg hP).mpr
      intro i
      apply (pi_norm_le_iff_of_nonneg hP).mpr
      intro j
      dsimp only [activeProjection]
      split_ifs with hactive
    · exact (hD K D G hn hK hr hc u i j hactive.2).trans (le_max_left _ _)
    · simpa only [norm_zero] using hP
    · exact (hG K D G hK hr hc u i j hactive.1 hactive.2).trans (le_max_right _ _)
    · simpa only [norm_zero] using hP
  rw [← active_coefficient_projection z ρ σ hρ (D,G) i j hi hj]
  exact ((norm_le_pi_norm (F (activeProjection ρ (D,G)) i) j).trans
    (norm_le_pi_norm (F (activeProjection ρ (D,G))) i)).trans
      ((hC _ (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp)).trans (le_max_left _ _))

end FMSA.Convergence.ActiveBathKernelBounds
/-- info: 'FMSA.Convergence.ActiveBathKernelBounds.active_coefficient_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActiveBathKernelBounds.active_coefficient_projection
/-- info: 'FMSA.Convergence.ActiveBathKernelBounds.active_coefficients_uniformly_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ActiveBathKernelBounds.active_coefficients_uniformly_bounded
