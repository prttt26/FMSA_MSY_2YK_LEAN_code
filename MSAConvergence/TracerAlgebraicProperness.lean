import MSAConvergence.ActiveMixtureAmplitudeBounds

/-! The remaining tracer properness gap is analytic: a bound for all rows
of G in positive-density columns suffices to bound the ENTIRE original pair.
The finite algebraic recovery is proved here, without inverting a tracer density. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators
namespace FMSA.Convergence.TracerAlgebraicProperness
open FMSA.Paper FMSA.Paper.ActualRDFParameters FMSA.ExactMSA.MultiTailMixture MSAMixture
open FMSA.Convergence.CanonicalInverseCovariance FMSA.Convergence.ActiveMixtureAmplitudeBounds
variable {N : ℕ} {T : Type*} [Fintype T]

abbrev Amp := TailMatrix T N × TailMatrix T N

def columnMask (ρ : Fin N → ℝ) (D : TailMatrix T N) : TailMatrix T N :=
  fun u i j => if ρ j = 0 then 0 else D u i j

omit [Fintype T] in
private theorem mask_weighted (ρ : Fin N → ℝ) (G : TailMatrix T N) (u : T) (i j : Fin N) :
    ρ j*columnMask ρ G u i j = ρ j*G u i j := by
  by_cases hj : ρ j = 0 <;> simp [columnMask,hj]

private theorem column_dictionary (z : T → ℝ) (ρ σ : Fin N → ℝ) (p q : Amp (T := T) (N := N))
    (hG : ∀ u i j, ρ j * p.2 u i j = ρ j * q.2 u i j)
    (j : Fin N) (hD : ∀ u i, p.1 u i j = q.1 u i j) :
    (∀ u i, nonlinearRootRecenteredTransform z ρ σ p.1 p.2 u i j=
      nonlinearRootRecenteredTransform z ρ σ q.1 q.2 u i j) ∧
    (∀ u i, secondRHS z ρ σ p.1 p.2 u i j=secondRHS z ρ σ q.1 q.2 u i j) := by
  have hW (u : T) (i : Fin N) : W z ρ p.1 p.2 u i j=W z ρ q.1 q.2 u i j := by
    unfold W Wt
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    rw [hG u i l,hD u l]
  have hgam (u : T) (i l : Fin N) : gam (z u) ρ σ (p.2 u) i l=gam (z u) ρ σ (q.2 u) i l := by
    unfold gam
    rw [show 2*Real.pi*ρ l*p.2 u i l=2*Real.pi*(ρ l*p.2 u i l) by ring,
      hG u i l]
    ring
  have hC (u : T) (i : Fin N) : C z ρ σ p.1 p.2 u i j=C z ρ σ q.1 q.2 u i j := by
    unfold C Ct
    apply Finset.sum_congr rfl
    intro l _
    rw [hgam u i l,hD u l]
  have hM (u : T) : mixM (z u) ρ σ (p.2 u) (p.1 u) j=mixM (z u) ρ σ (q.2 u) (q.1 u) j := by
    change -(1/z u)*(∑ l, ρ l*(W z ρ p.1 p.2 u l j+(1+z u*σ l)*C z ρ σ p.1 p.2 u l j))=_
    simp_rw [hW,hC]
    rfl
  have hN (u : T) : mixN (z u) ρ σ (p.2 u) (p.1 u) j=mixN (z u) ρ σ (q.2 u) (q.1 u) j := by
    change (∑ l, ρ l*((1+z u*((σ j-σ l)/2))/(z u)^2*W z ρ p.1 p.2 u l j+
      (((1+z u*σ l+(z u*σ l)^2/2)/(z u)^2)+((σ j-σ l)/2)*(1+z u*σ l)/z u)*C z ρ σ p.1 p.2 u l j))=_
    simp_rw [hW,hC]
    rfl
  have hA : amplitudeA z ρ σ p.1 p.2 j=amplitudeA z ρ σ q.1 q.2 j := by
    simp only [amplitudeA,mixDA,hM,hN]
  have hQ (i : Fin N) : amplitudeQp z ρ σ p.1 p.2 i j=amplitudeQp z ρ σ q.1 q.2 i j := by
    simp only [amplitudeQp,mixDqp,hM,hN]
  constructor
  · intro u i
    simp only [nonlinearRootRecenteredTransform,dressedQhat,Qhat,Matrix.of_apply,hA,hQ,hW,hC]
  · intro u i
    simp only [secondRHS,hA,hQ,hC]

/-- Weighted G and one ORIGINAL D column determine that actual column's
root transform and second source at ALL amplitudes. No root or density sign
is assumed in this finite locality identity. -/
theorem dictionary_column_locality (z : T → ℝ) (ρ σ : Fin N → ℝ) (p q : Amp (T := T) (N := N))
    (hG : ∀ u i j, ρ j * p.2 u i j = ρ j * q.2 u i j)
    (j : Fin N) (hD : ∀ u i, p.1 u i j = q.1 u i j) :
    (∀ u i, nonlinearRootRecenteredTransform z ρ σ p.1 p.2 u i j=
      nonlinearRootRecenteredTransform z ρ σ q.1 q.2 u i j) ∧
    (∀ u i, secondRHS z ρ σ p.1 p.2 u i j=secondRHS z ρ σ q.1 q.2 u i j) :=
  column_dictionary z ρ σ p q hG j hD

private def recoverD (z : T → ℝ) (ρ σ : Fin N → ℝ) (a : TailMatrix T N × Amp (T := T) (N := N)) : TailMatrix T N :=
  fun u i j => 2*Real.pi*a.1 u i j/z u+∑ l, a.2.1 u i l*ρ l*
    nonlinearRootRecenteredTransform z ρ σ a.2.1 a.2.2 u j l

private def recoverG (z : T → ℝ) (ρ σ : Fin N → ℝ) (p : Amp (T := T) (N := N)) : TailMatrix T N :=
  fun u i j => secondRHS z ρ σ p.1 p.2 u i j/(2*Real.pi)+∑ l, p.2 u i l*ρ l*
    nonlinearRootRecenteredTransform z ρ σ p.1 p.2 u l j

private theorem first_isolate (z : T → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix T N)
    (p : Amp (T := T) (N := N)) (hr : IsRoot z ρ σ K p.1 p.2) (u : T) (i j : Fin N) :
    p.1 u i j=2*Real.pi*K u i j/z u+∑ l, p.1 u i l*ρ l*
      nonlinearRootRecenteredTransform z ρ σ p.1 p.2 u j l := by
  have h := hr.1 u i j
  have he : firstLHS z ρ σ p.1 p.2 u i j=p.1 u i j-∑ l, p.1 u i l*ρ l*
      nonlinearRootRecenteredTransform z ρ σ p.1 p.2 u j l := by
    unfold firstLHS
    simp only [nonlinearRootRecenteredTransform,Matrix.of_apply]
    simp_rw [mul_sub,Finset.sum_sub_distrib]
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he] at h
  linarith

private theorem second_isolate (z : T → ℝ) (ρ σ : Fin N → ℝ) (K : TailMatrix T N)
    (p : Amp (T := T) (N := N)) (hr : IsRoot z ρ σ K p.1 p.2) (u : T) (i j : Fin N) :
    p.2 u i j=secondRHS z ρ σ p.1 p.2 u i j/(2*Real.pi)+∑ l, p.2 u i l*ρ l*
      nonlinearRootRecenteredTransform z ρ σ p.1 p.2 u l j := by
  have h := hr.2 u i j
  have he : secondLHS z ρ σ p.1 p.2 u i j=2*Real.pi*(p.2 u i j-∑ l, p.2 u i l*ρ l*
      nonlinearRootRecenteredTransform z ρ σ p.1 p.2 u l j) := by
    unfold secondLHS
    congr 1
    simp only [nonlinearRootRecenteredTransform,Matrix.of_apply]
    simp_rw [mul_sub,Finset.sum_sub_distrib]
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he] at h
  have hp : 2*Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  field_simp [hp]
  nlinarith [h]

private theorem mask_norm (ρ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (A : TailMatrix T N) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ u i j, 0 < ρ j → |A u i j| ≤ C) : ‖columnMask ρ A‖ ≤ C := by
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro u
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro j
  by_cases hj : ρ j = 0
  · simpa only [columnMask,if_pos hj,norm_zero] using hC
  · simp only [columnMask,if_neg hj,Real.norm_eq_abs]
    exact h u i j (lt_of_le_of_ne (hρ j) (Ne.symm hj))

/-- Conditional finite algebraic properness: bounding G ONLY in positive-
density columns, for ALL rows, suffices to bound the ENTIRE ORIGINAL pair.
It does not assume unweighted tracer columns or full amplitude bounds. -/
theorem full_bound_of_active_second_columns (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (ρ σ : Fin N → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (hσ : ∀ i, 0 < σ i)
    (hv : FMSA.MatrixQ0.vacMix ρ σ ≠ 0) (B C : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ K D G : TailMatrix T N,
      ‖K‖ ≤ B → (∀ t i j, K t i j = K t j i) → IsRoot z ρ σ K D G →
      (∀ s : ℂ, 0 ≤ s.re → IsUnit (causalFactor z ρ σ D G s)) →
      (∀ u i j, 0 < ρ j → |G u i j| ≤ C) → ‖(D,G)‖ ≤ M := by
  classical
  obtain ⟨CD,hCD,hDb⟩ := first_active_columns_uniformly_bounded z hz ρ σ hρ hσ hv B
  let P := max CD (max C 0)
  have hP : 0 ≤ P := hCD.trans (le_max_left _ _)
  have hRD : Continuous (recoverD z ρ σ) := by
    unfold recoverD nonlinearRootRecenteredTransform
    fun_prop
  obtain ⟨MD,hMD⟩ := (isCompact_closedBall (0 : TailMatrix T N × Amp (T := T) (N := N))
    (max (max B 0) P)).exists_bound_of_continuousOn hRD.continuousOn
  let Q := max (max MD 0) (max C 0)
  have hQ : 0 ≤ Q := (le_max_right MD 0).trans (le_max_left _ _)
  have hRG : Continuous (recoverG z ρ σ) := by
    unfold recoverG nonlinearRootRecenteredTransform secondRHS
    fun_prop
  obtain ⟨MG,hMG⟩ := (isCompact_closedBall (0 : Amp (T := T) (N := N)) Q).exists_bound_of_continuousOn hRG.continuousOn
  refine ⟨max (max MD 0) (max MG 0),(le_max_right MD 0).trans (le_max_left _ _),?_⟩
  intro K D G hn hK hr hc hGa
  let p : Amp (T := T) (N := N) := (D,G)
  let q : Amp (T := T) (N := N) := (columnMask ρ D,columnMask ρ G)
  have hqm : ‖q‖ ≤ P := by
    rw [Prod.norm_def,max_le_iff]
    exact ⟨(mask_norm ρ hρ D CD hCD (hDb K D G hn hK hr hc)).trans (le_max_left _ _),
      (mask_norm ρ hρ G (max C 0) (le_max_right _ _) (fun u i j hj => (hGa u i j hj).trans (le_max_left _ _))).trans (le_max_right _ _)⟩
  have hGpq : ∀ u i j, ρ j * p.2 u i j = ρ j * q.2 u i j := fun u i j => (mask_weighted ρ G u i j).symm
  have hDeq : D=recoverD z ρ σ (K,q) := by
    funext u i j
    change p.1 u i j=_
    rw [first_isolate z ρ σ K p hr u i j]
    dsimp only [recoverD]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : ρ l = 0
    · simp only [hl,mul_zero,zero_mul]
    · have hd : ∀ u i, p.1 u i l=q.1 u i l := fun _ _ => by simp only [p,q,columnMask,if_neg hl]
      have he := (column_dictionary z ρ σ p q hGpq l hd).1 u j
      rw [hd u i,he]
  have hDn : ‖D‖ ≤ max MD 0 := by
    rw [hDeq]
    apply (hMD (K,q) _).trans (le_max_left _ _)
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff]
    exact ⟨hn.trans ((le_max_left B 0).trans (le_max_left _ _)),hqm.trans (le_max_right _ _)⟩
  let r : Amp (T := T) (N := N) := (D,columnMask ρ G)
  have hrn : ‖r‖ ≤ Q := by
    rw [Prod.norm_def,max_le_iff]
    exact ⟨hDn.trans (le_max_left _ _),
      (mask_norm ρ hρ G (max C 0) (le_max_right _ _) (fun u i j hj => (hGa u i j hj).trans (le_max_left _ _))).trans (le_max_right _ _)⟩
  have hGpr : ∀ u i j, ρ j * p.2 u i j = ρ j*r.2 u i j := fun u i j => (mask_weighted ρ G u i j).symm
  have hGeq : G=recoverG z ρ σ r := by
    funext u i j
    change p.2 u i j=_
    rw [second_isolate z ρ σ K p hr u i j]
    dsimp only [recoverG]
    have he := column_dictionary z ρ σ p r hGpr j (fun _ _ => rfl)
    rw [he.2 u i]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    have hw := hGpr u i l
    have hq := he.1 u l
    rw [show p.2 u i l*ρ l=ρ l*p.2 u i l by ring,hw,hq]
    ring
  have hGn : ‖G‖ ≤ max MG 0 := by
    rw [hGeq]
    exact (hMG r (by simpa only [Metric.mem_closedBall,dist_zero_right] using hrn)).trans (le_max_left _ _)
  rw [Prod.norm_def,max_le_iff]
  exact ⟨hDn.trans (le_max_left _ _),hGn.trans (le_max_right _ _)⟩

end FMSA.Convergence.TracerAlgebraicProperness
/-- info: 'FMSA.Convergence.TracerAlgebraicProperness.dictionary_column_locality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerAlgebraicProperness.dictionary_column_locality
/-- info: 'FMSA.Convergence.TracerAlgebraicProperness.full_bound_of_active_second_columns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.TracerAlgebraicProperness.full_bound_of_active_second_columns
