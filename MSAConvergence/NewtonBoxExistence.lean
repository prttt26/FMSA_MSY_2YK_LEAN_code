import MSAConvergence.BHPolynomialJacobian

/-! A proved finite-dimensional Newton-box existence criterion. Derivative,
corner geometry and center residual bounds are explicit proof obligations.
No root, preconditioner inverse or fixed point is assumed. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators
namespace FMSA.Convergence.NewtonBoxExistence
open FMSA.Convergence.BHPolynomialJacobian
variable {I : Type*} [Fintype I] [DecidableEq I]
abbrev E (I : Type*) := I → ℝ

def matrixCLM (M : Matrix I I ℝ) : E I →L[ℝ] E I :=
  ContinuousLinearMap.pi (fun i => ∑ j, M i j • (ContinuousLinearMap.proj j : E I →L[ℝ] ℝ))

/-- The continuous linear map is exactly ordinary matrix-vector multiplication. -/
theorem matrixCLM_apply (M : Matrix I I ℝ) (v : E I) : matrixCLM M v = M.mulVec v := by
  ext i
  simp [matrixCLM,Matrix.mulVec,dotProduct]

/-- The actual Newton derivative has the exact preconditioned defect matrix. -/
theorem matrixCLM_defect (C J : Matrix I I ℝ) :
    matrixCLM (1-C*J) = ContinuousLinearMap.id ℝ (E I)-(matrixCLM C).comp (matrixCLM J) := by
  ext v i
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply,matrixCLM_apply,Matrix.sub_mulVec,Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec]

/-- An explicit row sum controls the Pi-space operator norm; no matrix-norm
convention is silently identified with a different operator norm. -/
theorem matrixCLM_norm_le (M : Matrix I I ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hrow : ∀ i, ∑ j, |M i j| ≤ q) : ‖matrixCLM M‖ ≤ q := by
  apply ContinuousLinearMap.opNorm_le_bound _ hq
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hq (norm_nonneg v))).mpr
  intro i
  rw [matrixCLM_apply]
  change ‖∑ j, M i j*v j‖ ≤ q*‖v‖
  calc
    ‖∑ j, M i j*v j‖ ≤ ∑ j, ‖M i j*v j‖ := norm_sum_le _ _
    _ ≤ ∑ j, |M i j| * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (abs_nonneg _)
    _ = (∑ j, |M i j|)*‖v‖ := (Finset.sum_mul ..).symm
    _ ≤ q*‖v‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg v)

/-- Row-defect bounds also prove injectivity of the preconditioner itself.
This is derived algebraically, rather than supplied as an inverse premise. -/
theorem preconditioner_injective (C J : Matrix I I ℝ)
    (hrow : ∀ i, ∑ j, |(1-C*J) i j| < 1) : Function.Injective (matrixCLM C) := by
  have hp : Function.Injective (C*J).mulVec := matrix_injective_of_row_defect (C*J) 1 (by
    intro i
    simpa only [one_mul] using hrow i)
  have hu : IsUnit (C*J) := Matrix.mulVec_injective_iff_isUnit.mp hp
  have hd : (C*J).det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have hc : C.det ≠ 0 := by
    intro h
    apply hd
    rw [Matrix.det_mul,h,zero_mul]
  have hci := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hc))
  intro v w h
  apply hci
  simpa only [matrixCLM_apply] using h

/-- A complete, nonempty box and proved derivative/residual bounds construct
one and only one root INSIDE the box. This is not global root uniqueness. -/
theorem exists_unique_root_in_box
    (lo hi c : E I) (C : Matrix I I ℝ) (f : E I → E I) (J : E I → Matrix I I ℝ)
    (q : NNReal) (R m epsilon : ℝ) (hq : q < 1) (hR : 0 ≤ R) (hm : 0 ≤ m)
    (hcenter : ∀ i, lo i+m ≤ c i ∧ c i+m ≤ hi i)
    (hradius : ∀ i, c i-lo i ≤ R ∧ hi i-c i ≤ R)
    (hf : ∀ x ∈ Icc lo hi, HasFDerivAt f (matrixCLM (J x)) x)
    (hrow : ∀ x ∈ Icc lo hi, ∀ i, ∑ j, |(1-C*J x) i j| ≤ (q : ℝ))
    (hseed : ‖matrixCLM C (f c)‖ ≤ epsilon)
    (hsmall : (q : ℝ)*R+epsilon ≤ m) :
    ∃! x : E I, x ∈ Icc lo hi ∧ f x = 0 := by
  let S : Set (E I) := Icc lo hi
  let G : E I → E I := fun x => x-matrixCLM C (f x)
  have hc : c ∈ S := by
    constructor
    · intro i; linarith [(hcenter i).1]
    · intro i; linarith [(hcenter i).2]
  have hq' : (q : ℝ) < 1 := by exact_mod_cast hq
  have hdiff (x : E I) (hx : x ∈ S) : HasFDerivAt G (matrixCLM (1-C*J x)) x := by
    rw [matrixCLM_defect]
    exact (hasFDerivAt_id x).sub ((matrixCLM C).hasFDerivAt.comp x (hf x hx))
  have hnorm (x : E I) (hx : x ∈ S) : ‖matrixCLM ((1 : Matrix I I ℝ)-C*J x)‖ ≤ (q : ℝ) :=
    matrixCLM_norm_le _ q q.property (hrow x hx)
  have hlip : LipschitzOnWith q G S := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x hx => (hdiff x hx).hasFDerivWithinAt) hnorm (convex_Icc lo hi) hy hx
  have hrad (x : E I) (hx : x ∈ S) : ‖x-c‖ ≤ R := by
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro i
    simp only [Pi.sub_apply,Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · linarith [hx.1 i,(hradius i).1]
    · linarith [hx.2 i,(hradius i).2]
  have hGc : ‖G c-c‖ ≤ epsilon := by
    have he : G c-c = -(matrixCLM C (f c)) := by dsimp [G]; abel
    rw [he,norm_neg]
    exact hseed
  have hmap : MapsTo G S S := by
    intro x hx
    have hn : ‖G x-c‖ ≤ m := by
      calc
        ‖G x-c‖ = ‖(G x-G c)+(G c-c)‖ := by congr 1; abel
        _ ≤ ‖G x-G c‖+‖G c-c‖ := norm_add_le _ _
        _ ≤ (q : ℝ)*‖x-c‖+epsilon := add_le_add
          ((lipschitzOnWith_iff_norm_sub_le.mp hlip) hx hc) hGc
        _ ≤ (q : ℝ)*R+epsilon := add_le_add
          (mul_le_mul_of_nonneg_left (hrad x hx) q.property) (le_refl epsilon)
        _ ≤ m := hsmall
    have hab (i : I) : |G x i-c i| ≤ m := by
      simpa only [Pi.sub_apply,Real.norm_eq_abs] using (norm_le_pi_norm (G x-c) i).trans hn
    constructor
    · intro i; linarith [(abs_le.mp (hab i)).1,(hcenter i).1]
    · intro i; linarith [(abs_le.mp (hab i)).2,(hcenter i).2]
  have hctr : ContractingWith q (hmap.restrict G S S) := by
    refine ⟨hq,?_⟩
    intro x y
    exact hlip x.property y.property
  obtain ⟨y,hy,hgy,_ht,_he⟩ := ContractingWith.exists_fixedPoint'
    (isClosed_Icc.isComplete : IsComplete S) hmap hctr hc (edist_ne_top _ _)
  have hCi : Function.Injective (matrixCLM C) := preconditioner_injective C (J c)
    (fun i => (hrow c hc i).trans_lt hq')
  have hfy : f y = 0 := by
    apply hCi
    have hCy : matrixCLM C (f y) = 0 := sub_eq_self.mp hgy
    simpa only [map_zero] using hCy
  refine ⟨y,⟨hy,hfy⟩,?_⟩
  intro x hx
  have hgx : G x = x := by simp [G,hx.2]
  have hn := (lipschitzOnWith_iff_norm_sub_le.mp hlip) hx.1 hy
  rw [hgx,hgy] at hn
  have hz : ‖x-y‖ = 0 := by
    by_contra h
    have hp : 0 < ‖x-y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
    have ht := mul_lt_mul_of_pos_right hq' hp
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end FMSA.Convergence.NewtonBoxExistence

/-- info: 'FMSA.Convergence.NewtonBoxExistence.matrixCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.NewtonBoxExistence.matrixCLM_apply

/-- info: 'FMSA.Convergence.NewtonBoxExistence.matrixCLM_defect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.NewtonBoxExistence.matrixCLM_defect

/-- info: 'FMSA.Convergence.NewtonBoxExistence.matrixCLM_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.NewtonBoxExistence.matrixCLM_norm_le

/-- info: 'FMSA.Convergence.NewtonBoxExistence.preconditioner_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.NewtonBoxExistence.preconditioner_injective

/-- info: 'FMSA.Convergence.NewtonBoxExistence.exists_unique_root_in_box' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.NewtonBoxExistence.exists_unique_root_in_box

