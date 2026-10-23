import LeanCode.YukawaOZMix.MSAMultiTailMixtureNonlinearLaplace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! BH G amplitudes are actual RDF Laplace moments when the actual kernel
budget is below one. No inverse-transform or supplied G-moment is used. -/
noncomputable section
open MeasureTheory Set Real Filter Topology
open FMSA.ExactMSA.Breakpoint MSAMixture FMSA.MatrixQ0
open scoped BigOperators
namespace FMSA.ExactMSA.MultiTailMixture
variable {N : ℕ} {ι : Type*} [Fintype ι]

theorem nonlinearRecenteredQ_actual_laplace (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (s : ℝ) (hs : 0 < s) (i j : Fin N) :
    realCausalLaplace (nonlinearRecenteredQ z ρ σ Dt G i j) s=
      exp (s*edgeLo σ i j)*dressedQhat z ρ σ Dt G s i j := by
  let Q := q z σ (amplitudeA z ρ σ Dt G) (amplitudeQp z ρ σ Dt G) (W z ρ Dt G) (C z ρ σ Dt G) i j
  have hset : (∫ r in Ioi (edgeLo σ i j), Q r*exp (-s*r))=∫ r, Q r*exp (-s*r) := by
    rw [← integral_Ici_eq_integral_Ioi]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    have hl : r < edgeLo σ i j := lt_of_not_ge hr
    simp [Q, q, hl]
  calc
    _ = exp (s*edgeLo σ i j)*∫ u in Ioi (0 : ℝ), Q (u+edgeLo σ i j)*exp (-s*(u+edgeLo σ i j)) := by
      unfold realCausalLaplace
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only
      rw [nonlinearRecenteredQ_eq_actual z ρ σ Dt G i j u hu.le]
      have he : exp (s*edgeLo σ i j)*exp (-s*(u+edgeLo σ i j))=exp (-s*u) := by
        rw [← exp_add]; congr 1; ring
      change exp (-s*u)*Q (u+edgeLo σ i j) = _
      linear_combination -Q (u+edgeLo σ i j)*he
    _ = exp (s*edgeLo σ i j)*dressedQhat z ρ σ Dt G s i j := by
      have hshift : (∫ u in Ioi (0 : ℝ), Q (u+edgeLo σ i j)*exp (-s*(u+edgeLo σ i j)))=
          ∫ r in Ioi (edgeLo σ i j), Q r*exp (-s*r) :=
        FMSA.ExactMSA.GSide.integral_Ioi_shift (fun r => Q r*exp (-s*r)) (edgeLo σ i j)
      rw [hshift, hset]
      dsimp only [Q]
      rw [laplaceQ_eq_Qhat z hz σ _ _ _ _ hσ i j s hs]
      rfl

theorem nonlinear_actual_secondBlock (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i) (u : ι) :
    Matrix.of (secondBlock z ρ σ Dt G u)=1-realMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) (z u) := by
  ext i j
  simp only [Matrix.of_apply, secondBlock, Matrix.sub_apply, Matrix.one_apply,
    realMatrixLaplace, realCausalLaplace, nonlinearCausalKernel, Matrix.of_apply]
  have he : (∫ t in Ioi (0 : ℝ), exp (-z u*t)*(ρ i*nonlinearRecenteredQ z ρ σ Dt G i j t)) =
      ρ i*realCausalLaplace (nonlinearRecenteredQ z ρ σ Dt G i j) (z u) := by
    unfold realCausalLaplace
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring
  rw [he, nonlinearRecenteredQ_actual_laplace z ρ σ Dt G hz hσ (z u) (hz u)]
  ring

theorem matrix_one_sub_isUnit_of_absSum (M : Matrix (Fin N) (Fin N) ℝ)
    (hM : FMSA.matrixAbsSum M < 1) : IsUnit (1-M) := by
  letI := Matrix.linftyOpNormedRing (n := Fin N) (α := ℝ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℝ)
  have hn : ‖M‖ ≤ FMSA.matrixAbsSum M := by
    have hh : (Finset.univ.sup fun i : Fin N => ∑ j, ‖M i j‖₊) ≤
        ∑ i, ∑ j, ‖M i j‖₊ := Finset.sup_le (fun i _ =>
          Finset.single_le_sum (f := fun i : Fin N => ∑ j, ‖M i j‖₊)
            (fun _ _ => by positivity) (Finset.mem_univ i))
    have hnn : ‖M‖₊ ≤ (∑ i, ∑ j, ‖M i j‖₊) := by
      rw [Matrix.linfty_opNNNorm_def]
      exact hh
    have hre : (‖M‖₊ : ℝ) ≤ ((∑ i, ∑ j, ‖M i j‖₊ : NNReal) : ℝ) :=
      NNReal.coe_le_coe.mpr hnn
    unfold FMSA.matrixAbsSum
    simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using hre
  exact isUnit_one_sub_of_norm_lt_one (hn.trans_lt hM)

theorem nonlinearCausalKernel_laplace_budget (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδz : ∀ u, δ < z u) (s : ℝ) (hs : 0 < s) :
    FMSA.matrixAbsSum (realMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s) ≤
      nonlinearWeightedKernelBudget z ρ σ Dt G δ := by
  have hiw := nonlinearCausalKernel_weighted_entry_integrable z ρ σ Dt G hσ δ hδz
  have hw (i j : Fin N) : |realMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s i j| ≤
      ∫ t in Ioi (0 : ℝ), exp (δ*t)*|nonlinearCausalKernel z ρ σ Dt G t i j| := by
    have hi := nonlinearCausalKernel_laplace_integrable z ρ σ Dt G hz hσ s hs i j
    apply (show |realMatrixLaplace (nonlinearCausalKernel z ρ σ Dt G) s i j| ≤
      ∫ t in Ioi (0 : ℝ), |exp (-s*t)*nonlinearCausalKernel z ρ σ Dt G t i j| from by
        simpa only [realMatrixLaplace, Matrix.of_apply, realCausalLaplace, Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun t => exp (-s*t)*nonlinearCausalKernel z ρ σ Dt G t i j)).trans
    apply integral_mono_ae hi.norm (hiw i j)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith : -s ≤ δ) ht.le)
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

/-- Every sampled BH second block is invertible under the actual integral
budget. An external determinant or inverse hypothesis is unnecessary. -/
theorem nonlinear_secondBlock_isUnit_of_weighted_budget (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (u : ι) :
    IsUnit (Matrix.of (secondBlock z ρ σ Dt G u)) := by
  rw [nonlinear_actual_secondBlock z ρ σ Dt G hz hσ]
  exact matrix_one_sub_isUnit_of_absSum _
    ((nonlinearCausalKernel_laplace_budget z ρ σ Dt G hz hσ δ hδ hδz (z u) (hz u)).trans_lt hb)

theorem nonlinearGSource_laplace_at_label (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (u : ι) (i j : Fin N) :
    realMatrixLaplace (nonlinearGSource z ρ σ Dt G) (z u) i j=
      secondRHS z ρ σ Dt G u i j/(2*π) := by
  rw [nonlinearGSource_actual_laplace z ρ σ Dt G hz (z u) (hz u)]
  unfold secondRHS
  have he : (∑ t, (z u)^2*z t/(z u+z t)*C z ρ σ Dt G t i j) =
      (z u)^2*∑ t, z t*C z ρ σ Dt G t i j/(z u+z t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [he]
  field_simp [(hz u).ne', pi_ne_zero]

/-- The actual constructed RDF has the supplied BH G moments. The root
condition and the actual integral budget suffice; no moment premise remains. -/
theorem nonlinearG_amplitude_eq_actual_causal_laplace (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (hroot : IsRoot z ρ σ K Dt G)
    (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (u : ι) :
    Matrix.of (G u)=realMatrixLaplace (nonlinearCausalG z ρ σ Dt G) (z u) := by
  let B := Matrix.of (secondBlock z ρ σ Dt G u)
  have hB : IsUnit B := nonlinear_secondBlock_isUnit_of_weighted_budget z ρ σ Dt G hz hσ δ hδ.le hδz hb u
  have hR : Matrix.of (G u)*B=realMatrixLaplace (nonlinearGSource z ρ σ Dt G) (z u) := by
    ext i j
    rw [nonlinearGSource_laplace_at_label z ρ σ Dt G hz u i j]
    have he := hroot.2 u i j
    have hsum : secondLHS z ρ σ Dt G u i j=2*π*(Matrix.of (G u)*B) i j := by
      simp only [secondLHS, B, Matrix.mul_apply, Matrix.of_apply, secondBlock, Finset.mul_sum]
    rw [hsum] at he
    exact (eq_div_iff (mul_ne_zero two_ne_zero pi_ne_zero)).mpr (by simpa only [mul_comm] using he)
  have hL := nonlinearCausalG_actual_laplace_renewal z ρ σ Dt G hz hσ hv δ hδ hδz hb (z u) (hz u)
  rw [← nonlinear_actual_secondBlock z ρ σ Dt G hz hσ] at hL
  exact (IsUnit.mul_left_injective hB) (hR.trans hL.symm)

theorem nonlinearG_radial_laplace_shift (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (i j : Fin N) (hR : 0 < edgeHi σ i j) (s : ℝ) :
    (∫ r in Ioi (0 : ℝ), exp (-s*r)*(r*nonlinearG z ρ σ Dt G i j r)) =
      exp (-s*edgeHi σ i j)*realCausalLaplace (fun t => nonlinearCausalG z ρ σ Dt G t i j) s := by
  have he : (∫ r in Ioi (0 : ℝ), exp (-s*r)*(r*nonlinearG z ρ σ Dt G i j r)) =
      ∫ r in Ioi (0 : ℝ), (Ici (edgeHi σ i j)).indicator
        (fun r => exp (-s*r)*nonlinearCausalG z ρ σ Dt G (r-edgeHi σ i j) i j) r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    change 0 < r at hr
    by_cases h : r < edgeHi σ i j
    · rw [nonlinearG_hardcore z ρ σ Dt G i j r h,
        indicator_of_notMem (show r ∉ Ici (edgeHi σ i j) from not_le.mpr h)]
      ring
    · rw [indicator_of_mem (show r ∈ Ici (edgeHi σ i j) from not_lt.mp h)]
      simp only [nonlinearG, if_neg h]
      field_simp [hr.ne']
  have hset : Ioi (0 : ℝ) ∩ Ici (edgeHi σ i j)=Ici (edgeHi σ i j) :=
    inter_eq_right.mpr (fun r hr => hR.trans_le hr)
  rw [he, setIntegral_indicator measurableSet_Ici, hset, integral_Ici_eq_integral_Ioi,
    ← FMSA.ExactMSA.GSide.integral_Ioi_shift
      (fun r => exp (-s*r)*nonlinearCausalG z ρ σ Dt G (r-edgeHi σ i j) i j) (edgeHi σ i j)]
  unfold realCausalLaplace
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [add_sub_cancel_right]
  rw [show -s*(t+edgeHi σ i j)= -s*edgeHi σ i j + -s*t by ring, exp_add]
  ring

/-- BH G is the normalized actual radial Laplace integral of the constructed
g, including unequal contact distances and the exact hard-core cutoff. -/
theorem nonlinearG_amplitude_eq_actual_radial_laplace (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 < σ i)
    (hv : vacMix ρ σ ≠ 0) (hroot : IsRoot z ρ σ K Dt G)
    (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (u : ι) (i j : Fin N) :
    (∫ r in Ioi (0 : ℝ), exp (-z u*r)*(r*nonlinearG z ρ σ Dt G i j r)) =
      exp (-z u*edgeHi σ i j)*G u i j := by
  rw [nonlinearG_radial_laplace_shift z ρ σ Dt G i j (by unfold edgeHi; linarith [hσ i, hσ j])]
  have he := congrFun (congrFun (nonlinearG_amplitude_eq_actual_causal_laplace z ρ σ K Dt G hz
    (fun i => (hσ i).le) hv hroot δ hδ hδz hb u) i) j
  simpa only [realMatrixLaplace, Matrix.of_apply] using congrArg (fun x => exp (-z u*edgeHi σ i j)*x) he.symm

theorem nonlinear_firstBlock_det_eq_secondBlock (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (u : ι) :
    (Matrix.of (firstBlock z ρ σ Dt G u)).det=(Matrix.of (secondBlock z ρ σ Dt G u)).det := by
  let Q : Matrix (Fin N) (Fin N) ℝ := Matrix.of (fun i j =>
    exp (z u*edgeLo σ i j)*dressedQhat z ρ σ Dt G (z u) i j)
  have hfirst : Matrix.of (firstBlock z ρ σ Dt G u)=1-Matrix.diagonal ρ*Q.transpose := by
    ext i j
    simp only [Matrix.of_apply, firstBlock, Matrix.sub_apply, Matrix.one_apply,
      Matrix.diagonal_mul, Matrix.transpose_apply, Q]
    ring
  have hsecond : Matrix.of (secondBlock z ρ σ Dt G u)=1-Matrix.diagonal ρ*Q := by
    ext i j
    simp only [Matrix.of_apply, secondBlock, Matrix.sub_apply, Matrix.one_apply,
      Matrix.diagonal_mul, Q]
    ring
  rw [hfirst, hsecond, Matrix.det_one_sub_mul_comm]
  have he : 1-Q.transpose*Matrix.diagonal ρ=(1-Matrix.diagonal ρ*Q).transpose := by
    simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.diagonal_transpose]
  rw [he, Matrix.det_transpose]

/-- Both BH multiplication blocks are units under the actual kernel budget.
This is not a theorem that the full nonlinear amplitude Jacobian is a unit. -/
theorem nonlinear_firstBlock_isUnit_of_weighted_budget (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1) (u : ι) :
    IsUnit (Matrix.of (firstBlock z ρ σ Dt G u)) := by
  rw [Matrix.isUnit_iff_isUnit_det, nonlinear_firstBlock_det_eq_secondBlock,
    ← Matrix.isUnit_iff_isUnit_det]
  exact nonlinear_secondBlock_isUnit_of_weighted_budget z ρ σ Dt G hz hσ δ hδ hδz hb u

theorem nonlinear_repeated_rate_G_consistency (z : ι → ℝ) (ρ σ : Fin N → ℝ)
    (K Dt G : TailMatrix ι N) (hz : ∀ u, 0 < z u) (hσ : ∀ i, 0 ≤ σ i)
    (hv : vacMix ρ σ ≠ 0) (hroot : IsRoot z ρ σ K Dt G)
    (δ : ℝ) (hδ : 0 < δ) (hδz : ∀ u, δ < z u)
    (hb : nonlinearWeightedKernelBudget z ρ σ Dt G δ < 1)
    (u v : ι) (huv : z u=z v) : G u=G v := by
  have hu := nonlinearG_amplitude_eq_actual_causal_laplace z ρ σ K Dt G hz hσ hv hroot δ hδ hδz hb u
  have hvv := nonlinearG_amplitude_eq_actual_causal_laplace z ρ σ K Dt G hz hσ hv hroot δ hδ hδz hb v
  rw [huv] at hu
  exact hu.trans hvv.symm

end FMSA.ExactMSA.MultiTailMixture
