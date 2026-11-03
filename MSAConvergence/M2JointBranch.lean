import MSAConvergence.M2WeightTransversality
import MSAConvergence.M2Curvature

/-! Joint analytic original M2 root germs in coupling and weight.
No joint branch, root or inverse is supplied to the existence theorem. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators ContDiff
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace FMSA.Convergence.M2JointBranch
open FMSA.ExactMSA.MultiTailMixture FMSA.Paper.ActualAnalyticBranch
open FMSA.Convergence.M2JacobianFormula FMSA.Convergence.M2ResidualFormula
open FMSA.Convergence.M2ResidualDerivative FMSA.Convergence.M2KernelCertificate
open FMSA.Convergence.M2TangencySystem FMSA.Convergence.M2ZeroMode
open FMSA.Convergence.BHPolynomialJacobian FMSA.Convergence.NewtonBoxExistence
open FMSA.Convergence.M2WeightBranch
abbrev E := Fin 4 → ℝ
abbrev Params := ℝ × ℝ

def jointSystem (u : Params × E) : E :=
  residualFormula (strength 0) 0 u.2-u.1.1 • forcing u.1.2

/-- Exact original residual at every coupling, weight and amplitude. -/
theorem jointSystem_eq (b w : ℝ) (x : E) :
    jointSystem ((b,w),x) = residualFormula (strength w) b x := by
  rw [residual_affine,residual_at_zero_independent]
  rfl

private theorem base_analyticAt (x : E) :
    AnalyticAt ℝ (residualFormula (strength 0) 0) x := by
  let R := FMSA.ExactMSA.MultiTailMixture.residual z rho sigma (strength 0)
  have hpair : AnalyticAt ℝ (fun y : E => ((0 : ℝ),coordinates.symm y)) x :=
    analyticAt_const.prod (coordinates.symm.toContinuousLinearMap.analyticAt x)
  have hR : AnalyticAt ℝ R ((fun y : E => ((0 : ℝ),coordinates.symm y)) x) :=
    residual_analyticAt z rho sigma (strength 0) (0,point x)
  have hr : AnalyticAt ℝ (fun y : E => R (0,coordinates.symm y)) x := hR.comp (f := fun y : E => ((0 : ℝ),coordinates.symm y)) hpair
  have h : AnalyticAt ℝ (fun y : E => coordinates (R (0,coordinates.symm y))) x :=
    (coordinates.toContinuousLinearMap.analyticAt (R (0,point x))).comp (f := fun y : E => R (0,coordinates.symm y)) hr
  have he : (fun y : E => coordinates (R (0,coordinates.symm y))) =
      residualFormula (strength 0) 0 := by
    funext y i
    exact actual_formula y (strength 0) 0 i
  exact he ▸ h

private theorem forcing_analyticAt (w : ℝ) : AnalyticAt ℝ forcing w := by
  apply analyticAt_pi_iff.mpr
  intro i
  fin_cases i <;> norm_num [forcing] <;> fun_prop

/-- Joint analyticity is derived from the original residual, not assumed. -/
theorem jointSystem_analyticAt (b w : ℝ) (x : E) :
    AnalyticAt ℝ jointSystem ((b,w),x) := by
  have hfw : AnalyticAt ℝ (fun u : Params × E => forcing u.1.2) ((b,w),x) :=
    AnalyticAt.comp (g := forcing) (f := fun u : Params × E => u.1.2)
      (x := ((b,w),x)) (forcing_analyticAt w)
      (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.fst ℝ Params E)).analyticAt _)
  have hfx : AnalyticAt ℝ (fun u : Params × E => residualFormula (strength 0) 0 u.2) ((b,w),x) :=
    AnalyticAt.comp (g := residualFormula (strength 0) 0)
      (f := fun u : Params × E => u.2) (x := ((b,w),x)) (base_analyticAt x) analyticAt_snd
  have hb : AnalyticAt ℝ (fun u : Params × E => u.1.1) ((b,w),x) :=
    (((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.fst ℝ Params E)).analyticAt _)
  exact hfx.sub (hb.smul hfw)

/-- The amplitude partial is the original four-dimensional Jacobian. -/
theorem amplitude_partial_eq (b w : ℝ) (x : E) :
    (fderiv ℝ jointSystem ((b,w),x)).comp (ContinuousLinearMap.inr ℝ Params E) =
      matrixCLM (formula x) := by
  have hi : HasFDerivAt (fun a : E => ((b,w),a)) (ContinuousLinearMap.inr ℝ Params E) x := by
    convert! (hasFDerivAt_const (b,w) x).prodMk (hasFDerivAt_id x) using 1
  have h := (jointSystem_analyticAt b w x).differentiableAt.hasFDerivAt.comp x hi
  have he : (fun a : E => jointSystem ((b,w),a)) = residualFormula (strength w) b :=
    funext (jointSystem_eq b w)
  change HasFDerivAt (fun a : E => jointSystem ((b,w),a)) _ x at h
  rw [he] at h
  exact h.unique (hasFDerivAt_formula (strength w) b x)

private theorem boxed_invertible (x : E)
    (hx : ∀ i, lower i ≤ x i ∧ x i ≤ upper i) :
    (matrixCLM (formula x)).IsInvertible := by
  have hinj := matrix_injective_of_row_defect (formula x) preconditioner
    (fun i => (row_defect_bound x hx i).trans (by norm_num))
  have hlinj : Function.Injective (matrixCLM (formula x)) := by
    intro u v huv
    apply hinj
    simpa only [matrixCLM_apply] using huv
  have hbij : Function.Bijective (matrixCLM (formula x)).toLinearMap :=
    ⟨hlinj, (LinearMap.injective_iff_surjective).mp hlinj⟩
  let e := (LinearEquiv.ofBijective (matrixCLM (formula x)).toLinearMap hbij).toContinuousLinearEquiv
  exact ⟨e,rfl⟩

/-- A boxed original root constructs a JOINT analytic root germ in both
coupling and weight, with original signed Dt/G amplitudes retained. -/
theorem root_in_box_constructs_joint_branch (b w : ℝ) (x : E)
    (hx : ∀ i, lower i ≤ x i ∧ x i ≤ upper i)
    (hr : residualFormula (strength w) b x = 0) :
    ∃ p : Params → E, p (b,w) = x ∧ AnalyticAt ℝ p (b,w) ∧
      (∀ᶠ u in 𝓝 (b,w), IsRoot z rho sigma (u.1 • strength u.2)
        (point (p u)).1 (point (p u)).2) := by
  have hc : ContDiffAt ℝ ω jointSystem ((b,w),x) := (jointSystem_analyticAt b w x).contDiffAt
  have hi : ((fderiv ℝ jointSystem ((b,w),x)).comp
      (ContinuousLinearMap.inr ℝ Params E)).IsInvertible := by
    rw [amplitude_partial_eq]
    exact boxed_invertible x hx
  let p := hc.implicitFunction (by simp) hi
  have hp0 : p (b,w) = x := hc.implicitFunction_apply_self (by simp) hi
  have hpa : AnalyticAt ℝ p (b,w) := (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt
  refine ⟨p,hp0,hpa,?_⟩
  filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with u hu
  apply (actual_root_iff_formula_zero (p u) (strength u.2) u.1).mpr
  rw [←jointSystem_eq,hu,jointSystem_eq,hr]

/-- The honest real observable is analytic along a joint analytic germ. -/
theorem observable_analyticAt {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (p : D → E) (a : D) (hp : AnalyticAt ℝ p a) :
    AnalyticAt ℝ (fun t => zeroMode (p t)) a := by
  have hpi (i : Fin 4) : AnalyticAt ℝ (fun t => p t i) a :=
    ((ContinuousLinearMap.proj i : E →L[ℝ] ℝ).analyticAt (p a)).comp (f := p) hp
  have hc (c : ℝ) : AnalyticAt ℝ (fun _ : D => c) a := analyticAt_const
  change AnalyticAt ℝ (fun t => 40/27+p t 0*(alpha 0+beta 0*p t 2)+
    p t 1*(alpha 1+beta 1*p t 3)) a
  exact ((hc (40/27)).add ((hpi 0).mul ((hc (alpha 0)).add ((hc (beta 0)).mul (hpi 2))))).add
    ((hpi 1).mul ((hc (alpha 1)).add ((hc (beta 1)).mul (hpi 3))))

end FMSA.Convergence.M2JointBranch

/-- info: 'FMSA.Convergence.M2JointBranch.jointSystem_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2JointBranch.jointSystem_eq

/-- info: 'FMSA.Convergence.M2JointBranch.jointSystem_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2JointBranch.jointSystem_analyticAt

/-- info: 'FMSA.Convergence.M2JointBranch.amplitude_partial_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2JointBranch.amplitude_partial_eq

/-- info: 'FMSA.Convergence.M2JointBranch.root_in_box_constructs_joint_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2JointBranch.root_in_box_constructs_joint_branch

/-- info: 'FMSA.Convergence.M2JointBranch.observable_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2JointBranch.observable_analyticAt
