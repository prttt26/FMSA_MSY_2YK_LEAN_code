import MSAConvergence.M2TangencySystem

/-! Actual analytic fixed-coupling weight germs and their true derivative
equation, using the original BH residual and the proved boxed Jacobian. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.M2WeightBranch
open FMSA.ExactMSA.MultiTailMixture FMSA.Paper.ActualAnalyticBranch
open FMSA.Convergence.M2JacobianFormula FMSA.Convergence.M2ResidualFormula
open FMSA.Convergence.M2ResidualDerivative FMSA.Convergence.M2KernelCertificate
open FMSA.Convergence.M2TangencySystem FMSA.Convergence.M2ZeroMode
open FMSA.Convergence.BHPolynomialJacobian FMSA.Convergence.NewtonBoxExistence
abbrev E := Fin 4 → ℝ
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem residual_at_zero_independent (w : ℝ) (x : E) :
    residualFormula (strength w) 0 x = residualFormula (strength 0) 0 x := by
  funext i
  fin_cases i <;> simp [residualFormula]

def weightDerivative : E := ![0, Real.pi/6, 0, 0]

theorem forcing_hasDerivAt (w : ℝ) : HasDerivAt forcing weightDerivative w := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [forcing,weightDerivative] using hasDerivAt_const w (10*Real.pi/9)
  · simpa [forcing,weightDerivative] using ((hasDerivAt_id w).const_mul Real.pi).div_const 6
  · simpa [forcing,weightDerivative] using hasDerivAt_const w (0 : ℝ)
  · simpa [forcing,weightDerivative] using hasDerivAt_const w (0 : ℝ)

def weightSystem (b : ℝ) (u : ℝ × E) : E :=
  residualFormula (strength 0) 0 u.2-b • forcing u.1

theorem weightSystem_eq (b w : ℝ) (x : E) :
    weightSystem b (w,x) = residualFormula (strength w) b x := by
  rw [residual_affine, residual_at_zero_independent]
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

private theorem weightSystem_analyticAt (b w : ℝ) (x : E) :
    AnalyticAt ℝ (weightSystem b) (w,x) := by
  have hf : AnalyticAt ℝ forcing w := by
    apply analyticAt_pi_iff.mpr
    intro i
    fin_cases i <;> norm_num [forcing] <;> fun_prop
  have hfw : AnalyticAt ℝ (fun u : ℝ × E => forcing u.1) (w,x) :=
    AnalyticAt.comp (g := forcing) (f := fun u : ℝ × E => u.1) (x := (w,x)) hf analyticAt_fst
  have hfx : AnalyticAt ℝ (fun u : ℝ × E => residualFormula (strength 0) 0 u.2) (w,x) :=
    AnalyticAt.comp (g := residualFormula (strength 0) 0)
      (f := fun u : ℝ × E => u.2) (x := (w,x)) (base_analyticAt x) analyticAt_snd
  exact hfx.sub (hfw.const_smul (c := b))

private theorem partial_eq (b w : ℝ) (x : E) :
    (fderiv ℝ (weightSystem b) (w,x)).comp (ContinuousLinearMap.inr ℝ ℝ E) =
      matrixCLM (formula x) := by
  have hi : HasFDerivAt (fun a : E => (w,a)) (ContinuousLinearMap.inr ℝ ℝ E) x := by
    convert! (hasFDerivAt_const w x).prodMk (hasFDerivAt_id x) using 1
  have h := (weightSystem_analyticAt b w x).differentiableAt.hasFDerivAt.comp x hi
  have he : (fun a : E => weightSystem b (w,a)) = residualFormula (strength w) b :=
    funext (weightSystem_eq b w)
  change HasFDerivAt (fun a : E => weightSystem b (w,a)) _ x at h
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

/-- A boxed genuine root constructs an actual analytic weight germ at fixed
coupling. No branch or inverse is supplied as a premise. -/
theorem root_in_box_constructs_weight_branch (b w : ℝ) (x : E)
    (hx : ∀ i, lower i ≤ x i ∧ x i ≤ upper i)
    (hr : residualFormula (strength w) b x = 0) :
    ∃ p : ℝ → E, p w = x ∧ AnalyticAt ℝ p w ∧
      (∀ᶠ s in 𝓝 w, IsRoot z rho sigma (b • strength s)
        (point (p s)).1 (point (p s)).2) := by
  have hc : ContDiffAt ℝ ω (weightSystem b) (w,x) := (weightSystem_analyticAt b w x).contDiffAt
  have hi : ((fderiv ℝ (weightSystem b) (w,x)).comp
      (ContinuousLinearMap.inr ℝ ℝ E)).IsInvertible := by
    rw [partial_eq]
    exact boxed_invertible x hx
  let p := hc.implicitFunction (by simp) hi
  have hp0 : p w = x := hc.implicitFunction_apply_self (by simp) hi
  have hpa : AnalyticAt ℝ p w := (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt
  refine ⟨p,hp0,hpa,?_⟩
  filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with s hs
  apply (actual_root_iff_formula_zero (p s) (strength s) b).mpr
  rw [←weightSystem_eq, hs, weightSystem_eq, hr]

/-- Differentiating genuine nearby roots gives the exact weight equation. -/
theorem root_curve_weight_velocity (b w : ℝ) (p : ℝ → E) (v : E)
    (hp : HasDerivAt p v w)
    (hr : ∀ᶠ s in 𝓝 w, residualFormula (strength s) b (p s) = 0) :
    (formula (p w)).mulVec v = b • weightDerivative := by
  have he : (fun s => residualFormula (strength 0) 0 (p s)) =ᶠ[𝓝 w]
      (fun s => b • forcing s) := by
    filter_upwards [hr] with s hs
    rw [residual_affine, residual_at_zero_independent] at hs
    exact sub_eq_zero.mp hs
  have hd := (hasFDerivAt_formula (strength 0) 0 (p w)).comp_hasDerivAt w hp
  have hf := (forcing_hasDerivAt w).const_smul b
  have hv := (hd.congr_of_eventuallyEq he.symm).unique hf
  simpa only [matrixCLM_apply] using hv
end FMSA.Convergence.M2WeightBranch

/-- info: 'FMSA.Convergence.M2WeightBranch.residual_at_zero_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2WeightBranch.residual_at_zero_independent

/-- info: 'FMSA.Convergence.M2WeightBranch.forcing_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2WeightBranch.forcing_hasDerivAt

/-- info: 'FMSA.Convergence.M2WeightBranch.weightSystem_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2WeightBranch.weightSystem_eq

/-- info: 'FMSA.Convergence.M2WeightBranch.root_in_box_constructs_weight_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2WeightBranch.root_in_box_constructs_weight_branch

/-- info: 'FMSA.Convergence.M2WeightBranch.root_curve_weight_velocity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2WeightBranch.root_curve_weight_velocity

