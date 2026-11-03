import MSAConvergence.ImplicitContourCurvature

/-! Actual M2 contour second derivatives with a numerical lower bound,
using only the earlier proved error and gradient budgets. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace FMSA.Convergence.M2ContourCurvature
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.M2JacobianFormula FMSA.Convergence.M2ResidualFormula
open FMSA.Convergence.M2TangencySystem FMSA.Convergence.M2ZeroMode
open FMSA.Convergence.M2KernelCertificate FMSA.Convergence.M2BranchSecondDerivative
open FMSA.Convergence.M2WeightBranch FMSA.Convergence.M2WeightCertificate
open FMSA.Convergence.M2WeightTransversality FMSA.Convergence.M2CurvatureCertificate
open FMSA.Convergence.M2JointBranch FMSA.Convergence.M2JointZeroContour
open FMSA.Convergence.PreconditionedLinearError
abbrev E := Fin 4 → ℝ
abbrev T := Fin 10 → ℝ
abbrev Params := ℝ × ℝ

/-- The actual tangent equation bounds the weight slope in absolute value.
Only existing row-defect, velocity-norm and gradient budgets are used. -/
theorem weight_slope_abs_lt_of_tangent_equation (y : T)
    (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i)
    (v : E) (hv : (formula (amplitudes y)).mulVec v = (y 4) • weightDerivative) :
    |∑ i, M2ZeroMode.gradient (amplitudes y) i*v i| < (10001 : ℝ) := by
  have hbox := M2TangencyData.amplitude_box y ⟨fun i => (hx i).1,fun i => (hx i).2⟩
  have he := solution_error_bound M2KernelCertificate.preconditioner
    (formula (amplitudes y)) v ((y 4) • weightDerivative)
    ((1 : ℝ)/1000000) 1000 (by norm_num) (by norm_num)
    (fun i => (M2KernelCertificate.row_defect_bound (amplitudes y) hbox i).le)
    hv (approximate_weight_velocity_norm y hx)
  change ‖v-approximateWeightVelocity y‖ ≤ _ at he
  have hsmall : ‖v-approximateWeightVelocity y‖ < (1 : ℝ)/100 :=
    lt_of_le_of_lt he (by norm_num)
  have hn : ‖v‖ ≤ ‖v-approximateWeightVelocity y‖+1000 := by
    calc
      ‖v‖ = ‖(v-approximateWeightVelocity y)+approximateWeightVelocity y‖ := by congr 1; abel
      _ ≤ ‖v-approximateWeightVelocity y‖+‖approximateWeightVelocity y‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (le_refl _) (approximate_weight_velocity_norm y hx)
  have hvsmall : ‖v‖ < (10001 : ℝ)/10 := by linarith
  have hg : (∑ i, |M2ZeroMode.gradient (amplitudes y) i|) ≤ (10 : ℝ) := by
    rw [←curvature_gradient_eq]
    exact curvature_gradient_bound y hx
  calc
    _ ≤ (∑ i, |M2ZeroMode.gradient (amplitudes y) i|)*‖v‖ := pairing_norm_le _ _
    _ ≤ 10*‖v‖ := mul_le_mul_of_nonneg_right hg (norm_nonneg _)
    _ < _ := by linarith

/-- Both scalar partials and the genuine contour second derivative refer
to the SAME actual joint root germ. The last clause is a local quadratic
lower bound for the actual contour, rather than its formal tangent model. -/
def CurvatureData (y : T) (P : Params → E) (ψ : ℝ → ℝ) (kappa d : ℝ) : Prop :=
  (4 : ℝ)/5 < kappa ∧ (-10001 : ℝ) < d ∧ d < -19 ∧
  HasDerivAt (deriv (fun t => zeroMode (P (t,y 5)))) kappa (y 4) ∧
  HasDerivAt (fun s => zeroMode (P (y 4,s))) d (y 5) ∧
  HasDerivAt (fun s => 1-rdfMatrixLaplace
    (nonlinearCausalKernel z rho sigma (point (P (y 4,s))).1 (point (P (y 4,s))).2) 0 0 0)
    (Complex.ofReal d) (y 5) ∧
  kappa+d*deriv (deriv ψ) (y 4) = 0 ∧
  HasDerivAt (deriv ψ) (-kappa/d) (y 4) ∧ (1 : ℝ)/20000 < -kappa/d ∧
  (∀ᶠ t in 𝓝 (y 4), y 5+(1 : ℝ)/100000*(t-y 4)^2 ≤ ψ t)

/-- Actual joint roots and their true contour identity internally discharge
all second-derivative hypotheses and give a positive numerical lower bound. -/
theorem contour_data_has_positive_curvature (y : T)
    (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i)
    (hy : system y = 0) (P : Params → E) (ψ : ℝ → ℝ) (hC : ContourData y P ψ) :
    ∃ kappa d : ℝ, CurvatureData y P ψ kappa d := by
  obtain ⟨hP0,hPa,hPR,hψ0,hψa,hψv,_hmin,_hsign,hcurve⟩ := hC
  obtain ⟨_hpv,kappa,hk,_hfirst,hsecond,_hq,_hpos⟩ :=
    joint_branch_coupling_geometry y hx hy P hP0 hPa hPR
  obtain ⟨d,hd,hweight,hcomplex⟩ := joint_branch_weight_geometry y hx P hP0 hPa hPR
  let p : ℝ → E := fun s => P (y 4,s)
  have hp0 : p (y 5) = amplitudes y := hP0
  have hpa : AnalyticAt ℝ p (y 5) := hPa.comp (f := fun s : ℝ => (y 4,s))
    (analyticAt_const.prod analyticAt_id)
  have ht : Tendsto (fun s : ℝ => (y 4,s)) (𝓝 (y 5)) (𝓝 (y 4,y 5)) :=
    continuousAt_const.prodMk continuousAt_id
  have hr : ∀ᶠ s in 𝓝 (y 5), residualFormula (strength s) (y 4) (p s) = 0 := by
    filter_upwards [ht.eventually hPR] with s hs
    exact (actual_root_iff_formula_zero (p s) (strength s) (y 4)).mp hs
  have hpder := hpa.differentiableAt.hasDerivAt
  have hvel := root_curve_weight_velocity (y 4) (y 5) p (deriv p (y 5)) hpder hr
  rw [hp0] at hvel
  have hid : (∑ i, M2ZeroMode.gradient (amplitudes y) i*deriv p (y 5) i) = d := by
    have he := (hasDerivAt_along p _ _ hpder).unique hweight
    simpa only [hp0] using he
  have habs : |d| < (10001 : ℝ) := by
    rw [←hid]
    exact weight_slope_abs_lt_of_tangent_equation y hx _ hvel
  have hdlo : (-10001 : ℝ) < d := (abs_lt.mp habs).1
  have hdneg : d < 0 := by linarith
  let f : Params → ℝ := fun u => zeroMode (P u)
  have hfa : AnalyticAt ℝ f (y 4,y 5) := observable_analyticAt P (y 4,y 5) hPa
  have hroot : ∀ᶠ t in 𝓝 (y 4), f (t,ψ t) = 0 := by
    filter_upwards [hcurve] with t ht
    exact ht.2.2.2.1
  have heq := ImplicitContourCurvature.contour_acceleration_equation f (y 4) (y 5) kappa d
    hfa hsecond hweight ψ hψ0 hψa hψv hroot
  have hψ2 := ImplicitContourCurvature.contour_second_derivative f (y 4) (y 5) kappa d
    hfa hsecond hweight (ne_of_lt hdneg) ψ hψ0 hψa hψv hroot
  have hden : 0 < -d := neg_pos.mpr hdneg
  have hbound : (1 : ℝ)/20000 < -kappa/d := by
    have hh : (1 : ℝ)/20000*(-d) < kappa := by linarith
    have h := (lt_div_iff₀ hden).mpr hh
    simpa only [div_neg,neg_div] using h
  have hquad := ImplicitContourCurvature.quadratic_lower_bound ψ (y 4) (-kappa/d)
    ((1 : ℝ)/100000) hψa hψv hψ2 (by linarith)
  have hquad' : ∀ᶠ t in 𝓝 (y 4), y 5+(1 : ℝ)/100000*(t-y 4)^2 ≤ ψ t := by
    simpa only [hψ0] using hquad
  exact ⟨kappa,d,hk,hdlo,hd,hsecond,hweight,hcomplex,heq,hψ2,hbound,hquad'⟩

/-- Physical data alone construct the original joint root germ, its contour,
the actual second-derivative formula, and its positive numerical lower bound. -/
theorem exists_actual_positive_contour_curvature :
    ∃ (y : T) (P : Params → E) (ψ : ℝ → ℝ) (kappa d : ℝ),
      y ∈ Icc M2TangencyData.lower M2TangencyData.upper ∧ system y = 0 ∧
      ContourData y P ψ ∧ CurvatureData y P ψ kappa d := by
  obtain ⟨y,P,ψ,hbox,hy,hC⟩ := exists_actual_strict_minimum_zero_contour
  obtain ⟨kappa,d,hD⟩ := contour_data_has_positive_curvature y
    (fun i => ⟨hbox.1 i,hbox.2 i⟩) hy P ψ hC
  exact ⟨y,P,ψ,kappa,d,hbox,hy,hC,hD⟩

end FMSA.Convergence.M2ContourCurvature

/-- info: 'FMSA.Convergence.M2ContourCurvature.weight_slope_abs_lt_of_tangent_equation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2ContourCurvature.weight_slope_abs_lt_of_tangent_equation

/-- info: 'FMSA.Convergence.M2ContourCurvature.contour_data_has_positive_curvature' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2ContourCurvature.contour_data_has_positive_curvature

/-- info: 'FMSA.Convergence.M2ContourCurvature.exists_actual_positive_contour_curvature' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2ContourCurvature.exists_actual_positive_contour_curvature
