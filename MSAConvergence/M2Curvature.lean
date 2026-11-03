import MSAConvergence.M2CurvatureCertificate
import MSAConvergence.PreconditionedLinearError
import Mathlib.Analysis.Calculus.DerivativeTest

/-! Constructed actual M2 branches with a true positive second derivative
and a strict zero-frequency minimum. No PY matching or first-loss premise. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace FMSA.Convergence.M2Curvature
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.M2BranchSecondDerivative FMSA.Convergence.M2CurvatureCertificate
open FMSA.Convergence.PreconditionedLinearError FMSA.Convergence.M2TangencySystem
open FMSA.Convergence.M2ZeroMode FMSA.Convergence.M2JacobianFormula
open FMSA.Convergence.M2ResidualFormula

/-- The actual acceleration equation and proved row bounds give positive
curvature, without assuming an inverse or an external Hessian enclosure. -/
theorem curvature_positive_of_acceleration_equation (y : T)
    (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i)
    (a : E) (ha : (accelerationMatrix y).mulVec a = accelerationForcing y) :
    (4 : ℝ)/5 < curvature y a := by
  have he := solution_error_bound preconditioner (accelerationMatrix y) a
    (accelerationForcing y) ((1 : ℝ)/1000000) 1000 (by norm_num) (by norm_num)
    (fun i => (acceleration_row_defect_bound y hx i).le) ha (approximate_acceleration_norm y hx)
  change ‖a-approximateAcceleration y‖ ≤ _ at he
  have hsmall : ‖a-approximateAcceleration y‖ < (1 : ℝ)/100 :=
    lt_of_le_of_lt he (by norm_num)
  have hid : curvature y a-curvature y (approximateAcceleration y) =
      ∑ i,curvatureGradient y i*(a-approximateAcceleration y) i := by
    simp only [curvature,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]
    ring
  have hd : |curvature y a-curvature y (approximateAcceleration y)| ≤
      (10 : ℝ)*‖a-approximateAcceleration y‖ := by
    rw [hid]
    exact (pairing_norm_le (curvatureGradient y) (a-approximateAcceleration y)).trans
      (mul_le_mul_of_nonneg_right (curvature_gradient_bound y hx) (norm_nonneg _))
  have hab : |curvature y a-curvature y (approximateAcceleration y)| < (1 : ℝ)/10 := by
    nlinarith
  have hlo := (abs_lt.mp hab).1
  have happrox := approximate_curvature_gt y hx
  linarith

private theorem observable_analyticAt (p : ℝ → E) (b : ℝ) (hp : AnalyticAt ℝ p b) :
    AnalyticAt ℝ (fun t => zeroMode (p t)) b := by
  have hpi (i : Fin 4) : AnalyticAt ℝ (fun t => p t i) b :=
    ((ContinuousLinearMap.proj i : E →L[ℝ] ℝ).analyticAt (p b)).comp hp
  have hc (c : ℝ) : AnalyticAt ℝ (fun _ : ℝ => c) b := analyticAt_const
  change AnalyticAt ℝ (fun t => 40/27+p t 0*(alpha 0+beta 0*p t 2)+
    p t 1*(alpha 1+beta 1*p t 3)) b
  exact ((hc (40/27)).add ((hpi 0).mul ((hc (alpha 0)).add ((hc (beta 0)).mul (hpi 2))))).add
    ((hpi 1).mul ((hc (alpha 1)).add ((hc (beta 1)).mul (hpi 3))))

private theorem honest_factor_second_derivative (p : ℝ → E) (b kappa : ℝ)
    (hp : AnalyticAt ℝ p b)
    (h2 : HasDerivAt (deriv (fun t => zeroMode (p t))) kappa b) :
    HasDerivAt (deriv (fun t => 1-rdfMatrixLaplace
      (nonlinearCausalKernel z rho sigma (point (p t)).1 (point (p t)).2) 0 0 0))
      (kappa : ℂ) b := by
  have he : (deriv (fun t => 1-rdfMatrixLaplace
      (nonlinearCausalKernel z rho sigma (point (p t)).1 (point (p t)).2) 0 0 0)) =ᶠ[𝓝 b]
      (fun t => Complex.ofReal (deriv (fun s : ℝ => zeroMode (p s)) t)) := by
    filter_upwards [hp.eventually_analyticAt] with t ht
    rw [(hasDerivAt_along p (deriv p t) t ht.differentiableAt.hasDerivAt).deriv]
    exact (honest_factor_hasDerivAt p (deriv p t) t ht.differentiableAt.hasDerivAt).deriv
  have hd : HasDerivAt (fun t => Complex.ofReal (deriv (fun s : ℝ => zeroMode (p s)) t)) (kappa : ℂ) b :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt b h2
  exact hd.congr_of_eventuallyEq he

private theorem quadratic_lower_bound (f : ℝ → ℝ) (b kappa : ℝ)
    (ha : AnalyticAt ℝ f b) (hzero : f b = 0)
    (h1 : HasDerivAt f 0 b) (h2 : HasDerivAt (deriv f) kappa b)
    (hk : (4 : ℝ)/5 < kappa) :
    ∀ᶠ t in 𝓝 b, (1 : ℝ)/10*(t-b)^2 ≤ f t := by
  let h : ℝ → ℝ := fun t => f t-(1/10)*(t-b)^2
  have hq (t : ℝ) : HasDerivAt (fun s : ℝ => (1 : ℝ)/10*(s-b)^2) ((1 : ℝ)/5*(t-b)) t := by
    convert! (((hasDerivAt_id t).sub_const b).pow 2).const_mul ((1 : ℝ)/10) using 1 <;> norm_num <;> ring
  have hh0 : HasDerivAt h 0 b := by
    convert! h1.sub (hq b) using 1 <;> norm_num [h]
  have he : deriv h =ᶠ[𝓝 b] (fun t => deriv f t-(1 : ℝ)/5*(t-b)) := by
    filter_upwards [ha.eventually_analyticAt] with t ht
    exact ((ht.differentiableAt.hasDerivAt).sub (hq t)).deriv
  have hd : HasDerivAt (fun t => deriv f t-(1 : ℝ)/5*(t-b)) (kappa-(1 : ℝ)/5) b := by
    convert! h2.sub (((hasDerivAt_id b).sub_const b).const_mul ((1 : ℝ)/5)) using 1 <;> norm_num
  have hh2 : HasDerivAt (deriv h) (kappa-(1 : ℝ)/5) b := hd.congr_of_eventuallyEq he
  have hpos : 0 < deriv (deriv h) b := by
    rw [hh2.deriv]
    linarith
  have hm := isLocalMin_of_deriv_deriv_pos hpos hh0.deriv hh0.continuousAt
  change ∀ᶠ t in 𝓝 b, h b ≤ h t at hm
  filter_upwards [hm] with t ht
  norm_num [h,hzero] at ht
  linarith

/-- A true original BH analytic root curve is constructed at the actual
contact. Its real observable has positive second derivative, and the HONEST
complex Laplace factor has that same genuine second derivative. -/
theorem exists_actual_positive_curvature_branch :
    ∃ (y : T) (p : ℝ → E) (kappa : ℝ),
      y ∈ Icc M2TangencyData.lower M2TangencyData.upper ∧ system y = 0 ∧
      p (y 4) = amplitudes y ∧ AnalyticAt ℝ p (y 4) ∧
      (∀ᶠ t in 𝓝 (y 4), IsRoot z rho sigma (t • strength (y 5))
        (point (p t)).1 (point (p t)).2) ∧ HasDerivAt p (velocity y) (y 4) ∧
      zeroMode (p (y 4)) = 0 ∧ HasDerivAt (fun t => zeroMode (p t)) 0 (y 4) ∧
      (4 : ℝ)/5 < kappa ∧ HasDerivAt (deriv (fun t => zeroMode (p t))) kappa (y 4) ∧
      HasDerivAt (deriv (fun t => 1-rdfMatrixLaplace
        (nonlinearCausalKernel z rho sigma (point (p t)).1 (point (p t)).2) 0 0 0))
        (kappa : ℂ) (y 4) := by
  obtain ⟨y,p,hbox,hy,hp0,hpa,hroot,hpv,hzero,_hobs⟩ :=
    M2TangencyExistence.exists_actual_stationary_branch
  have hr : ∀ᶠ t in 𝓝 (y 4), residualFormula (strength (y 5)) t (p t) = 0 := by
    filter_upwards [hroot] with t ht
    exact (actual_root_iff_formula_zero (p t) (strength (y 5)) t).mp ht
  obtain ⟨hacc,hsecond⟩ := root_curve_second_derivative y p hp0 hpa hpv hr
  have hpositive := curvature_positive_of_acceleration_equation y
    (fun i => ⟨hbox.1 i,hbox.2 i⟩) _ hacc
  have hvzero := ((system_zero_iff y).mp hy).2.2.2
  have hfirst := hasDerivAt_along p (velocity y) (y 4) hpv
  rw [hp0,hvzero] at hfirst
  refine ⟨y,p,curvature y (deriv (deriv p) (y 4)),hbox,hy,hp0,hpa,hroot,hpv,hzero,
    hfirst,hpositive,hsecond,?_⟩
  exact honest_factor_second_derivative p (y 4) _ hpa hsecond

/-- The constructed contact is a strict nondegenerate local minimum of the
HONEST zero-frequency observable, with an explicit quadratic lower coefficient.
No first contact, HS/PY identification or all-wave stability follows. -/
theorem exists_actual_strict_zero_mode_minimum :
    ∃ (y : T) (p : ℝ → E) (kappa : ℝ),
      y ∈ Icc M2TangencyData.lower M2TangencyData.upper ∧ system y = 0 ∧
      p (y 4) = amplitudes y ∧ AnalyticAt ℝ p (y 4) ∧
      (∀ᶠ t in 𝓝 (y 4), IsRoot z rho sigma (t • strength (y 5))
        (point (p t)).1 (point (p t)).2) ∧ HasDerivAt p (velocity y) (y 4) ∧
      zeroMode (p (y 4)) = 0 ∧ HasDerivAt (fun t => zeroMode (p t)) 0 (y 4) ∧
      (4 : ℝ)/5 < kappa ∧ HasDerivAt (deriv (fun t => zeroMode (p t))) kappa (y 4) ∧
      HasDerivAt (deriv (fun t => 1-rdfMatrixLaplace
        (nonlinearCausalKernel z rho sigma (point (p t)).1 (point (p t)).2) 0 0 0))
        (kappa : ℂ) (y 4) ∧
      (∀ᶠ t in 𝓝 (y 4), (1 : ℝ)/10*(t-y 4)^2 ≤ zeroMode (p t)) ∧
      (∀ᶠ t in 𝓝 (y 4), t ≠ y 4 → 0 < zeroMode (p t)) := by
  obtain ⟨y,p,kappa,hbox,hy,hp0,hpa,hroot,hpv,hzero,hfirst,hpositive,hsecond,hcomplex⟩ :=
    exists_actual_positive_curvature_branch
  have hq := quadratic_lower_bound (fun t => zeroMode (p t)) (y 4) kappa
    (observable_analyticAt p (y 4) hpa) hzero hfirst hsecond hpositive
  have hstrict : ∀ᶠ t in 𝓝 (y 4), t ≠ y 4 → 0 < zeroMode (p t) := by
    filter_upwards [hq] with t ht hne
    have hs : 0 < (t-y 4)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    nlinarith
  exact ⟨y,p,kappa,hbox,hy,hp0,hpa,hroot,hpv,hzero,hfirst,hpositive,hsecond,hcomplex,hq,hstrict⟩

end FMSA.Convergence.M2Curvature

/-- info: 'FMSA.Convergence.M2Curvature.curvature_positive_of_acceleration_equation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2Curvature.curvature_positive_of_acceleration_equation

/-- info: 'FMSA.Convergence.M2Curvature.exists_actual_positive_curvature_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2Curvature.exists_actual_positive_curvature_branch

/-- info: 'FMSA.Convergence.M2Curvature.exists_actual_strict_zero_mode_minimum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2Curvature.exists_actual_strict_zero_mode_minimum
