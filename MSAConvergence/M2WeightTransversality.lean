import MSAConvergence.M2WeightCertificate
import MSAConvergence.PreconditionedLinearError

/-! Actual fixed-coupling M2 weight transversality. The root germ and its
negative honest zero-mode derivative are constructed, not assumed. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace FMSA.Convergence.M2WeightTransversality
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.M2WeightBranch FMSA.Convergence.M2WeightCertificate
open FMSA.Convergence.M2BranchSecondDerivative FMSA.Convergence.M2CurvatureCertificate
open FMSA.Convergence.M2TangencySystem FMSA.Convergence.M2ZeroMode
open FMSA.Convergence.M2ResidualFormula FMSA.Convergence.M2JacobianFormula
open FMSA.Convergence.PreconditionedLinearError

/-- The velocity block of the full system's last derivative is exactly the
original observable gradient, at every point, without any root premise. -/
theorem curvature_gradient_eq (y : T) :
    curvatureGradient y = gradient (amplitudes y) := by
  funext i
  fin_cases i
  · change ((-566 : ℝ)/729)*(Real.pi^1)⁻¹ +
      ((-520 : ℝ)/2187)*y 2*(Real.pi^1)⁻¹ +
      ((1132 : ℝ)/2187)*y 2*(Real.pi^1)⁻¹*Real.exp ((-9 : ℝ)/5) =
        alpha 0+beta 0*y 2
    norm_num [alpha,beta] <;> ring
  · change ((-227 : ℝ)/324)*(Real.pi^1)⁻¹ +
      ((-23 : ℝ)/3240)*y 3*(Real.pi^1)⁻¹ +
      ((227 : ℝ)/3240)*y 3*(Real.pi^1)⁻¹*Real.exp (-12) =
        alpha 1+beta 1*y 3
    norm_num [alpha,beta] <;> ring
  · change ((-520 : ℝ)/2187)*y 0*(Real.pi^1)⁻¹ +
      ((1132 : ℝ)/2187)*y 0*(Real.pi^1)⁻¹*Real.exp ((-9 : ℝ)/5) = beta 0*y 0
    norm_num [beta] <;> ring
  · change ((-23 : ℝ)/3240)*y 1*(Real.pi^1)⁻¹ +
      ((227 : ℝ)/3240)*y 1*(Real.pi^1)⁻¹*Real.exp (-12) = beta 1*y 1
    norm_num [beta] <;> ring

/-- The actual weight tangent equation, with the original four-dimensional
Jacobian, gives a strict negative derivative with a rigorous error budget. -/
theorem weight_slope_lt_of_tangent_equation (y : T)
    (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i)
    (v : Fin 4 → ℝ)
    (hv : (formula (amplitudes y)).mulVec v = (y 4) • weightDerivative) :
    (∑ i, gradient (amplitudes y) i*v i) < (-19 : ℝ) := by
  have hbox := M2TangencyData.amplitude_box y ⟨fun i => (hx i).1,fun i => (hx i).2⟩
  have he := solution_error_bound M2KernelCertificate.preconditioner
    (formula (amplitudes y)) v ((y 4) • weightDerivative)
    ((1 : ℝ)/1000000) 1000 (by norm_num) (by norm_num)
    (fun i => (M2KernelCertificate.row_defect_bound (amplitudes y) hbox i).le)
    hv (approximate_weight_velocity_norm y hx)
  change ‖v-approximateWeightVelocity y‖ ≤ _ at he
  have hsmall : ‖v-approximateWeightVelocity y‖ < (1 : ℝ)/100 :=
    lt_of_le_of_lt he (by norm_num)
  have hg : (∑ i, |gradient (amplitudes y) i|) ≤ (10 : ℝ) := by
    rw [←curvature_gradient_eq]
    exact curvature_gradient_bound y hx
  have hdiff : (∑ i, gradient (amplitudes y) i*v i)-
      (∑ i, gradient (amplitudes y) i*approximateWeightVelocity y i) =
      ∑ i, gradient (amplitudes y) i*(v-approximateWeightVelocity y) i := by
    simp only [Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]
  have hd : |(∑ i, gradient (amplitudes y) i*v i)-
      (∑ i, gradient (amplitudes y) i*approximateWeightVelocity y i)| ≤
      (10 : ℝ)*‖v-approximateWeightVelocity y‖ := by
    rw [hdiff]
    exact (pairing_norm_le (gradient (amplitudes y)) (v-approximateWeightVelocity y)).trans
      (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
  have ha : (∑ i, gradient (amplitudes y) i*approximateWeightVelocity y i) < (-20 : ℝ) := by
    rw [←curvature_gradient_eq]
    exact approximate_weight_slope_lt y hx
  have hup := (abs_le.mp hd).2
  linarith

/-- Every boxed full contact constructs an actual analytic weight germ at
fixed coupling, with strictly negative genuine real and complex derivatives. -/
theorem zero_in_box_constructs_negative_weight_branch (y : T)
    (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i)
    (hy : system y = 0) :
    ∃ (p : ℝ → Fin 4 → ℝ) (slope : ℝ),
      p (y 5) = amplitudes y ∧ AnalyticAt ℝ p (y 5) ∧
      (∀ᶠ s in 𝓝 (y 5), IsRoot z rho sigma ((y 4) • strength s)
        (point (p s)).1 (point (p s)).2) ∧
      zeroMode (p (y 5)) = 0 ∧ slope < -19 ∧
      HasDerivAt (fun s => zeroMode (p s)) slope (y 5) ∧
      HasDerivAt (fun s => 1-rdfMatrixLaplace
        (nonlinearCausalKernel z rho sigma (point (p s)).1 (point (p s)).2) 0 0 0)
        (Complex.ofReal slope) (y 5) := by
  obtain ⟨hr,_hv,hz,_hd⟩ := (system_zero_iff y).mp hy
  have hbox := M2TangencyData.amplitude_box y ⟨fun i => (hx i).1,fun i => (hx i).2⟩
  obtain ⟨p,hp0,hpa,hpr⟩ := root_in_box_constructs_weight_branch (y 4) (y 5) (amplitudes y) hbox hr
  have hpv := hpa.differentiableAt.hasDerivAt
  have hpf : ∀ᶠ s in 𝓝 (y 5), residualFormula (strength s) (y 4) (p s) = 0 := by
    filter_upwards [hpr] with s hs
    exact (actual_root_iff_formula_zero (p s) (strength s) (y 4)).mp hs
  have heq := root_curve_weight_velocity (y 4) (y 5) p (deriv p (y 5)) hpv hpf
  rw [hp0] at heq
  let slope := ∑ i, gradient (p (y 5)) i*deriv p (y 5) i
  refine ⟨p,slope,hp0,hpa,hpr,?_,?_,hasDerivAt_along p _ _ hpv,honest_factor_hasDerivAt p _ _ hpv⟩
  · rwa [hp0]
  · dsimp [slope]
    rw [hp0]
    exact weight_slope_lt_of_tangent_equation y hx _ heq

/-- A boxed contact and its transverse weight germ are constructed from the
fixed physical data. No root, inverse, tangent or branch is supplied. -/
theorem exists_actual_negative_weight_branch :
    ∃ (y : T) (p : ℝ → Fin 4 → ℝ) (slope : ℝ),
      y ∈ Icc M2TangencyData.lower M2TangencyData.upper ∧ system y = 0 ∧
      p (y 5) = amplitudes y ∧ AnalyticAt ℝ p (y 5) ∧
      (∀ᶠ s in 𝓝 (y 5), IsRoot z rho sigma ((y 4) • strength s)
        (point (p s)).1 (point (p s)).2) ∧
      zeroMode (p (y 5)) = 0 ∧ slope < -19 ∧
      HasDerivAt (fun s => zeroMode (p s)) slope (y 5) ∧
      HasDerivAt (fun s => 1-rdfMatrixLaplace
        (nonlinearCausalKernel z rho sigma (point (p s)).1 (point (p s)).2) 0 0 0)
        (Complex.ofReal slope) (y 5) := by
  obtain ⟨y,hy,_⟩ := M2TangencyExistence.exists_unique_system_zero
  obtain ⟨p,s,hp⟩ := zero_in_box_constructs_negative_weight_branch y
    (fun i => ⟨hy.1.1 i,hy.1.2 i⟩) hy.2
  exact ⟨y,p,s,hy.1,hy.2,hp⟩

end FMSA.Convergence.M2WeightTransversality

/-- info: 'FMSA.Convergence.M2WeightTransversality.curvature_gradient_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2WeightTransversality.curvature_gradient_eq

/-- info: 'FMSA.Convergence.M2WeightTransversality.weight_slope_lt_of_tangent_equation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2WeightTransversality.weight_slope_lt_of_tangent_equation

/-- info: 'FMSA.Convergence.M2WeightTransversality.zero_in_box_constructs_negative_weight_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2WeightTransversality.zero_in_box_constructs_negative_weight_branch

/-- info: 'FMSA.Convergence.M2WeightTransversality.exists_actual_negative_weight_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2WeightTransversality.exists_actual_negative_weight_branch

