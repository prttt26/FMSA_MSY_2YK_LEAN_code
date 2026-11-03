import MSAConvergence.M2TangencyExistence

/-! Actual second derivatives through the proved full ten-variable Jacobian.
Curvature signs and firstness are separate obligations, never premises here. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace FMSA.Convergence.M2BranchSecondDerivative
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.M2TangencySystem FMSA.Convergence.M2ZeroMode
open FMSA.Convergence.M2ResidualFormula FMSA.Convergence.NewtonBoxExistence

abbrev E := Fin 4 → ℝ
abbrev T := Fin 10 → ℝ

def amplitudeIndex : Fin 4 → Fin 10 := ![0,1,2,3]
def residualIndex : Fin 4 → Fin 10 := ![4,5,6,7]
def velocityIndex : Fin 4 → Fin 10 := ![6,7,8,9]
def jacobian (y : T) : Fin 10 → Fin 10 → ℝ := M2TangencyJacobian.formula y

def accelerationMatrix (y : T) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => jacobian y (residualIndex i) (velocityIndex j)
def accelerationForcing (y : T) : E := fun i =>
  -(∑ j, jacobian y (residualIndex i) (amplitudeIndex j)*velocity y j) -
    jacobian y (residualIndex i) 4

def curvatureGradient (y : T) : E := fun j => jacobian y 9 (velocityIndex j)
def curvatureConstant (y : T) : ℝ :=
  (∑ j, jacobian y 9 (amplitudeIndex j)*velocity y j) + jacobian y 9 4
def curvature (y : T) (a : E) : ℝ :=
  curvatureConstant y+∑ j,curvatureGradient y j*a j

def accelerationDirection (v a : E) : T := ![v 0,v 1,v 2,v 3,1,0,a 0,a 1,a 2,a 3]
def liftedCurve (p : ℝ → E) (w t : ℝ) : T :=
  ![p t 0,p t 1,p t 2,p t 3,t,w,deriv p t 0,deriv p t 1,deriv p t 2,deriv p t 3]

private theorem sum_ten (f : Fin 10 → ℝ) : (∑ i, f i) =
  f 0+(f 1+(f 2+(f 3+(f 4+(f 5+(f 6+(f 7+(f 8+f 9)))))))) := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  rfl

/-- A ten-coordinate derivative has exactly the asserted block action. -/
theorem direction_action (M : Matrix (Fin 10) (Fin 10) ℝ) (v a : E) (i : Fin 10) :
    M.mulVec (accelerationDirection v a) i =
      (∑ j, M i (amplitudeIndex j)*v j)+M i 4+
      ∑ j, M i (velocityIndex j)*a j := by
  simp only [Matrix.mulVec,dotProduct,sum_ten,accelerationDirection,Matrix.cons_val,
    Fin.sum_univ_four,amplitudeIndex,velocityIndex]
  norm_num
  ring

/-- The first four lifted coordinates are exactly the original curve. -/
theorem lifted_amplitudes (p : ℝ → E) (w t : ℝ) :
    amplitudes (liftedCurve p w t) = p t := by
  funext i
  fin_cases i <;> rfl

/-- The last four lifted coordinates are the genuine derivative function. -/
theorem lifted_velocity (p : ℝ → E) (w t : ℝ) :
    velocity (liftedCurve p w t) = deriv p t := by
  funext i
  fin_cases i <;> rfl

/-- The lifted curve is differentiated componentwise with its true acceleration. -/
theorem lifted_hasDerivAt (p : ℝ → E) (w b : ℝ) (v a : E)
    (hp : HasDerivAt p v b) (ha : HasDerivAt (deriv p) a b) :
    HasDerivAt (liftedCurve p w) (accelerationDirection v a) b := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt (fun t => p t 0) (v 0) b
    exact (hasDerivAt_pi.mp hp) 0
  · change HasDerivAt (fun t => p t 1) (v 1) b
    exact (hasDerivAt_pi.mp hp) 1
  · change HasDerivAt (fun t => p t 2) (v 2) b
    exact (hasDerivAt_pi.mp hp) 2
  · change HasDerivAt (fun t => p t 3) (v 3) b
    exact (hasDerivAt_pi.mp hp) 3
  · change HasDerivAt (fun t : ℝ => t) (1 : ℝ) b
    exact hasDerivAt_id b
  · change HasDerivAt (fun _ : ℝ => w) (0 : ℝ) b
    exact hasDerivAt_const b w
  · change HasDerivAt (fun t => deriv p t 0) (a 0) b
    exact (hasDerivAt_pi.mp ha) 0
  · change HasDerivAt (fun t => deriv p t 1) (a 1) b
    exact (hasDerivAt_pi.mp ha) 1
  · change HasDerivAt (fun t => deriv p t 2) (a 2) b
    exact (hasDerivAt_pi.mp ha) 2
  · change HasDerivAt (fun t => deriv p t 3) (a 3) b
    exact (hasDerivAt_pi.mp ha) 3

/-- Matching the actual point and velocity identifies the whole lifted base point. -/
theorem lifted_at (y : T) (p : ℝ → E)
    (hp0 : p (y 4) = amplitudes y) (hpv : HasDerivAt p (velocity y) (y 4)) :
    liftedCurve p (y 5) (y 4) = y := by
  have hd := hpv.deriv
  funext i
  fin_cases i <;> simp [liftedCurve,hp0,hd,amplitudes,velocity,Matrix.cons_val]

private theorem system_middle (p : ℝ → E) (w t : ℝ) (i : Fin 4) :
    system (liftedCurve p w t) (residualIndex i) =
      ((M2JacobianFormula.formula (p t)).mulVec (deriv p t)-forcing w) i := by
  have he : system (liftedCurve p w t) (residualIndex i) =
      ((M2JacobianFormula.formula (amplitudes (liftedCurve p w t))).mulVec
        (velocity (liftedCurve p w t))-forcing w) i := by
    fin_cases i <;> rfl
  rw [he,lifted_amplitudes,lifted_velocity]

private theorem system_last (p : ℝ → E) (w t : ℝ) :
    system (liftedCurve p w t) 9 = ∑ i,gradient (p t) i*deriv p t i := by
  change (∑ i,gradient (amplitudes (liftedCurve p w t)) i*velocity (liftedCurve p w t) i) = _
  rw [lifted_amplitudes,lifted_velocity]

/-- Differentiating actual root germs proves both the acceleration equation
and the true second derivative of the honest real zero-frequency observable. -/
theorem root_curve_second_derivative (y : T) (p : ℝ → E)
    (hp0 : p (y 4) = amplitudes y) (hpa : AnalyticAt ℝ p (y 4))
    (hpv : HasDerivAt p (velocity y) (y 4))
    (hroot : ∀ᶠ t in 𝓝 (y 4), residualFormula (strength (y 5)) t (p t) = 0) :
    (accelerationMatrix y).mulVec (deriv (deriv p) (y 4)) = accelerationForcing y ∧
      HasDerivAt (deriv (fun t => zeroMode (p t)))
        (curvature y (deriv (deriv p) (y 4))) (y 4) := by
  let a := deriv (deriv p) (y 4)
  have ha : HasDerivAt (deriv p) a (y 4) := hpa.deriv.differentiableAt.hasDerivAt
  have hGamma := lifted_hasDerivAt p (y 5) (y 4) (velocity y) a hpv ha
  have hbase := lifted_at y p hp0 hpv
  have hfull := (M2TangencyJacobian.system_hasFDerivAt (liftedCurve p (y 5) (y 4))).comp_hasDerivAt (y 4) hGamma
  rw [hbase] at hfull
  have hnear : ∀ᶠ t in 𝓝 (y 4), AnalyticAt ℝ p t := by
    obtain ⟨r,hr,h⟩ := hpa.exists_ball_analyticOnNhd
    exact Filter.eventually_of_mem (Metric.ball_mem_nhds _ hr) (fun t ht => h t ht)
  have hmiddle (i : Fin 4) :
      (fun t => system (liftedCurve p (y 5) t) (residualIndex i)) =ᶠ[𝓝 (y 4)] (fun _ => 0) := by
    filter_upwards [hnear,hroot.eventually_nhds] with t ht hr
    have hv := root_curve_velocity (y 5) t p (deriv p t) ht.differentiableAt.hasDerivAt hr
    rw [system_middle,hv,sub_self]
    rfl
  have hlast : (fun t => system (liftedCurve p (y 5) t) 9) =ᶠ[𝓝 (y 4)]
      (deriv (fun t => zeroMode (p t))) := by
    filter_upwards [hnear] with t ht
    rw [system_last]
    exact (hasDerivAt_along p (deriv p t) t ht.differentiableAt.hasDerivAt).deriv.symm
  constructor
  · funext i
    have hd := (hasDerivAt_pi.mp hfull) (residualIndex i)
    have hz := (hd.congr_of_eventuallyEq (hmiddle i).symm).unique (hasDerivAt_const (y 4) (0 : ℝ))
    rw [matrixCLM_apply,direction_action] at hz
    change (∑ j,jacobian y (residualIndex i) (velocityIndex j)*a j) = _
    dsimp only [accelerationForcing]
    change (∑ j,jacobian y (residualIndex i) (amplitudeIndex j)*velocity y j)+
      jacobian y (residualIndex i) 4+(∑ j,jacobian y (residualIndex i) (velocityIndex j)*a j) = 0 at hz
    linarith
  · have hd := ((hasDerivAt_pi.mp hfull) 9).congr_of_eventuallyEq hlast.symm
    have he : (matrixCLM (M2TangencyJacobian.formula y) (accelerationDirection (velocity y) a)) 9 = curvature y a := by
      rw [matrixCLM_apply,direction_action]
      rfl
    rw [he] at hd
    exact hd

end FMSA.Convergence.M2BranchSecondDerivative

/-- info: 'FMSA.Convergence.M2BranchSecondDerivative.direction_action' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2BranchSecondDerivative.direction_action

/-- info: 'FMSA.Convergence.M2BranchSecondDerivative.lifted_amplitudes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2BranchSecondDerivative.lifted_amplitudes

/-- info: 'FMSA.Convergence.M2BranchSecondDerivative.lifted_velocity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2BranchSecondDerivative.lifted_velocity

/-- info: 'FMSA.Convergence.M2BranchSecondDerivative.lifted_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2BranchSecondDerivative.lifted_hasDerivAt

/-- info: 'FMSA.Convergence.M2BranchSecondDerivative.lifted_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2BranchSecondDerivative.lifted_at

/-- info: 'FMSA.Convergence.M2BranchSecondDerivative.root_curve_second_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2BranchSecondDerivative.root_curve_second_derivative
