import MSAConvergence.M2ZeroMode

/-! The actual TEN-dimensional M2 zero-mode contact system, including all
four coupling velocities. A zero is connected to true BH roots and honest
zero-frequency factors. Existence of a zero is a separate certificate. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators ContDiff
namespace FMSA.Convergence.M2TangencySystem
open FMSA.ExactMSA.MultiTailMixture FMSA.Paper.ActualAnalyticBranch
open FMSA.Convergence.BHResidualPolynomials FMSA.Convergence.BHPolynomialJacobian
open FMSA.Convergence.M2JacobianFormula FMSA.Convergence.M2ResidualFormula
open FMSA.Convergence.M2ResidualDerivative FMSA.Convergence.M2KernelCertificate
open FMSA.Convergence.M2ZeroMode FMSA.Convergence.RegularEndpointContinuation
open FMSA.Convergence.CanonicalFirstLoss FMSA.Convergence.CanonicalNeighborhood

/-- Unknown order: all Dt/G, coupling, weight, all Dt/G coupling velocities. -/
def amplitudes (y : Fin 10 → ℝ) : Fin 4 → ℝ := ![y 0,y 1,y 2,y 3]
def velocity (y : Fin 10 → ℝ) : Fin 4 → ℝ := ![y 6,y 7,y 8,y 9]
def strength (w : ℝ) : TailMatrix (Fin 2) 1 := fun u _ _ => ![1,w] u
def forcing (w : ℝ) : Fin 4 → ℝ := ![10*Real.pi/9,Real.pi*w/6,0,0]
def system (y : Fin 10 → ℝ) : Fin 10 → ℝ :=
  let x := amplitudes y
  let v := velocity y
  let r := residualFormula (strength (y 5)) (y 4) x
  let d := (formula x).mulVec v-forcing (y 5)
  ![r 0,r 1,r 2,r 3,d 0,d 1,d 2,d 3,zeroMode x,∑ i, gradient x i*v i]

/-- Exact affine coupling dependence, with the original residual scaling. -/
theorem residual_affine (w b : ℝ) (x : Fin 4 → ℝ) :
    residualFormula (strength w) b x = residualFormula (strength w) 0 x-b • forcing w := by
  funext i
  fin_cases i <;> norm_num [residualFormula,strength,forcing,Matrix.cons_val_two,Matrix.cons_val_three] <;> ring

/-- All ten equations are retained, including four velocity equations. -/
theorem system_zero_iff (y : Fin 10 → ℝ) :
    system y = 0 ↔
      residualFormula (strength (y 5)) (y 4) (amplitudes y) = 0 ∧
      (formula (amplitudes y)).mulVec (velocity y) = forcing (y 5) ∧
      zeroMode (amplitudes y) = 0 ∧ ∑ i, gradient (amplitudes y) i*velocity y i = 0 := by
  constructor
  · intro h
    have hi (i : Fin 10) := congrFun h i
    have h0 := hi 0; have h1 := hi 1; have h2 := hi 2; have h3 := hi 3
    have h4 := hi 4; have h5 := hi 5; have h6 := hi 6; have h7 := hi 7
    have h8 := hi 8; have h9 := hi 9
    simp only [system,Matrix.cons_val_zero,Matrix.cons_val_succ,Pi.zero_apply,Pi.sub_apply] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    refine ⟨?_,?_,h8,h9⟩
    · funext i
      fin_cases i <;> assumption
    · funext i
      fin_cases i
      · exact sub_eq_zero.mp h4
      · exact sub_eq_zero.mp h5
      · exact sub_eq_zero.mp h6
      · exact sub_eq_zero.mp h7
  · rintro ⟨hr,hv,hz,hd⟩
    funext i
    simp only [system,hr,hv,sub_self,hz,hd]
    fin_cases i <;> rfl

/-- The coordinate velocity equation is EXACTLY the original amplitude
partial equation, including its nonzero forcing and all four coordinates. -/
theorem velocity_equation_iff (x v : Fin 4 → ℝ) (w b : ℝ) :
    (formula x).mulVec v = forcing w ↔
      actualPartial z rho sigma (strength w) b (point x) (point v) = point (forcing w) := by
  constructor
  · intro h
    apply amplitude_values_injective
    funext j
    obtain ⟨i,rfl⟩ := index.surjective j
    have he := (ordered_partial_coordinates (point x) (point v) (strength w) b i).symm
    have he' : amplitudeValues (actualPartial z rho sigma (strength w) b (point x) (point v)) (index i) =
        (formula x).mulVec v i := by
      simpa only [point_coordinates,Matrix.mulVec,dotProduct] using he
    rw [he',h,point_coordinates]
  · intro h
    funext i
    have he := ordered_partial_coordinates (point x) (point v) (strength w) b i
    have he' : (formula x).mulVec v i =
        amplitudeValues (actualPartial z rho sigma (strength w) b (point x) (point v)) (index i) := by
      simpa only [point_coordinates,Matrix.mulVec,dotProduct] using he
    rw [he',h,point_coordinates]

/-- A zero is an actual BH root and an honest physical Fourier/renewal zero.
No conclusion about first contact or the PY branch follows from this alone. -/
theorem zero_gives_actual_root_and_noncanonical (y : Fin 10 → ℝ) (hy : system y = 0) :
    IsRoot z rho sigma ((y 4) • strength (y 5))
      (point (amplitudes y)).1 (point (amplitudes y)).2 ∧
    renewalDet z rho sigma (point (amplitudes y)) 0 = 0 ∧
    point (amplitudes y) ∉ canonicalAmplitudes z rho sigma := by
  obtain ⟨hr,_hv,hz,_hd⟩ := (system_zero_iff y).mp hy
  refine ⟨(actual_root_iff_formula_zero _ _ _).mpr hr,?_,not_canonical_of_zero _ hz⟩
  rw [actual_renewalDet_at_zero,hz,Complex.ofReal_zero]

/-- Any differentiable original coordinate root curve satisfies J*q'=forcing.
The derivative equation is proved from exact coupling dependence, not assumed. -/
theorem root_curve_velocity
    (w b : ℝ) (p : ℝ → Fin 4 → ℝ) (v : Fin 4 → ℝ) (hp : HasDerivAt p v b)
    (hr : ∀ᶠ t in 𝓝 b, residualFormula (strength w) t (p t) = 0) :
    (formula (p b)).mulVec v = forcing w := by
  have he : (fun t => residualFormula (strength w) 0 (p t)) =ᶠ[𝓝 b] (fun t => t • forcing w) := by
    filter_upwards [hr] with t ht
    rw [residual_affine] at ht
    exact sub_eq_zero.mp ht
  have hd := (hasFDerivAt_formula (strength w) 0 (p b)).comp_hasDerivAt b hp
  have hf : HasDerivAt (fun t : ℝ => t • forcing w) (forcing w) b := by
    simpa using (hasDerivAt_id b).smul_const (forcing w)
  have hv := (hd.congr_of_eventuallyEq he.symm).unique hf
  simpa only [NewtonBoxExistence.matrixCLM_apply] using hv

/-- A regular boxed zero CONSTRUCTS a two-sided actual analytic root branch,
whose TRUE coupling velocity is the certified v and whose HONEST zero-mode
factor has value and first derivative zero. This is stationarity, not a
proved nondegenerate minimum, first loss or PY-prefix identification. -/
theorem zero_in_box_constructs_stationary_branch
    (y : Fin 10 → ℝ) (hy : system y = 0)
    (hbox : ∀ i, lower i ≤ amplitudes y i ∧ amplitudes y i ≤ upper i) :
    ∃ p : ℝ → Fin 4 → ℝ,
      p (y 4) = amplitudes y ∧ AnalyticAt ℝ p (y 4) ∧
      (∀ᶠ t in 𝓝 (y 4), IsRoot z rho sigma (t • strength (y 5)) (point (p t)).1 (point (p t)).2) ∧
      HasDerivAt p (velocity y) (y 4) ∧
      zeroMode (p (y 4)) = 0 ∧
      HasDerivAt (fun t => 1-rdfMatrixLaplace
        (nonlinearCausalKernel z rho sigma (point (p t)).1 (point (p t)).2) 0 0 0) 0 (y 4) := by
  obtain ⟨hr,hv,hz,hd⟩ := (system_zero_iff y).mp hy
  let x := amplitudes y
  let b := y 4
  let K := strength (y 5)
  let R := FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K
  have hi : EndpointRegular z rho sigma K b (point x) := actual_regular_on_box _ _ _ (by
    simpa only [point_coordinates] using hbox)
  have hc : ContDiffAt ℝ ω R (b,point x) := (residual_analyticAt z rho sigma K (b,point x)).contDiffAt
  let q := hc.implicitFunction (by simp) hi
  have hq0 : q b = point x := hc.implicitFunction_apply_self (by simp) hi
  have hqa : AnalyticAt ℝ q b := (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt
  have hR0 : R (b,point x) = 0 := (residual_eq_zero_iff _ _ _ _ _ _ _).mpr
    ((actual_root_iff_formula_zero x K b).mpr hr)
  have hqr : ∀ᶠ t in 𝓝 b, IsRoot z rho sigma (t • K) (q t).1 (q t).2 := by
    filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with t ht
    exact (residual_eq_zero_iff _ _ _ _ _ _ _).mp (ht.trans hR0)
  let p := fun t => coordinates (q t)
  have hp0 : p b = x := by
    dsimp [p]
    rw [hq0]
    funext i
    exact point_coordinates x i
  have hpa : AnalyticAt ℝ p b := (coordinates.toContinuousLinearMap.analyticAt (q b)).comp hqa
  have hpr : ∀ᶠ t in 𝓝 b, IsRoot z rho sigma (t • K) (point (p t)).1 (point (p t)).2 := by
    filter_upwards [hqr] with t ht
    change IsRoot z rho sigma (t • K)
      (point (fun i => amplitudeValues (q t) (index i))).1
      (point (fun i => amplitudeValues (q t) (index i))).2
    simpa only [point_coordinates_inverse] using ht
  have hpf : ∀ᶠ t in 𝓝 b, residualFormula K t (p t) = 0 := by
    filter_upwards [hpr] with t ht
    exact (actual_root_iff_formula_zero (p t) K t).mp ht
  have hpder := hpa.differentiableAt.hasDerivAt
  have hj := root_curve_velocity (y 5) b p (deriv p b) hpder hpf
  rw [hp0] at hj
  have hji := matrix_injective_of_row_defect (formula x) preconditioner
    (fun i => (row_defect_bound x hbox i).trans (by norm_num))
  have hvel : deriv p b = velocity y := hji (hj.trans hv.symm)
  have hpv : HasDerivAt p (velocity y) b := hvel ▸ hpder
  refine ⟨p,hp0,hpa,hpr,hpv,?_,?_⟩
  · rwa [hp0]
  · have hobs := honest_factor_hasDerivAt p (velocity y) b hpv
    rw [hp0,hd,Complex.ofReal_zero] at hobs
    exact hobs

end FMSA.Convergence.M2TangencySystem

/-- info: 'FMSA.Convergence.M2TangencySystem.residual_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2TangencySystem.residual_affine

/-- info: 'FMSA.Convergence.M2TangencySystem.system_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2TangencySystem.system_zero_iff

/-- info: 'FMSA.Convergence.M2TangencySystem.velocity_equation_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2TangencySystem.velocity_equation_iff

/-- info: 'FMSA.Convergence.M2TangencySystem.zero_gives_actual_root_and_noncanonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2TangencySystem.zero_gives_actual_root_and_noncanonical

/-- info: 'FMSA.Convergence.M2TangencySystem.root_curve_velocity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2TangencySystem.root_curve_velocity

/-- info: 'FMSA.Convergence.M2TangencySystem.zero_in_box_constructs_stationary_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2TangencySystem.zero_in_box_constructs_stationary_branch

