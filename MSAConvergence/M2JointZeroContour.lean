import MSAConvergence.M2JointBranch
import MSAConvergence.ImplicitZeroContour

/-! A constructed joint original BH root germ and its actual local zero-mode
contour, with strict minimum and sign classification. No first-loss claim. -/
noncomputable section
open Set Real Filter Topology
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace FMSA.Convergence.M2JointZeroContour
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.M2JacobianFormula FMSA.Convergence.M2ResidualFormula
open FMSA.Convergence.M2TangencySystem FMSA.Convergence.M2ZeroMode
open FMSA.Convergence.M2ResidualDerivative FMSA.Convergence.M2KernelCertificate
open FMSA.Convergence.M2BranchSecondDerivative FMSA.Convergence.M2Curvature
open FMSA.Convergence.M2WeightBranch FMSA.Convergence.M2WeightTransversality
open FMSA.Convergence.M2JointBranch FMSA.Convergence.BHPolynomialJacobian
open FMSA.Convergence.CanonicalNeighborhood
abbrev E := Fin 4 → ℝ
abbrev T := Fin 10 → ℝ
abbrev Params := ℝ × ℝ

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

/-- The coupling restriction of THIS joint root germ has the actual
certified velocity, positive true curvature and quadratic lower bound. -/
theorem joint_branch_coupling_geometry (y : T)
    (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i)
    (hy : system y = 0) (P : Params → E)
    (hP0 : P (y 4,y 5) = amplitudes y) (hPa : AnalyticAt ℝ P (y 4,y 5))
    (hPR : ∀ᶠ u in 𝓝 (y 4,y 5), IsRoot z rho sigma (u.1 • strength u.2)
      (point (P u)).1 (point (P u)).2) :
    HasDerivAt (fun t => P (t,y 5)) (velocity y) (y 4) ∧
    ∃ kappa : ℝ, (4 : ℝ)/5 < kappa ∧
      HasDerivAt (fun t => zeroMode (P (t,y 5))) 0 (y 4) ∧
      HasDerivAt (deriv (fun t => zeroMode (P (t,y 5)))) kappa (y 4) ∧
      (∀ᶠ t in 𝓝 (y 4), (1 : ℝ)/10*(t-y 4)^2 ≤ zeroMode (P (t,y 5))) ∧
      (∀ᶠ t in 𝓝 (y 4), t ≠ y 4 → 0 < zeroMode (P (t,y 5))) := by
  let p : ℝ → E := fun t => P (t,y 5)
  have hp0 : p (y 4) = amplitudes y := hP0
  have hpa : AnalyticAt ℝ p (y 4) := hPa.comp (f := fun t : ℝ => (t,y 5))
    (analyticAt_id.prod analyticAt_const)
  have ht : Tendsto (fun t : ℝ => (t,y 5)) (𝓝 (y 4)) (𝓝 (y 4,y 5)) :=
    continuousAt_id.prodMk continuousAt_const
  have hpr := ht.eventually hPR
  have hr : ∀ᶠ t in 𝓝 (y 4), residualFormula (strength (y 5)) t (p t) = 0 := by
    filter_upwards [hpr] with t ht
    exact (actual_root_iff_formula_zero (p t) (strength (y 5)) t).mp ht
  have hpder := hpa.differentiableAt.hasDerivAt
  have hvel := root_curve_velocity (y 5) (y 4) p (deriv p (y 4)) hpder hr
  rw [hp0] at hvel
  obtain ⟨_hroot,hv,hz,hd⟩ := (system_zero_iff y).mp hy
  have hbox := M2TangencyData.amplitude_box y ⟨fun i => (hx i).1,fun i => (hx i).2⟩
  have hjinj := matrix_injective_of_row_defect (formula (amplitudes y)) M2KernelCertificate.preconditioner
    (fun i => (M2KernelCertificate.row_defect_bound (amplitudes y) hbox i).trans (by norm_num))
  have hvtrue : deriv p (y 4) = velocity y := hjinj (hvel.trans hv.symm)
  have hpv : HasDerivAt p (velocity y) (y 4) := hvtrue ▸ hpder
  obtain ⟨hacc,hsecond⟩ := root_curve_second_derivative y p hp0 hpa hpv hr
  have hpositive := curvature_positive_of_acceleration_equation y hx _ hacc
  have hfirst := hasDerivAt_along p (velocity y) (y 4) hpv
  rw [hp0,hd] at hfirst
  have hzero : zeroMode (p (y 4)) = 0 := by rwa [hp0]
  have hq := quadratic_lower_bound (fun t => zeroMode (p t)) (y 4) _
    (observable_analyticAt p (y 4) hpa) hzero hfirst hsecond hpositive
  refine ⟨hpv,curvature y (deriv (deriv p) (y 4)),hpositive,hfirst,hsecond,hq,?_⟩
  filter_upwards [hq] with t ht hne
  have hs : 0 < (t-y 4)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  nlinarith

/-- The weight restriction of the SAME joint germ has negative true
observable derivative, and the honest complex-factor derivative agrees. -/
theorem joint_branch_weight_geometry (y : T)
    (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i)
    (P : Params → E) (hP0 : P (y 4,y 5) = amplitudes y)
    (hPa : AnalyticAt ℝ P (y 4,y 5))
    (hPR : ∀ᶠ u in 𝓝 (y 4,y 5), IsRoot z rho sigma (u.1 • strength u.2)
      (point (P u)).1 (point (P u)).2) :
    ∃ slope : ℝ, slope < -19 ∧
      HasDerivAt (fun s => zeroMode (P (y 4,s))) slope (y 5) ∧
      HasDerivAt (fun s => 1-rdfMatrixLaplace
        (nonlinearCausalKernel z rho sigma (point (P (y 4,s))).1 (point (P (y 4,s))).2) 0 0 0)
        (Complex.ofReal slope) (y 5) := by
  let p : ℝ → E := fun s => P (y 4,s)
  have hp0 : p (y 5) = amplitudes y := hP0
  have hpa : AnalyticAt ℝ p (y 5) := hPa.comp (f := fun s : ℝ => (y 4,s))
    (analyticAt_const.prod analyticAt_id)
  have ht : Tendsto (fun s : ℝ => (y 4,s)) (𝓝 (y 5)) (𝓝 (y 4,y 5)) :=
    continuousAt_const.prodMk continuousAt_id
  have hpr := ht.eventually hPR
  have hr : ∀ᶠ s in 𝓝 (y 5), residualFormula (strength s) (y 4) (p s) = 0 := by
    filter_upwards [hpr] with s hs
    exact (actual_root_iff_formula_zero (p s) (strength s) (y 4)).mp hs
  have hpder := hpa.differentiableAt.hasDerivAt
  have hvel := root_curve_weight_velocity (y 4) (y 5) p (deriv p (y 5)) hpder hr
  rw [hp0] at hvel
  let slope := ∑ i, M2ZeroMode.gradient (p (y 5)) i*deriv p (y 5) i
  refine ⟨slope,?_,hasDerivAt_along p _ _ hpder,honest_factor_hasDerivAt p _ _ hpder⟩
  dsimp [slope]
  rw [hp0]
  exact weight_slope_lt_of_tangent_equation y hx _ hvel

/-- All conditions concern original roots and honest zero-mode factors.
The zero contour has a strict minimum in weight as coupling varies. -/
def ContourData (y : T) (P : Params → E) (ψ : ℝ → ℝ) : Prop :=
  P (y 4,y 5) = amplitudes y ∧ AnalyticAt ℝ P (y 4,y 5) ∧
  (∀ᶠ u in 𝓝 (y 4,y 5), IsRoot z rho sigma (u.1 • strength u.2)
    (point (P u)).1 (point (P u)).2) ∧
  ψ (y 4) = y 5 ∧ AnalyticAt ℝ ψ (y 4) ∧ HasDerivAt ψ 0 (y 4) ∧
  (∀ᶠ t in 𝓝 (y 4), t ≠ y 4 → y 5 < ψ t) ∧
  (∀ᶠ u in 𝓝 (y 4,y 5),
    (0 < zeroMode (P u) ↔ u.2 < ψ u.1) ∧
    (zeroMode (P u) < 0 ↔ ψ u.1 < u.2) ∧
    (zeroMode (P u) = 0 ↔ u.2 = ψ u.1)) ∧
  (∀ᶠ t in 𝓝 (y 4), 0 < t ∧ ψ t < 0 ∧
    IsRoot z rho sigma (t • strength (ψ t)) (point (P (t,ψ t))).1 (point (P (t,ψ t))).2 ∧
    zeroMode (P (t,ψ t)) = 0 ∧
    1-rdfMatrixLaplace (nonlinearCausalKernel z rho sigma
      (point (P (t,ψ t))).1 (point (P (t,ψ t))).2) 0 0 0 = 0 ∧
    point (P (t,ψ t)) ∉ canonicalAmplitudes z rho sigma)

/-- A boxed contact constructs one joint analytic original root germ,
its locally unique zero contour, a strict minimum, and both signs of F0. -/
theorem zero_in_box_constructs_joint_zero_contour (y : T)
    (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i)
    (hy : system y = 0) :
    ∃ (P : Params → E) (ψ : ℝ → ℝ), ContourData y P ψ := by
  obtain ⟨hr,_hv,hz,_hd⟩ := (system_zero_iff y).mp hy
  have hbox := M2TangencyData.amplitude_box y ⟨fun i => (hx i).1,fun i => (hx i).2⟩
  obtain ⟨P,hP0,hPa,hPR⟩ := root_in_box_constructs_joint_branch (y 4) (y 5) (amplitudes y) hbox hr
  obtain ⟨_hvel,kappa,_hk,_hfirst,_hsecond,_hq,hpos⟩ := joint_branch_coupling_geometry y hx hy P hP0 hPa hPR
  obtain ⟨slope,hs,hweight,_hcweight⟩ := joint_branch_weight_geometry y hx P hP0 hPa hPR
  let f : Params → ℝ := fun u => zeroMode (P u)
  have hfa : AnalyticAt ℝ f (y 4,y 5) := observable_analyticAt P (y 4,y 5) hPa
  have hf0 : f (y 4,y 5) = 0 := by change zeroMode (P (y 4,y 5)) = 0; rwa [hP0]
  have hs0 : slope < 0 := by linarith
  obtain ⟨ψ,hψ0,hψa,hψroot,_hψiff⟩ :=
    ImplicitZeroContour.exists_analytic_zero_contour f (y 4) (y 5) slope hfa hf0 hweight hs0
  have hstrict := ImplicitZeroContour.strict_minimum_of_positive_axis f (y 4) (y 5) slope hfa hweight hs0
    ψ hψ0 hψa.continuousAt hψroot hpos
  have hmin : IsLocalMin ψ (y 4) := by
    change ∀ᶠ t in 𝓝 (y 4), ψ (y 4) ≤ ψ t
    filter_upwards [hstrict] with t ht
    by_cases he : t = y 4
    · subst t; exact le_rfl
    · rw [hψ0]; exact (ht he).le
  have hψder : HasDerivAt ψ 0 (y 4) := by
    simpa only [hmin.deriv_eq_zero] using hψa.differentiableAt.hasDerivAt
  have hsign := ImplicitZeroContour.local_sign_classification f (y 4) (y 5) slope hfa hweight hs0
    ψ hψ0 hψa.continuousAt hψroot
  have ht : Tendsto (fun t : ℝ => (t,ψ t)) (𝓝 (y 4)) (𝓝 (y 4,y 5)) := by
    have hc : ContinuousAt (fun t : ℝ => (t,ψ t)) (y 4) :=
      continuousAt_id.prodMk hψa.continuousAt
    change Tendsto (fun t : ℝ => (t,ψ t)) (𝓝 (y 4)) (𝓝 (y 4,ψ (y 4))) at hc
    rw [hψ0] at hc
    exact hc
  have hcurveR := ht.eventually hPR
  obtain ⟨hbpos,hwneg⟩ := M2TangencyData.parameter_signs y ⟨fun i => (hx i).1,fun i => (hx i).2⟩
  have htpos : ∀ᶠ t in 𝓝 (y 4), 0 < t := Ioi_mem_nhds hbpos
  have hwnegative : ∀ᶠ t in 𝓝 (y 4), ψ t < 0 :=
    hψa.continuousAt.eventually (Iio_mem_nhds (by rw [hψ0]; exact hwneg))
  refine ⟨P,ψ,hP0,hPa,hPR,hψ0,hψa,hψder,hstrict,hsign,?_⟩
  filter_upwards [hcurveR,hψroot,htpos,hwnegative] with t ht hz htb htw
  have hzero : zeroMode (P (t,ψ t)) = 0 := hz
  refine ⟨htb,htw,ht,hzero,?_,not_canonical_of_zero _ hzero⟩
  rw [actual_laplace_at_zero,hzero,Complex.ofReal_zero]

/-- Physical data alone construct the boxed contact, joint original root
germ and strict-minimum zero contour with actual local sign classification. -/
theorem exists_actual_strict_minimum_zero_contour :
    ∃ (y : T) (P : Params → E) (ψ : ℝ → ℝ),
      y ∈ Icc M2TangencyData.lower M2TangencyData.upper ∧ system y = 0 ∧ ContourData y P ψ := by
  obtain ⟨y,hy,_⟩ := M2TangencyExistence.exists_unique_system_zero
  obtain ⟨P,ψ,h⟩ := zero_in_box_constructs_joint_zero_contour y (fun i => ⟨hy.1.1 i,hy.1.2 i⟩) hy.2
  exact ⟨y,P,ψ,hy.1,hy.2,h⟩

end FMSA.Convergence.M2JointZeroContour

/-- info: 'FMSA.Convergence.M2JointZeroContour.joint_branch_coupling_geometry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2JointZeroContour.joint_branch_coupling_geometry

/-- info: 'FMSA.Convergence.M2JointZeroContour.joint_branch_weight_geometry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2JointZeroContour.joint_branch_weight_geometry

/-- info: 'FMSA.Convergence.M2JointZeroContour.zero_in_box_constructs_joint_zero_contour' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2JointZeroContour.zero_in_box_constructs_joint_zero_contour

/-- info: 'FMSA.Convergence.M2JointZeroContour.exists_actual_strict_minimum_zero_contour' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2JointZeroContour.exists_actual_strict_minimum_zero_contour
