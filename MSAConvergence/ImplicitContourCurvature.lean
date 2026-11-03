import MSAConvergence.M2JointZeroContour

/-! True analytic implicit-contour acceleration and quantitative local
quadratic bounds. Every derivative is obtained by genuine chain rules. -/

noncomputable section
open Set Real Filter Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace FMSA.Convergence.ImplicitContourCurvature

/-- Twice differentiating an ACTUAL analytic zero-contour germ gives its
true acceleration equation. No Hessian or second chain rule is assumed. -/
theorem contour_acceleration_equation (f : ℝ × ℝ → ℝ) (b w kappa d : ℝ)
    (hf : AnalyticAt ℝ f (b,w))
    (haxis : HasDerivAt (deriv (fun t => f (t,w))) kappa b)
    (hweight : HasDerivAt (fun s => f (b,s)) d w)
    (ψ : ℝ → ℝ) (hp0 : ψ b = w) (hpa : AnalyticAt ℝ ψ b)
    (hpv : HasDerivAt ψ 0 b)
    (hroot : ∀ᶠ t in 𝓝 b, f (t,ψ t) = 0) :
    kappa+d*deriv (deriv ψ) b = 0 := by
  let H := fderiv ℝ (fderiv ℝ f) (b,w) (1,0)
  have haxisPair : HasDerivAt (fun t : ℝ => (t,w)) (1,0) b :=
    (hasDerivAt_id b).prodMk (hasDerivAt_const b w)
  have haxisOp : HasDerivAt (fun t => fderiv ℝ f (t,w)) H b :=
    hf.fderiv.differentiableAt.hasFDerivAt.comp_hasDerivAt b haxisPair
  have haxisId : deriv (fun t => f (t,w)) =ᶠ[𝓝 b]
      (fun t => fderiv ℝ f (t,w) (1,0)) := by
    have ht : Tendsto (fun t : ℝ => (t,w)) (𝓝 b) (𝓝 (b,w)) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [ht.eventually hf.eventually_analyticAt] with t ht
    exact (ht.differentiableAt.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t w))).deriv
  have hH : H (1,0) = kappa := by
    have hd := haxisOp.clm_apply (hasDerivAt_const b ((1,0) : ℝ × ℝ))
    have he := (hd.congr_of_eventuallyEq haxisId).unique haxis
    simpa only [map_zero,add_zero] using he
  have hd : fderiv ℝ f (b,w) (0,1) = d :=
    (hf.differentiableAt.hasFDerivAt.comp_hasDerivAt w
      ((hasDerivAt_const w b).prodMk (hasDerivAt_id w))).unique hweight
  have hgamma : HasDerivAt (fun t => (t,ψ t)) (1,0) b :=
    (hasDerivAt_id b).prodMk hpv
  have hAt : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (b,w)) (b,ψ b) := by
    simpa only [hp0] using hf.fderiv.differentiableAt.hasFDerivAt
  have hA : HasDerivAt (fun t => fderiv ℝ f (t,ψ t)) H b :=
    hAt.comp_hasDerivAt b hgamma
  have hV : HasDerivAt (fun t => ((1 : ℝ),deriv ψ t)) (0,deriv (deriv ψ) b) b :=
    (hasDerivAt_const b (1 : ℝ)).prodMk hpa.deriv.differentiableAt.hasDerivAt
  have hprod := hA.clm_apply hV
  have hzero : (fun t => fderiv ℝ f (t,ψ t) (1,deriv ψ t)) =ᶠ[𝓝 b]
      (fun _ => (0 : ℝ)) := by
    have ht : Tendsto (fun t => (t,ψ t)) (𝓝 b) (𝓝 (b,w)) := by
      have hc : ContinuousAt (fun t => (t,ψ t)) b := continuousAt_id.prodMk hpa.continuousAt
      change Tendsto (fun t => (t,ψ t)) (𝓝 b) (𝓝 (b,ψ b)) at hc
      rw [hp0] at hc
      exact hc
    filter_upwards [ht.eventually hf.eventually_analyticAt,hpa.eventually_analyticAt,
      hroot.eventually_nhds] with t hf' hp' hr'
    have hchain := hf'.differentiableAt.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk hp'.differentiableAt.hasDerivAt)
    have hfe : (fun s : ℝ => f (s,ψ s)) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := hr'
    exact (hchain.congr_of_eventuallyEq hfe.symm).unique (hasDerivAt_const t (0 : ℝ))
  have heq := (hprod.congr_of_eventuallyEq hzero.symm).unique (hasDerivAt_const b (0 : ℝ))
  have hlinear : fderiv ℝ f (b,w) (0,deriv (deriv ψ) b) = deriv (deriv ψ) b*d := by
    have h := (fderiv ℝ f (b,w)).map_smul (deriv (deriv ψ) b) ((0,1) : ℝ × ℝ)
    simpa only [Prod.smul_mk,smul_zero,smul_eq_mul,mul_zero,mul_one,hd] using h
  simpa only [hpv.deriv,hp0,hH,hlinear,mul_comm] using heq

/-- The genuine contour second derivative is determined by the true two
axis derivatives, not by an external or assumed Hessian. -/
theorem contour_second_derivative (f : ℝ × ℝ → ℝ) (b w kappa d : ℝ)
    (hf : AnalyticAt ℝ f (b,w))
    (haxis : HasDerivAt (deriv (fun t => f (t,w))) kappa b)
    (hweight : HasDerivAt (fun s => f (b,s)) d w) (hd : d ≠ 0)
    (ψ : ℝ → ℝ) (hp0 : ψ b = w) (hpa : AnalyticAt ℝ ψ b)
    (hpv : HasDerivAt ψ 0 b)
    (hroot : ∀ᶠ t in 𝓝 b, f (t,ψ t) = 0) :
    HasDerivAt (deriv ψ) (-kappa/d) b := by
  have he := contour_acceleration_equation f b w kappa d hf haxis hweight ψ hp0 hpa hpv hroot
  have hv : deriv (deriv ψ) b = -kappa/d := (eq_div_iff hd).mpr (by nlinarith)
  rw [←hv]
  exact hpa.deriv.differentiableAt.hasDerivAt

/-- A true positive second derivative gives a local quadratic lower bound,
with the value at the base point retained exactly. -/
theorem quadratic_lower_bound (f : ℝ → ℝ) (b kappa c : ℝ)
    (hf : AnalyticAt ℝ f b) (h1 : HasDerivAt f 0 b)
    (h2 : HasDerivAt (deriv f) kappa b) (hc : 2*c < kappa) :
    ∀ᶠ t in 𝓝 b, f b+c*(t-b)^2 ≤ f t := by
  let h : ℝ → ℝ := fun t => f t-c*(t-b)^2
  have hq (t : ℝ) : HasDerivAt (fun s : ℝ => c*(s-b)^2) (2*c*(t-b)) t := by
    convert! (((hasDerivAt_id t).sub_const b).pow 2).const_mul c using 1 <;> norm_num <;> ring
  have hh0 : HasDerivAt h 0 b := by
    convert! h1.sub (hq b) using 1 <;> norm_num [h]
  have he : deriv h =ᶠ[𝓝 b] (fun t => deriv f t-2*c*(t-b)) := by
    filter_upwards [hf.eventually_analyticAt] with t ht
    exact (ht.differentiableAt.hasDerivAt.sub (hq t)).deriv
  have hd : HasDerivAt (fun t => deriv f t-2*c*(t-b)) (kappa-2*c) b := by
    convert! h2.sub (((hasDerivAt_id b).sub_const b).const_mul (2*c)) using 1 <;> norm_num
  have hh2 : HasDerivAt (deriv h) (kappa-2*c) b := hd.congr_of_eventuallyEq he
  have hpos : 0 < deriv (deriv h) b := by rw [hh2.deriv]; linarith
  have hm := isLocalMin_of_deriv_deriv_pos hpos hh0.deriv hh0.continuousAt
  change ∀ᶠ t in 𝓝 b, h b ≤ h t at hm
  filter_upwards [hm] with t ht
  norm_num [h] at ht
  linarith

end FMSA.Convergence.ImplicitContourCurvature

/-- info: 'FMSA.Convergence.ImplicitContourCurvature.contour_acceleration_equation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ImplicitContourCurvature.contour_acceleration_equation

/-- info: 'FMSA.Convergence.ImplicitContourCurvature.contour_second_derivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ImplicitContourCurvature.contour_second_derivative

/-- info: 'FMSA.Convergence.ImplicitContourCurvature.quadratic_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.ImplicitContourCurvature.quadratic_lower_bound
