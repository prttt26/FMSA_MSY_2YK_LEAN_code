import MSAConvergence.PureFluidNodeResidues
import MSAConvergence.PureFluidHardSphereNodePositivity

set_option linter.style.header false

/-! Step 3's closed node formulas connected to the ACTUAL pure-fluid BH
root equations, conditional on the still-open global dressing basis.
The formulas themselves use the frozen factor and root definitions. -/
noncomputable section
open Real
namespace FMSA.Convergence.PureFluidNodeClosedForm
open FMSA.ExactMSA
open FMSA.Convergence.PureFluidExponentialSplit
open FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.Convergence.PureFluidHardSphereNodePositivity
open FMSA.Convergence.PureFluidNodeResidues
variable {T : Type*} [Fintype T]

/-- Candidate dressed factor expressed only through the actual PY factor. -/
def hardDressedFactor (xi s U g : ℝ) : ℝ :=
  (U-g/s)*F0 xi s+(g/s)*exp (-s)*F0 xi (-s)

/-- The candidate factor has the node form `F0 U (1-kappa r)` whenever
`g=U r`. -/
theorem hardDressedFactor_eq_node (xi s U r : ℝ) (hs : s ≠ 0)
    (hF0 : F0 xi s ≠ 0) :
    hardDressedFactor xi s U (U*r) = F0 xi s*U*(1-hardKappa xi s*r) := by
  unfold hardDressedFactor hardKappa hardOmega
  field_simp [hs,hF0]
  ring

/-- If the ACTUAL rational and exponential BH pieces have the proposed
dressing basis, their actual factor is the candidate dressed factor. -/
theorem actual_factor_of_dressing_basis
    (xi s U g : ℝ) (z D G : T → ℝ) (hs : s ≠ 0)
    (hP : rationalPart xi z D G s =
      (U-g/s)*hardP xi s+(g/s)*hardShat xi (-s))
    (hS : exponentialPart xi z D G s =
      (U-g/s)*hardShat xi s+(g/s)*hardP xi (-s)) :
    MultiTail.factor xi z D G s = hardDressedFactor xi s U g := by
  rw [factor_split xi z D G s hs, hP, hS]
  unfold hardDressedFactor
  rw [actual_F0_split xi z G s hs,
    actual_F0_split xi z G (-s) (neg_ne_zero.mpr hs)]
  simp only [neg_neg]
  have he : exp (-s)*exp s=1 := by rw [← exp_add]; simp
  linear_combination -(g/s)*hardShat xi (-s)*he

/-- Finite algebra behind the `theta=tauhat/f²` node relation. -/
theorem theta_algebra (rho tau F F0 w U f : ℝ)
    (hF : F ≠ 0) (hF0 : F0 ≠ 0) (hU : U ≠ 0)
    (hLam : rho*tau/F^2 = w/U)
    (hFactor : F = F0*U*f) :
    rho*tau/F0^2 = w*U*f^2 := by
  have heq : rho*tau*U = w*F^2 := by
    apply (div_eq_div_iff (pow_ne_zero 2 hF) hU).mp at hLam
    nlinarith [hLam]
  rw [hFactor] at heq
  have hh : (rho*tau)*U = (w*F0^2*U*f^2)*U := by rw [heq]; ring
  have hcore : rho*tau = w*F0^2*U*f^2 :=
    (mul_right_cancel₀ hU hh)
  apply (div_eq_iff (pow_ne_zero 2 hF0)).mpr
  nlinarith [hcore]

/-- The actual factor's Step 3 node expression, conditional on both
actual split-piece dressing identities. -/
theorem actual_factor_eq_node_of_basis
    (xi s U r : ℝ) (z D G : T → ℝ)
    (hxi0 : 0 < xi) (hxi1 : xi < 1) (hs : 0 < s)
    (hP : rationalPart xi z D G s =
      (U-(U*r)/s)*hardP xi s+((U*r)/s)*hardShat xi (-s))
    (hS : exponentialPart xi z D G s =
      (U-(U*r)/s)*hardShat xi s+((U*r)/s)*hardP xi (-s)) :
    MultiTail.factor xi z D G s = F0 xi s*U*(1-hardKappa xi s*r) := by
  have hF0 : F0 xi s ≠ 0 :=
    ne_of_gt (lt_trans one_pos (actual_F0_gt_one xi s hxi0 hxi1 hs))
  exact (actual_factor_of_dressing_basis xi s U (U*r) z D G
    (ne_of_gt hs) hP hS).trans
      (hardDressedFactor_eq_node xi s U r (ne_of_gt hs) hF0)

/-- The original first BH amplitude obeys the Step 3 node formula once
its actual factor and dressed strength have the proposed representation. -/
theorem actual_D_node_of_dressing
    (xi : ℝ) (z D G : T → ℝ) (t : T)
    (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : 0 < z t)
    (hF : MultiTail.factor xi z D G (z t) ≠ 0)
    (U r w : ℝ) (hU : U ≠ 0)
    (hP : rationalPart xi z D G (z t) =
      (U-(U*r)/(z t))*hardP xi (z t)+
      ((U*r)/(z t))*hardShat xi (-(z t)))
    (hS : exponentialPart xi z D G (z t) =
      (U-(U*r)/(z t))*hardShat xi (z t)+
      ((U*r)/(z t))*hardP xi (-(z t)))
    (hLam : dressedStrength xi z D G t = w/U) :
    rhoOf xi*D t = F0 xi (z t)*w*(1-hardKappa xi (z t)*r) := by
  have hFactor := actual_factor_eq_node_of_basis xi (z t) U r z D G
    hxi0 hxi1 hz hP hS
  unfold dressedStrength at hLam
  have hprod := (div_eq_div_iff hF hU).mp hLam
  rw [hFactor] at hprod
  have hh : (rhoOf xi*D t)*U =
      (F0 xi (z t)*w*(1-hardKappa xi (z t)*r))*U := by
    nlinarith [hprod]
  exact mul_right_cancel₀ hU hh

/-- The actual first BH root equation yields the proposed theta equation,
conditional on the dressing basis and the dressed-strength parameterization. -/
theorem actual_theta_equation_of_dressing
    (xi : ℝ) (z K D G : T → ℝ) (t : T)
    (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : 0 < z t)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : MultiTail.factor xi z D G (z t) ≠ 0)
    (U r w : ℝ) (hU : U ≠ 0)
    (hP : rationalPart xi z D G (z t) =
      (U-(U*r)/(z t))*hardP xi (z t)+
      ((U*r)/(z t))*hardShat xi (-(z t)))
    (hS : exponentialPart xi z D G (z t) =
      (U-(U*r)/(z t))*hardShat xi (z t)+
      ((U*r)/(z t))*hardP xi (-(z t)))
    (hLam : dressedStrength xi z D G t = w/U) :
    rhoOf xi*(2*Real.pi*K t/(z t))/(F0 xi (z t))^2 =
      (w*U)*(1-hardKappa xi (z t)*r)^2 := by
  have hF0 : F0 xi (z t) ≠ 0 :=
    ne_of_gt (lt_trans one_pos (actual_F0_gt_one xi (z t) hxi0 hxi1 hz))
  have hFactor : MultiTail.factor xi z D G (z t) =
      F0 xi (z t)*U*(1-hardKappa xi (z t)*r) :=
    actual_factor_eq_node_of_basis xi (z t) U r z D G
      hxi0 hxi1 hz hP hS
  have hStrength := dressedStrength_eq_coupling xi z K D G hroot t hF
  rw [hLam] at hStrength
  exact theta_algebra (rhoOf xi) (2*Real.pi*K t/(z t))
    (MultiTail.factor xi z D G (z t)) (F0 xi (z t)) w U
    (1-hardKappa xi (z t)*r) hF hF0 hU hStrength.symm hFactor

/-- Pure algebra converting the hard-sphere cross identity and true second
root node relation to the `G-G0` formula. -/
theorem cross_to_G_algebra
    (rho s F F0 S S0 G U r f : ℝ)
    (hs : s ≠ 0) (hρ : rho ≠ 0) (hF0 : F0 ≠ 0)
    (hU : U ≠ 0) (hf : f ≠ 0)
    (hS : S*s = rho*(2*Real.pi*G*F))
    (hCross : S*F0-S0*F = U*r/s)
    (hFactor : F = F0*U*f) :
    (2*Real.pi*rho*F0^2)*(G-s*S0/(2*Real.pi*rho*F0)) = r/f := by
  have hCross' : (S*F0-S0*F)*s = U*r := by
    rw [hCross]
    field_simp [hs]
  have h3 : rho*(2*Real.pi*G*F)*F0-S0*F*s = U*r := by
    linear_combination hCross' - F0*hS
  rw [hFactor] at h3
  have h4 : U*(rho*2*Real.pi*G*F0^2*f-S0*F0*s*f-r)=0 := by
    nlinarith [h3]
  have h5 : rho*2*Real.pi*G*F0^2*f-S0*F0*s*f-r=0 := by
    rcases mul_eq_zero.mp h4 with h|h
    · exact False.elim (hU h)
    · exact h
  rw [eq_div_iff hf]
  field_simp [hρ,hF0,Real.pi_ne_zero]
  nlinarith [h5]

/-- The PY second amplitude read from the true zero-tail node equation. -/
def hardG0Node (xi s : ℝ) : ℝ :=
  s*hardShat xi s/(2*Real.pi*rhoOf xi*F0 xi s)

/-- This `G0` is exactly the second amplitude of any actual zero-tail
root at a positive node. -/
theorem actual_zero_tail_G_eq_hardG0Node
    (xi : ℝ) (z G : T → ℝ) (t : T)
    (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z (fun _ => 0) (fun _ => 0) G) :
    G t = hardG0Node xi (z t) := by
  have hS := node_exponentialPart_eq_G xi z (fun _ => 0) (fun _ => 0) G hz hroot t
  rw [exponentialPart_zero, MultiTail.factor_zero] at hS
  have hρ : rhoOf xi ≠ 0 := by unfold rhoOf; positivity
  have hF0 : F0 xi (z t) ≠ 0 :=
    ne_of_gt (lt_trans one_pos (actual_F0_gt_one xi (z t) hxi0 hxi1 (hz t)))
  unfold hardG0Node
  have hden : 2*Real.pi*rhoOf xi*F0 xi (z t) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hρ) hF0
  rw [eq_div_iff hden]
  field_simp [(hz t).ne'] at hS
  nlinarith [hS]

/-- The ACTUAL second BH root equation, together with the hard-sphere
unimodular cross identity, gives the Step 3 `G-G0` node formula.
The still-open dressing basis is stated as explicit hypotheses. -/
theorem actual_G_node_of_dressing
    (xi : ℝ) (z K D G : T → ℝ) (t : T)
    (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : MultiTail.factor xi z D G (z t) ≠ 0)
    (U r : ℝ) (hU : U ≠ 0)
    (hP : rationalPart xi z D G (z t) =
      (U-(U*r)/(z t))*hardP xi (z t)+
      ((U*r)/(z t))*hardShat xi (-(z t)))
    (hS : exponentialPart xi z D G (z t) =
      (U-(U*r)/(z t))*hardShat xi (z t)+
      ((U*r)/(z t))*hardP xi (-(z t))) :
    (2*Real.pi*rhoOf xi*(F0 xi (z t))^2)*
      (G t-hardG0Node xi (z t)) =
        r/(1-hardKappa xi (z t)*r) := by
  let s := z t
  let f := 1-hardKappa xi s*r
  have hF0 : F0 xi s ≠ 0 :=
    ne_of_gt (lt_trans one_pos (actual_F0_gt_one xi s hxi0 hxi1 (hz t)))
  have hρ : rhoOf xi ≠ 0 := by
    unfold rhoOf
    positivity
  have hFactor : MultiTail.factor xi z D G s = F0 xi s*U*f :=
    actual_factor_eq_node_of_basis xi s U r z D G
      hxi0 hxi1 (hz t) hP hS
  have hf : f ≠ 0 := by
    intro hzero
    apply hF
    rw [hFactor,hzero,mul_zero]
  have hSprod : exponentialPart xi z D G s*s =
      rhoOf xi*(2*Real.pi*G t*MultiTail.factor xi z D G s) := by
    rw [node_exponentialPart_eq_G xi z K D G hz hroot t]
    dsimp only [s]
    field_simp [(hz t).ne']
  have hCross : exponentialPart xi z D G s*F0 xi s-
      hardShat xi s*MultiTail.factor xi z D G s = U*r/s := by
    have hc := actual_hard_dressed_cross_identity
      (T := T) xi s z G U (U*r/s) (ne_of_lt hxi1) (hz t).ne'
    dsimp at hc
    rw [← hP, ← hS] at hc
    rw [← factor_split xi z D G s (hz t).ne'] at hc
    exact hc
  change (2*Real.pi*rhoOf xi*(F0 xi s)^2)*
    (G t-s*hardShat xi s/(2*Real.pi*rhoOf xi*F0 xi s)) = r/f
  exact cross_to_G_algebra (rhoOf xi) s
    (MultiTail.factor xi z D G s) (F0 xi s)
    (exponentialPart xi z D G s) (hardShat xi s) (G t) U r f
    (hz t).ne' hρ hF0 hU hf hSprod hCross hFactor

end FMSA.Convergence.PureFluidNodeClosedForm

/-- info: 'FMSA.Convergence.PureFluidNodeClosedForm.hardDressedFactor_eq_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeClosedForm.hardDressedFactor_eq_node
/-- info: 'FMSA.Convergence.PureFluidNodeClosedForm.actual_factor_of_dressing_basis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeClosedForm.actual_factor_of_dressing_basis
/-- info: 'FMSA.Convergence.PureFluidNodeClosedForm.theta_algebra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeClosedForm.theta_algebra
/-- info: 'FMSA.Convergence.PureFluidNodeClosedForm.actual_factor_eq_node_of_basis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeClosedForm.actual_factor_eq_node_of_basis
/-- info: 'FMSA.Convergence.PureFluidNodeClosedForm.actual_D_node_of_dressing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeClosedForm.actual_D_node_of_dressing
/-- info: 'FMSA.Convergence.PureFluidNodeClosedForm.actual_theta_equation_of_dressing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeClosedForm.actual_theta_equation_of_dressing
/-- info: 'FMSA.Convergence.PureFluidNodeClosedForm.cross_to_G_algebra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeClosedForm.cross_to_G_algebra
/-- info: 'FMSA.Convergence.PureFluidNodeClosedForm.actual_zero_tail_G_eq_hardG0Node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeClosedForm.actual_zero_tail_G_eq_hardG0Node
/-- info: 'FMSA.Convergence.PureFluidNodeClosedForm.actual_G_node_of_dressing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidNodeClosedForm.actual_G_node_of_dressing
