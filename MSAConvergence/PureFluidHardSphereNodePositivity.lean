import MSAConvergence.PureFluidHardSphereUnimodular

set_option linter.style.header false

/-! Exact node inequalities for the frozen pure-fluid PY factor. The proof
uses the strict exponential tangent bound, not a new analytic axiom. -/
noncomputable section
open Real Set
namespace FMSA.Convergence.PureFluidHardSphereNodePositivity

def nodeGap (z : ℝ) : ℝ := z - 2 + (z + 2) * exp (-z)

/-- Strict positivity of the elementary gap equivalent to
`tanh (z/2) < z/2`, proved directly with the exponential tangent bound. -/
theorem nodeGap_pos (z : ℝ) (hz : 0 < z) : 0 < nodeGap z := by
  have hder (x : ℝ) : deriv nodeGap x = 1 - (x + 1) * exp (-x) := by
    have hd := (((hasDerivAt_id x).sub_const 2).add
      (((hasDerivAt_id x).add_const 2).mul
        ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x))))
    have hd' : HasDerivAt nodeGap (1 - (x+1)*exp (-x)) x := by
      have hfun : nodeGap = (fun y : ℝ => y - 2 + (y + 2) * exp (-y)) := rfl
      have hfun' : (fun y : ℝ => y - 2 + (y + 2) * exp (-y)) =
          (fun y : ℝ => id y - 2) + (fun y : ℝ => id y + 2) * (exp ∘ Neg.neg) := by
        funext y
        simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply, id_eq, Neg.neg]
      have hcoef : 1 + (1 * (exp ∘ Neg.neg) x + (id x + 2) *
          (exp (-x) * -1)) = 1 - (x+1)*exp (-x) := by
        simp only [Function.comp_apply, id_eq]
        ring
      rw [hcoef, ← hfun', ← hfun] at hd
      exact hd
    exact hd'.deriv
  have hm : StrictMonoOn nodeGap (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by unfold nodeGap; fun_prop)
    intro x hx
    have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
    have hxexp : x + 1 < exp x := Real.add_one_lt_exp (ne_of_gt hx0)
    have hmul : (x + 1) * exp (-x) < 1 := by
      calc
        (x + 1) * exp (-x) < exp x * exp (-x) :=
          mul_lt_mul_of_pos_right hxexp (exp_pos _)
        _ = 1 := by rw [← exp_add]; simp
    rw [hder]
    linarith
  have h := hm (by simp : (0:ℝ) ∈ Ici 0) (by simpa using hz.le) hz
  simpa [nodeGap] using h

/-- The form of the positive gap used by the actual PY identity. -/
theorem basic_gap_pos (z : ℝ) (hz : 0 < z) :
    0 < z * (1 + exp (-z)) - 2 * (1 - exp (-z)) := by
  convert nodeGap_pos z hz using 1
  unfold nodeGap
  ring

/-- The paper's node difference formula derived from the actual frozen
`F0`, rather than assumed as a hard-sphere identity. -/
theorem actual_F0_gap_identity (xi z : ℝ) (hxi : xi ≠ 1) (hz : z ≠ 0) :
    FMSA.ExactMSA.F0 xi z - exp (-z) * FMSA.ExactMSA.F0 xi (-z) =
      (1 - exp (-z)) + (6*xi/(1-xi)) *
        (z*(1+exp (-z))-2*(1-exp (-z)))/z^2 := by
  have h1 : 1-xi ≠ 0 := by intro h; apply hxi; linarith
  have he : exp z = (exp (-z))⁻¹ := by rw [exp_neg]; simp
  unfold FMSA.ExactMSA.F0 FMSA.ExactMSA.Qhat0 FMSA.ExactMSA.phi1
    FMSA.ExactMSA.phi2 FMSA.ExactMSA.rhoOf FMSA.ExactMSA.qp0
    FMSA.ExactMSA.bA0
  simp only [neg_neg, he]
  field_simp [hz, h1, Real.pi_ne_zero, (exp_pos (-z)).ne']
  ring

/-- The actual factor at a positive node exceeds its reflected value
multiplied by the exterior exponential. -/
theorem actual_F0_gap_pos (xi z : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (hz : 0 < z) :
    0 < FMSA.ExactMSA.F0 xi z - exp (-z) * FMSA.ExactMSA.F0 xi (-z) := by
  have hxi : xi ≠ 1 := ne_of_lt hxi1
  rw [actual_F0_gap_identity xi z hxi (ne_of_gt hz)]
  have he : exp (-z) < 1 := exp_lt_one_iff.mpr (by linarith)
  have hA : 0 < 6*xi/(1-xi) := div_pos (by positivity) (by linarith)
  have hd : 0 < (6*xi/(1-xi))*(z*(1+exp (-z))-2*(1-exp (-z)))/z^2 :=
    div_pos (mul_pos hA (basic_gap_pos z hz)) (sq_pos_of_pos hz)
  exact add_pos (sub_pos.mpr he) hd

/-- The first frozen BH transform is strictly negative at positive rate. -/
theorem phi1_neg (z : ℝ) (hz : 0 < z) : FMSA.ExactMSA.phi1 z < 0 := by
  have he : -z + 1 < exp (-z) := Real.add_one_lt_exp (neg_ne_zero.mpr (ne_of_gt hz))
  unfold FMSA.ExactMSA.phi1
  apply div_neg_of_neg_of_pos
  · linarith
  · exact sq_pos_of_pos hz

/-- The useful second transform combination equals minus the positive gap
divided by `z^3`. -/
theorem phi1_plus_two_phi2_neg (z : ℝ) (hz : 0 < z) :
    FMSA.ExactMSA.phi1 z + 2*FMSA.ExactMSA.phi2 z < 0 := by
  have h : FMSA.ExactMSA.phi1 z + 2*FMSA.ExactMSA.phi2 z =
      -(z*(1+exp (-z))-2*(1-exp (-z)))/z^3 := by
    unfold FMSA.ExactMSA.phi1 FMSA.ExactMSA.phi2
    field_simp [(ne_of_gt hz)]
    ring
  rw [h]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (basic_gap_pos z hz)) (pow_pos hz _)

/-- An exact frozen PY coefficient relation used to sign the factor. -/
theorem qp_minus_half_A (xi : ℝ) (hxi : xi ≠ 1) :
    FMSA.ExactMSA.qp0 xi - FMSA.ExactMSA.bA0 xi/2 = Real.pi/(1-xi) := by
  have h1 : 1-xi ≠ 0 := by intro h; apply hxi; linarith
  unfold FMSA.ExactMSA.qp0 FMSA.ExactMSA.bA0
  field_simp [h1]
  ring

/-- The actual hard-sphere factor exceeds one at every positive node for
physical packing fraction `0 < xi < 1`. -/
theorem actual_F0_gt_one (xi z : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (hz : 0 < z) : 1 < FMSA.ExactMSA.F0 xi z := by
  have hxi : xi ≠ 1 := ne_of_lt hxi1
  have hq : 0 < FMSA.ExactMSA.qp0 xi - FMSA.ExactMSA.bA0 xi/2 := by
    rw [qp_minus_half_A xi hxi]
    exact div_pos Real.pi_pos (by linarith)
  have ha : 0 < FMSA.ExactMSA.bA0 xi/2 := by
    unfold FMSA.ExactMSA.bA0
    have h1 : 1-xi ≠ 0 := by intro h; apply hxi; linarith
    positivity
  have hQ : FMSA.ExactMSA.Qhat0 xi z < 0 := by
    have heq : FMSA.ExactMSA.Qhat0 xi z =
        (FMSA.ExactMSA.qp0 xi - FMSA.ExactMSA.bA0 xi/2)*FMSA.ExactMSA.phi1 z +
        (FMSA.ExactMSA.bA0 xi/2)*(FMSA.ExactMSA.phi1 z+2*FMSA.ExactMSA.phi2 z) := by
      unfold FMSA.ExactMSA.Qhat0
      ring
    rw [heq]
    exact add_neg (mul_neg_of_pos_of_neg hq (phi1_neg z hz))
      (mul_neg_of_pos_of_neg ha (phi1_plus_two_phi2_neg z hz))
  have hρ : 0 < FMSA.ExactMSA.rhoOf xi := by
    unfold FMSA.ExactMSA.rhoOf
    positivity
  unfold FMSA.ExactMSA.F0
  nlinarith [mul_neg_of_pos_of_neg hρ hQ]

/-- The frozen rational definition uses totalized division at zero,
and therefore has value one there. The analytic removable-singularity
extension invoked in the paper has a different value at zero. -/
theorem actual_F0_at_zero (xi : ℝ) : FMSA.ExactMSA.F0 xi 0 = 1 := by
  simp [FMSA.ExactMSA.F0, FMSA.ExactMSA.Qhat0,
    FMSA.ExactMSA.phi1, FMSA.ExactMSA.phi2]

def hardOmega (xi z : ℝ) : ℝ :=
  exp (-z)*FMSA.ExactMSA.F0 xi (-z)/FMSA.ExactMSA.F0 xi z

def hardKappa (xi z : ℝ) : ℝ := (1-hardOmega xi z)/z

/-- The actual PY node ratio is strictly below one. -/
theorem hardOmega_lt_one (xi z : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (hz : 0 < z) : hardOmega xi z < 1 := by
  have hF : 0 < FMSA.ExactMSA.F0 xi z := lt_trans one_pos (actual_F0_gt_one xi z hxi0 hxi1 hz)
  rw [hardOmega, div_lt_iff₀ hF]
  linarith [actual_F0_gap_pos xi z hxi0 hxi1 hz]

/-- The `κ` parameter of the proposed pure-fluid dressing is positive at
every positive tail rate. This is Step 4's usable node statement. -/
theorem hardKappa_pos (xi z : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (hz : 0 < z) : 0 < hardKappa xi z := by
  exact div_pos (sub_pos.mpr (hardOmega_lt_one xi z hxi0 hxi1 hz)) hz

end FMSA.Convergence.PureFluidHardSphereNodePositivity

/-- info: 'FMSA.Convergence.PureFluidHardSphereNodePositivity.nodeGap_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereNodePositivity.nodeGap_pos
/-- info: 'FMSA.Convergence.PureFluidHardSphereNodePositivity.basic_gap_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereNodePositivity.basic_gap_pos
/-- info: 'FMSA.Convergence.PureFluidHardSphereNodePositivity.actual_F0_gap_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereNodePositivity.actual_F0_gap_identity
/-- info: 'FMSA.Convergence.PureFluidHardSphereNodePositivity.actual_F0_gap_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereNodePositivity.actual_F0_gap_pos
/-- info: 'FMSA.Convergence.PureFluidHardSphereNodePositivity.phi1_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereNodePositivity.phi1_neg
/-- info: 'FMSA.Convergence.PureFluidHardSphereNodePositivity.phi1_plus_two_phi2_neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereNodePositivity.phi1_plus_two_phi2_neg
/-- info: 'FMSA.Convergence.PureFluidHardSphereNodePositivity.qp_minus_half_A' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereNodePositivity.qp_minus_half_A
/-- info: 'FMSA.Convergence.PureFluidHardSphereNodePositivity.actual_F0_gt_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereNodePositivity.actual_F0_gt_one
/-- info: 'FMSA.Convergence.PureFluidHardSphereNodePositivity.actual_F0_at_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereNodePositivity.actual_F0_at_zero
/-- info: 'FMSA.Convergence.PureFluidHardSphereNodePositivity.hardOmega_lt_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereNodePositivity.hardOmega_lt_one
/-- info: 'FMSA.Convergence.PureFluidHardSphereNodePositivity.hardKappa_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereNodePositivity.hardKappa_pos
