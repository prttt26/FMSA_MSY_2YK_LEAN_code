import MSAConvergence.PureFluidActualAnalyticGerm

set_option linter.style.header false

/-! The physical pure-fluid BH root satisfies the finite theta and H node
equations in its actual inverse-dressing coordinates. Coincident tail rates
are permitted. These are value identities; coefficient positivity is later. -/
noncomputable section
open Real Filter Topology
namespace FMSA.Convergence.PureFluidActualThetaEquation
open FMSA.ExactMSA
open FMSA.Convergence.PureFluidActualPerTailWeights
open FMSA.Convergence.PureFluidActualGlobalPartialFractions
open FMSA.Convergence.PureFluidActualNodeWeightIdentification
open FMSA.Convergence.PureFluidDressingCandidates
open FMSA.Convergence.PureFluidNodeClosedForm
open FMSA.Convergence.PureFluidNodeResidues
open FMSA.Convergence.PureFluidHardSphereNodePositivity
open FMSA.Convergence.PureFluidActualDressingCoordinates
open FMSA.Convergence.PureFluidActualAnalyticGerm
open FMSA.Convergence.PureFluidActualNodeGerm
variable {T : Type*} [Fintype T]

def actualTheta (xi : ℝ) (z D G : T → ℝ) (t : T) : ℝ :=
  actualWeight xi z D G t*actualU xi z D G (z t)

def actualH (xi : ℝ) (z D G : T → ℝ) (s : ℝ) : ℝ :=
  (actualU xi z D G s)⁻¹

/-- The factor at a true node is the closed H-coordinate factor. -/
theorem actual_factor_eq_closed_node_all_rates
    (xi : ℝ) (z K D G : T → ℝ)
    (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0)
    (hU : ∀ u, actualU xi z D G (z u) ≠ 0) (t : T) :
    MultiTail.factor xi z D G (z t) =
      F0 xi (z t)*actualU xi z D G (z t)*
        (1-hardKappa xi (z t)*actualNodeR xi z D G t) := by
  have hlin := actualNodeR_solves_linear_system_all_rates
    xi z K D G (ne_of_lt hxi1) hz hroot hF hU
  have hnode := candidateG_node_eq_U_mul_r z
    (actualWeight xi z D G) (actualNodeR xi z D G) hlin t
  have hUeq := actualU_eq_candidateU_explicit xi z D G
    (ne_of_lt hxi1) (fun u => (hz u).ne') (z t) (hz t).ne'
    (fun u => (add_pos (hz t) (hz u)).ne')
  have hfactor := actual_factor_eq_candidate_dressing_root_all_rates
    xi z K D G (ne_of_lt hxi1) hz hroot hF hU
    (z t) (hz t).ne' (fun u => (add_pos (hz t) (hz u)).ne')
  rw [hnode] at hfactor
  rw [← hUeq] at hfactor
  exact hfactor.trans (hardDressedFactor_eq_node xi (z t)
    (actualU xi z D G (z t))
    (actualNodeR xi z D G t) (hz t).ne'
    (ne_of_gt (lt_trans one_pos
      (actual_F0_gt_one xi (z t) hxi0 hxi1 (hz t)))))

/-- The actual first BH equation is exactly the paper's theta node equation,
with no distinct-rate premise or supplied dressing-basis equations. -/
theorem actual_theta_equation_all_rates
    (xi : ℝ) (z K D G : T → ℝ)
    (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0)
    (hU : ∀ u, actualU xi z D G (z u) ≠ 0) (t : T) :
    rhoOf xi*(2*Real.pi*K t/z t)/(F0 xi (z t))^2 =
      actualTheta xi z D G t*
        (1-hardKappa xi (z t)*actualNodeR xi z D G t)^2 := by
  have hF0 : F0 xi (z t) ≠ 0 := ne_of_gt
    (lt_trans one_pos (actual_F0_gt_one xi (z t) hxi0 hxi1 (hz t)))
  have hweight := actualWeight_eq_dressedStrength_mul_U_all_rates
    xi z K D G hz hroot hF t
  have hstrength := dressedStrength_eq_coupling xi z K D G hroot t (hF t)
  have hLam : rhoOf xi*(2*Real.pi*K t/z t)/
      (MultiTail.factor xi z D G (z t))^2 =
      actualWeight xi z D G t/actualU xi z D G (z t) := by
    rw [← hstrength,hweight]
    field_simp [hU t]
  have hfac := actual_factor_eq_closed_node_all_rates
    xi z K D G hxi0 hxi1 hz hroot hF hU t
  simpa only [actualTheta] using theta_algebra
    (rhoOf xi) (2*Real.pi*K t/z t)
    (MultiTail.factor xi z D G (z t)) (F0 xi (z t))
    (actualWeight xi z D G t) (actualU xi z D G (z t))
    (1-hardKappa xi (z t)*actualNodeR xi z D G t)
    (hF t) hF0 (hU t) hLam hfac

/-- The actual H inverse obeys the finite Chandrasekhar equation wherever
the rational coordinates are defined and the node U values are nonzero.
The reciprocal uses Lean's totalized inverse at a possible off-node zero. -/
theorem actual_h_equation_all_rates
    (xi : ℝ) (z D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ t, 0 < z t)
    (hU : ∀ t, actualU xi z D G (z t) ≠ 0)
    (s : ℝ) (hs : s ≠ 0) (hsz : ∀ t, s+z t ≠ 0) :
    (actualH xi z D G s)⁻¹ =
      1-∑ t, actualTheta xi z D G t*
        actualH xi z D G (z t)/(s+z t) := by
  unfold actualH actualTheta
  simp only [inv_inv]
  rw [actualU_eq_candidateU_explicit xi z D G hxi
    (fun t => (hz t).ne') s hs hsz]
  unfold candidateU
  apply congrArg (fun x : ℝ => 1-x)
  apply Finset.sum_congr rfl
  intro t _
  field_simp [hU t]

/-- The genuine analytic HS-seeded root germ satisfies both the theta
node equation and finite H equation near zero coupling. No root path,
factor nonvanishing or node U nonvanishing is supplied by the caller. -/
theorem exists_analytic_hs_root_germ_with_theta_h_equations
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ u, 0 < z u) :
    ∃ p : ℝ → (T → ℝ) × (T → ℝ),
      p 0 = ((fun _ => 0),fun u => G0 xi (z u)) ∧
      AnalyticAt ℝ p 0 ∧
      ∀ᶠ tau : ℝ in 𝓝 0,
        MultiTail.IsRoot xi z (fun u => tau*K u) (p tau).1 (p tau).2 ∧
        (∀ t, rhoOf xi*(2*Real.pi*(tau*K t)/z t)/(F0 xi (z t))^2 =
          actualTheta xi z (p tau).1 (p tau).2 t*
            (1-hardKappa xi (z t)*
              actualNodeR xi z (p tau).1 (p tau).2 t)^2) ∧
        ∀ s : ℝ, 0 < s →
          (actualH xi z (p tau).1 (p tau).2 s)⁻¹ =
            1-∑ t, actualTheta xi z (p tau).1 (p tau).2 t*
              actualH xi z (p tau).1 (p tau).2 (z t)/(s+z t) := by
  obtain ⟨p,hp0,hpa,hroot,_⟩ :=
    exists_analytic_hs_root_germ_with_candidate_identification
      xi hxi0 hxi1 z K hz
  have hU := actualU_nodes_nonzero_eventually_of_continuous_seed
    xi z hxi1.ne hz p (fun u => G0 xi (z u)) hpa.continuousAt hp0
  have hF := actual_factor_nodes_nonzero_eventually_of_continuous_seed
    xi hxi0 hxi1 z hz p (fun u => G0 xi (z u)) hpa.continuousAt hp0
  refine ⟨p,hp0,hpa,?_⟩
  filter_upwards [hroot,hU,hF] with tau hr hu hf
  refine ⟨hr,?_,?_⟩
  · intro t
    exact actual_theta_equation_all_rates xi z (fun u => tau*K u)
      (p tau).1 (p tau).2 hxi0 hxi1 hz hr hf hu t
  · intro s hs
    exact actual_h_equation_all_rates xi z (p tau).1 (p tau).2
      hxi1.ne hz hu s hs.ne' (fun t => (add_pos hs (hz t)).ne')

end FMSA.Convergence.PureFluidActualThetaEquation
/-- info: 'FMSA.Convergence.PureFluidActualThetaEquation.actual_factor_eq_closed_node_all_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualThetaEquation.actual_factor_eq_closed_node_all_rates
/-- info: 'FMSA.Convergence.PureFluidActualThetaEquation.actual_theta_equation_all_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualThetaEquation.actual_theta_equation_all_rates
/-- info: 'FMSA.Convergence.PureFluidActualThetaEquation.actual_h_equation_all_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualThetaEquation.actual_h_equation_all_rates
/-- info: 'FMSA.Convergence.PureFluidActualThetaEquation.exists_analytic_hs_root_germ_with_theta_h_equations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualThetaEquation.exists_analytic_hs_root_germ_with_theta_h_equations
