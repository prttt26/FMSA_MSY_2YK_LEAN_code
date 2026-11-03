import MSAConvergence.PureFluidHFormalSolution
import MSAConvergence.PureFluidActualThetaEquation

/-! The actual pure-fluid MSA inverse-dressing nodes obey the same
denominator-free H equation used by the formal θ-coordinate solution. -/
noncomputable section
open Real Filter Topology
namespace FMSA.Convergence.PureFluidHActualNodeBridge
open FMSA.ExactMSA
open FMSA.Convergence.PureFluidActualThetaEquation
open FMSA.Convergence.PureFluidHFormalSolution
open FMSA.Convergence.PureFluidHardSphereNodePositivity
open FMSA.Convergence.PureFluidActualNodeGerm
open FMSA.Convergence.PureFluidActualDressingCoordinates
open FMSA.Convergence.PureFluidActualGlobalPartialFractions
variable {T : Type*} [Fintype T]

/-- The scalar-value counterpart of the finite formal H-node equation. -/
def HNodeValue (c : T → T → ℝ) (theta H : T → ℝ) : Prop :=
  ∀ s, H s = 1 + ∑ t, c s t * theta t * H s * H t

/-- The original BH tail weight is analytic along every analytic
amplitude germ; the positive node denominators are fixed constants. -/
theorem actualWeight_analyticAt_germ
    (xi : ℝ) (z : T → ℝ)
    (p : ℝ → (T → ℝ) × (T → ℝ)) (hp : AnalyticAt ℝ p 0)
    (t : T) :
    AnalyticAt ℝ (fun tau => actualWeight xi z (p tau).1 (p tau).2 t) 0 := by
  have hD : AnalyticAt ℝ (fun tau => (p tau).1 t) 0 :=
    analyticAt_pi_iff.mp (analyticAt_fst.comp hp) t
  have hG : AnalyticAt ℝ (fun tau => (p tau).2 t) 0 :=
    analyticAt_pi_iff.mp (analyticAt_snd.comp hp) t
  unfold actualWeight tailAlpha MultiTail.W MultiTail.C gam
  fun_prop (disch := first | exact hD | exact hG | positivity)

/-- The true inverse-dressing U at every positive node is analytic along
an analytic original amplitude germ. -/
theorem actualU_node_analyticAt_germ
    (xi : ℝ) (hxi : xi ≠ 1) (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (p : ℝ → (T → ℝ) × (T → ℝ)) (hp : AnalyticAt ℝ p 0)
    (s : T) :
    AnalyticAt ℝ (fun tau => actualU xi z (p tau).1 (p tau).2 (z s)) 0 := by
  have hfun : (fun tau => actualU xi z (p tau).1 (p tau).2 (z s)) =
      (fun tau => PureFluidDressingCandidates.candidateU z
        (actualWeight xi z (p tau).1 (p tau).2) (z s)) := by
    funext tau
    exact actualU_eq_candidateU_explicit xi z (p tau).1 (p tau).2 hxi
      (fun t => (hz t).ne') (z s) (hz s).ne'
      (fun t => (add_pos (hz s) (hz t)).ne')
  rw [hfun]
  unfold PureFluidDressingCandidates.candidateU
  apply analyticAt_const.sub
  have hs : AnalyticAt ℝ (∑ t : T,
      fun tau : ℝ => actualWeight xi z (p tau).1 (p tau).2 t / (z s + z t)) 0 := by
    apply Finset.analyticAt_sum
    intro t _
    exact (actualWeight_analyticAt_germ xi z p hp t).div_const
  have heq : (∑ t : T,
      fun tau : ℝ => actualWeight xi z (p tau).1 (p tau).2 t / (z s + z t)) =
      (fun tau : ℝ => ∑ t : T,
        actualWeight xi z (p tau).1 (p tau).2 t / (z s + z t)) := by
    funext tau
    simp only [Finset.sum_apply]
  rw [← heq]
  exact hs

/-- The actual θ coordinate is analytic along every analytic original
amplitude germ at positive nodes. -/
theorem actualTheta_analyticAt_germ
    (xi : ℝ) (hxi : xi ≠ 1) (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (p : ℝ → (T → ℝ) × (T → ℝ)) (hp : AnalyticAt ℝ p 0)
    (t : T) :
    AnalyticAt ℝ (fun tau => actualTheta xi z (p tau).1 (p tau).2 t) 0 := by
  unfold actualTheta
  exact (actualWeight_analyticAt_germ xi z p hp t).mul
    (actualU_node_analyticAt_germ xi hxi z hz p hp t)

/-- A nonzero seed U node gives an analytic actual H node along the same
original-amplitude germ. -/
theorem actualH_node_analyticAt_germ
    (xi : ℝ) (hxi : xi ≠ 1) (z : T → ℝ) (hz : ∀ t, 0 < z t)
    (p : ℝ → (T → ℝ) × (T → ℝ)) (hp : AnalyticAt ℝ p 0)
    (s : T)
    (hU0 : actualU xi z (p 0).1 (p 0).2 (z s) ≠ 0) :
    AnalyticAt ℝ (fun tau => actualH xi z (p tau).1 (p tau).2 (z s)) 0 := by
  unfold actualH
  exact (actualU_node_analyticAt_germ xi hxi z hz p hp s).inv hU0

/-- At any actual MSA amplitudes with nonzero dressing nodes, the physical
θ and H coordinates satisfy the denominator-free H-node equation. This
does not require distinct rates or an analytic root curve. -/
theorem actual_HNodeValue_all_rates
    (xi : ℝ) (z D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ t, 0 < z t)
    (hU : ∀ t, PureFluidActualDressingCoordinates.actualU xi z D G (z t) ≠ 0) :
    HNodeValue (fun s t => 1 / (z s + z t))
      (actualTheta xi z D G)
      (fun s => actualH xi z D G (z s)) := by
  intro s
  let h : ℝ := actualH xi z D G (z s)
  have hh : h ≠ 0 := by
    dsimp [h, actualH]
    exact inv_ne_zero (hU s)
  have heq := actual_h_equation_all_rates xi z D G hxi hz hU
    (z s) (hz s).ne' (fun t => (add_pos (hz s) (hz t)).ne')
  change h⁻¹ = 1 - ∑ t, actualTheta xi z D G t *
    actualH xi z D G (z t) / (z s + z t) at heq
  have hmul := congrArg (fun q : ℝ => h * q) heq
  rw [mul_inv_cancel₀ hh, mul_sub, mul_one, Finset.mul_sum] at hmul
  have hsolve : h = 1 + ∑ t,
      h * (actualTheta xi z D G t * actualH xi z D G (z t) / (z s + z t)) := by
    linear_combination -hmul
  calc
    actualH xi z D G (z s) = h := rfl
    _ = 1 + ∑ t, h *
        (actualTheta xi z D G t * actualH xi z D G (z t) / (z s + z t)) := hsolve
    _ = 1 + ∑ t, (1 / (z s + z t)) *
        actualTheta xi z D G t * actualH xi z D G (z s) *
        actualH xi z D G (z t) := by
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      dsimp [h]
      ring

/-- The true inverse-dressing H and θ nodes have the formal system's
constant term at the hard-sphere seed. -/
theorem actual_hs_seed_nodes
    (xi : ℝ) (z G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ t, 0 < z t) :
    (∀ t, actualTheta xi z (fun _ => 0) G t = 0) ∧
    (∀ s, actualH xi z (fun _ => 0) G (z s) = 1) := by
  constructor
  · intro t
    exact FMSA.Convergence.PureFluidHDispersion.actualTheta_zero_first_amplitudes
      xi z G t
  · intro s
    unfold actualH
    rw [(actual_dressing_zero_tail xi z G (z s) hxi (hz s).ne').1]
    norm_num

/-- Physical pure-fluid data construct an actual analytic HS root germ on
which the original θ and H values satisfy the same finite node equation as
the unique formal solution. This is a value identity, not yet a statement
about multivariate Taylor coefficients in θ. -/
theorem exists_actual_hs_root_germ_with_HNodeValue
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t) :
    ∃ p : ℝ → (T → ℝ) × (T → ℝ),
      p 0 = ((fun _ => 0), fun t => G0 xi (z t)) ∧
      AnalyticAt ℝ p 0 ∧
      (∀ t, AnalyticAt ℝ
        (fun tau => actualTheta xi z (p tau).1 (p tau).2 t) 0) ∧
      (∀ s, AnalyticAt ℝ
        (fun tau => actualH xi z (p tau).1 (p tau).2 (z s)) 0) ∧
      ∀ᶠ tau : ℝ in 𝓝 0,
        MultiTail.IsRoot xi z (fun t => tau * K t) (p tau).1 (p tau).2 ∧
        HNodeValue (fun s t => 1 / (z s + z t))
          (actualTheta xi z (p tau).1 (p tau).2)
          (fun s => actualH xi z (p tau).1 (p tau).2 (z s)) := by
  obtain ⟨p, hp0, hpa, hfacts⟩ :=
    exists_analytic_hs_root_germ_with_theta_h_equations xi hxi0 hxi1 z K hz
  have hU := actualU_nodes_nonzero_eventually_of_continuous_seed
    xi z hxi1.ne hz p (fun t => G0 xi (z t)) hpa.continuousAt hp0
  refine ⟨p, hp0, hpa, ?_, ?_, ?_⟩
  · intro t
    exact actualTheta_analyticAt_germ xi hxi1.ne z hz p hpa t
  · intro s
    apply actualH_node_analyticAt_germ xi hxi1.ne z hz p hpa s
    have hseed := actual_dressing_zero_tail xi z
      (fun t => G0 xi (z t)) (z s) hxi1.ne (hz s).ne'
    rw [hp0]
    rw [hseed.1]
    norm_num
  · filter_upwards [hfacts, hU] with tau hfact hu
    exact ⟨hfact.1, actual_HNodeValue_all_rates xi z
      (p tau).1 (p tau).2 hxi1.ne hz hu⟩

end FMSA.Convergence.PureFluidHActualNodeBridge

/-- info: 'FMSA.Convergence.PureFluidHActualNodeBridge.actualWeight_analyticAt_germ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHActualNodeBridge.actualWeight_analyticAt_germ
/-- info: 'FMSA.Convergence.PureFluidHActualNodeBridge.actualU_node_analyticAt_germ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHActualNodeBridge.actualU_node_analyticAt_germ
/-- info: 'FMSA.Convergence.PureFluidHActualNodeBridge.actualTheta_analyticAt_germ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHActualNodeBridge.actualTheta_analyticAt_germ
/-- info: 'FMSA.Convergence.PureFluidHActualNodeBridge.actualH_node_analyticAt_germ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHActualNodeBridge.actualH_node_analyticAt_germ
/-- info: 'FMSA.Convergence.PureFluidHActualNodeBridge.actual_HNodeValue_all_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHActualNodeBridge.actual_HNodeValue_all_rates
/-- info: 'FMSA.Convergence.PureFluidHActualNodeBridge.actual_hs_seed_nodes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHActualNodeBridge.actual_hs_seed_nodes
/-- info: 'FMSA.Convergence.PureFluidHActualNodeBridge.exists_actual_hs_root_germ_with_HNodeValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHActualNodeBridge.exists_actual_hs_root_germ_with_HNodeValue
