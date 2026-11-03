import MSAConvergence.PureFluidHActualNodeBridge

set_option linter.style.header false

/-! The actual pure-fluid r nodes obey a finite equation in the same
theta and H coordinates as the Chandrasekhar node system. -/
noncomputable section
open Filter Topology
namespace FMSA.Convergence.PureFluidRActualNodeBridge
open FMSA.Convergence.PureFluidDressingCandidates
open FMSA.Convergence.PureFluidActualPerTailWeights
open FMSA.Convergence.PureFluidActualThetaEquation
open FMSA.Convergence.PureFluidActualNodeWeightIdentification
open FMSA.Convergence.PureFluidActualGlobalPartialFractions
open FMSA.Convergence.PureFluidActualDressingCoordinates
open FMSA.Convergence.PureFluidExponentialSplit
open FMSA.Convergence.PureFluidHActualNodeBridge
open FMSA.Convergence.PureFluidActualNodeGerm
open FMSA.ExactMSA
variable {T : Type*} [Fintype T]

def RNodeValue (z theta H r : T → ℝ) : Prop :=
  ∀ s, r s = H s * ∑ t, theta t * H t *
    ((z t - r t) / (z s + z t))

/-- The candidate linear r system becomes the theta/H node equation
where all positive-node U factors are nonzero. -/
theorem nodeRLinearEquation_to_RNodeValue
    (z w r : T → ℝ)
    (hlin : nodeRLinearEquation z w r)
    (hU : ∀ t, candidateU z w (z t) ≠ 0) :
    RNodeValue z
      (fun t => w t * candidateU z w (z t))
      (fun t => (candidateU z w (z t))⁻¹) r := by
  intro s
  have hnode := candidateG_node_eq_U_mul_r z w r hlin s
  unfold candidateG at hnode
  have htheta (t : T) :
      (w t * candidateU z w (z t)) *
        (candidateU z w (z t))⁻¹ = w t := by
    field_simp [hU t]
  calc
    r s = (candidateU z w (z s))⁻¹ *
        (candidateU z w (z s) * r s) := by
          field_simp [hU s]
    _ = (candidateU z w (z s))⁻¹ *
        ∑ t, w t * ((z t - r t) / (z s + z t)) := by
          rw [← hnode]
          congr 1
          apply Finset.sum_congr rfl
          intro t _
          ring
    _ = (candidateU z w (z s))⁻¹ *
        ∑ t, (w t * candidateU z w (z t)) *
          (candidateU z w (z t))⁻¹ *
            ((z t - r t) / (z s + z t)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro t _
          rw [htheta t]

/-- At every genuine pure-fluid BH root with nonzero factor and U nodes,
the original r ratio satisfies the theta/H node equation, including
coincident positive tail rates. -/
theorem actual_RNodeValue_all_rates
    (xi : ℝ) (z K D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ t, 0 < z t)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ t, MultiTail.factor xi z D G (z t) ≠ 0)
    (hU : ∀ t, actualU xi z D G (z t) ≠ 0) :
    RNodeValue z (actualTheta xi z D G)
      (fun t => actualH xi z D G (z t))
      (actualNodeR xi z D G) := by
  let w := actualWeight xi z D G
  have hcandidateU (t : T) :
      candidateU z w (z t) = actualU xi z D G (z t) :=
    (actualU_eq_candidateU_explicit xi z D G hxi
      (fun u => (hz u).ne') (z t) (hz t).ne'
      (fun u => (add_pos (hz t) (hz u)).ne')).symm
  have hc : ∀ t, candidateU z w (z t) ≠ 0 := by
    intro t
    rw [hcandidateU t]
    exact hU t
  have hlin := actualNodeR_solves_linear_system_all_rates
    xi z K D G hxi hz hroot hF hU
  have h := nodeRLinearEquation_to_RNodeValue z w
    (actualNodeR xi z D G) hlin hc
  intro s
  have hs := h s
  simp only [actualTheta, actualH] at hs ⊢
  simp_rw [hcandidateU] at hs
  exact hs

/-- The true off-diagonal dressing coordinate is analytic along an
analytic amplitude germ at each positive node. -/
theorem actualG_node_analyticAt_germ
    (xi : ℝ) (z : T → ℝ)
    (p : ℝ → (T → ℝ) × (T → ℝ)) (hp : AnalyticAt ℝ p 0)
    (s : T) :
    AnalyticAt ℝ
      (fun tau => actualG xi z (p tau).1 (p tau).2 (z s)) 0 := by
  have hD : ∀ t, AnalyticAt ℝ (fun tau => (p tau).1 t) 0 :=
    analyticAt_pi_iff.mp (analyticAt_fst.comp hp)
  have hG : ∀ t, AnalyticAt ℝ (fun tau => (p tau).2 t) 0 :=
    analyticAt_pi_iff.mp (analyticAt_snd.comp hp)
  have hMterm (t : T) : AnalyticAt ℝ
      (fun tau => (p tau).1 t * Mtil xi (z t) ((p tau).2 t)) 0 := by
    apply (hD t).mul
    unfold Mtil gam
    fun_prop (disch := exact hG t)
  have hNterm (t : T) : AnalyticAt ℝ
      (fun tau => (p tau).1 t * Ntil xi (z t) ((p tau).2 t)) 0 := by
    apply (hD t).mul
    unfold Ntil gam
    fun_prop (disch := exact hG t)
  have hM : AnalyticAt ℝ
      (fun tau => MultiTail.momentM xi z (p tau).1 (p tau).2) 0 := by
    unfold MultiTail.momentM
    convert Finset.analyticAt_sum Finset.univ (fun t _ => hMterm t) using 1
    funext tau
    simp only [Finset.sum_apply]
  have hN : AnalyticAt ℝ
      (fun tau => MultiTail.momentN xi z (p tau).1 (p tau).2) 0 := by
    unfold MultiTail.momentN
    convert Finset.analyticAt_sum Finset.univ (fun t _ => hNterm t) using 1
    funext tau
    simp only [Finset.sum_apply]
  have hA : AnalyticAt ℝ
      (fun tau => MultiTail.amplitudeA xi z (p tau).1 (p tau).2) 0 := by
    unfold MultiTail.amplitudeA
    fun_prop (disch := first | exact hM | exact hN)
  have hq : AnalyticAt ℝ
      (fun tau => MultiTail.amplitudeQp xi z (p tau).1 (p tau).2) 0 := by
    unfold MultiTail.amplitudeQp
    fun_prop (disch := first | exact hM | exact hN)
  have hWt (t : T) : AnalyticAt ℝ
      (fun tau => MultiTail.W xi z (p tau).1 (p tau).2 t) 0 := by
    unfold MultiTail.W
    fun_prop (disch := first | exact hD t | exact hG t)
  have hCt (t : T) : AnalyticAt ℝ
      (fun tau => MultiTail.C xi z (p tau).1 (p tau).2 t) 0 := by
    unfold MultiTail.C gam
    fun_prop (disch := first | exact hD t | exact hG t)
  have hPterm (t : T) : AnalyticAt ℝ (fun tau =>
      rhoOf xi * (MultiTail.W xi z (p tau).1 (p tau).2 t /
        (z s + z t) + MultiTail.C xi z (p tau).1 (p tau).2 t /
        (z s))) 0 := by
    exact (analyticAt_const.mul
      ((hWt t).div_const.add (hCt t).div_const))
  have hPsum : AnalyticAt ℝ (fun tau => ∑ t,
      rhoOf xi * (MultiTail.W xi z (p tau).1 (p tau).2 t /
        (z s + z t) + MultiTail.C xi z (p tau).1 (p tau).2 t /
        (z s))) 0 := by
    convert Finset.analyticAt_sum Finset.univ (fun t _ => hPterm t) using 1
    funext tau
    simp only [Finset.sum_apply]
  have hPhead : AnalyticAt ℝ (fun tau =>
      1 - rhoOf xi * MultiTail.amplitudeA xi z (p tau).1 (p tau).2 /
        (z s)^3 +
      rhoOf xi * (MultiTail.amplitudeA xi z (p tau).1 (p tau).2 -
        MultiTail.amplitudeQp xi z (p tau).1 (p tau).2) / (z s)^2 +
      rhoOf xi * (MultiTail.amplitudeQp xi z (p tau).1 (p tau).2 -
        MultiTail.amplitudeA xi z (p tau).1 (p tau).2 / 2) /
        (z s)) 0 := by
    exact (((analyticAt_const.sub
      ((analyticAt_const.mul hA).div_const)).add
      ((analyticAt_const.mul (hA.sub hq)).div_const)).add
      ((analyticAt_const.mul (hq.sub (hA.div_const))).div_const))
  have hP : AnalyticAt ℝ
      (fun tau => rationalPart xi z (p tau).1 (p tau).2 (z s)) 0 := by
    change AnalyticAt ℝ (fun tau =>
      (1 - rhoOf xi * MultiTail.amplitudeA xi z (p tau).1 (p tau).2 /
        (z s)^3 +
      rhoOf xi * (MultiTail.amplitudeA xi z (p tau).1 (p tau).2 -
        MultiTail.amplitudeQp xi z (p tau).1 (p tau).2) / (z s)^2 +
      rhoOf xi * (MultiTail.amplitudeQp xi z (p tau).1 (p tau).2 -
        MultiTail.amplitudeA xi z (p tau).1 (p tau).2 / 2) /
        (z s)) -
      ∑ t, rhoOf xi * (MultiTail.W xi z (p tau).1 (p tau).2 t /
        (z s + z t) + MultiTail.C xi z (p tau).1 (p tau).2 t /
        (z s))) 0
    exact hPhead.sub hPsum
  have hSterm (t : T) : AnalyticAt ℝ (fun tau =>
      rhoOf xi * MultiTail.C xi z (p tau).1 (p tau).2 t *
        (1/(z s)-1/(z s+z t))) 0 := by
    exact ((analyticAt_const.mul (hCt t)).mul analyticAt_const)
  have hSsum : AnalyticAt ℝ (fun tau => ∑ t,
      rhoOf xi * MultiTail.C xi z (p tau).1 (p tau).2 t *
        (1/(z s)-1/(z s+z t))) 0 := by
    convert Finset.analyticAt_sum Finset.univ (fun t _ => hSterm t) using 1
    funext tau
    simp only [Finset.sum_apply]
  have hShead : AnalyticAt ℝ (fun tau =>
      rhoOf xi * MultiTail.amplitudeA xi z (p tau).1 (p tau).2 /
        (z s)^3 +
      rhoOf xi * MultiTail.amplitudeQp xi z (p tau).1 (p tau).2 /
        (z s)^2) 0 := by
    exact ((analyticAt_const.mul hA).div_const).add
      ((analyticAt_const.mul hq).div_const)
  have hS : AnalyticAt ℝ
      (fun tau => exponentialPart xi z (p tau).1 (p tau).2 (z s)) 0 := by
    change AnalyticAt ℝ (fun tau =>
      (rhoOf xi * MultiTail.amplitudeA xi z (p tau).1 (p tau).2 /
        (z s)^3 +
      rhoOf xi * MultiTail.amplitudeQp xi z (p tau).1 (p tau).2 /
        (z s)^2) +
      ∑ t, rhoOf xi * MultiTail.C xi z (p tau).1 (p tau).2 t *
        (1/(z s)-1/(z s+z t))) 0
    exact hShead.add hSsum
  unfold actualG dressingG dressingD
  exact analyticAt_const.mul
    ((analyticAt_const.mul hS).sub (analyticAt_const.mul hP))

/-- The actual r ratio has a genuine analytic coupling germ wherever
its seed U node is nonzero. -/
theorem actualNodeR_analyticAt_germ
    (xi : ℝ) (hxi : xi ≠ 1) (z : T → ℝ)
    (hz : ∀ t, 0 < z t)
    (p : ℝ → (T → ℝ) × (T → ℝ)) (hp : AnalyticAt ℝ p 0)
    (s : T)
    (hU0 : actualU xi z (p 0).1 (p 0).2 (z s) ≠ 0) :
    AnalyticAt ℝ
      (fun tau => actualNodeR xi z (p tau).1 (p tau).2 s) 0 := by
  unfold actualNodeR
  exact (actualG_node_analyticAt_germ xi z p hp s).div
    (actualU_node_analyticAt_germ xi hxi z hz p hp s) hU0

/-- Physical data construct one actual analytic hard-sphere-root germ
where theta, H, and r simultaneously satisfy their node equations. -/
theorem exists_actual_hs_root_germ_with_RNodeValue
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ t, 0 < z t) :
    ∃ p : ℝ → (T → ℝ) × (T → ℝ),
      p 0 = ((fun _ => 0), fun t => G0 xi (z t)) ∧
      AnalyticAt ℝ p 0 ∧
      (∀ t, AnalyticAt ℝ
        (fun tau => actualTheta xi z (p tau).1 (p tau).2 t) 0) ∧
      (∀ t, AnalyticAt ℝ
        (fun tau => actualH xi z (p tau).1 (p tau).2 (z t)) 0) ∧
      (∀ t, AnalyticAt ℝ
        (fun tau => actualNodeR xi z (p tau).1 (p tau).2 t) 0) ∧
      ∀ᶠ tau : ℝ in 𝓝 0,
        MultiTail.IsRoot xi z (fun t => tau * K t)
          (p tau).1 (p tau).2 ∧
        HNodeValue (fun s t => 1 / (z s + z t))
          (actualTheta xi z (p tau).1 (p tau).2)
          (fun t => actualH xi z (p tau).1 (p tau).2 (z t)) ∧
        RNodeValue z
          (actualTheta xi z (p tau).1 (p tau).2)
          (fun t => actualH xi z (p tau).1 (p tau).2 (z t))
          (actualNodeR xi z (p tau).1 (p tau).2) := by
  obtain ⟨p, hp0, hpa, htheta, hH, hrootH⟩ :=
    exists_actual_hs_root_germ_with_HNodeValue xi hxi0 hxi1 z K hz
  have hU := actualU_nodes_nonzero_eventually_of_continuous_seed
    xi z hxi1.ne hz p (fun t => G0 xi (z t)) hpa.continuousAt hp0
  have hF := actual_factor_nodes_nonzero_eventually_of_continuous_seed
    xi hxi0 hxi1 z hz p (fun t => G0 xi (z t)) hpa.continuousAt hp0
  refine ⟨p, hp0, hpa, htheta, hH, ?_, ?_⟩
  · intro t
    apply actualNodeR_analyticAt_germ xi hxi1.ne z hz p hpa t
    rw [hp0]
    rw [(actual_dressing_zero_tail xi z
      (fun u => G0 xi (z u)) (z t) hxi1.ne (hz t).ne').1]
    norm_num
  · filter_upwards [hrootH, hU, hF] with tau hr hu hf
    exact ⟨hr.1, hr.2, actual_RNodeValue_all_rates xi z
      (fun t => tau * K t) (p tau).1 (p tau).2
      hxi1.ne hz hr.1 hf hu⟩

end FMSA.Convergence.PureFluidRActualNodeBridge

/-- info: 'FMSA.Convergence.PureFluidRActualNodeBridge.nodeRLinearEquation_to_RNodeValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRActualNodeBridge.nodeRLinearEquation_to_RNodeValue
/-- info: 'FMSA.Convergence.PureFluidRActualNodeBridge.actual_RNodeValue_all_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRActualNodeBridge.actual_RNodeValue_all_rates
/-- info: 'FMSA.Convergence.PureFluidRActualNodeBridge.actualG_node_analyticAt_germ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRActualNodeBridge.actualG_node_analyticAt_germ
/-- info: 'FMSA.Convergence.PureFluidRActualNodeBridge.actualNodeR_analyticAt_germ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRActualNodeBridge.actualNodeR_analyticAt_germ
/-- info: 'FMSA.Convergence.PureFluidRActualNodeBridge.exists_actual_hs_root_germ_with_RNodeValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidRActualNodeBridge.exists_actual_hs_root_germ_with_RNodeValue
