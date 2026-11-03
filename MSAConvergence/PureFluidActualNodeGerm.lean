import MSAConvergence.PureFluidActualNodeWeightIdentification
import MSAConvergence.PureFluidActualPerTailWeights
import LeanCode.YukawaOZ.MSAMultiTailFamily

set_option linter.style.header false

/-! The actual inverse-dressing node U equals one at the zero-tail
hard-sphere seed and stays nonzero along every continuous seed germ. -/
noncomputable section
open Real Filter Topology
open scoped ContDiff
namespace FMSA.Convergence.PureFluidActualNodeGerm
open FMSA.ExactMSA
open FMSA.Convergence.PureFluidActualGlobalPartialFractions
open FMSA.Convergence.PureFluidActualDressingCoordinates
open FMSA.Convergence.PureFluidDressingCandidates
open FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.Convergence.PureFluidHardSphereNodePositivity
open FMSA.Convergence.PureFluidActualNodeWeightIdentification
open FMSA.Convergence.PureFluidActualPerTailWeights
open FMSA.Convergence.PureFluidNodeClosedForm
variable {T : Type*} [Fintype T]

omit [Fintype T] in
theorem actualWeight_continuous (xi : ℝ) (z : T → ℝ) (u : T) :
    Continuous (fun a : (T → ℝ) × (T → ℝ) =>
      actualWeight xi z a.1 a.2 u) := by
  unfold actualWeight tailAlpha MultiTail.W MultiTail.C gam
  fun_prop

theorem actualU_node_continuous_amplitudes
    (xi : ℝ) (z : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ u, 0 < z u) (t : T) :
    Continuous (fun a : (T → ℝ) × (T → ℝ) =>
      actualU xi z a.1 a.2 (z t)) := by
  have heq : (fun a : (T → ℝ) × (T → ℝ) =>
      actualU xi z a.1 a.2 (z t)) =
      (fun a => candidateU z (actualWeight xi z a.1 a.2) (z t)) := by
    funext a
    exact actualU_eq_candidateU_explicit xi z a.1 a.2 hxi
      (fun u => (hz u).ne') (z t) (hz t).ne'
      (fun u => (add_pos (hz t) (hz u)).ne')
  rw [heq]
  unfold candidateU
  apply continuous_const.sub
  apply continuous_finsetSum
  intro u _
  exact (actualWeight_continuous xi z u).div_const _

/-- Every continuous amplitude path through zero first amplitudes has
nonvanishing true inverse-dressing U at all positive nodes near the seed.
The path need not be an MSA root for this local statement. -/
theorem actualU_nodes_nonzero_eventually_of_continuous_seed
    (xi : ℝ) (z : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ u, 0 < z u)
    (p : ℝ → (T → ℝ) × (T → ℝ)) (G0 : T → ℝ)
    (hp : ContinuousAt p 0) (hp0 : p 0 = ((fun _ => 0),G0)) :
    ∀ᶠ tau : ℝ in 𝓝 0, ∀ t,
      actualU xi z (p tau).1 (p tau).2 (z t) ≠ 0 := by
  apply Filter.eventually_all.mpr
  intro t
  have hc : ContinuousAt (fun tau : ℝ =>
      actualU xi z (p tau).1 (p tau).2 (z t)) 0 :=
    (actualU_node_continuous_amplitudes xi z hxi hz t).continuousAt.comp hp
  have hseed : actualU xi z (p 0).1 (p 0).2 (z t) = 1 := by
    rw [hp0]
    exact (actual_dressing_zero_tail xi z G0 (z t) hxi (hz t).ne').1
  exact hc.eventually_ne (by rw [hseed]; norm_num)

/-- The original BH factor at a fixed positive node depends continuously
on all original first and second tail amplitudes. -/
theorem actual_factor_node_continuous_amplitudes
    (xi : ℝ) (z : T → ℝ) (t : T) :
    Continuous (fun a : (T → ℝ) × (T → ℝ) =>
      MultiTail.factor xi z a.1 a.2 (z t)) := by
  unfold MultiTail.factor MultiTail.Qhat MultiTail.amplitudeA
    MultiTail.amplitudeQp MultiTail.momentM MultiTail.momentN
    MultiTail.W MultiTail.C Mtil Ntil gam
  fun_prop

/-- On every continuous seed germ at physical packing fraction, the
actual factor remains nonzero at all positive tail nodes. -/
theorem actual_factor_nodes_nonzero_eventually_of_continuous_seed
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z : T → ℝ) (hz : ∀ u, 0 < z u)
    (p : ℝ → (T → ℝ) × (T → ℝ)) (G0 : T → ℝ)
    (hp : ContinuousAt p 0) (hp0 : p 0 = ((fun _ => 0),G0)) :
    ∀ᶠ tau : ℝ in 𝓝 0, ∀ t,
      MultiTail.factor xi z (p tau).1 (p tau).2 (z t) ≠ 0 := by
  apply Filter.eventually_all.mpr
  intro t
  have hc : ContinuousAt (fun tau : ℝ =>
      MultiTail.factor xi z (p tau).1 (p tau).2 (z t)) 0 :=
    (actual_factor_node_continuous_amplitudes xi z t).continuousAt.comp hp
  have hseed : MultiTail.factor xi z (p 0).1 (p 0).2 (z t) = F0 xi (z t) := by
    rw [hp0]
    exact MultiTail.factor_zero xi z G0 (z t)
  have hF0 : F0 xi (z t) ≠ 0 := ne_of_gt
    (lt_trans one_pos (actual_F0_gt_one xi (z t) hxi0 hxi1 (hz t)))
  exact hc.eventually_ne (by rw [hseed]; exact hF0)

/-- Any continuous actual MSA root germ through the HS seed satisfies the
paper's finite H-function node system and factor formula near zero
coupling, including coincident rates. The needed node nonvanishing is
proved from continuity. -/
theorem actual_candidate_identification_eventually_on_seed_root_germ
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ u, 0 < z u)
    (p : ℝ → (T → ℝ) × (T → ℝ)) (G0 : T → ℝ)
    (hp : ContinuousAt p 0) (hp0 : p 0 = ((fun _ => 0),G0))
    (hroot : ∀ᶠ tau : ℝ in 𝓝 0,
      MultiTail.IsRoot xi z (fun u => tau*K u) (p tau).1 (p tau).2) :
    ∀ᶠ tau : ℝ in 𝓝 0,
      nodeRLinearEquation z
        (actualWeight xi z (p tau).1 (p tau).2)
        (actualNodeR xi z (p tau).1 (p tau).2) ∧
      ∀ s : ℝ, s ≠ 0 → (∀ u, s+z u ≠ 0) →
        MultiTail.factor xi z (p tau).1 (p tau).2 s =
          hardDressedFactor xi s
            (candidateU z (actualWeight xi z (p tau).1 (p tau).2) s)
            (candidateG z (actualWeight xi z (p tau).1 (p tau).2)
              (actualNodeR xi z (p tau).1 (p tau).2) s) := by
  have hU := actualU_nodes_nonzero_eventually_of_continuous_seed
    xi z hxi1.ne hz p G0 hp hp0
  have hF := actual_factor_nodes_nonzero_eventually_of_continuous_seed
    xi hxi0 hxi1 z hz p G0 hp hp0
  filter_upwards [hroot,hU,hF] with tau hr hu hf
  constructor
  · exact actualNodeR_solves_linear_system_all_rates
      xi z (fun u => tau*K u) (p tau).1 (p tau).2 hxi1.ne hz
      hr hf hu
  · intro s hs hsz
    exact actual_factor_eq_candidate_dressing_root_all_rates
      xi z (fun u => tau*K u) (p tau).1 (p tau).2 hxi1.ne hz
      hr hf hu s hs hsz

/-- Physical pure-fluid data construct a genuine smooth original BH root
germ on which the paper's finite H-function node and factor formulas
hold near zero coupling. No supplied root path or node nonvanishing. -/
theorem exists_actual_hs_root_germ_with_candidate_identification
    (xi : ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1)
    (z K : T → ℝ) (hz : ∀ u, 0 < z u) :
    ∃ p : ℝ → (T → ℝ) × (T → ℝ),
      p 0 = ((fun _ => 0),fun u => G0 xi (z u)) ∧
      ContDiffAt ℝ ∞ p 0 ∧
      (∀ᶠ tau : ℝ in 𝓝 0,
        MultiTail.IsRoot xi z (fun u => tau*K u) (p tau).1 (p tau).2) ∧
      ∀ᶠ tau : ℝ in 𝓝 0,
        nodeRLinearEquation z
          (actualWeight xi z (p tau).1 (p tau).2)
          (actualNodeR xi z (p tau).1 (p tau).2) ∧
        ∀ s : ℝ, s ≠ 0 → (∀ u, s+z u ≠ 0) →
          MultiTail.factor xi z (p tau).1 (p tau).2 s =
            hardDressedFactor xi s
              (candidateU z (actualWeight xi z (p tau).1 (p tau).2) s)
              (candidateG z (actualWeight xi z (p tau).1 (p tau).2)
                (actualNodeR xi z (p tau).1 (p tau).2) s) := by
  obtain ⟨p,hp0,hroot,hsmooth⟩ := MultiTail.exists_contDiffAt_root
    z K ⟨hxi0,hxi1⟩ hz
  have hp0' : p 0 = ((fun _ => 0),fun u => G0 xi (z u)) := by
    have hzero : (0 : T → ℝ) = (fun _ => 0) := by
      funext u
      rfl
    simpa only [hzero] using hp0
  refine ⟨p,hp0',hsmooth,hroot,?_⟩
  exact actual_candidate_identification_eventually_on_seed_root_germ
    xi hxi0 hxi1 z K hz p (fun u => G0 xi (z u))
    hsmooth.continuousAt hp0' hroot

end FMSA.Convergence.PureFluidActualNodeGerm
/-- info: 'FMSA.Convergence.PureFluidActualNodeGerm.actualWeight_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeGerm.actualWeight_continuous
/-- info: 'FMSA.Convergence.PureFluidActualNodeGerm.actualU_node_continuous_amplitudes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeGerm.actualU_node_continuous_amplitudes
/-- info: 'FMSA.Convergence.PureFluidActualNodeGerm.actualU_nodes_nonzero_eventually_of_continuous_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeGerm.actualU_nodes_nonzero_eventually_of_continuous_seed
/-- info: 'FMSA.Convergence.PureFluidActualNodeGerm.actual_factor_node_continuous_amplitudes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeGerm.actual_factor_node_continuous_amplitudes
/-- info: 'FMSA.Convergence.PureFluidActualNodeGerm.actual_factor_nodes_nonzero_eventually_of_continuous_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeGerm.actual_factor_nodes_nonzero_eventually_of_continuous_seed
/-- info: 'FMSA.Convergence.PureFluidActualNodeGerm.actual_candidate_identification_eventually_on_seed_root_germ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeGerm.actual_candidate_identification_eventually_on_seed_root_germ
/-- info: 'FMSA.Convergence.PureFluidActualNodeGerm.exists_actual_hs_root_germ_with_candidate_identification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeGerm.exists_actual_hs_root_germ_with_candidate_identification
