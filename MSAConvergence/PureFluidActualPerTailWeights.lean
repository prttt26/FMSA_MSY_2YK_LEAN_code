import MSAConvergence.PureFluidActualNodeWeightIdentification

set_option linter.style.header false

/-! Per-tail identification of the actual H-function weights directly
from the true BH W,C node identities. No distinct-rate assumption. -/
noncomputable section
open Real
namespace FMSA.Convergence.PureFluidActualPerTailWeights
open FMSA.ExactMSA
open FMSA.Convergence.PureFluidActualGlobalPartialFractions
open FMSA.Convergence.PureFluidActualDressingCoordinates
open FMSA.Convergence.PureFluidNodeResidues
open FMSA.Convergence.PureFluidExponentialSplit
open FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.Convergence.PureFluidActualNodeWeightIdentification
open FMSA.Convergence.PureFluidDressingCandidates
open FMSA.Convergence.PureFluidNodeClosedForm
variable {T : Type*} [Fintype T]

/-- Exact per-tail alpha identity in the actual hard-sphere basis. The
two arguments are respectively Lambda times S and Lambda times P. -/
theorem tailAlpha_eq_node_U (xi z lam P S : ℝ) (hz : z ≠ 0) :
    tailAlpha (hardA xi) (hardQ xi) z (lam*S) (lam*P) =
      -(lam*dressingU xi z P S) := by
  unfold tailAlpha dressingU dressingD hardP hardShat
  field_simp [hz]
  ring

/-- Companion exact per-tail beta identity. -/
theorem tailBeta_eq_node_gap (xi z lam P S : ℝ) (hz : z ≠ 0) :
    tailBeta (hardA xi) (hardQ xi) z (lam*S) (lam*P) =
      lam*(z*dressingU xi z P S-dressingG xi z P S) := by
  unfold tailBeta dressingU dressingG dressingD hardP hardShat
  field_simp [hz]
  ring

/-- Every individual true-root tail weight equals Lambda_t U(z_t),
including when other indices have exactly the same decay rate. -/
theorem actualWeight_eq_dressedStrength_mul_U_all_rates
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0) (t : T) :
    actualWeight xi z D G t =
      dressedStrength xi z D G t*actualU xi z D G (z t) := by
  have hW := node_W_dressed xi z K D G hz hroot t (hF t)
  have hC := node_C_dressed xi z K D G hz hroot t (hF t)
  unfold actualWeight
  rw [hW,hC]
  rw [tailAlpha_eq_node_U xi (z t) (dressedStrength xi z D G t)
    (rationalPart xi z D G (z t)) (exponentialPart xi z D G (z t)) (hz t).ne']
  simp only [neg_neg]
  rfl

/-- Every individual true-root g numerator has the companion node
expression, with no rate injectivity or grouping. -/
theorem actualGNumerator_eq_dressedStrength_node_all_rates
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0) (t : T) :
    actualGNumerator xi z D G t =
      dressedStrength xi z D G t*
        (z t*actualU xi z D G (z t)-actualG xi z D G (z t)) := by
  have hW := node_W_dressed xi z K D G hz hroot t (hF t)
  have hC := node_C_dressed xi z K D G hz hroot t (hF t)
  unfold actualGNumerator
  rw [hW,hC]
  rw [tailBeta_eq_node_gap xi (z t) (dressedStrength xi z D G t)
    (rationalPart xi z D G (z t)) (exponentialPart xi z D G (z t)) (hz t).ne']
  rfl

/-- The coefficient equation for the actual node ratio holds for every
finite positive-rate family, including coincident rates. -/
theorem actualWeight_mul_node_gap_eq_actualGNumerator_all_rates
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0)
    (hU : ∀ u, actualU xi z D G (z u) ≠ 0) (t : T) :
    actualWeight xi z D G t*(z t-actualNodeR xi z D G t) =
      actualGNumerator xi z D G t := by
  rw [actualWeight_eq_dressedStrength_mul_U_all_rates xi z K D G hz hroot hF t,
    actualGNumerator_eq_dressedStrength_node_all_rates xi z K D G hz hroot hF t]
  unfold actualNodeR
  field_simp [hU t]

/-- The actual g coordinate equals the finite H-function candidate
without requiring pairwise distinct tail rates. -/
theorem actualG_eq_candidateG_root_all_rates
    (xi : ℝ) (z K D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0)
    (hU : ∀ u, actualU xi z D G (z u) ≠ 0)
    (s : ℝ) (hs : s ≠ 0) (hsz : ∀ u, s+z u ≠ 0) :
    actualG xi z D G s =
      candidateG z (actualWeight xi z D G) (actualNodeR xi z D G) s := by
  exact actualG_eq_candidateG_of_coefficients xi z D G (actualNodeR xi z D G)
    hxi (fun u => (hz u).ne')
    (actualWeight_mul_node_gap_eq_actualGNumerator_all_rates xi z K D G
      hz hroot hF hU) s hs hsz

/-- The actual node ratios solve the paper's finite r system even when
several tails share one rate. -/
theorem actualNodeR_solves_linear_system_all_rates
    (xi : ℝ) (z K D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0)
    (hU : ∀ u, actualU xi z D G (z u) ≠ 0) :
    nodeRLinearEquation z (actualWeight xi z D G) (actualNodeR xi z D G) := by
  apply (nodeRLinearEquation_iff_candidate_node _ _ _).2
  intro u
  have hu0 : z u ≠ 0 := (hz u).ne'
  have huz : ∀ v, z u+z v ≠ 0 := fun v => ne_of_gt (add_pos (hz u) (hz v))
  rw [← actualG_eq_candidateG_root_all_rates xi z K D G hxi hz hroot hF hU
      (z u) hu0 huz,
    ← actualU_eq_candidateU_explicit xi z D G hxi
      (fun v => (hz v).ne') (z u) hu0 huz]
  unfold actualNodeR
  field_simp [hU u]

/-- The ORIGINAL BH factor equals the finite H-function candidate for
all finite positive tail-rate families, coincident rates included. -/
theorem actual_factor_eq_candidate_dressing_root_all_rates
    (xi : ℝ) (z K D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0)
    (hU : ∀ u, actualU xi z D G (z u) ≠ 0)
    (s : ℝ) (hs : s ≠ 0) (hsz : ∀ u, s+z u ≠ 0) :
    MultiTail.factor xi z D G s =
      hardDressedFactor xi s
        (candidateU z (actualWeight xi z D G) s)
        (candidateG z (actualWeight xi z D G) (actualNodeR xi z D G) s) := by
  rw [actual_factor_dressing_reconstruction xi z D G s hxi hs,
    actualU_eq_candidateU_explicit xi z D G hxi (fun u => (hz u).ne') s hs hsz,
    actualG_eq_candidateG_root_all_rates xi z K D G hxi hz hroot hF hU s hs hsz]

end FMSA.Convergence.PureFluidActualPerTailWeights
/-- info: 'FMSA.Convergence.PureFluidActualPerTailWeights.tailAlpha_eq_node_U' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualPerTailWeights.tailAlpha_eq_node_U
/-- info: 'FMSA.Convergence.PureFluidActualPerTailWeights.tailBeta_eq_node_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualPerTailWeights.tailBeta_eq_node_gap
/-- info: 'FMSA.Convergence.PureFluidActualPerTailWeights.actualWeight_eq_dressedStrength_mul_U_all_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualPerTailWeights.actualWeight_eq_dressedStrength_mul_U_all_rates
/-- info: 'FMSA.Convergence.PureFluidActualPerTailWeights.actualGNumerator_eq_dressedStrength_node_all_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualPerTailWeights.actualGNumerator_eq_dressedStrength_node_all_rates
/-- info: 'FMSA.Convergence.PureFluidActualPerTailWeights.actualWeight_mul_node_gap_eq_actualGNumerator_all_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualPerTailWeights.actualWeight_mul_node_gap_eq_actualGNumerator_all_rates
/-- info: 'FMSA.Convergence.PureFluidActualPerTailWeights.actualG_eq_candidateG_root_all_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualPerTailWeights.actualG_eq_candidateG_root_all_rates
/-- info: 'FMSA.Convergence.PureFluidActualPerTailWeights.actualNodeR_solves_linear_system_all_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualPerTailWeights.actualNodeR_solves_linear_system_all_rates
/-- info: 'FMSA.Convergence.PureFluidActualPerTailWeights.actual_factor_eq_candidate_dressing_root_all_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualPerTailWeights.actual_factor_eq_candidate_dressing_root_all_rates
