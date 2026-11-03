import MSAConvergence.PureFluidActualGlobalPartialFractions
import MSAConvergence.PureFluidActualDressingPoles

set_option linter.style.header false

/-! Identify the explicit global inverse-dressing pole coefficients with
the actual MSA root's local H-function pole equations. Coincident rates
are compared as groups; individual weights require distinct rates. -/

noncomputable section
open Real Filter Topology Set
namespace FMSA.Convergence.PureFluidActualNodeWeightIdentification
open FMSA.ExactMSA
open FMSA.Convergence.PureFluidActualGlobalPartialFractions
open FMSA.Convergence.PureFluidActualDressingPoles
open FMSA.Convergence.PureFluidCoincidentPoleLimits
open FMSA.Convergence.PureFluidActualDressingCoordinates
open FMSA.Convergence.PureFluidDressingCandidates
open FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.Convergence.PureFluidNodeResidues
open FMSA.Convergence.PureFluidExponentialSplit
open FMSA.Convergence.PureFluidNodeClosedForm
variable {T : Type*} [Fintype T]

/-- Near one negative tail rate, the punctured real axis eventually avoids
the origin and every tail denominator, including repeated-rate poles. -/
theorem eventually_actual_pole_domain (z : T → ℝ)
    (hz : ∀ u, 0 < z u) (t : T) :
    ∀ᶠ s : ℝ in 𝓝[≠] (-z t), s ≠ 0 ∧ ∀ u, s+z u ≠ 0 := by
  have hzero : ∀ᶠ s : ℝ in 𝓝[≠] (-z t), s ≠ 0 :=
    eventually_ne_nhdsWithin (neg_ne_zero.mpr (hz t).ne')
  have hden : ∀ᶠ s : ℝ in 𝓝[≠] (-z t), ∀ u, s+z u ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro u
    by_cases hu : z u = z t
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs : s ≠ -z t := by
        simpa only [mem_compl_iff, mem_singleton_iff] using hs
      rw [hu]
      intro he
      apply hs
      linarith
    · have hpoint : -z t+z u ≠ 0 := by
        intro he
        apply hu
        linarith
      have hc : ContinuousAt (fun s : ℝ => s+z u) (-z t) := by fun_prop
      exact (hc.eventually_ne hpoint).filter_mono nhdsWithin_le_nhds
  exact hzero.and hden

/-- The explicit global U partial fractions have the expected combined
pole limit, with no MSA root hypothesis. -/
theorem actualU_explicit_collected_pole_limit
    (xi : ℝ) (z D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ u, 0 < z u) (t : T) :
    Tendsto (fun s => (s+z t)*actualU xi z D G s)
      (𝓝[≠] (-z t))
      (𝓝 (∑ u ∈ Finset.univ.filter (fun u => z u = z t),
        tailAlpha (hardA xi) (hardQ xi) (z u)
          (rhoOf xi*MultiTail.W xi z D G u)
          (rhoOf xi*MultiTail.C xi z D G u))) := by
  have hlim := finite_coincident_pole_tendsto z
    (fun u _ => tailAlpha (hardA xi) (hardQ xi) (z u)
      (rhoOf xi*MultiTail.W xi z D G u)
      (rhoOf xi*MultiTail.C xi z D G u))
    (fun _ => 1) t (continuousAt_const)
    (fun _ => continuousAt_const)
  have heq : (fun s => (s+z t)*(1+∑ u,
      tailAlpha (hardA xi) (hardQ xi) (z u)
        (rhoOf xi*MultiTail.W xi z D G u)
        (rhoOf xi*MultiTail.C xi z D G u)/(s+z u))) =ᶠ[𝓝[≠] (-z t)]
      (fun s => (s+z t)*actualU xi z D G s) := by
    filter_upwards [eventually_actual_pole_domain z hz t] with s hs
    rw [(actual_dressing_global_partial_fractions xi z D G hxi
      (fun u => (hz u).ne') s hs.1 hs.2).1]
  exact hlim.congr' heq

/-- The companion global g partial fractions have a combined pole limit
without a root hypothesis. -/
theorem actualG_explicit_collected_pole_limit
    (xi : ℝ) (z D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ u, 0 < z u) (t : T) :
    Tendsto (fun s => (s+z t)*actualG xi z D G s)
      (𝓝[≠] (-z t))
      (𝓝 (∑ u ∈ Finset.univ.filter (fun u => z u = z t),
        tailBeta (hardA xi) (hardQ xi) (z u)
          (rhoOf xi*MultiTail.W xi z D G u)
          (rhoOf xi*MultiTail.C xi z D G u))) := by
  have hlim := finite_coincident_pole_tendsto z
    (fun u _ => tailBeta (hardA xi) (hardQ xi) (z u)
      (rhoOf xi*MultiTail.W xi z D G u)
      (rhoOf xi*MultiTail.C xi z D G u))
    (fun _ => 0) t (continuousAt_const)
    (fun _ => continuousAt_const)
  have heq : (fun s => (s+z t)*(0+∑ u,
      tailBeta (hardA xi) (hardQ xi) (z u)
        (rhoOf xi*MultiTail.W xi z D G u)
        (rhoOf xi*MultiTail.C xi z D G u)/(s+z u))) =ᶠ[𝓝[≠] (-z t)]
      (fun s => (s+z t)*actualG xi z D G s) := by
    filter_upwards [eventually_actual_pole_domain z hz t] with s hs
    rw [(actual_dressing_global_partial_fractions xi z D G hxi
      (fun u => (hz u).ne') s hs.1 hs.2).2]
    ring
  exact hlim.congr' heq

/-- At a true MSA root, the sum of explicit U coefficients at each rate
is exactly the total dressed strength times the true positive-node U. -/
theorem actualU_collected_coefficient_eq_root_node
    (xi : ℝ) (z K D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0) (t : T) :
    (∑ u ∈ Finset.univ.filter (fun u => z u = z t),
      tailAlpha (hardA xi) (hardQ xi) (z u)
        (rhoOf xi*MultiTail.W xi z D G u)
        (rhoOf xi*MultiTail.C xi z D G u)) =
      -(collectedStrength xi z D G t*actualU xi z D G (z t)) := by
  exact tendsto_nhds_unique
    (actualU_explicit_collected_pole_limit xi z D G hxi hz t)
    (actualU_collected_pole_limit xi z K D G hz hroot hF t)

/-- Companion grouped coefficient identity for the true g coordinate. -/
theorem actualG_collected_coefficient_eq_root_node
    (xi : ℝ) (z K D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0) (t : T) :
    (∑ u ∈ Finset.univ.filter (fun u => z u = z t),
      tailBeta (hardA xi) (hardQ xi) (z u)
        (rhoOf xi*MultiTail.W xi z D G u)
        (rhoOf xi*MultiTail.C xi z D G u)) =
      collectedStrength xi z D G t*
        (z t*actualU xi z D G (z t)-actualG xi z D G (z t)) := by
  exact tendsto_nhds_unique
    (actualG_explicit_collected_pole_limit xi z D G hxi hz t)
    (actualG_collected_pole_limit xi z K D G hz hroot hF t)

/-- If the rates are distinct, each matching-rate fiber is a singleton. -/
theorem matching_rate_sum_eq_of_injective (z : T → ℝ)
    (hzinj : Function.Injective z) (f : T → ℝ) (t : T) :
    (∑ u ∈ Finset.univ.filter (fun u => z u = z t), f u) = f t := by
  classical
  have hset : Finset.univ.filter (fun u => z u = z t) = {t} := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    exact ⟨fun h => hzinj h,fun hu => by rw [hu]⟩
  rw [hset]
  simp

/-- At distinct rates the explicit inverse-U weight is the true dressed
strength times the actual positive-node U value. -/
theorem actualWeight_eq_dressedStrength_mul_U
    (xi : ℝ) (z K D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ u, 0 < z u)
    (hzinj : Function.Injective z)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0) (t : T) :
    actualWeight xi z D G t =
      dressedStrength xi z D G t*actualU xi z D G (z t) := by
  have h := actualU_collected_coefficient_eq_root_node
    xi z K D G hxi hz hroot hF t
  rw [matching_rate_sum_eq_of_injective z hzinj,
    collectedStrength_eq_of_injective xi z D G hzinj t] at h
  unfold actualWeight
  linarith

/-- At distinct rates the explicit g numerator has the true root's
H-function node value. -/
theorem actualGNumerator_eq_dressedStrength_node
    (xi : ℝ) (z K D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ u, 0 < z u)
    (hzinj : Function.Injective z)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0) (t : T) :
    actualGNumerator xi z D G t =
      dressedStrength xi z D G t*
        (z t*actualU xi z D G (z t)-actualG xi z D G (z t)) := by
  have h := actualG_collected_coefficient_eq_root_node
    xi z K D G hxi hz hroot hF t
  rw [matching_rate_sum_eq_of_injective z hzinj,
    collectedStrength_eq_of_injective xi z D G hzinj t] at h
  exact h

/-- The node ratio is defined only as a totalized real expression; the
theorems using it explicitly assume true-node U does not vanish. -/
def actualNodeR (xi : ℝ) (z D G : T → ℝ) (t : T) : ℝ :=
  actualG xi z D G (z t)/actualU xi z D G (z t)

/-- The actual root's two identified pole coefficients satisfy exactly
the coefficient equation needed by the paper's candidate g. -/
theorem actualWeight_mul_node_gap_eq_actualGNumerator
    (xi : ℝ) (z K D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ u, 0 < z u)
    (hzinj : Function.Injective z)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0)
    (hU : ∀ u, actualU xi z D G (z u) ≠ 0) (t : T) :
    actualWeight xi z D G t*(z t-actualNodeR xi z D G t) =
      actualGNumerator xi z D G t := by
  rw [actualWeight_eq_dressedStrength_mul_U xi z K D G hxi hz hzinj hroot hF t,
    actualGNumerator_eq_dressedStrength_node xi z K D G hxi hz hzinj hroot hF t]
  unfold actualNodeR
  field_simp [hU t]

/-- Under distinct rates and nonvanishing positive-node U, the actual
g coordinate equals the paper's finite candidate for the actual weights
and actual node ratios, away from zero and the finite negative poles. -/
theorem actualG_eq_candidateG_root
    (xi : ℝ) (z K D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ u, 0 < z u)
    (hzinj : Function.Injective z)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0)
    (hU : ∀ u, actualU xi z D G (z u) ≠ 0)
    (s : ℝ) (hs : s ≠ 0) (hsz : ∀ u, s+z u ≠ 0) :
    actualG xi z D G s =
      candidateG z (actualWeight xi z D G) (actualNodeR xi z D G) s := by
  exact actualG_eq_candidateG_of_coefficients xi z D G (actualNodeR xi z D G)
    hxi (fun u => (hz u).ne')
    (actualWeight_mul_node_gap_eq_actualGNumerator xi z K D G
      hxi hz hzinj hroot hF hU) s hs hsz

/-- The actual node ratios solve the paper's finite linear r system
under the same distinct-rate and nonvanishing-node hypotheses. -/
theorem actualNodeR_solves_linear_system
    (xi : ℝ) (z K D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ u, 0 < z u)
    (hzinj : Function.Injective z)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0)
    (hU : ∀ u, actualU xi z D G (z u) ≠ 0) :
    nodeRLinearEquation z (actualWeight xi z D G) (actualNodeR xi z D G) := by
  apply (nodeRLinearEquation_iff_candidate_node _ _ _).2
  intro u
  have hu0 : z u ≠ 0 := (hz u).ne'
  have huz : ∀ v, z u+z v ≠ 0 := fun v => ne_of_gt (add_pos (hz u) (hz v))
  rw [← actualG_eq_candidateG_root xi z K D G hxi hz hzinj hroot hF hU
      (z u) hu0 huz,
    ← actualU_eq_candidateU_explicit xi z D G hxi
      (fun v => (hz v).ne') (z u) hu0 huz]
  unfold actualNodeR
  field_simp [hU u]

/-- Conditional global identification of the ORIGINAL rational BH piece
with the explicit finite H-function dressing candidate. -/
theorem actual_rational_eq_candidate_root
    (xi : ℝ) (z K D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ u, 0 < z u)
    (hzinj : Function.Injective z)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0)
    (hU : ∀ u, actualU xi z D G (z u) ≠ 0)
    (s : ℝ) (hs : s ≠ 0) (hsz : ∀ u, s+z u ≠ 0) :
    rationalPart xi z D G s =
      candidateRational xi s
        (candidateU z (actualWeight xi z D G) s)
        (candidateG z (actualWeight xi z D G) (actualNodeR xi z D G) s) := by
  rw [actual_rational_dressing_reconstruction xi z D G s hxi hs,
    actualU_eq_candidateU_explicit xi z D G hxi (fun u => (hz u).ne') s hs hsz,
    actualG_eq_candidateG_root xi z K D G hxi hz hzinj hroot hF hU s hs hsz]

/-- Companion identification of the ORIGINAL exponential BH piece. -/
theorem actual_exponential_eq_candidate_root
    (xi : ℝ) (z K D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ u, 0 < z u)
    (hzinj : Function.Injective z)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0)
    (hU : ∀ u, actualU xi z D G (z u) ≠ 0)
    (s : ℝ) (hs : s ≠ 0) (hsz : ∀ u, s+z u ≠ 0) :
    exponentialPart xi z D G s =
      candidateExponential xi s
        (candidateU z (actualWeight xi z D G) s)
        (candidateG z (actualWeight xi z D G) (actualNodeR xi z D G) s) := by
  rw [actual_exponential_dressing_reconstruction xi z D G s hxi hs,
    actualU_eq_candidateU_explicit xi z D G hxi (fun u => (hz u).ne') s hs hsz,
    actualG_eq_candidateG_root xi z K D G hxi hz hzinj hroot hF hU s hs hsz]

/-- The original BH factor has the paper's finite H-function dressing
form under the explicit distinct-rate and node-nonvanishing hypotheses. -/
theorem actual_factor_eq_candidate_dressing_root
    (xi : ℝ) (z K D G : T → ℝ)
    (hxi : xi ≠ 1) (hz : ∀ u, 0 < z u)
    (hzinj : Function.Injective z)
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
    actualG_eq_candidateG_root xi z K D G hxi hz hzinj hroot hF hU s hs hsz]

end FMSA.Convergence.PureFluidActualNodeWeightIdentification
/-- info: 'FMSA.Convergence.PureFluidActualNodeWeightIdentification.eventually_actual_pole_domain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeWeightIdentification.eventually_actual_pole_domain
/-- info: 'FMSA.Convergence.PureFluidActualNodeWeightIdentification.actualU_explicit_collected_pole_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeWeightIdentification.actualU_explicit_collected_pole_limit
/-- info: 'FMSA.Convergence.PureFluidActualNodeWeightIdentification.actualG_explicit_collected_pole_limit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeWeightIdentification.actualG_explicit_collected_pole_limit
/-- info: 'FMSA.Convergence.PureFluidActualNodeWeightIdentification.actualU_collected_coefficient_eq_root_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeWeightIdentification.actualU_collected_coefficient_eq_root_node
/-- info: 'FMSA.Convergence.PureFluidActualNodeWeightIdentification.actualG_collected_coefficient_eq_root_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeWeightIdentification.actualG_collected_coefficient_eq_root_node
/-- info: 'FMSA.Convergence.PureFluidActualNodeWeightIdentification.matching_rate_sum_eq_of_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeWeightIdentification.matching_rate_sum_eq_of_injective
/-- info: 'FMSA.Convergence.PureFluidActualNodeWeightIdentification.actualWeight_eq_dressedStrength_mul_U' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeWeightIdentification.actualWeight_eq_dressedStrength_mul_U
/-- info: 'FMSA.Convergence.PureFluidActualNodeWeightIdentification.actualGNumerator_eq_dressedStrength_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeWeightIdentification.actualGNumerator_eq_dressedStrength_node
/-- info: 'FMSA.Convergence.PureFluidActualNodeWeightIdentification.actualWeight_mul_node_gap_eq_actualGNumerator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeWeightIdentification.actualWeight_mul_node_gap_eq_actualGNumerator
/-- info: 'FMSA.Convergence.PureFluidActualNodeWeightIdentification.actualG_eq_candidateG_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeWeightIdentification.actualG_eq_candidateG_root
/-- info: 'FMSA.Convergence.PureFluidActualNodeWeightIdentification.actualNodeR_solves_linear_system' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeWeightIdentification.actualNodeR_solves_linear_system
/-- info: 'FMSA.Convergence.PureFluidActualNodeWeightIdentification.actual_rational_eq_candidate_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeWeightIdentification.actual_rational_eq_candidate_root
/-- info: 'FMSA.Convergence.PureFluidActualNodeWeightIdentification.actual_exponential_eq_candidate_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeWeightIdentification.actual_exponential_eq_candidate_root
/-- info: 'FMSA.Convergence.PureFluidActualNodeWeightIdentification.actual_factor_eq_candidate_dressing_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualNodeWeightIdentification.actual_factor_eq_candidate_dressing_root
