import MSAConvergence.PureFluidExactResidueForm
import MSAConvergence.PureFluidNodeClosedForm

set_option linter.style.header false

/-! The explicit finite-sum candidate `U,g` from the paper's pure-fluid
dressing construction. The linear `r` equation is exactly equivalent to
its node identity `g(z_t)=U(z_t)r_t`. This does not identify the candidate
with an actual BH root; that is a later global comparison theorem. -/
noncomputable section
open Real
open scoped BigOperators
namespace FMSA.Convergence.PureFluidDressingCandidates
open FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.Convergence.PureFluidNodeClosedForm
variable {T : Type*} [Fintype T]

/-- Candidate Chandrasekhar factor's reciprocal rational piece. -/
def candidateU (z w : T → ℝ) (s : ℝ) : ℝ :=
  1 - ∑ t, w t/(s+z t)

/-- Candidate off-diagonal dressing function, called `g` in the paper. -/
def candidateG (z w r : T → ℝ) (s : ℝ) : ℝ :=
  ∑ t, w t*(z t-r t)/(s+z t)

/-- The finite linear system defining the candidate `r_t`. -/
def nodeRLinearEquation (z w r : T → ℝ) : Prop :=
  ∀ u, r u - ∑ t, w t*(r u-r t)/(z u+z t) =
    ∑ t, w t*z t/(z u+z t)

/-- Every solution of the paper's `r` linear system obeys `g_t=U_t r_t`. -/
theorem candidateG_node_eq_U_mul_r
    (z w r : T → ℝ) (hlin : nodeRLinearEquation z w r) (u : T) :
    candidateG z w r (z u) = candidateU z w (z u)*r u := by
  have hu := hlin u
  unfold candidateG candidateU
  have hterm (t : T) : w t*(z t-r t)/(z u+z t) =
      w t*z t/(z u+z t)-w t*r t/(z u+z t) := by ring
  have hterm2 (t : T) : w t*(r u-r t)/(z u+z t) =
      (w t/(z u+z t))*r u-w t*r t/(z u+z t) := by ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  simp_rw [hterm2] at hu
  rw [Finset.sum_sub_distrib] at hu
  rw [← Finset.sum_mul] at hu
  linear_combination -hu

/-- The node condition is equivalent to the entire finite linear system,
without assuming distinct or positive rates. -/
theorem nodeRLinearEquation_iff_candidate_node
    (z w r : T → ℝ) :
    nodeRLinearEquation z w r ↔
      ∀ u, candidateG z w r (z u) = candidateU z w (z u)*r u := by
  constructor
  · intro h u
    exact candidateG_node_eq_U_mul_r z w r h u
  · intro h u
    have hu := h u
    unfold candidateG candidateU at hu
    have hterm (t : T) : w t*(z t-r t)/(z u+z t) =
        w t*z t/(z u+z t)-w t*r t/(z u+z t) := by ring
    have hterm2 (t : T) : w t*(r u-r t)/(z u+z t) =
        (w t/(z u+z t))*r u-w t*r t/(z u+z t) := by ring
    simp_rw [hterm] at hu
    rw [Finset.sum_sub_distrib] at hu
    simp_rw [hterm2]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    linear_combination -hu

/-- Proposed rational dressing in the actual hard-sphere basis. -/
def candidateRational (xi s U g : ℝ) : ℝ :=
  (U-g/s)*hardP xi s+(g/s)*hardShat xi (-s)

/-- Proposed exponential coefficient in the actual hard-sphere basis. -/
def candidateExponential (xi s U g : ℝ) : ℝ :=
  (U-g/s)*hardShat xi s+(g/s)*hardP xi (-s)

/-- Algebraic node form of the proposed rational dressing. -/
theorem candidate_node_rational (xi s U r : ℝ) :
    candidateRational xi s U (U*r) =
      U*((1-r/s)*hardP xi s+(r/s)*hardShat xi (-s)) := by
  unfold candidateRational
  ring

/-- Algebraic node form of the proposed exponential dressing. -/
theorem candidate_node_exponential (xi s U r : ℝ) :
    candidateExponential xi s U (U*r) =
      U*((1-r/s)*hardShat xi s+(r/s)*hardP xi (-s)) := by
  unfold candidateExponential
  ring

/-- Substituting the finite-sum `U,g` and linear `r` system gives the
rational node expression used in the residue comparison. -/
theorem candidateRational_at_node
    (xi : ℝ) (z w r : T → ℝ) (hlin : nodeRLinearEquation z w r) (u : T) :
    candidateRational xi (z u) (candidateU z w (z u))
      (candidateG z w r (z u)) =
      candidateU z w (z u)*
        ((1-r u/(z u))*hardP xi (z u)+
          (r u/(z u))*hardShat xi (-(z u))) := by
  rw [candidateG_node_eq_U_mul_r z w r hlin u]
  exact candidate_node_rational xi (z u) (candidateU z w (z u)) (r u)

/-- Companion exponential node expression. -/
theorem candidateExponential_at_node
    (xi : ℝ) (z w r : T → ℝ) (hlin : nodeRLinearEquation z w r) (u : T) :
    candidateExponential xi (z u) (candidateU z w (z u))
      (candidateG z w r (z u)) =
      candidateU z w (z u)*
        ((1-r u/(z u))*hardShat xi (z u)+
          (r u/(z u))*hardP xi (-(z u))) := by
  rw [candidateG_node_eq_U_mul_r z w r hlin u]
  exact candidate_node_exponential xi (z u) (candidateU z w (z u)) (r u)

end FMSA.Convergence.PureFluidDressingCandidates

/-- info: 'FMSA.Convergence.PureFluidDressingCandidates.candidateG_node_eq_U_mul_r' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidDressingCandidates.candidateG_node_eq_U_mul_r
/-- info: 'FMSA.Convergence.PureFluidDressingCandidates.nodeRLinearEquation_iff_candidate_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidDressingCandidates.nodeRLinearEquation_iff_candidate_node
/-- info: 'FMSA.Convergence.PureFluidDressingCandidates.candidate_node_rational' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidDressingCandidates.candidate_node_rational
/-- info: 'FMSA.Convergence.PureFluidDressingCandidates.candidate_node_exponential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidDressingCandidates.candidate_node_exponential
/-- info: 'FMSA.Convergence.PureFluidDressingCandidates.candidateRational_at_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidDressingCandidates.candidateRational_at_node
/-- info: 'FMSA.Convergence.PureFluidDressingCandidates.candidateExponential_at_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidDressingCandidates.candidateExponential_at_node
