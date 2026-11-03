import MSAConvergence.PureFluidDressingCandidates

set_option linter.style.header false

/-! Algebraic pole-coefficient matching for the proposed pure-fluid
dressing. `formalPoleP/S` are explicit coefficients obtained by
substituting `s=-z_t` into the candidate's one-pole numerator; an
analytic residue-limit theorem is still required to identify them as
actual residues of the full finite sum. -/
noncomputable section
open Real
namespace FMSA.Convergence.PureFluidCandidatePoleCoefficients
open FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.Convergence.PureFluidDressingCandidates
variable {T : Type*} [Fintype T]

/-- Numerator of the rational candidate's individual `1/(s+z)` term. -/
def poleNumeratorP (xi s z w r : ℝ) : ℝ :=
  -w*(1+(z-r)/s)*hardP xi s+
    w*((z-r)/s)*hardShat xi (-s)

/-- Companion exponential numerator. -/
def poleNumeratorS (xi s z w r : ℝ) : ℝ :=
  -w*(1+(z-r)/s)*hardShat xi s+
    w*((z-r)/s)*hardP xi (-s)

/-- Expected rational-piece coefficient at a candidate `-z` pole. -/
def formalPoleP (xi z w r : ℝ) : ℝ :=
  -w*((r/z)*hardP xi (-z)+(1-r/z)*hardShat xi z)

/-- Expected exponential-piece coefficient at a candidate `-z` pole. -/
def formalPoleS (xi z w r : ℝ) : ℝ :=
  -w*((r/z)*hardShat xi (-z)+(1-r/z)*hardP xi z)

/-- Evaluating the rational one-pole numerator at `s=-z` gives the formal coefficient. -/
theorem poleNumeratorP_at_pole (xi z w r : ℝ) (hz : z ≠ 0) :
    poleNumeratorP xi (-z) z w r = formalPoleP xi z w r := by
  unfold poleNumeratorP formalPoleP
  field_simp [hz]
  ring

/-- Companion exponential numerator evaluation. -/
theorem poleNumeratorS_at_pole (xi z w r : ℝ) (hz : z ≠ 0) :
    poleNumeratorS xi (-z) z w r = formalPoleS xi z w r := by
  unfold poleNumeratorS formalPoleS
  field_simp [hz]
  ring

private theorem dressing_sum_linear (p q s : ℝ) (A B : T → ℝ) :
    ((1-∑ t, A t)-(∑ t, B t)/s)*p+((∑ t, B t)/s)*q =
      p+∑ t, (-A t*p+(B t/s)*(q-p)) := by
  simp only [Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_mul]
  rw [Finset.sum_neg_distrib]
  ring

/-- Exact full finite-pole decomposition of the candidate rational piece. -/
theorem candidateRational_partial_fraction (xi s : ℝ) (z w r : T → ℝ) :
    candidateRational xi s (candidateU z w s) (candidateG z w r s) =
      hardP xi s+∑ t, poleNumeratorP xi s (z t) (w t) (r t)/(s+z t) := by
  unfold candidateRational candidateU candidateG
  rw [dressing_sum_linear (hardP xi s) (hardShat xi (-s)) s
    (fun t => w t/(s+z t)) (fun t => w t*(z t-r t)/(s+z t))]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  unfold poleNumeratorP
  ring

/-- Exact full finite-pole decomposition of the candidate exponential piece. -/
theorem candidateExponential_partial_fraction (xi s : ℝ) (z w r : T → ℝ) :
    candidateExponential xi s (candidateU z w s) (candidateG z w r s) =
      hardShat xi s+∑ t, poleNumeratorS xi s (z t) (w t) (r t)/(s+z t) := by
  unfold candidateExponential candidateU candidateG
  rw [dressing_sum_linear (hardShat xi s) (hardP xi (-s)) s
    (fun t => w t/(s+z t)) (fun t => w t*(z t-r t)/(s+z t))]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  unfold poleNumeratorS
  ring

/-- The expected rational coefficient equals the Step 1 cross-node
coefficient after `Lambda=w/U`. -/
theorem formalPoleP_eq_cross_node (xi z w U r : ℝ)
    (hz : z ≠ 0) (hU : U ≠ 0) :
    formalPoleP xi z w r = -(w/U)*candidateExponential xi z U (U*r) := by
  rw [candidate_node_exponential]
  unfold formalPoleP
  field_simp [hz,hU]
  ring

/-- Companion expected exponential coefficient identity. -/
theorem formalPoleS_eq_cross_node (xi z w U r : ℝ)
    (hz : z ≠ 0) (hU : U ≠ 0) :
    formalPoleS xi z w r = -(w/U)*candidateRational xi z U (U*r) := by
  rw [candidate_node_rational]
  unfold formalPoleS
  field_simp [hz,hU]
  ring

/-- Substitute the actual candidate finite sums and `r` linear system. -/
theorem formalPoleP_eq_candidate_node
    (xi : ℝ) (z w r : T → ℝ) (hlin : nodeRLinearEquation z w r)
    (t : T) (hz : z t ≠ 0) (hU : candidateU z w (z t) ≠ 0) :
    formalPoleP xi (z t) (w t) (r t) =
      -(w t/candidateU z w (z t))*
        candidateExponential xi (z t) (candidateU z w (z t))
          (candidateG z w r (z t)) := by
  rw [candidateG_node_eq_U_mul_r z w r hlin t]
  exact formalPoleP_eq_cross_node xi (z t) (w t)
    (candidateU z w (z t)) (r t) hz hU

/-- Companion candidate exponential coefficient matching. -/
theorem formalPoleS_eq_candidate_node
    (xi : ℝ) (z w r : T → ℝ) (hlin : nodeRLinearEquation z w r)
    (t : T) (hz : z t ≠ 0) (hU : candidateU z w (z t) ≠ 0) :
    formalPoleS xi (z t) (w t) (r t) =
      -(w t/candidateU z w (z t))*
        candidateRational xi (z t) (candidateU z w (z t))
          (candidateG z w r (z t)) := by
  rw [candidateG_node_eq_U_mul_r z w r hlin t]
  exact formalPoleS_eq_cross_node xi (z t) (w t)
    (candidateU z w (z t)) (r t) hz hU

end FMSA.Convergence.PureFluidCandidatePoleCoefficients

/-- info: 'FMSA.Convergence.PureFluidCandidatePoleCoefficients.poleNumeratorP_at_pole' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidatePoleCoefficients.poleNumeratorP_at_pole
/-- info: 'FMSA.Convergence.PureFluidCandidatePoleCoefficients.poleNumeratorS_at_pole' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidatePoleCoefficients.poleNumeratorS_at_pole
/-- info: 'FMSA.Convergence.PureFluidCandidatePoleCoefficients.candidateRational_partial_fraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidatePoleCoefficients.candidateRational_partial_fraction
/-- info: 'FMSA.Convergence.PureFluidCandidatePoleCoefficients.candidateExponential_partial_fraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidatePoleCoefficients.candidateExponential_partial_fraction
/-- info: 'FMSA.Convergence.PureFluidCandidatePoleCoefficients.formalPoleP_eq_cross_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidatePoleCoefficients.formalPoleP_eq_cross_node
/-- info: 'FMSA.Convergence.PureFluidCandidatePoleCoefficients.formalPoleS_eq_cross_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidatePoleCoefficients.formalPoleS_eq_cross_node
/-- info: 'FMSA.Convergence.PureFluidCandidatePoleCoefficients.formalPoleP_eq_candidate_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidatePoleCoefficients.formalPoleP_eq_candidate_node
/-- info: 'FMSA.Convergence.PureFluidCandidatePoleCoefficients.formalPoleS_eq_candidate_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidCandidatePoleCoefficients.formalPoleS_eq_candidate_node
