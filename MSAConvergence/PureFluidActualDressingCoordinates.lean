import MSAConvergence.PureFluidCandidateOriginConstraint

set_option linter.style.header false

/-! Canonical hard-sphere dressing coordinates recovered from the ACTUAL
pure-fluid BH rational and exponential pieces. Unimodularity gives an
exact global reconstruction and uniqueness at every nonzero real
frequency. These coordinates are not yet identified with the paper's
finite-sum candidate U,g. -/

noncomputable section
open Real
namespace FMSA.Convergence.PureFluidActualDressingCoordinates
open FMSA.ExactMSA
open FMSA.Convergence.PureFluidExponentialSplit
open FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.Convergence.PureFluidDressingCandidates
open FMSA.Convergence.PureFluidNodeClosedForm
open FMSA.Convergence.PureFluidNodeResidues
variable {T : Type*} [Fintype T]

/-- The off-diagonal coordinate g/s of a pair of factor pieces. -/
def dressingD (xi s P S : ℝ) : ℝ := hardP xi s*S-hardShat xi s*P

/-- The diagonal coordinate U of a pair of factor pieces. -/
def dressingU (xi s P S : ℝ) : ℝ :=
  hardP xi (-s)*P-hardShat xi (-s)*S+dressingD xi s P S

/-- The undivided off-diagonal coordinate g. -/
def dressingG (xi s P S : ℝ) : ℝ := s*dressingD xi s P S

/-- The frozen hard-sphere basis reconstructs any two real factor pieces
from their unique dressing coordinates at nonzero frequency. -/
theorem generic_dressing_reconstruction (xi s P S : ℝ)
    (hxi : xi ≠ 1) (hs : s ≠ 0) :
    candidateRational xi s (dressingU xi s P S)
      (dressingG xi s P S) = P ∧
    candidateExponential xi s (dressingU xi s P S)
      (dressingG xi s P S) = S := by
  have hd : dressingG xi s P S/s=dressingD xi s P S := by
    unfold dressingG
    field_simp [hs]
  have hdet := hard_unimodular xi s hxi hs
  constructor
  · unfold candidateRational dressingU
    rw [hd]
    unfold dressingD
    linear_combination P*hdet
  · unfold candidateExponential dressingU
    rw [hd]
    unfold dressingD
    linear_combination S*hdet

/-- Any proposed U,g representation in the frozen hard-sphere basis
must equal the inverse coordinates. -/
theorem generic_dressing_unique (xi s P S U g : ℝ)
    (hxi : xi ≠ 1) (hs : s ≠ 0)
    (hP : candidateRational xi s U g = P)
    (hS : candidateExponential xi s U g = S) :
    dressingU xi s P S = U ∧ dressingG xi s P S = g := by
  have hdet := hard_unimodular xi s hxi hs
  have hD : dressingD xi s P S = g/s := by
    rw [← hP, ← hS]
    unfold dressingD candidateRational candidateExponential
    linear_combination (g/s)*hdet
  have hV : hardP xi (-s)*P-hardShat xi (-s)*S = U-g/s := by
    rw [← hP, ← hS]
    unfold candidateRational candidateExponential
    linear_combination (U-g/s)*hdet
  constructor
  · unfold dressingU
    rw [hD]
    linarith [hV]
  · unfold dressingG
    rw [hD]
    field_simp [hs]

/-- Inverse diagonal dressing coordinate of the actual BH pieces. -/
def actualU (xi : ℝ) (z D G : T → ℝ) (s : ℝ) : ℝ :=
  dressingU xi s (rationalPart xi z D G s) (exponentialPart xi z D G s)

/-- Inverse off-diagonal dressing coordinate of the actual BH pieces. -/
def actualG (xi : ℝ) (z D G : T → ℝ) (s : ℝ) : ℝ :=
  dressingG xi s (rationalPart xi z D G s) (exponentialPart xi z D G s)

/-- The actual rational BH piece has an exact inverse-basis representation. -/
theorem actual_rational_dressing_reconstruction
    (xi : ℝ) (z D G : T → ℝ) (s : ℝ)
    (hxi : xi ≠ 1) (hs : s ≠ 0) :
    rationalPart xi z D G s =
      candidateRational xi s (actualU xi z D G s) (actualG xi z D G s) := by
  exact (generic_dressing_reconstruction xi s
    (rationalPart xi z D G s) (exponentialPart xi z D G s) hxi hs).1.symm

/-- The actual exponential BH piece has the companion representation. -/
theorem actual_exponential_dressing_reconstruction
    (xi : ℝ) (z D G : T → ℝ) (s : ℝ)
    (hxi : xi ≠ 1) (hs : s ≠ 0) :
    exponentialPart xi z D G s =
      candidateExponential xi s (actualU xi z D G s) (actualG xi z D G s) := by
  exact (generic_dressing_reconstruction xi s
    (rationalPart xi z D G s) (exponentialPart xi z D G s) hxi hs).2.symm

/-- The original BH factor equals the hard-sphere dressed factor
formed from the inverse coordinates. -/
theorem actual_factor_dressing_reconstruction
    (xi : ℝ) (z D G : T → ℝ) (s : ℝ)
    (hxi : xi ≠ 1) (hs : s ≠ 0) :
    MultiTail.factor xi z D G s =
      hardDressedFactor xi s (actualU xi z D G s)
        (actualG xi z D G s) := by
  exact actual_factor_of_dressing_basis xi s
    (actualU xi z D G s) (actualG xi z D G s)
    z D G hs
    (actual_rational_dressing_reconstruction xi z D G s hxi hs)
    (actual_exponential_dressing_reconstruction xi z D G s hxi hs)

/-- The actual inverse off-diagonal coordinate is the true BH/PY
factor cross difference times frequency. -/
theorem actualG_cross_identity (xi : ℝ) (z D G : T → ℝ)
    (s : ℝ) (hs : s ≠ 0) :
    actualG xi z D G s =
      s*(exponentialPart xi z D G s*F0 xi s-
        hardShat xi s*MultiTail.factor xi z D G s) := by
  rw [factor_split xi z D G s hs,
    actual_F0_split xi z G s hs]
  unfold actualG dressingG dressingD
  ring

/-- At a genuine BH root node, the inverse off-diagonal coordinate
is expressed directly through the original second amplitude. -/
theorem actualG_at_root_node
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ t, 0 < z t)
    (hroot : MultiTail.IsRoot xi z K D G) (t : T) :
    actualG xi z D G (z t) =
      MultiTail.factor xi z D G (z t)*
        (rhoOf xi*(2*Real.pi*G t*F0 xi (z t))-
          z t*hardShat xi (z t)) := by
  rw [actualG_cross_identity xi z D G (z t) (hz t).ne',
    node_exponentialPart_eq_G xi z K D G hz hroot t]
  field_simp [(hz t).ne']

/-- At zero original tail amplitudes, the inverse coordinates are
exactly the hard-sphere seed U=1 and g=0. -/
theorem actual_dressing_zero_tail
    (xi : ℝ) (z G : T → ℝ) (s : ℝ)
    (hxi : xi ≠ 1) (hs : s ≠ 0) :
    actualU xi z (fun _ => 0) G s = 1 ∧
      actualG xi z (fun _ => 0) G s = 0 := by
  have hP : candidateRational xi s 1 0 =
      rationalPart xi z (fun _ => 0) G s := by
    rw [rationalPart_zero]
    simp [candidateRational]
  have hS : candidateExponential xi s 1 0 =
      exponentialPart xi z (fun _ => 0) G s := by
    rw [exponentialPart_zero]
    simp [candidateExponential]
  exact generic_dressing_unique xi s
    (rationalPart xi z (fun _ => 0) G s)
    (exponentialPart xi z (fun _ => 0) G s) 1 0 hxi hs hP hS

end FMSA.Convergence.PureFluidActualDressingCoordinates
/-- info: 'FMSA.Convergence.PureFluidActualDressingCoordinates.generic_dressing_reconstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualDressingCoordinates.generic_dressing_reconstruction
/-- info: 'FMSA.Convergence.PureFluidActualDressingCoordinates.generic_dressing_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualDressingCoordinates.generic_dressing_unique
/-- info: 'FMSA.Convergence.PureFluidActualDressingCoordinates.actual_rational_dressing_reconstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualDressingCoordinates.actual_rational_dressing_reconstruction
/-- info: 'FMSA.Convergence.PureFluidActualDressingCoordinates.actual_exponential_dressing_reconstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualDressingCoordinates.actual_exponential_dressing_reconstruction
/-- info: 'FMSA.Convergence.PureFluidActualDressingCoordinates.actual_factor_dressing_reconstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualDressingCoordinates.actual_factor_dressing_reconstruction
/-- info: 'FMSA.Convergence.PureFluidActualDressingCoordinates.actualG_cross_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualDressingCoordinates.actualG_cross_identity
/-- info: 'FMSA.Convergence.PureFluidActualDressingCoordinates.actualG_at_root_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualDressingCoordinates.actualG_at_root_node
/-- info: 'FMSA.Convergence.PureFluidActualDressingCoordinates.actual_dressing_zero_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidActualDressingCoordinates.actual_dressing_zero_tail
