import MSAConvergence.PureFluidHardSphereUnimodular

set_option linter.style.header false

/-! The finite algebra behind the two pure-fluid Laurent constraints.
The displayed jet formulas are explicit inputs here; identifying them
with coefficients of the dressed rational functions is a separate task. -/
noncomputable section
namespace FMSA.Convergence.PureFluidLaurentJetAlgebra
open FMSA.ExactMSA FMSA.Convergence.PureFluidHardSphereUnimodular

/-- The hard-sphere B coefficient is fixed by A and q in the frozen PY data. -/
theorem hard_B_relation (xi : ℝ) :
    -4*rhoOf xi*bB0 xi = 4*(hardA xi-hardQ xi) := by
  unfold hardA hardQ bA0 qp0 bB0
  ring

/-- Two moment combinations read from the Laurent coefficients of the
proposed dressing. Only the first jets of U and g survive. -/
def momentMJet (a q u0 u1 g0 g1 : ℝ) : ℝ :=
  (-a*g1-a*u1-2*g0+2*g1*q+2*u0-2)/2

def momentNJet (a q _u0 u1 g0 g1 : ℝ) : ℝ :=
  (a*g1+2*g0-2*g1*q-4*g1+2*q*u1+4*u1)/4

def amplitudeAJet (a q u0 g0 : ℝ) : ℝ :=
  a*g0+a*u0-2*g0*q

def amplitudeQJet (a q u0 u1 g0 g1 : ℝ) : ℝ :=
  (a*g0+2*a*g1+2*a*u1-2*g0*q-4*g1*q+2*q*u0)/2

/-- Exact factorization of the first BH coefficient-relation defect.
It vanishes under the actual PY determinant relation. -/
theorem amplitudeA_defect (a q u0 u1 g0 g1 : ℝ) :
    amplitudeAJet a q u0 g0 -
      a*(1+momentMJet a q u0 u1 g0 g1) -
      4*(a-q)*momentNJet a q u0 u1 g0 g1 =
      (u1-g1)*(a^2-4*a*q-8*a+4*q^2+8*q)/2 := by
  unfold amplitudeAJet momentMJet momentNJet
  ring

/-- Exact factorization of the second BH coefficient-relation defect. -/
theorem amplitudeQ_defect (a q u0 u1 g0 g1 : ℝ) :
    amplitudeQJet a q u0 u1 g0 g1 -
      q*(1+momentMJet a q u0 u1 g0 g1) -
      a*momentNJet a q u0 u1 g0 g1 =
      -g1*(a^2-4*a*q-8*a+4*q^2+8*q)/4 := by
  unfold amplitudeQJet momentMJet momentNJet
  ring

/-- The first Laurent coefficient relation, after the coefficient-extraction
interface has supplied the jet formulas. -/
theorem amplitudeA_constraint (a q u0 u1 g0 g1 : ℝ)
    (hdet : a^2-4*a*q-8*a+4*q^2+8*q = 0) :
    amplitudeAJet a q u0 g0 =
      a*(1+momentMJet a q u0 u1 g0 g1) +
      4*(a-q)*momentNJet a q u0 u1 g0 g1 := by
  have h := amplitudeA_defect a q u0 u1 g0 g1
  rw [hdet, mul_zero, zero_div] at h
  linarith

/-- The second Laurent coefficient relation under the same actual PY data. -/
theorem amplitudeQ_constraint (a q u0 u1 g0 g1 : ℝ)
    (hdet : a^2-4*a*q-8*a+4*q^2+8*q = 0) :
    amplitudeQJet a q u0 u1 g0 g1 =
      q*(1+momentMJet a q u0 u1 g0 g1) +
      a*momentNJet a q u0 u1 g0 g1 := by
  have h := amplitudeQ_defect a q u0 u1 g0 g1
  rw [hdet, mul_zero, zero_div] at h
  linarith

/-- The two relations specialized to the ACTUAL frozen hard-sphere
coefficients. This does not yet extract jets from arbitrary U and g. -/
theorem actual_hard_jet_constraints (xi u0 u1 g0 g1 : ℝ) (hxi : xi ≠ 1) :
    amplitudeAJet (hardA xi) (hardQ xi) u0 g0 =
      hardA xi*(1+momentMJet (hardA xi) (hardQ xi) u0 u1 g0 g1) +
      (-4*rhoOf xi*bB0 xi)*momentNJet (hardA xi) (hardQ xi) u0 u1 g0 g1 ∧
    amplitudeQJet (hardA xi) (hardQ xi) u0 u1 g0 g1 =
      hardQ xi*(1+momentMJet (hardA xi) (hardQ xi) u0 u1 g0 g1) +
      hardA xi*momentNJet (hardA xi) (hardQ xi) u0 u1 g0 g1 := by
  rw [hard_B_relation]
  exact ⟨amplitudeA_constraint _ _ _ _ _ _ (hard_coefficient_relation xi hxi),
    amplitudeQ_constraint _ _ _ _ _ _ (hard_coefficient_relation xi hxi)⟩

end FMSA.Convergence.PureFluidLaurentJetAlgebra
/-- info: 'FMSA.Convergence.PureFluidLaurentJetAlgebra.hard_B_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidLaurentJetAlgebra.hard_B_relation
/-- info: 'FMSA.Convergence.PureFluidLaurentJetAlgebra.amplitudeA_defect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidLaurentJetAlgebra.amplitudeA_defect
/-- info: 'FMSA.Convergence.PureFluidLaurentJetAlgebra.amplitudeQ_defect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidLaurentJetAlgebra.amplitudeQ_defect
/-- info: 'FMSA.Convergence.PureFluidLaurentJetAlgebra.amplitudeA_constraint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidLaurentJetAlgebra.amplitudeA_constraint
/-- info: 'FMSA.Convergence.PureFluidLaurentJetAlgebra.amplitudeQ_constraint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidLaurentJetAlgebra.amplitudeQ_constraint
/-- info: 'FMSA.Convergence.PureFluidLaurentJetAlgebra.actual_hard_jet_constraints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidLaurentJetAlgebra.actual_hard_jet_constraints
