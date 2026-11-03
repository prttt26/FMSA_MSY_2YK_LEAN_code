import MSAConvergence.PureFluidExponentialSplit

set_option linter.style.header false

/-! Hard-sphere unimodularity in the actual pure-fluid BH normalization.
The scalar relation among the two PY coefficients is proved from the
frozen density formulas; no hard-sphere determinant is assumed. -/
noncomputable section
open Real
namespace FMSA.Convergence.PureFluidHardSphereUnimodular
open FMSA.ExactMSA FMSA.Convergence.PureFluidExponentialSplit
variable {T : Type*} [Fintype T]

def hardA (xi : ℝ) : ℝ := rhoOf xi * bA0 xi
def hardQ (xi : ℝ) : ℝ := rhoOf xi * qp0 xi

/-- Rational and exponential pieces at zero tail amplitude. -/
def hardP (xi s : ℝ) : ℝ :=
  1 - hardA xi/s^3 + (hardA xi-hardQ xi)/s^2 + (hardQ xi-hardA xi/2)/s

def hardShat (xi s : ℝ) : ℝ := hardA xi/s^3 + hardQ xi/s^2

/-- The actual PY coefficients satisfy precisely the determinant relation. -/
theorem hard_coefficient_relation (xi : ℝ) (hxi : xi ≠ 1) :
    (hardA xi)^2 - 4*hardA xi*hardQ xi - 8*hardA xi +
      4*(hardQ xi)^2 + 8*hardQ xi = 0 := by
  have h1 : 1 - xi ≠ 0 := by intro h; apply hxi; linarith
  unfold hardA hardQ rhoOf bA0 qp0
  field_simp [Real.pi_ne_zero, h1]
  ring

/-- A rational algebra identity: one relation among the two PY coefficients
is enough for the hard-sphere matrix to have determinant one. -/
theorem generic_unimodular (a q s : ℝ) (hs : s ≠ 0)
    (hrel : a^2 - 4*a*q - 8*a + 4*q^2 + 8*q = 0) :
    (1 - a / s^3 + (a-q) / s^2 + (q-a/2) / s) *
      (1 - a / (-s)^3 + (a-q) / (-s)^2 + (q-a/2) / (-s)) -
      (a / s^3 + q / s^2) * (a / (-s)^3 + q / (-s)^2) = 1 := by
  have hmul : (a^2 - 4*a*q - 8*a + 4*q^2 + 8*q)*s^4 = 0 := by
    rw [hrel]
    ring
  field_simp [hs]
  nlinarith [hmul]

/-- The actual hard-sphere two-by-two dressing matrix is unimodular at
every nonzero real frequency and every density parameter except xi=1. -/
theorem hard_unimodular (xi s : ℝ) (hxi : xi ≠ 1) (hs : s ≠ 0) :
    hardP xi s * hardP xi (-s) - hardShat xi s * hardShat xi (-s) = 1 := by
  simpa only [hardP, hardShat] using
    generic_unimodular (hardA xi) (hardQ xi) s hs (hard_coefficient_relation xi hxi)

/-- At zero original tail amplitude, the rational part of the actual BH
factor is exactly the PY hard-sphere rational part. -/
theorem rationalPart_zero (xi : ℝ) (z G : T → ℝ) (s : ℝ) :
    rationalPart xi z (fun _ => 0) G s = hardP xi s := by
  simp [rationalPart, hardP, hardA, hardQ, MultiTail.amplitudeA,
    MultiTail.amplitudeQp, MultiTail.momentM, MultiTail.momentN,
    MultiTail.W, MultiTail.C]
  ring

theorem exponentialPart_zero (xi : ℝ) (z G : T → ℝ) (s : ℝ) :
    exponentialPart xi z (fun _ => 0) G s = hardShat xi s := by
  simp [exponentialPart, hardShat, hardA, hardQ, MultiTail.amplitudeA,
    MultiTail.amplitudeQp, MultiTail.momentM, MultiTail.momentN, MultiTail.C]

/-- The frozen actual PY factor has the same unimodular rational basis. -/
theorem actual_F0_split (xi : ℝ) (z G : T → ℝ) (s : ℝ) (hs : s ≠ 0) :
    F0 xi s = hardP xi s + exp (-s)*hardShat xi s := by
  rw [← MultiTail.factor_zero xi z G s, factor_split xi z (fun _ => 0) G s hs,
    rationalPart_zero, exponentialPart_zero]

/-- Generic dressing cancellation: the exponential terms cancel and the
hard-sphere determinant leaves exactly the off-diagonal dressing entry. -/
theorem dressed_cross_identity (p q pm qm u d e : ℝ)
    (hdet : p*pm-q*qm=1) :
    ((u-d)*q+d*pm)*(p+e*q) -
      q*(((u-d)*p+d*qm)+e*((u-d)*q+d*pm)) = d := by
  linear_combination d*hdet

/-- Step E with the ACTUAL frozen PY factor. When a later BH dressing has
the displayed form, its cross difference is the off-diagonal entry `d`.
This theorem does not yet assert that every BH root has such a dressing. -/
theorem actual_hard_dressed_cross_identity
    (xi s : ℝ) (z G : T → ℝ) (u d : ℝ)
    (hxi : xi ≠ 1) (hs : s ≠ 0) :
    let P := (u-d)*hardP xi s+d*hardShat xi (-s)
    let S := (u-d)*hardShat xi s+d*hardP xi (-s)
    S*F0 xi s-hardShat xi s*(P+exp (-s)*S)=d := by
  dsimp
  rw [actual_F0_split xi z G s hs]
  exact dressed_cross_identity (hardP xi s) (hardShat xi s)
    (hardP xi (-s)) (hardShat xi (-s)) u d (exp (-s))
    (hard_unimodular xi s hxi hs)

end FMSA.Convergence.PureFluidHardSphereUnimodular
/-- info: 'FMSA.Convergence.PureFluidHardSphereUnimodular.hard_coefficient_relation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereUnimodular.hard_coefficient_relation
/-- info: 'FMSA.Convergence.PureFluidHardSphereUnimodular.generic_unimodular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereUnimodular.generic_unimodular
/-- info: 'FMSA.Convergence.PureFluidHardSphereUnimodular.hard_unimodular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereUnimodular.hard_unimodular
/-- info: 'FMSA.Convergence.PureFluidHardSphereUnimodular.rationalPart_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereUnimodular.rationalPart_zero
/-- info: 'FMSA.Convergence.PureFluidHardSphereUnimodular.exponentialPart_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereUnimodular.exponentialPart_zero
/-- info: 'FMSA.Convergence.PureFluidHardSphereUnimodular.actual_F0_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereUnimodular.actual_F0_split
/-- info: 'FMSA.Convergence.PureFluidHardSphereUnimodular.dressed_cross_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereUnimodular.dressed_cross_identity
/-- info: 'FMSA.Convergence.PureFluidHardSphereUnimodular.actual_hard_dressed_cross_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidHardSphereUnimodular.actual_hard_dressed_cross_identity
