import MSAConvergence.PureFluidNodeResidues

set_option linter.style.header false

/-! Full finite-pole formulas for the ACTUAL pure-fluid BH rational and
exponential factor pieces. These are the paper's Step 1 residue forms,
derived from the original root equations for all real frequencies where
Lean's totalized rational expressions are defined. Coincident rates are
allowed; a separate analytic residue limit would combine their poles. -/
noncomputable section
open Real
open scoped BigOperators
namespace FMSA.Convergence.PureFluidExactResidueForm
open FMSA.ExactMSA FMSA.Convergence.PureFluidExponentialSplit
open FMSA.Convergence.PureFluidNodeResidues
variable {T : Type*} [Fintype T]

/-- The coefficient of the simple origin pole in the exponential piece. -/
def poleMass (xi : ℝ) (z D G : T → ℝ) : ℝ :=
  ∑ t, dressedStrength xi z D G t * rationalPart xi z D G (z t)

/-- The actual rational BH factor piece has exactly the finite pole
dictionary displayed in Step 1. No candidate dressing is assumed. -/
theorem actual_rational_residue_form
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ t, 0 < z t)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ t, MultiTail.factor xi z D G (z t) ≠ 0) (s : ℝ) :
    rationalPart xi z D G s =
      1 - rhoOf xi * MultiTail.amplitudeA xi z D G / s^3 +
      rhoOf xi * (MultiTail.amplitudeA xi z D G-
        MultiTail.amplitudeQp xi z D G) / s^2 +
      (rhoOf xi*(MultiTail.amplitudeQp xi z D G-
        MultiTail.amplitudeA xi z D G/2)-poleMass xi z D G)/s -
      ∑ t, dressedStrength xi z D G t *
        exponentialPart xi z D G (z t)/(s+z t) := by
  have htail (t : T) :
      rhoOf xi*(MultiTail.W xi z D G t/(s+z t)+
        MultiTail.C xi z D G t/s) =
      dressedStrength xi z D G t*exponentialPart xi z D G (z t)/(s+z t)+
      dressedStrength xi z D G t*rationalPart xi z D G (z t)/s := by
    have hW := node_W_dressed xi z K D G hz hroot t (hF t)
    have hC := node_C_dressed xi z K D G hz hroot t (hF t)
    linear_combination (1/(s+z t))*hW+(1/s)*hC
  simp only [rationalPart]
  simp_rw [htail]
  rw [Finset.sum_add_distrib]
  dsimp only [poleMass]
  rw [← Finset.sum_div]
  ring

/-- The actual exponential BH factor piece has the companion finite
pole dictionary. The same `poleMass` appears in both formulas. -/
theorem actual_exponential_residue_form
    (xi : ℝ) (z K D G : T → ℝ) (hz : ∀ t, 0 < z t)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ t, MultiTail.factor xi z D G (z t) ≠ 0) (s : ℝ) :
    exponentialPart xi z D G s =
      rhoOf xi*MultiTail.amplitudeA xi z D G/s^3+
      rhoOf xi*MultiTail.amplitudeQp xi z D G/s^2+
      poleMass xi z D G/s-
      ∑ t, dressedStrength xi z D G t*
        rationalPart xi z D G (z t)/(s+z t) := by
  have htail (t : T) :
      rhoOf xi*MultiTail.C xi z D G t*(1/s-1/(s+z t)) =
      dressedStrength xi z D G t*rationalPart xi z D G (z t)/s-
      dressedStrength xi z D G t*rationalPart xi z D G (z t)/(s+z t) := by
    have hC := node_C_dressed xi z K D G hz hroot t (hF t)
    linear_combination (1/s-1/(s+z t))*hC
  simp only [exponentialPart]
  simp_rw [htail]
  rw [Finset.sum_sub_distrib]
  dsimp only [poleMass]
  rw [Finset.sum_div]
  ring

end FMSA.Convergence.PureFluidExactResidueForm

/-- info: 'FMSA.Convergence.PureFluidExactResidueForm.actual_rational_residue_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidExactResidueForm.actual_rational_residue_form
/-- info: 'FMSA.Convergence.PureFluidExactResidueForm.actual_exponential_residue_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidExactResidueForm.actual_exponential_residue_form
