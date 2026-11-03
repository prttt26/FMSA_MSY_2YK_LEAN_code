import MSAConvergence.PureFluidFoldCore
import MSAConvergence.PureFluidPositiveSubstitution
import MSAConvergence.PureFluidNodeClosedForm

set_option linter.style.header false

/-! Original amplitudes as closed functions of the actual nodes, at any root with nonvanishing
node factors: `ρ D_t = F0 w_t f_t` and `2 π ρ F0² (G_t - G0_t) = r_t/f_t`, with `f_t = 1 - κ_t r_t`.
No distinct-rate premise. -/

noncomputable section
namespace FMSA.Convergence.PureFluidFoldClosedForm
open FMSA.ExactMSA
open FMSA.Convergence.PureFluidActualThetaEquation FMSA.Convergence.PureFluidActualPerTailWeights
open FMSA.Convergence.PureFluidActualNodeWeightIdentification FMSA.Convergence.PureFluidActualDressingCoordinates
open FMSA.Convergence.PureFluidActualGlobalPartialFractions
open FMSA.Convergence.PureFluidHardSphereNodePositivity FMSA.Convergence.PureFluidNodeClosedForm
open FMSA.Convergence.PureFluidNodeResidues FMSA.Convergence.PureFluidDressingCandidates
open FMSA.Convergence.PureFluidHardSphereUnimodular FMSA.Convergence.PureFluidExponentialSplit

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- `ρ D_t = F0 w_t f_t` at a root. -/
theorem actual_D_closed_all_rates
    (xi : ℝ) (z K D G : T → ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0)
    (hU : ∀ u, actualU xi z D G (z u) ≠ 0) (t : T) :
    rhoOf xi * D t = F0 xi (z t) * actualWeight xi z D G t *
      (1 - hardKappa xi (z t) * actualNodeR xi z D G t) := by
  have hw := actualWeight_eq_dressedStrength_mul_U_all_rates xi z K D G hz hroot hF t
  have hfac := actual_factor_eq_closed_node_all_rates xi z K D G hxi0 hxi1 hz hroot hF hU t
  have hFt := hF t
  rw [hw]
  unfold dressedStrength
  rw [hfac] at hFt ⊢
  have h1 : F0 xi (z t) ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hFt)
  have h2 := hU t
  have h3 : 1 - hardKappa xi (z t) * actualNodeR xi z D G t ≠ 0 := right_ne_zero_of_mul hFt
  field_simp

/-- `2 π ρ F0² (G_t - G0_t) = r_t/f_t` at a root. -/
theorem actual_G_closed_all_rates
    (xi : ℝ) (z K D G : T → ℝ) (hxi0 : 0 < xi) (hxi1 : xi < 1) (hz : ∀ u, 0 < z u)
    (hroot : MultiTail.IsRoot xi z K D G)
    (hF : ∀ u, MultiTail.factor xi z D G (z u) ≠ 0)
    (hU : ∀ u, actualU xi z D G (z u) ≠ 0) (t : T) :
    (2 * Real.pi * rhoOf xi * (F0 xi (z t)) ^ 2) * (G t - hardG0Node xi (z t)) =
      actualNodeR xi z D G t / (1 - hardKappa xi (z t) * actualNodeR xi z D G t) := by
  have hg : actualU xi z D G (z t) * actualNodeR xi z D G t = actualG xi z D G (z t) := by
    unfold actualNodeR
    field_simp [hU t]
  refine actual_G_node_of_dressing xi z K D G t hxi0 hxi1 (hz) hroot (hF t)
    (actualU xi z D G (z t)) (actualNodeR xi z D G t) (hU t) ?_ ?_
  · rw [hg, actual_rational_dressing_reconstruction xi z D G (z t) hxi1.ne (hz t).ne']
    rfl
  · rw [hg, actual_exponential_dressing_reconstruction xi z D G (z t) hxi1.ne (hz t).ne']
    rfl


end FMSA.Convergence.PureFluidFoldClosedForm

/-- info: 'FMSA.Convergence.PureFluidFoldClosedForm.actual_D_closed_all_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldClosedForm.actual_D_closed_all_rates
/-- info: 'FMSA.Convergence.PureFluidFoldClosedForm.actual_G_closed_all_rates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PureFluidFoldClosedForm.actual_G_closed_all_rates
