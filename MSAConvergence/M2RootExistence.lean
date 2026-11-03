import MSAConvergence.M2ResidualDerivative
import MSAConvergence.M2RootCertificate

/-! An actual original BH root is constructed inside the existing M2 box.
Uniqueness is local to that box. The exact rational coupling/weight are fixed
state parameters; tangency, PY membership and Taylor bounds are not asserted. -/
noncomputable section
open Set
open scoped BigOperators
namespace FMSA.Convergence.M2RootExistence
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.BHResidualPolynomials FMSA.Convergence.BHPolynomialJacobian
open FMSA.Convergence.M2JacobianFormula FMSA.Convergence.M2ResidualFormula
open FMSA.Convergence.M2KernelCertificate FMSA.Convergence.NewtonBoxExistence
open FMSA.Convergence.M2RootCertificate FMSA.Convergence.M2ResidualDerivative
open FMSA.Convergence.RegularEndpointContinuation

/-- Constructed unique coordinate root inside the literal original amplitude
box. No root witness, inverse or numerical analytic enclosure is a premise. -/
theorem exists_unique_coordinate_root :
    ∃! x : Fin 4 → ℝ, x ∈ Icc lower upper ∧ residualFormula strength beta x = 0 := by
  refine exists_unique_root_in_box lower upper center preconditioner
    (residualFormula strength beta) formula
    (⟨1/1000000,by norm_num⟩ : NNReal)
    (1/500000000) (1/10000000000) (1/1000000000000)
    (by change (1 : ℝ)/1000000 < 1; norm_num) (by norm_num) (by norm_num)
    center_margin center_radius ?_ ?_ center_residual_bound
    (by change (1 : ℝ)/1000000*(1/500000000)+1/1000000000000 ≤ 1/10000000000; norm_num)
  · intro x _hx
    exact hasFDerivAt_formula strength beta x
  · intro x hx i
    exact (row_defect_bound x (fun j => ⟨hx.1 j,hx.2 j⟩) i).le

/-- The actual ORIGINAL signed Dt/G amplitude root exists and is unique among
all original amplitudes in the same box. No positivity of Dt/G is imposed. -/
theorem exists_unique_actual_root :
    ∃! a : TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1,
      (∀ i, lower i ≤ amplitudeValues a (index i) ∧ amplitudeValues a (index i) ≤ upper i) ∧
      IsRoot z rho sigma (beta • strength) a.1 a.2 := by
  obtain ⟨x,hx,hu⟩ := exists_unique_coordinate_root
  refine ⟨point x,⟨?_,(actual_root_iff_formula_zero x strength beta).mpr hx.2⟩,?_⟩
  · intro i
    rw [point_coordinates]
    exact ⟨hx.1.1 i,hx.1.2 i⟩
  · intro a ha
    let y : Fin 4 → ℝ := fun i => amplitudeValues a (index i)
    have hy : y ∈ Icc lower upper := ⟨fun i => (ha.1 i).1,fun i => (ha.1 i).2⟩
    have hf : residualFormula strength beta y = 0 := by
      apply (actual_root_iff_formula_zero y strength beta).mp
      simpa only [y,point_coordinates_inverse] using ha.2
    have he : y = x := hu y ⟨hy,hf⟩
    calc
      a = point y := (point_coordinates_inverse a).symm
      _ = point x := congrArg point he

/-- A genuine non-vacuous EndpointRegular instance at an actual positive-
density two-tail BH root, constructed without any supplied root premises. -/
theorem exists_actual_regular_root :
    ∃ a : TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1,
      (∀ i, lower i ≤ amplitudeValues a (index i) ∧ amplitudeValues a (index i) ≤ upper i) ∧
      IsRoot z rho sigma (beta • strength) a.1 a.2 ∧
      EndpointRegular z rho sigma strength beta a := by
  obtain ⟨a,ha,_⟩ := exists_unique_actual_root
  exact ⟨a,ha.1,ha.2,actual_regular_on_box a strength beta ha.1⟩

end FMSA.Convergence.M2RootExistence

/-- info: 'FMSA.Convergence.M2RootExistence.exists_unique_coordinate_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2RootExistence.exists_unique_coordinate_root

/-- info: 'FMSA.Convergence.M2RootExistence.exists_unique_actual_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2RootExistence.exists_unique_actual_root

/-- info: 'FMSA.Convergence.M2RootExistence.exists_actual_regular_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2RootExistence.exists_actual_regular_root

