import MSAConvergence.M2ResidualFormula
import MSAConvergence.M2KernelCertificate
import MSAConvergence.NewtonBoxExistence

/-! The proved four-coordinate residual has the actual derivative. The
continuous coordinate equivalence is constructed explicitly; no choice of
norm or reduced variables is substituted for the original amplitudes. -/
noncomputable section
open scoped BigOperators
namespace FMSA.Convergence.M2ResidualDerivative
open FMSA.ExactMSA.MultiTailMixture FMSA.Paper.ActualAnalyticBranch
open FMSA.Convergence.BHResidualPolynomials FMSA.Convergence.BHPolynomialJacobian
open FMSA.Convergence.M2JacobianFormula FMSA.Convergence.M2ResidualFormula
open FMSA.Convergence.M2KernelCertificate FMSA.Convergence.NewtonBoxExistence
abbrev A := TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1

def linearCoordinates : A ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun a := fun i => amplitudeValues a (index i)
  invFun := point
  map_add' a b := by
    funext i
    exact congrFun ((amplitudeEquiv (T := Fin 2) (N := 1)).map_add a b) (index i)
  map_smul' c a := by
    funext i
    exact congrFun ((amplitudeEquiv (T := Fin 2) (N := 1)).map_smul c a) (index i)
  left_inv := point_coordinates_inverse
  right_inv x := funext (point_coordinates x)

def coordinates : A ≃L[ℝ] (Fin 4 → ℝ) := linearCoordinates.toContinuousLinearEquiv

/-- The inverse is exactly the original Dt/G amplitude constructor. -/
theorem coordinates_symm (x : Fin 4 → ℝ) : coordinates.symm x = point x := rfl

/-- The forward map reads all four original coordinates. -/
theorem coordinates_apply (a : A) (i : Fin 4) :
    coordinates a i = amplitudeValues a (index i) := rfl

/-- Exact differentiation of the four-coordinate original residual, at every
amplitude and arbitrary parameter and strengths, not only at roots. -/
theorem hasFDerivAt_formula (K : TailMatrix (Fin 2) 1) (b : ℝ) (x : Fin 4 → ℝ) :
    HasFDerivAt (residualFormula K b) (matrixCLM (formula x)) x := by
  let R := FMSA.ExactMSA.MultiTailMixture.residual z rho sigma K
  have hr : HasFDerivAt R (fderiv ℝ R (b,point x)) (b,point x) :=
    (residual_analyticAt z rho sigma K (b,point x)).differentiableAt.hasFDerivAt
  have hi : HasFDerivAt (fun a : A => (b,a)) (ContinuousLinearMap.inr ℝ ℝ A) (point x) := by
    convert! (hasFDerivAt_const b (point x)).prodMk (hasFDerivAt_id (point x)) using 1
  have ha : HasFDerivAt (fun a : A => R (b,a)) (actualPartial z rho sigma K b (point x)) (point x) :=
    hr.comp (point x) hi
  let Q := coordinates.toContinuousLinearMap
  let P := coordinates.symm.toContinuousLinearMap
  have he : (fun y => Q (R (b,P y))) = residualFormula K b := by
    funext y i
    exact actual_formula y K b i
  have hd := Q.hasFDerivAt.comp x (ha.comp x P.hasFDerivAt)
  have hL : Q.comp ((actualPartial z rho sigma K b (point x)).comp P) = matrixCLM (formula x) := by
    ext v i
    simp only [ContinuousLinearMap.comp_apply,matrixCLM_apply]
    change amplitudeValues (actualPartial z rho sigma K b (point x) (point v)) (index i) =
      (formula x).mulVec v i
    have hc := (ordered_partial_coordinates (point x) (point v) K b i).symm
    simpa only [point_coordinates,Matrix.mulVec,dotProduct] using hc
  change HasFDerivAt (fun y => Q (R (b,P y)))
    (Q.comp ((actualPartial z rho sigma K b (point x)).comp P)) x at hd
  rw [he,hL] at hd
  exact hd

end FMSA.Convergence.M2ResidualDerivative

/-- info: 'FMSA.Convergence.M2ResidualDerivative.coordinates_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2ResidualDerivative.coordinates_symm

/-- info: 'FMSA.Convergence.M2ResidualDerivative.coordinates_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2ResidualDerivative.coordinates_apply

/-- info: 'FMSA.Convergence.M2ResidualDerivative.hasFDerivAt_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.M2ResidualDerivative.hasFDerivAt_formula

