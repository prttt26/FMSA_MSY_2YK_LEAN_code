import MSAConvergence.NewtonBoxExistence

/-! The exact finite polynomial Jacobian as a genuine Frechet derivative
in the SAME Pi-space norm as the proved Newton-box criterion. -/
noncomputable section
open scoped BigOperators
namespace FMSA.Convergence.PolynomialNewtonMap
open FMSA.Convergence.NewtonBoxExistence
variable {I : Type*} [Fintype I] [DecidableEq I]

def scalarDerivative (P : MvPolynomial I ℝ) (x : I → ℝ) : (I → ℝ) →L[ℝ] ℝ :=
  ∑ i, MvPolynomial.eval x (MvPolynomial.pderiv i P) •
    (ContinuousLinearMap.proj i : (I → ℝ) →L[ℝ] ℝ)

/-- Formal polynomial differentiation is a genuine derivative at EVERY point. -/
theorem scalar_hasFDerivAt (P : MvPolynomial I ℝ) (x : I → ℝ) :
    HasFDerivAt (fun y => MvPolynomial.eval y P) (scalarDerivative P x) x := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa [scalarDerivative] using hasFDerivAt_const c x
  | add p q hp hq =>
    convert! hp.add hq using 1 <;> ext v <;>
      simp [scalarDerivative,Finset.sum_add_distrib,add_mul]
  | mul_X p j hp =>
    have hx : HasFDerivAt (fun y : I → ℝ => y j) (ContinuousLinearMap.proj j) x :=
      (ContinuousLinearMap.proj j : (I → ℝ) →L[ℝ] ℝ).hasFDerivAt
    convert! hp.mul hx using 1 <;> ext v <;>
      simp [scalarDerivative,Pi.single_apply,Finset.sum_add_distrib,mul_add,
        Finset.mul_sum,apply_ite,mul_left_comm,mul_comm] <;> ring

def polynomialMap (P : I → MvPolynomial I ℝ) (x : I → ℝ) : I → ℝ := fun i => MvPolynomial.eval x (P i)
def jacobian (P : I → MvPolynomial I ℝ) (x : I → ℝ) : Matrix I I ℝ :=
  fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (P i))

/-- The proved polynomial derivative has EXACTLY the matrix/operator
convention consumed by the Newton existence theorem. -/
theorem polynomialMap_hasFDerivAt (P : I → MvPolynomial I ℝ) (x : I → ℝ) :
    HasFDerivAt (polynomialMap P) (matrixCLM (jacobian P x)) x := by
  have h := (hasFDerivAt_pi.mpr (fun i => scalar_hasFDerivAt (P i) x))
  convert! h using 1

end FMSA.Convergence.PolynomialNewtonMap

/-- info: 'FMSA.Convergence.PolynomialNewtonMap.scalar_hasFDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PolynomialNewtonMap.scalar_hasFDerivAt

/-- info: 'FMSA.Convergence.PolynomialNewtonMap.polynomialMap_hasFDerivAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.Convergence.PolynomialNewtonMap.polynomialMap_hasFDerivAt

