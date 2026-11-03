#!/usr/bin/env python3
"""Emit literal ten-variable polynomial candidates; Lean proves actual identity."""
from m2_tangency_symbolics import symbolic_system,lean_polynomial
variables,S,J=symbolic_system()
print('''import MSAConvergence.M2TangencySystem
import MSAConvergence.PolynomialNewtonMap

/-! Literal polynomials for the FULL ten-equation M2 contact system.
Every expression candidate is proved against the actual ten-coordinate
system. No root, tangency witness or numerical interval is a premise. -/
noncomputable section
open scoped BigOperators
namespace FMSA.Convergence.M2TangencyPolynomials
open FMSA.Convergence.M2TangencySystem FMSA.Convergence.M2ZeroMode
open FMSA.Convergence.M2ResidualFormula FMSA.Convergence.M2JacobianFormula
open FMSA.Convergence.PolynomialNewtonMap FMSA.Convergence.NewtonBoxExistence
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
''')
for i,e in enumerate(S):print(f'def equation_{i} : MvPolynomial (Fin 10) ℝ :=\n  {lean_polynomial(e,variables)}\n')
print('def polynomial : Fin 10 → MvPolynomial (Fin 10) ℝ :=\n  !['+','.join('equation_'+str(i) for i in range(10))+']\n')
for i in range(10):
 rhs=(f'residualFormula (strength (y 5)) (y 4) (amplitudes y) {i}' if i<4 else
      f'(formula (amplitudes y)).mulVec (velocity y) {i-4}-forcing (y 5) {i-4}' if i<8 else
      'M2ZeroMode.zeroMode (amplitudes y)' if i==8 else
      '∑ k, M2ZeroMode.gradient (amplitudes y) k*velocity y k')
 print(f'''private theorem entry_{i} (y : Fin 10 → ℝ) :
    MvPolynomial.eval y equation_{i} = system y {i} := by
  change MvPolynomial.eval y equation_{i} = {rhs}
  norm_num [equation_{i},amplitudes,velocity,residualFormula,formula,
    strength,forcing,M2ZeroMode.zeroMode,M2ZeroMode.gradient,M2ZeroMode.alpha,M2ZeroMode.beta,Matrix.mulVec,dotProduct,
    Fin.sum_univ_four,Fin.castAdd,Fin.castLE,Fin.natAdd,Matrix.cons_val_succ,Matrix.cons_val_two,Matrix.cons_val_three] <;> ring
''')
print('''/-- Literal polynomial evaluation equals ALL ten actual equations. -/
theorem system_eq_polynomialMap : system = polynomialMap polynomial := by
  funext y i
  fin_cases i''')
for i in range(10):print(f'  · exact (entry_{i} y).symm')
print('''
/-- The formal polynomial partials are the actual full system derivative. -/
theorem system_hasFDerivAt (y : Fin 10 → ℝ) :
    HasFDerivAt system (matrixCLM (jacobian polynomial y)) y := by
  rw [system_eq_polynomialMap]
  exact polynomialMap_hasFDerivAt polynomial y

end FMSA.Convergence.M2TangencyPolynomials''')
