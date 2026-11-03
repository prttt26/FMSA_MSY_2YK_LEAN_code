#!/usr/bin/env python3
"""Emit 100 candidate entries; each is proved from literal formal pderiv."""
from m2_tangency_symbolics import symbolic_system,lean_real
variables,S,J=symbolic_system()
print('''import MSAConvergence.M2TangencyPolynomials

/-! Every entry of the genuine ten-variable M2 contact Jacobian, proved
from the exact literal polynomials. Symbolic differentiation is not trusted. -/
noncomputable section
open scoped BigOperators
namespace FMSA.Convergence.M2TangencyJacobian
open FMSA.Convergence.M2TangencyPolynomials FMSA.Convergence.NewtonBoxExistence
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
''')
print('def formula (y : Fin 10 → ℝ) : Matrix (Fin 10) (Fin 10) ℝ :=\n  !!['+
 ';\n    '.join(','.join(lean_real(J[i,j],variables) for j in range(10)) for i in range(10))+']\n')
for i in range(10):
 for j in range(10):
  print(f'''private theorem entry_{i}_{j} (y : Fin 10 → ℝ) :
    PolynomialNewtonMap.jacobian polynomial y {i} {j} = {lean_real(J[i,j],variables)} := by
  change MvPolynomial.eval y (MvPolynomial.pderiv {j} equation_{i}) = _
  norm_num [equation_{i},Fin.ext_iff,Pi.single_apply,MvPolynomial.pderiv_C] <;> ring
''')
print('''/-- All 100 entries agree with the ORIGINAL full system derivative. -/
theorem jacobian_formula (y : Fin 10 → ℝ) (i j : Fin 10) :
    PolynomialNewtonMap.jacobian polynomial y i j = formula y i j := by
  fin_cases i <;> fin_cases j''')
for i in range(10):
 for j in range(10):print(f'  · exact entry_{i}_{j} y')
print('''
/-- The expanded full Jacobian is exactly the Frechet derivative, EVERYWHERE. -/
theorem system_hasFDerivAt (y : Fin 10 → ℝ) :
    HasFDerivAt M2TangencySystem.system (matrixCLM (formula y)) y := by
  have he : PolynomialNewtonMap.jacobian polynomial y = formula y := by
    ext i j
    exact jacobian_formula y i j
  rw [← he]
  exact M2TangencyPolynomials.system_hasFDerivAt y

end FMSA.Convergence.M2TangencyJacobian''')
