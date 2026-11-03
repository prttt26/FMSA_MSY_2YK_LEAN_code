#!/usr/bin/env python3
"""Emit ordinary-kernel center residual and exact Newton box geometry proofs.

The beta and weight below are exact rational STATE PARAMETERS. They are not
assumed roots of a tangency system. SymPy chooses a simplified expression only;
Lean proves both its original residual identity and every analytic bound.
"""
from contextlib import redirect_stdout
from fractions import Fraction as Q
import io
import importlib.util
from pathlib import Path
import sympy as sp
from codex_m2_jacobian_arb import symbolic_residual

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('interval_generator',HERE/'generate_m2_kernel_certificate.py')
g=importlib.util.module_from_spec(spec)
with redirect_stdout(io.StringIO()):spec.loader.exec_module(g)
amp,(tau,weight),residual,_=symbolic_residual()
beta=Q(11227143292458953,2000000000000000)
w=Q(-9657507677060143,2000000000000000)
center=[(lo+hi)/2 for lo,hi in g.box]
subs=dict(zip(amp+ (tau,weight),[sp.Rational(x.numerator,x.denominator) for x in center+[beta,w]]))
rc=[sp.expand(e.subs(subs)) for e in residual]
cr=[sp.expand(sum(sp.Rational(g.C[i][j].numerator,g.C[i][j].denominator)*rc[j] for j in range(4))) for i in range(4)]
assert all(not e.free_symbols and not e.atoms(sp.Float) for e in cr)
print('''import MSAConvergence.M2ResidualFormula
import MSAConvergence.M2KernelCertificate
import MSAConvergence.NewtonBoxExistence

/-! Exact rational M2 state and ordinary-kernel center residual certificate.
The explicit state is not claimed to be an exact tangency parameter. -/
noncomputable section
open Set
open scoped BigOperators
namespace FMSA.Convergence.M2RootCertificate
open FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.M2JacobianFormula FMSA.Convergence.M2ResidualFormula
open FMSA.Convergence.M2KernelCertificate FMSA.Convergence.RealIntervalCertificates
open FMSA.Convergence.NewtonBoxExistence
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
''')
print('def beta : ℝ := '+g.lit(beta))
print('def weight : ℝ := '+g.lit(w))
print('def strength : TailMatrix (Fin 2) 1 := fun u _ _ => ![1,weight] u')
print('def center : Fin 4 → ℝ := !['+', '.join(g.lit(x) for x in center)+']\n')

for i,e in enumerate(cr):
    g.reset();buf=io.StringIO()
    with redirect_stdout(buf): n,h,bounds=g.emit(e)
    rad=max(map(abs,bounds));assert rad<Q(1,10**12),(i,bounds)
    print(f'private theorem center_bound_{i} :')
    print(f'    |preconditioner.mulVec (residualFormula strength beta center) {i}| ≤ (1 : ℝ)/1000000000000 := by')
    print(buf.getvalue(),end='')
    print(f'  have he : preconditioner.mulVec (residualFormula strength beta center) {i} = {n} := by')
    print('    norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_four,preconditioner,residualFormula,strength,beta,weight,center,Matrix.of_apply,Matrix.cons_val_two,Matrix.cons_val_three,'+','.join(g.defs)+']')
    print('    field_simp [Real.pi_ne_zero]')
    print('    ring')
    print(f'  rw [he]\n  exact abs_bound {h} (by norm_num) (by norm_num)\n')

print('''/-- Exact center residual estimate in the SAME Pi-space norm used by Banach. -/
theorem center_residual_bound :
    ‖matrixCLM preconditioner (residualFormula strength beta center)‖ ≤ (1 : ℝ)/1000000000000 := by
  rw [matrixCLM_apply]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/1000000000000)).mpr
  intro i
  fin_cases i
  · exact center_bound_0
  · exact center_bound_1
  · exact center_bound_2
  · exact center_bound_3

/-- The exact rational center is separated from EVERY face by at least 10^-10. -/
theorem center_margin : ∀ i, lower i+(1 : ℝ)/10000000000 ≤ center i ∧
    center i+(1 : ℝ)/10000000000 ≤ upper i := by
  intro i
  fin_cases i <;> norm_num [lower,upper,center]

/-- The box is contained in the uniform closed ball of radius 2*10^-9. -/
theorem center_radius : ∀ i, center i-lower i ≤ (1 : ℝ)/500000000 ∧
    upper i-center i ≤ (1 : ℝ)/500000000 := by
  intro i
  fin_cases i <;> norm_num [lower,upper,center]

end FMSA.Convergence.M2RootCertificate''')
