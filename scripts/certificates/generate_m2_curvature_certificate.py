#!/usr/bin/env python3
"""Emit Lean curvature bounds using already proved full-Jacobian intervals.

Python chooses arithmetic expressions only. Each interval, exact expression
identity, scalar bound and matrix row estimate must pass the Lean kernel.
"""
import argparse
from contextlib import redirect_stdout
from fractions import Fraction as Q
import io
import json
from pathlib import Path

import sympy as sp
import generate_m2_tangency_certificate as previous

ROOT = Path(__file__).resolve().parents[2]
engine = previous.g
lit = engine.lit
C = [[Q(c) for c in row] for row in json.loads(
    (ROOT/'results/certificates/codex_m2_jacobian_arb.json').read_text())['C_rational']]
J = {(i, j): sp.Symbol(f'jac_{i}_{j}') for i in range(10) for j in range(10)}
speeds = sp.symbols('speed0:4')
indices = {value: key for key, value in J.items()}
base_emit = engine.emit


def emit(expression):
    if expression in engine.cache:
        return engine.cache[expression]
    if expression in indices:
        i, j = indices[expression]
        def proof(n):
            return ('by\n    simpa ['+n+',jacobian,'
                    'M2TangencyJacobianBounds.jacobianLower,M2TangencyJacobianBounds.jacobianUpper,'
                    'Matrix.of_apply,Matrix.cons_val] using '
                    f'M2TangencyJacobianBounds.entry_bounds y hx {i} {j}')
        out = engine.declare(f'jacobian y {i} {j}', previous.Jbounds[i, j], proof)
    elif expression in speeds:
        j = speeds.index(expression)
        out = engine.declare(f'velocity y {j}', previous.box[6+j], lambda n:
            f'by simpa [{n},velocity,M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx {6+j}')
    else:
        return base_emit(expression)
    engine.cache[expression] = out
    return out


engine.emit = emit


def rational(q):
    return sp.Rational(q.numerator, q.denominator)


def derive(expression):
    engine.reset()
    buf = io.StringIO()
    with redirect_stdout(buf):
        out = engine.emit(expression)
    return buf.getvalue(), out, list(engine.defs)


bacc = [-sum(J[4+i, j]*speeds[j] for j in range(4))-J[4+i, 4] for i in range(4)]
approx = [sum(rational(C[i][k])*bacc[k] for k in range(4)) for i in range(4)]
constant = sum(J[9, j]*speeds[j] for j in range(4))+J[9, 4]
approx_curvature = constant+sum(J[9, 6+j]*approx[j] for j in range(4))
defects = {(i, j): sp.Integer(i == j)-sum(rational(C[i][k])*J[4+k, 6+j]
                                          for k in range(4)) for i in range(4) for j in range(4)}
radii = {key: max(map(abs, derive(expr)[1][2])) for key, expr in defects.items()}
assert max(sum((radii[i, j] for j in range(4)), Q(0)) for i in range(4)) < Q(1, 10**6)
assert derive(approx_curvature)[1][2][0] > Q(9, 10)
assert all(max(map(abs, derive(expr)[1][2])) < 1000 for expr in approx)


def header():
    print('''import MSAConvergence.M2BranchSecondDerivative
import MSAConvergence.M2TangencyJacobianBounds

/-! Kernel-checked local curvature bounds from actual full-Jacobian entries.
No external Hessian, inverse, acceleration or analytic enclosure is assumed. -/
noncomputable section
open scoped BigOperators
namespace FMSA.Convergence.M2CurvatureCertificate
open FMSA.Convergence.M2BranchSecondDerivative
open FMSA.Convergence.M2TangencySystem FMSA.Convergence.NewtonBoxExistence
open FMSA.Convergence.RealIntervalCertificates
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

abbrev preconditioner := M2KernelCertificate.preconditioner
def approximateAcceleration (y : T) : E := matrixCLM preconditioner (accelerationForcing y)
''')
    print('def radius : Matrix (Fin 4) (Fin 4) ℝ :=\n  '+engine.vmatrix(
        [[radii[i, j] for j in range(4)] for i in range(4)])+'\n')


def identity(defs, rules):
    print('    simp only ['+','.join(rules)+']')
    print('    norm_num ['+','.join(defs)+'] <;> (try simp only '
          '[Matrix.vecMul,dotProduct,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Fin.ext_iff]) <;> norm_num <;> ring')


BOX = '(y : T) (hx : ∀ i, M2TangencyData.lower i ≤ y i ∧ y i ≤ M2TangencyData.upper i)'
DEFECT_RULES = ['Matrix.sub_apply', 'Matrix.one_apply', 'Fin.ext_iff', 'Matrix.mul_apply',
                 'accelerationMatrix', 'preconditioner', 'M2KernelCertificate.preconditioner',
                 'residualIndex', 'velocityIndex', 'Fin.sum_univ_four', 'Matrix.of_apply', 'Matrix.cons_val']
APPROX_RULES = ['approximateAcceleration', 'matrixCLM_apply', 'Matrix.mulVec', 'dotProduct',
                'accelerationForcing', 'preconditioner', 'M2KernelCertificate.preconditioner',
                'residualIndex', 'amplitudeIndex', 'Fin.sum_univ_four', 'Matrix.of_apply', 'Matrix.cons_val']


def absolute_bound(name, term, expression, bound, rules):
    proof, (n, h, ends), defs = derive(expression)
    assert max(map(abs, ends)) <= bound
    print(f'private theorem {name} {BOX} :\n    |{term}| ≤ {lit(bound)} := by')
    print(proof, end='')
    print(f'  have he : {term} = {n} := by')
    identity(defs, rules)
    print(f'  rw [he]\n  exact abs_bound {h} (by norm_num) (by norm_num)\n')


def curvature_bound():
    proof, (n, h, ends), defs = derive(approx_curvature)
    assert ends[0] > Q(9, 10)
    print(f'''/-- A positive rational lower bound for the preconditioned curvature.
This is an approximation bound, not an assumed true acceleration. -/
theorem approximate_curvature_gt {BOX} :
    (9 : ℝ)/10 < curvature y (approximateAcceleration y) := by''')
    print(proof, end='')
    print(f'  have he : curvature y (approximateAcceleration y) = {n} := by')
    identity(defs, ['curvature', 'curvatureConstant', 'curvatureGradient', 'velocityIndex', *APPROX_RULES])
    print(f'  rw [he]\n  exact lt_of_lt_of_le (by norm_num) {h}.1\n')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--probe', action='store_true')
    args = parser.parse_args()
    header()
    for i in range(1 if args.probe else 4):
        for j in range(1 if args.probe else 4):
            absolute_bound(f'e_bound_{i}_{j}', f'(1-preconditioner*accelerationMatrix y) {i} {j}',
                           defects[i, j], radii[i, j], DEFECT_RULES)
    for i in range(1 if args.probe else 4):
        absolute_bound(f'approx_bound_{i}', f'approximateAcceleration y {i}', approx[i], Q(1000), APPROX_RULES)
        absolute_bound(f'gradient_bound_{i}', f'curvatureGradient y {i}', J[9, 6+i], Q(2),
                       ['curvatureGradient', 'velocityIndex', 'Matrix.cons_val'])
    curvature_bound()
    if not args.probe:
        print(f'''private theorem entry_defect_bound {BOX} (i j : Fin 4) :
    |(1-preconditioner*accelerationMatrix y) i j| ≤ radius i j := by
  fin_cases i <;> fin_cases j''')
        for i in range(4):
            for j in range(4):
                print(f'  · exact e_bound_{i}_{j} y hx')
        print(f'''
/-- Actual acceleration-block row defects, uniform over the full joint box. -/
theorem acceleration_row_defect_bound {BOX} (i : Fin 4) :
    ∑ j, |(1-preconditioner*accelerationMatrix y) i j| < (1 : ℝ)/1000000 := by
  calc
    _ ≤ ∑ j, radius i j := Finset.sum_le_sum (fun j _ => entry_defect_bound y hx i j)
    _ < _ := by
      fin_cases i''')
        for i in range(4):
            row = '+'.join(lit(radii[i, j]) for j in range(4))
            print(f'      · rw [Fin.sum_univ_four]\n        change ({row}) < (1 : ℝ)/1000000\n        norm_num')
        print(f'''
/-- The exact preconditioned acceleration vector has a proved norm bound. -/
theorem approximate_acceleration_norm {BOX} : ‖approximateAcceleration y‖ ≤ (1000 : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1000)).mpr
  intro i
  fin_cases i''')
        for i in range(4):
            print(f'  · change |approximateAcceleration y {i}| ≤ (1000 : ℝ)\n    simpa only [div_one] using approx_bound_{i} y hx')
        print(f'''
/-- The true curvature response has a uniform scalar pairing budget. -/
theorem curvature_gradient_bound {BOX} : (∑ i, |curvatureGradient y i|) ≤ (10 : ℝ) := by
  have h0 := gradient_bound_0 y hx
  have h1 := gradient_bound_1 y hx
  have h2 := gradient_bound_2 y hx
  have h3 := gradient_bound_3 y hx
  simp only [Fin.sum_univ_four]
  linarith
''')
    print('end FMSA.Convergence.M2CurvatureCertificate')


if __name__ == '__main__':
    main()
