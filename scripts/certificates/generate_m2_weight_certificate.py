#!/usr/bin/env python3
"""Emit kernel proofs for the M2 fixed-coupling weight response.

Only arithmetic candidates are generated here. Existing proved Jacobian
intervals and pi bounds are leaves; Lean checks every operation and identity.
"""
from contextlib import redirect_stdout
from fractions import Fraction as Q
import io
import sympy as sp
import generate_m2_curvature_certificate as previous

engine = previous.engine
lit = engine.lit
coupling = sp.Symbol('weight_coupling')
base_emit = engine.emit


def emit(expression):
    if expression in engine.cache:
        return engine.cache[expression]
    if expression == coupling:
        out = engine.declare('y 4', previous.previous.box[4], lambda n:
            f'by simpa [{n},M2TangencyData.lower,M2TangencyData.upper,Matrix.cons_val] using hx 4')
        engine.cache[expression] = out
        return out
    return base_emit(expression)


engine.emit = emit
approx = [previous.rational(previous.C[i][1])*coupling*sp.pi/6 for i in range(4)]
slope = sum(previous.J[9,6+i]*approx[i] for i in range(4))
BOX = previous.BOX
RULES = ['approximateWeightVelocity', 'matrixCLM_apply', 'Matrix.mulVec', 'dotProduct',
         'weightDerivative', 'Pi.smul_apply', 'smul_eq_mul',
         'M2KernelCertificate.preconditioner', 'Fin.sum_univ_four',
         'Matrix.of_apply', 'Matrix.cons_val']


def main():
    print('''import MSAConvergence.M2WeightBranch
import MSAConvergence.M2CurvatureCertificate

/-! Proved uniform weight-response approximation bounds. No actual
velocity, inverse or external analytic enclosure is assumed. -/
noncomputable section
open scoped BigOperators
namespace FMSA.Convergence.M2WeightCertificate
open FMSA.Convergence.M2WeightBranch FMSA.Convergence.M2BranchSecondDerivative
open FMSA.Convergence.M2TangencySystem FMSA.Convergence.NewtonBoxExistence
open FMSA.Convergence.RealIntervalCertificates
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def approximateWeightVelocity (y : T) : Fin 4 → ℝ :=
  matrixCLM M2KernelCertificate.preconditioner ((y 4) • weightDerivative)
''')
    for i in range(4):
        previous.absolute_bound(f'approx_bound_{i}', f'approximateWeightVelocity y {i}',
                                approx[i], Q(1000), RULES)
    proof, (n,h,ends), defs = previous.derive(slope)
    assert ends[1] < -20
    print(f'''/-- Uniform negative bound on the exact preconditioned response.
The true branch derivative is identified and bounded separately. -/
theorem approximate_weight_slope_lt {BOX} :
    (∑ i, curvatureGradient y i*approximateWeightVelocity y i) < (-20 : ℝ) := by''')
    print(proof,end='')
    print(f'  have he : (∑ i, curvatureGradient y i*approximateWeightVelocity y i) = {n} := by')
    previous.identity(defs, ['curvatureGradient','velocityIndex',*RULES])
    print(f'  rw [he]\n  exact lt_of_le_of_lt {h}.2 (by norm_num)\n')
    print(f'''/-- A genuine Pi-space bound on the preconditioned weight velocity. -/
theorem approximate_weight_velocity_norm {BOX} :
    ‖approximateWeightVelocity y‖ ≤ (1000 : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1000)).mpr
  intro i
  fin_cases i''')
    for i in range(4):
        print(f'  · change |approximateWeightVelocity y {i}| ≤ (1000 : ℝ)\n    simpa only [div_one] using approx_bound_{i} y hx')
    print('\nend FMSA.Convergence.M2WeightCertificate')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled.')
    main()
