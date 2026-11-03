#!/usr/bin/env python3
"""Independent exact rational audit of Claude 147's EXTERNAL M3 Arb report.

Checks all eight Krawczyk witnesses, dimensions, ordered intervals, centers,
source/model/code hashes, physical data, parameter matching and endpoint signs.
Analytic f/J/A enclosures require replaying the pinned Arb generator; this
standard-library checker and those external calculations are NOT Lean proofs.
"""
from argparse import ArgumentParser
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

import check_endpoint_witness_rational as exact

if not __debug__:
    raise RuntimeError('Certificate assertions must remain enabled; do not use python -O.')

ROOT = Path(__file__).resolve().parents[2]
DEFAULT = ROOT/'results/two_tail/two_tail_m3_arb_recheck.json'
SOURCE = ROOT/'results/two_tail/two_tail_endpoint_interval_exact.json'
GENERATOR = ROOT/'scripts/two_tail/two_tail_m3_arb_recheck.py'
MODEL = [ROOT/'MSAConvergence/BHResidualPolynomials.lean',
         ROOT.parent/'MSA_and_1st_Truncation/LeanCode/HSMixture/MatrixQ0.lean']


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def intersects(a, b):
    return a[0] <= b[1] and b[0] <= a[1]


def point_vector(values):
    assert len(values) == 4
    return list(map(Q, values))


def check_witness(w):
    # Reuse the independently implemented Fraction interval products, NOT
    # the generator or its checker. That checker also rejects reversed
    # intervals and verifies center in int(X), all dimensions and dyadic C.
    adapted = dict(w, f_center=w['f_center_arb'], J_over_X=w['J_over_X_arb'],
                   exact_check_K_strictly_inside_X=w['K_strictly_inside_X'],
                   exact_check_norm_lt_1=w['norm_lt_1'])
    bound, box = exact.check_krawczyk(adapted)
    T = exact.interval(w['T'])
    assert T[0] <= Q(w['tau_center']) <= T[1]
    assert Q(w['tau_center']) == sum(T)/2
    assert bound < Q(20943, 10**6)  # strictly below 0.020943; rounded UP
    return bound, box


def check_data(d):
    assert Path(d['source']).resolve() == SOURCE
    assert d['source_sha256'] == digest(SOURCE)
    assert d['script_sha256'] == digest(GENERATOR)
    assert d['lean_sha256'] == {str(p.relative_to(ROOT.parent)): digest(p) for p in MODEL}
    assert d['coordinate_order'] == ['D1', 'D2', 'G1', 'G2', 'tau']
    assert d['data'] == dict(eta='49/100', z=['7', '14'], w='-419/384', sigma='1', rho='6*eta/pi')
    assert d['versions']['python_flint'] == '0.6.0' and d['versions']['sympy'] == '1.13.2'
    assert isinstance(d['precision_bits'], int) and d['precision_bits'] >= 256
    source = json.loads(SOURCE.read_text())
    controls = [c for c in source['controls'] if c['name'].startswith('M3')]
    assert len(controls) == 1
    c = controls[0]
    assert Q(c['eta']) == Q(49, 100) and list(map(Q, c['z'])) == [7, 14]
    assert Q(c['w']) == Q(-419, 384) and Q(c['f']) == Q(2095, 4096)
    specs = {f'runs.{k}': (c['runs'][k]['krawczyk'], (Q(c['runs'][k]['tau']),)*2)
             for k in ('tau_hat', 'tau_lo', 'tau_hi')}
    specs.update({f'rigorous_bracket.{k}': (c['rigorous_bracket'][k]['krawczyk'],
                                          (Q(c['rigorous_bracket'][k]['tau']),)*2)
                  for k in ('lo', 'hi')})
    bracket = tuple(Q(c['rigorous_bracket'][k]['tau']) for k in ('lo', 'hi'))
    assert bracket[0] < bracket[1]
    assert exact.interval(c['parametric']['tau_interval_exact']) == bracket
    specs['parametric'] = c['parametric']['krawczyk'], bracket
    assert set(d['witnesses']) == set(specs)
    bounds = []
    for name, (old, T) in specs.items():
        w = d['witnesses'][name]
        bound, _ = check_witness(w)
        bounds.append(bound)
        assert point_vector(w['center']) == point_vector(old['center'])
        assert exact.matrix(w['C_rational'], Q) == exact.matrix(old['C_rational'], Q)
        assert exact.vector(w['X']) == exact.vector(old['X'])
        assert exact.interval(w['T']) == T
        new_f, old_f = exact.vector(w['f_center_arb']), exact.vector(old['f_center'])
        new_J = exact.matrix(w['J_over_X_arb'], exact.interval)
        old_J = exact.matrix(old['J_over_X'], exact.interval)
        assert all(intersects(a, b) for a, b in zip(new_f, old_f))
        assert all(intersects(new_J[i][j], old_J[i][j]) for i in range(4) for j in range(4))
        assert w['stored_enclosures_intersect_arb'] is True
    param_box = exact.vector(d['witnesses']['parametric']['X'])
    assert set(d['endpoints']) == {'lo', 'hi'}
    for e, tau, sign in [('lo', bracket[0], '+'), ('hi', bracket[1], '-')]:
        endpoint = d['endpoints'][e]
        w = endpoint['witness']
        bound, box = check_witness(w)
        bounds.append(bound)
        assert Q(endpoint['tau']) == tau and exact.interval(w['T']) == (tau, tau)
        assert all(exact.contains(big, small, strict=True) for big, small in zip(param_box, box))
        A = exact.interval(endpoint['A_over_S'])
        assert A[0] < A[1]
        assert (A[0] > 0 if sign == '+' else A[1] < 0)
        assert endpoint['detF0_sign'] == c['rigorous_bracket'][e]['detF0_sign'] == sign
        assert intersects(A, exact.interval(c['rigorous_bracket'][e]['A_over_root']))
        assert all(endpoint[k] is True for k in ('S_strictly_inside_parametric_X',
                                                'stored_A_intersects_arb', 'stored_sign_agrees'))
    assert d['passed'] is True and d['opposite_signs'] is True
    return max(bounds), bracket


def check_symbolic_model():
    """Optional exact comparison against Codex's earlier independent model.

    Requires the Arb/SymPy dependencies; no numerical report is written.
    This remains an EXTERNAL symbolic computation, not a Lean proof.
    """
    import sys
    import sympy as sp
    sys.path.insert(0, str(ROOT/'scripts/two_tail'))
    import two_tail_m3_arb_recheck as other
    import codex_m1_parameter_monotonicity_arb as own

    amp, tau, R = own.exact_residual(dict(z=['7', '14'], w='-419/384'))
    V, R2, J2, A2 = other.symbolic(sp.Rational(49, 100),
                                  [sp.Integer(7), sp.Integer(14)], sp.Rational(-419, 384))
    assert [*amp, tau] == list(V)
    assert all(sp.expand(R[i]-R2[i]) == 0 for i in range(4))
    assert all(sp.expand(sp.diff(R[i], amp[j])-J2[i][j]) == 0
               for i in range(4) for j in range(4))
    rho, vac = 6*sp.Rational(49, 100)/sp.pi, sp.Rational(51, 100)
    z = [sp.Integer(7), sp.Integer(14)]
    cs = [(1-2*sp.pi*rho*amp[i+2]*sp.exp(-z[i])/z[i])*amp[i] for i in range(2)]
    ws = [2*sp.pi/z[i]*rho*amp[i+2]*amp[i] for i in range(2)]
    ms = [-rho/z[i]*(ws[i]+(1+z[i])*cs[i]) for i in range(2)]
    ns = [rho*(ws[i]/z[i]**2+(1+z[i]+z[i]**2/2)*cs[i]/z[i]**2) for i in range(2)]
    a0 = 2*sp.pi/vac*(1+sp.pi*rho/(2*vac))
    A = a0+sum(a0*ms[i]+2*sp.pi**2*rho/vac**2*ns[i] for i in range(2))
    assert sp.expand(A-A2) == 0
    # own.exact_residual also checks the true removable block limits and
    # the honest moment identity F0=A/(2*pi) at these same M3 data.
    print('PASS exact symbolic equality: four residuals, 16 amplitude derivatives, A and honest F0 identity.')


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('report', nargs='?', type=Path, default=DEFAULT)
    parser.add_argument('--symbolic', action='store_true',
                        help='also compare the two independent symbolic models (requires Arb/SymPy)')
    args = parser.parse_args()
    bound, _ = check_data(json.loads(args.report.read_text()))
    if args.symbolic:
        check_symbolic_model()
    print(f'PASS eight M3 witnesses; norm <= {exact.upper_display(bound)} < 0.020943.')
    print('PASS exact source/model/code pins, dimensions, ordered intervals, parameter matching and signs + / -.')
    print('Both tiny endpoint root boxes lie strictly inside the common parameter box.')
    print('Analytic f/J/A enclosures require the pinned Arb replay; EXTERNAL, NOT a Lean proof.')


if __name__ == '__main__':
    main()
