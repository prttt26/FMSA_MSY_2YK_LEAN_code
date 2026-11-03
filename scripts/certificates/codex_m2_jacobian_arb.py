#!/usr/bin/env python3
"""Independent EXTERNAL Arb check of the M2 BH amplitude Jacobian.

Requires python-flint 0.6.0 and SymPy 1.13.2 (versions are recorded, not
silently substituted). Run with these packages on PYTHONPATH, for example:
  PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 \
    scripts/certificates/codex_m2_jacobian_arb.py

Uses symbolic differentiation of the literal one-species, two-tail residual,
NOT Claude's interval AD, stored interval Jacobian, or recorded PASS flag.
All physical constants, decimal input endpoints, widening, preconditioner
entries and serialized output bounds use exact rationals; only pi and exp
need transcendental interval enclosures. No root-existence, first-loss,
canonicity, global finite-fiber, or Lean-verification claim is made.
"""
from argparse import ArgumentParser
from decimal import Decimal, localcontext, ROUND_CEILING
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import sys

import flint
from flint import arb, ctx, fmpq
import sympy as sp

if not __debug__:
    raise RuntimeError('Certificate assertions must remain enabled; do not use python -O.')

RESEARCH = Path(__file__).resolve().parents[2]
FOUNDATION = RESEARCH.parent / 'MSA_and_1st_Truncation'
ROOT_SOURCE = FOUNDATION / 'results/coupling_singularities/codex_m2_zero_mode_firstness.json'
PRECONDITIONER_SOURCE = RESEARCH / 'results/two_tail/two_tail_m2_jacobian_interval.json'
EXPECTED_ROOT_SHA256 = 'd75a89d83c0c5fb80c3bdcf243e04c9de906384f1a1da4e573a3c518dff0cbb9'
OUTPUT = RESEARCH / 'results/certificates/codex_m2_jacobian_arb.json'


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read_exact(path):
    return json.loads(Path(path).read_text(), parse_float=Decimal)


def rat_ball(q):
    q = Fraction(q)
    return arb(fmpq(q.numerator, q.denominator))


def exact_bound(x):
    """Convert an exact Arb endpoint to an exact dyadic Fraction."""
    assert x.is_exact() and x.is_finite(), str(x)
    mantissa, exponent = map(int, x.man_exp())
    return Fraction(mantissa) * Fraction(2)**exponent


def enclosure(x):
    assert x.is_finite(), str(x)
    return [str(exact_bound(x.lower())), str(exact_bound(x.upper()))]


def ceil_decimal(q):
    """An explicitly upward-rounded decimal display; fractions are authoritative."""
    with localcontext() as c:
        c.prec = 12
        c.rounding = ROUND_CEILING
        return str(Decimal(q.numerator) / Decimal(q.denominator))


def interval(lo, hi):
    """An Arb ball proven to cover BOTH EXACT rational endpoints."""
    assert lo <= hi
    b = arb(rat_ball((lo + hi)/2), rat_ball((hi - lo)/2))
    assert exact_bound(b.lower()) <= lo <= hi <= exact_bound(b.upper())
    return b


def symbolic_residual():
    """Literal N=1 specialization, sigma=1, eta=1/10, z=(9/5,12).

    Compare BHResidualPolynomials.lean: gammaPoly, cPoly, wPoly, mPoly,
    nPoly, aPoly, qpPoly, qhatPoly, firstPoly, secondPoly. Original variables
    remain D1,D2,G1,G2, with no X=D*G substitution or residual rescaling.
    """
    D1, D2, G1, G2 = amplitudes = sp.symbols('D1 D2 G1 G2')
    tau, weight = sp.symbols('tau weight')
    ds, gs = (D1, D2), (G1, G2)
    rho = sp.Rational(3, 5) / sp.pi
    z = (sp.Rational(9, 5), sp.Integer(12))
    vac = sp.Rational(9, 10)
    qpp0 = 2*sp.pi/vac*(1 + sp.pi*rho/(2*vac))
    qp0 = 2*sp.pi/vac*(1 + sp.pi*rho/(4*vac))
    cs = [(1 - 2*sp.pi*rho*gs[i]*sp.exp(-z[i])/z[i])*ds[i]
          for i in range(2)]
    ws = [2*sp.pi/z[i]*rho*gs[i]*ds[i] for i in range(2)]
    # Keep the per-tail moment formulas visible rather than importing any
    # numerical residual implementation from the other session.
    ms = [-rho/z[i]*(ws[i] + (1 + z[i])*cs[i]) for i in range(2)]
    ns = [rho*(ws[i]/z[i]**2 + (1 + z[i] + z[i]**2/2)/z[i]**2*cs[i])
          for i in range(2)]
    aa = qpp0 + sum(qpp0*ms[i] + 2*sp.pi**2*rho/vac**2*ns[i] for i in range(2))
    qp = qp0 + sum(qp0*ms[i] + qpp0*ns[i] for i in range(2))
    first, second = [], []
    for i, s in enumerate(z):
        e = sp.exp(-s)
        qhat = ((1 - s - e)/s**2*qp + (1 - s + s**2/2 - e)/s**3*aa
                + sum(ws[j]/(s+z[j]) + cs[j]*(1-e)/s for j in range(2))
                + sum(cs[j]*e/(s+z[j]) for j in range(2)))
        factor = 1 - rho*qhat
        source = (aa + s*qp + sum(s**2*z[j]/(s+z[j])*cs[j] for j in range(2)))/s**2
        first.append(ds[i]*factor - 2*sp.pi*tau*(1 if i == 0 else weight)/s)
        second.append(2*sp.pi*gs[i]*factor - source)
    residual = tuple(map(sp.expand, first + second))
    jacobian = tuple(tuple(sp.expand(sp.diff(r, a)) for a in amplitudes)
                     for r in residual)
    # Check algebraic degree and exact parameter independence, not a float
    # comparison or a finite-difference derivative test.
    assert all(sp.Poly(r, *amplitudes).total_degree() <= 3 for r in residual)
    assert all(sp.Poly(v, *amplitudes).total_degree() <= 2 for row in jacobian for v in row)
    assert all(not (v.free_symbols & {tau, weight}) for row in jacobian for v in row)
    return amplitudes, (tau, weight), residual, jacobian


def arb_evaluator(values):
    @lru_cache(None)
    def evaluate(expr):
        if expr in values:
            return values[expr]
        if expr.is_Rational:
            return rat_ball(Fraction(int(expr.p), int(expr.q)))
        if expr == sp.pi:
            return arb.pi()
        if expr.func == sp.Add:
            return sum((evaluate(a) for a in expr.args), arb(0))
        if expr.func == sp.Mul:
            value = arb(1)
            for a in expr.args:
                value *= evaluate(a)
            return value
        if expr.func == sp.Pow and expr.exp.is_Integer:
            return evaluate(expr.base)**int(expr.exp)
        if expr.func == sp.exp:
            return evaluate(expr.args[0]).exp()
        raise TypeError(f'Unenclosed symbolic node: {expr!r}')
    return evaluate


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=OUTPUT)
    parser.add_argument('--relative-widen', type=Fraction, default=Fraction(1, 10**10))
    parser.add_argument('--precision', type=int, default=192)
    args = parser.parse_args()
    assert args.precision >= 128 and args.relative_widen > 0
    output = args.output.resolve()
    assert FOUNDATION not in output.parents, 'Frozen foundation is read-only.'
    assert output not in {ROOT_SOURCE, PRECONDITIONER_SOURCE, Path(__file__).resolve()}
    ctx.prec = args.precision
    root_raw = ROOT_SOURCE.read_bytes()
    assert hashlib.sha256(root_raw).hexdigest() == EXPECTED_ROOT_SHA256
    root, pre = read_exact(ROOT_SOURCE), read_exact(PRECONDITIONER_SOURCE)
    assert root['model'] == {'eta': '0.1', 'z': ['1.8', '12'], 'sigma': '1'}
    assert pre['root_box_sha256'] == EXPECTED_ROOT_SHA256
    boxes, rational_boxes = [], []
    for endpoints in root['root_box'][:6]:
        lo, hi = map(Fraction, endpoints)
        delta = args.relative_widen * max(Fraction(1), abs(lo), abs(hi))
        lo, hi = lo-delta, hi+delta
        rational_boxes.append([str(lo), str(hi)])
        boxes.append(interval(lo, hi))
    Cq = [[Fraction(x) for x in row] for row in pre['C_rational']]
    assert len(Cq) == 4 and all(len(row) == 4 for row in Cq)
    C = [[rat_ball(x) for x in row] for row in Cq]
    assert all(v.is_exact() for row in C for v in row), 'Preconditioner must be represented exactly.'
    amplitudes, parameters, residual, jacobian = symbolic_residual()
    values = dict(zip(amplitudes + parameters, boxes))
    evaluate = arb_evaluator(values)
    J = [[evaluate(v) for v in row] for row in jacobian]
    # Serialize J first; derive the entire contraction witness by EXACT
    # rational interval arithmetic on these outward dyadic endpoints. Thus
    # the matrix product and norm can be checked without Arb or SymPy.
    Jbounds = [[tuple(Fraction(q) for q in enclosure(v)) for v in row] for row in J]
    E, rows = [], []
    for i in range(4):
        row = []
        for j in range(4):
            lo = hi = Fraction(int(i == j))
            for k in range(4):
                products = (-Cq[i][k]*Jbounds[k][j][0], -Cq[i][k]*Jbounds[k][j][1])
                lo += min(products)
                hi += max(products)
            row.append((lo, hi))
        E.append(row)
        rows.append(sum((max(abs(lo), abs(hi)) for lo, hi in row), Fraction(0)))
    bound = max(rows)
    assert 0 <= bound < 1, f'No contraction certificate: {bound}'
    cnorm = max(sum(map(abs, row), Fraction(0)) for row in Cq)
    inverse_bound = cnorm/(1-bound)
    residual_box = [evaluate(v) for v in residual]
    residual_contains_zero = [r.contains(0) for r in residual_box]
    assert all(residual_contains_zero), 'Convention check failed; not a root-existence test.'
    source_paths = [
        Path(__file__).resolve(), Path(__file__).with_name('check_m2_jacobian_rational.py'),
        ROOT_SOURCE, PRECONDITIONER_SOURCE,
        RESEARCH / 'MSAConvergence/BHResidualPolynomials.lean',
        FOUNDATION / 'LeanCode/YukawaOZMix/MSAMultiTailMixtureSystem.lean',
        FOUNDATION / 'LeanCode/YukawaOZMix/MSAMixtureConcrete.lean',
        FOUNDATION / 'LeanCode/YukawaOZMix/MSAMixtureCancellation.lean',
        FOUNDATION / 'LeanCode/HSMixture/MatrixQ0.lean',
    ]
    sources = {str(p.relative_to(RESEARCH.parent)): digest(p) for p in source_paths}
    symbolic_text = '\n'.join(sp.srepr(v) for v in residual + sum(jacobian, ()))
    result = {
        'status': 'PASS_EXTERNAL_UNIFORM_JACOBIAN_REGULARITY',
        'label': 'EXTERNAL Arb interval certificate; NOT a Lean proof',
        'scope': ('BH amplitude Jacobian in original D1,D2,G1,G2 coordinates is invertible '
                  'everywhere in the explicitly rational widened amplitude box. '
                  'No root-existence, first-loss, canonicity or global finite-fiber claim.'),
        'method': 'Exact SymPy differentiation; Arb evaluation of expanded derivative expression trees; exact rational norm bound.',
        'source_sha256': sources,
        'versions': {'python': sys.version.split()[0], 'python_flint': flint.__version__, 'sympy': sp.__version__},
        'precision_bits': ctx.prec,
        'physical_data': {'eta': '1/10', 'rho': '3/(5*pi)', 'sigma': '1', 'z': ['9/5', '12'], 'K': ['1', 'weight']},
        'coordinate_order': ['D1', 'D2', 'G1', 'G2', 'tau', 'weight'],
        'decimal_input_semantics': 'JSON decimal tokens parsed exactly, WITHOUT binary floats',
        'relative_widen_rational': str(args.relative_widen),
        'exact_widened_box_rational': rational_boxes,
        'arb_input_box_rational_enclosure': [enclosure(b) for b in boxes],
        'C_rational': [[str(x) for x in row] for row in Cq],
        'J_rational_enclosure': [[enclosure(x) for x in row] for row in J],
        'I_minus_CJ_rational_enclosure': [[[str(q) for q in x] for x in row] for row in E],
        'row_sum_upper_rational': list(map(str, rows)),
        'norm_upper_rational': str(bound),
        'norm_upper_decimal_rounded_up': ceil_decimal(bound),
        'strict_comparison': '0 <= norm_upper_rational < 1 (exact Fraction comparison)',
        'C_infinity_norm_rational': str(cnorm),
        'inverse_norm_upper_rational': str(inverse_bound),
        'inverse_norm_upper_decimal_rounded_up': ceil_decimal(inverse_bound),
        'residual_rational_enclosure': [enclosure(v) for v in residual_box],
        'residual_contains_zero': residual_contains_zero,
        'symbolic_residual_and_jacobian_srepr_sha256': hashlib.sha256(symbolic_text.encode()).hexdigest(),
        'symbolic_degree_checks': {'residual_max': 3, 'jacobian_max': 2, 'jacobian_independent_of_tau_and_weight': True},
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(f"PASS EXTERNAL: ||I-CJ(box)||_inf <= {ceil_decimal(bound)} < 1")
    print(f"||J(u)^(-1)||_inf <= {ceil_decimal(inverse_bound)} throughout the rational box")
    print('Symbolic derivatives, Arb bounds, exact-rational endpoints and comparisons; NOT a Lean proof.')
    print(output)


if __name__ == '__main__':
    main()
