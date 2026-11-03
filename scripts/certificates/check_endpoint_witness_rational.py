#!/usr/bin/env python3
"""Independent EXACT RATIONAL PART check of the M1/M3 external witnesses.

Python standard library only. Checks source pins, I-CJ from stored J,C,
Krawczyk images from stored center/f(center),E,X, row norms, A signs, and
M3 endpoint/common-parameter-box matching. It does NOT prove the analytic
J/f/A enclosures or root preservation along the unrecorded shrinking steps.
Those remain EXTERNAL mpmath-AD evidence, not Lean proofs.
"""
from argparse import ArgumentParser
from decimal import Decimal, localcontext, ROUND_CEILING
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError('Certificate assertions must remain enabled; do not use python -O.')

ROOT = Path(__file__).resolve().parents[2]
DEFAULT = ROOT / 'results/two_tail/two_tail_endpoint_interval_exact.json'


def interval(pair):
    assert len(pair) == 2
    lo, hi = map(Q, pair)
    assert lo <= hi
    return lo, hi


def plus(a, b):
    return a[0]+b[0], a[1]+b[1]


def negative(a):
    return -a[1], -a[0]


def times(a, b):
    ends = [x*y for x in a for y in b]
    return min(ends), max(ends)


def total(xs):
    result = Q(0), Q(0)
    for x in xs:
        result = plus(result, x)
    return result


def contains(outer, inner, strict=False):
    if strict:
        return outer[0] < inner[0] <= inner[1] < outer[1]
    return outer[0] <= inner[0] <= inner[1] <= outer[1]


def vector(items):
    assert len(items) == 4
    return list(map(interval, items))


def matrix(items, entry):
    assert len(items) == 4 and all(len(row) == 4 for row in items)
    return [[entry(v) for v in row] for row in items]


def upper_display(q):
    with localcontext() as c:
        c.prec, c.rounding = 12, ROUND_CEILING
        return str(Decimal(q.numerator)/Decimal(q.denominator))


def check_krawczyk(w):
    center = list(map(Q, w['center']))
    assert len(center) == 4
    C = matrix(w['C_rational'], Q)
    assert all(q.denominator & (q.denominator-1) == 0 for row in C for q in row)
    X, K, fx = map(vector, (w['X'], w['K'], w['f_center']))
    J, E = map(lambda xs: matrix(xs, interval), (w['J_over_X'], w['I_minus_CJ']))
    assert all(lo < c < hi for c, (lo, hi) in zip(center, X))
    for i in range(4):
        for j in range(4):
            d = Q(i == j)
            exact = plus((d, d), negative(total(times((C[i][k], C[i][k]), J[k][j]) for k in range(4))))
            assert contains(E[i][j], exact), ('I-CJ does not enclose exact interval product', i, j)
    rows = [sum((max(abs(lo), abs(hi)) for lo, hi in row), Q(0)) for row in E]
    bound = Q(w['inf_norm_upper'])
    assert max(rows) <= bound < 1
    for i in range(4):
        exact = plus((center[i], center[i]), negative(total(times((C[i][k], C[i][k]), fx[k]) for k in range(4))))
        exact = plus(exact, total(times(E[i][j], plus(X[j], (-center[j], -center[j]))) for j in range(4)))
        assert contains(K[i], exact), ('K does not enclose exact Krawczyk interval expression', i)
        assert contains(X[i], K[i], strict=True), ('K not strictly inside X', i)
    assert w['exact_check_K_strictly_inside_X'] is True and w['exact_check_norm_lt_1'] is True
    return bound, X


def check_data(r):
    assert set(r['source_sha256']) == {'two_tail_endpoint_interval.py', 'two_tail_m2_jacobian_interval.py'}
    for filename, expected in r['source_sha256'].items():
        assert hashlib.sha256((ROOT/'scripts/two_tail'/filename).read_bytes()).hexdigest() == expected, filename
    diag = ROOT/'results/two_tail/two_tail_fiber_diag.json'
    assert Path(r['diag_source']).resolve() == diag
    assert hashlib.sha256(diag.read_bytes()).hexdigest() == r['diag_sha256']
    diag_data = json.loads(diag.read_text())
    controls = r['controls']
    assert len(controls) == 2
    summaries = []
    for c, (tag, zs, f) in zip(controls, [('M1', [Q(3,5),Q(21,25)], Q(7548807031658907,2**53)),
                                       ('M3', [Q(7),Q(14)], Q(2095,4096))]):
        assert c['name'].startswith(tag) and c['eta'] == '49/100'
        assert list(map(Q,c['z'])) == zs and Q(c['f']) == f
        w0 = -(1/zs[0]+1/zs[0]**2)/(1/zs[1]+1/zs[1]**2)
        assert Q(c['w']) == f*w0
        d = next(d for d in diag_data['controls'] if d['name'] == c['name'])
        assert Q(d['f']) == f
        assert Q(c['taus']['tau_hat']) == Q(d['beta'])
        assert Q(c['taus']['tau_lo']) == Q(d['beta_bracket'][0])
        assert Q(c['taus']['tau_hi']) == Q(d['beta_bracket'][1])
        assert set(c['runs']) == {'tau_hat','tau_lo','tau_hi'}
        assert all(Q(v['tau']) == Q(c['taus'][k]) for k,v in c['runs'].items())
        br = c['rigorous_bracket']
        assert br is not None
        th, rel = Q(c['taus']['tau_hat']), Q(br['rel'])
        assert Q(br['lo']['tau']) == th*(1-rel) and Q(br['hi']['tau']) == th*(1+rel)
        runs = [*c['runs'].values(), br['lo'], br['hi']]
        bounds = []
        for run in runs:
            assert run['certified'] is True
            bound, X = check_krawczyk(run['krawczyk'])
            bounds.append(bound)
            shrunk = vector(run['root_enclosure_after_shrink'])
            assert all(lo < hi for lo, hi in shrunk), 'Lost nonzero-width endpoint serialization'
            assert all(contains(x,s) for x,s in zip(X,shrunk))
            assert run['exact_check_shrunk_inside_X'] is True
            A = interval(run['A_over_root'])
            assert A[0] < A[1]
            sign = '+' if A[0] > 0 else '-' if A[1] < 0 else '0?'
            assert sign == run['detF0_sign']
        assert br['lo']['detF0_sign'] == '+' and br['hi']['detF0_sign'] == '-'
        assert c['float_bracket_sign_change'] is False
        assert c['runs']['tau_lo']['detF0_sign'] == c['runs']['tau_hi']['detF0_sign']
        par = c['parametric']
        param_bound = None
        if tag == 'M1':
            assert par is None  # No common-box certificate supplied; not a nonexistence proof.
        else:
            assert par is not None
            param_bound, X = check_krawczyk(par['krawczyk'])
            taus = list(map(Q,par['tau_interval_exact']))
            assert taus == [Q(br['lo']['tau']), Q(br['hi']['tau'])]
            assert contains(interval(par['tau_interval_iv']), tuple(taus))
            for end in ['lo','hi']:
                assert all(contains(x,s,strict=True) for x,s in zip(X,vector(br[end]['root_enclosure_after_shrink'])))
            assert all(par['exact_check_endpoint_roots_strictly_inside_common_X'].values())
        summaries.append((tag, max(bounds), param_bound))
    return summaries


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('report', nargs='?', type=Path, default=DEFAULT)
    args = parser.parse_args()
    for tag, bound, param in check_data(json.loads(args.report.read_text())):
        print(f'PASS {tag}: five exact rational point witnesses; norm <= {upper_display(bound)}')
        if param is not None:
            print(f'PASS M3 common parameter witness: norm <= {upper_display(param)}; both exact endpoint boxes match')
    print('PASS source hashes, matrix expressions, strict inclusion, positive-width serialization and stored A signs.')
    print('Analytic J/f/A enclosures and shrink-root preservation remain EXTERNAL; NOT a Lean proof.')


if __name__ == '__main__':
    main()
