#!/usr/bin/env python3
"""Independent rational audit of Claude 157's EXTERNAL PY-seeded chains.

Uses the earlier Codex Fraction interval engine, never the chain generator's
Krawczyk checker. Optional 320-bit Arb replay uses the pinned generator's
analytic model; this is a fresh replay, not another independent analytic model.
No result here is a Lean proof or a premise of the Lean validation.
"""
from argparse import ArgumentParser
from copy import deepcopy
from datetime import datetime, timezone
from fractions import Fraction as Q
import gzip
import hashlib
import json
from pathlib import Path
import sys

import check_endpoint_witness_rational as arithmetic

if not __debug__:
    raise RuntimeError('Assertions must remain enabled; do not use python -O.')

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT/'results/two_tail/two_tail_endpoint_interval_exact.json'
GENERATOR = ROOT/'scripts/two_tail/two_tail_py_chain.py'
MODEL = ROOT/'scripts/two_tail/two_tail_m3_arb_recheck.py'
LEAN = [ROOT/'MSAConvergence/BHResidualPolynomials.lean',
        ROOT.parent/'MSA_and_1st_Truncation/LeanCode/HSMixture/MatrixQ0.lean']


def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def number(s):
    if 'p' in s:
        m, e = s.split('p')
        return Q(int(m))*Q(2)**int(e)
    return Q(s)


def interval(p):
    assert len(p) == 2
    a, b = map(number, p)
    assert a <= b, 'Reversed interval'
    return a, b


def vector(p, n=4, parse=interval):
    assert len(p) == n, 'Vector dimension'
    return [parse(x) for x in p]


def matrix(p, parse):
    assert len(p) == 4 and all(len(row) == 4 for row in p), 'Matrix dimension'
    return [list(map(parse, row)) for row in p]


def point(q):
    return q, q


def magnitude(p):
    return max(map(abs, p))


add, neg, mul, total = arithmetic.plus, arithmetic.negative, arithmetic.times, arithmetic.total
contains = arithmetic.contains


def witness(w):
    k = w['k']
    assert k in (0, 4), 'Unsupported parameter coordinate'
    u = [i for i in range(5) if i != k]
    c = vector(w['c'], 5, number)
    C = matrix(w['C'], number)
    assert all(x.denominator & (x.denominator-1) == 0 for row in C for x in row)
    Y, P = vector(w['Y']), interval(w['P'])
    assert all(a < c[j] < b for j, (a, b) in zip(u, Y)), 'Center outside unknown box'
    assert P[0] <= c[k] <= P[1], 'Center outside parameter interval'
    f, J, Rp = vector(w['f']), matrix(w['Jy'], interval), vector(w['Rp'])
    E = [[add(point(Q(i == j)), neg(total(mul(point(C[i][m]), J[m][j])
                                           for m in range(4)))) for j in range(4)] for i in range(4)]
    CRp = [total(mul(point(C[i][m]), Rp[m]) for m in range(4)) for i in range(4)]
    dP = add(P, point(-c[k]))
    images = [total([point(c[u[i]]), neg(total(mul(point(C[i][m]), f[m])
                                            for m in range(4))), neg(mul(CRp[i], dP)),
                    total(mul(E[i][j], add(Y[j], point(-c[u[j]])))
                          for j in range(4))]) for i in range(4)]
    assert all(contains(y, image, strict=True) for y, image in zip(Y, images)), 'No strict self-map'
    radii = [(b-a)/2 for a, b in Y]
    rows = [sum((magnitude(E[i][j])*radii[j] for j in range(4)), Q(0)) for i in range(4)]
    q = max(rows[i]/radii[i] for i in range(4))
    assert 0 <= q <= number(w['q']) < 1, 'No weighted contraction'
    dl = None
    if k == 0:
        bound = max(magnitude(CRp[i])/radii[i] for i in range(4))/(1-q)
        dl = -CRp[3][1]-rows[3]*bound
    B = [None]*5
    B[k] = P
    for j, y in zip(u, Y):
        B[j] = y
    return dict(k=k, box=B, q=q, derivative_lower=dl, center=c, C=C)


def inside(small, big, k):
    return all(contains(big[j], small[j], strict=(j != k)) for j in range(5))


def metadata(d):
    assert Path(d['source']).resolve() == SOURCE
    assert d['source_sha256'] == digest(SOURCE), 'Stale endpoint data'
    assert d['script_sha256'] == {p.name: digest(p) for p in (GENERATOR, MODEL)}, 'Stale generator/model'
    assert d['lean_sha256'] == {str(p.relative_to(ROOT.parent)): digest(p) for p in LEAN}, 'Stale Lean model'
    assert d['coordinates'] == ['Dt1', 'Dt2', 'G1', 'G2', 'tau']
    assert d['versions']['python_flint'] == '0.6.0' and d['versions']['sympy'] == '1.13.2'
    assert isinstance(d['precision_bits'], int) and d['precision_bits'] >= 256
    assert d['passed'] is True
    c = next(c for c in json.loads(SOURCE.read_text())['controls'] if c['name'] == d['control'])
    assert d['data'] == dict(eta=c['eta'], z=c['z'], w=c['w'], sigma='1', rho='6*eta/pi')
    assert 0 < Q(c['eta']) < 1 and all(Q(z) > 0 for z in c['z'])
    bracket = tuple(Q(c['rigorous_bracket'][e]['tau']) for e in ('lo', 'hi'))
    assert tuple(map(Q, d['bracket'])) == bracket and 0 < bracket[0] < bracket[1]
    return bracket


def check_data(d):
    lo, hi = metadata(d)
    slabs = d['slabs']
    assert slabs
    if d['tau_switch'] is None:
        # Positivity only on slabs ENDING before lo leaves a gap if one slab
        # straddles lo. An exact breakpoint is essential for firstness.
        assert any(s['phase'] == 'tau' and interval(s['w']['P'])[1] == lo
                   for s in slabs), 'No exact tau_lo slab boundary'
    result = [witness(s['w']) for s in slabs]
    nt = sum(s['phase'] == 'tau' for s in slabs)
    assert nt > 0 and [s['phase'] for s in slabs] == ['tau']*nt+['p']*(len(slabs)-nt)
    assert all(r['k'] == (4 if i < nt else 0) for i, r in enumerate(result))
    switch = Q(d['tau_switch']) if d['tau_switch'] is not None else None
    star = number(d['p_star']) if d['p_star'] is not None else None
    assert (switch is None) == (nt == len(slabs)) == (star is None)
    assert result[0]['box'][4][0] == 0
    assert result[nt-1]['box'][4][1] == (hi if switch is None else switch)
    assert switch is None or 0 < switch < lo
    for i in range(len(slabs)):
        r, s = result[i], slabs[i]
        k, B = r['k'], r['box']
        assert B[k][0] < B[k][1], 'Empty slab'
        if i+1 < len(slabs) and i+1 != nt:
            assert B[k][1] == result[i+1]['box'][k][0], 'Gap/overlap between parameters'
        need = B[k][1] <= (lo if k == 4 else star)
        assert s['A_required'] is need
        A = interval(s['A'])
        assert not need or A[0] > 0, 'Required A positivity absent'
        if k == 0:
            assert r['derivative_lower'] > 0, 'Parameter graph not monotone'
            assert 0 < number(s['dtau_dp_lower']) <= r['derivative_lower']
        else:
            assert s['dtau_dp_lower'] is None
    assert star is None or any(r['k'] == 0 and r['box'][0][1] == star for r in result)
    seed = vector(d['seed']['enclosure'], 5)
    assert seed[0] == seed[1] == seed[4] == (0, 0)
    assert inside(seed, result[0]['box'], 4), 'HS seed not in initial box'
    pairs = [(i, i+1) for i in range(len(slabs)-1) if i+1 != nt]
    assert len(d['links']) == len(pairs), 'Missing link'
    for item, (a, b) in zip(d['links'], pairs):
        r = witness(item['w'])
        k, B = r['k'], r['box']
        assert k == result[a]['k'] == result[b]['k']
        edge = result[a]['box'][k][1]
        assert B[k] == (edge, edge)
        assert inside(B, result[a]['box'], k) and inside(B, result[b]['box'], k), 'Disconnected link'
    if switch is not None:
        s = d['switch']
        r = witness(s['w'])
        assert r['k'] == 4 and Q(s['tau']) == switch and r['box'][4] == (switch, switch)
        assert inside(r['box'], result[nt-1]['box'], 4) and inside(r['box'], result[nt]['box'], 0)
    else:
        assert d['switch'] is None
    assert set(d['endpoints']) == {'lo', 'hi'}
    for e, tau, sign in [('lo', lo, '+'), ('hi', hi, '-')]:
        s = d['endpoints'][e]
        j = s['slab']
        assert isinstance(j, int) and 0 <= j < len(slabs)
        r = witness(s['w'])
        assert r['k'] == 4 and Q(s['tau']) == tau and r['box'][4] == (tau, tau)
        assert s['ok'] is True and inside(r['box'], result[j]['box'], result[j]['k'])
        A = interval(s['A'])
        assert (A[0] > 0 if sign == '+' else A[1] < 0)
        assert s['detF0_sign'] == s['endpoint_certificate_sign'] == sign
        if e == 'lo' and star is not None:
            assert r['box'][0][1] <= star
    assert d['counts']['slabs'] == len(slabs) and d['counts']['tau_slabs'] == nt
    assert d['counts']['p_slabs'] == len(slabs)-nt and d['counts']['links'] == len(pairs)
    assert number(d['max_q_upper']) == max(number(s['w']['q']) for s in slabs)
    assert max(r['q'] for r in result) <= number(d['max_q_upper']) < 1
    ds = [r['derivative_lower'] for r in result if r['k'] == 0]
    return dict(slabs=len(slabs), tau_slabs=nt, p_slabs=len(slabs)-nt, links=len(pairs),
                switches=int(switch is not None), witnesses=len(slabs)+len(pairs)+int(switch is not None)+2,
                max_weighted_q=arithmetic.upper_display(max(r['q'] for r in result)),
                min_dtau_dp_lower=str(min(ds)) if ds else None, bracket=[str(lo), str(hi)])


def all_witnesses(d):
    yield from (s['w'] for s in d['slabs'])
    yield from (s['w'] for s in d['links'])
    if d['switch'] is not None:
        yield d['switch']['w']
    yield from (d['endpoints'][e]['w'] for e in ('lo', 'hi'))


def replay_arb(d, precision):
    # Deliberately separate the independent rational proof calculations above
    # from fresh evaluation using the generator's pinned analytic model.
    sys.path.insert(0, str(ROOT/'scripts/two_tail'))
    import sympy as sp
    from flint import ctx, arb
    import two_tail_py_chain as model
    import codex_m1_parameter_monotonicity_arb as independent
    ctx.prec = precision
    eta, z, w = sp.Rational(d['data']['eta']), list(map(sp.Rational, d['data']['z'])), sp.Rational(d['data']['w'])
    assert eta == sp.Rational(49, 100)
    M = model.Model(eta, z, w)
    amp, tau, R = independent.exact_residual(d['data'])
    assert [*amp, tau] == list(M.V)
    assert all(sp.expand(R[i]-M.R[i]) == 0 for i in range(4)), 'Independent residual models differ'
    seedG = []
    for i in (2, 3):
        expression = sp.expand(M.R[i].subs({M.V[0]: 0, M.V[1]: 0, M.V[4]: 0}))
        a1, a0 = sp.Poly(expression, M.V[i], domain='EX').all_coeffs()
        assert not (a1.free_symbols | a0.free_symbols) and a1 != 0
        a1_box = model.bounds(model.ev(a1))
        assert a1_box[0] > 0 or a1_box[1] < 0, 'HS seed denominator may vanish'
        seedG.append(-a0/a1)
    assert [sp.srepr(g) for g in seedG] == d['seed']['G_srepr']
    assert all(sp.expand(r.subs({M.V[0]: 0, M.V[1]: 0, M.V[4]: 0})) == 0 for r in M.R[:2])
    for i, g in enumerate(seedG):
        assert contains(interval(d['seed']['enclosure'][i+2]), model.bounds(model.ev(g))), 'False HS seed enclosure'
    count = 0
    for record in all_witnesses(d):
        c = vector(record['c'], 5, number)
        k = record['k']
        u = [i for i in range(5) if i != k]
        B = [None]*5
        B[k] = interval(record['P'])
        for j, y in zip(u, vector(record['Y'])):
            B[j] = y
        h = [model.iball(B[j][0]-c[j], B[j][1]-c[j]) for j in range(5)]
        zero = [arb(0)]*5
        fresh_f = [model.bounds(p.over(c, zero)) for p in M.Rp]
        fresh_J = [[model.bounds(M.JF[i][j].over(c, h)) for j in u] for i in range(4)]
        fresh_Rp = [model.bounds(M.JF[i][k].over(c, h)) for i in range(4)]
        assert all(contains(old, fresh) for old, fresh in zip(vector(record['f']), fresh_f)), 'False residual enclosure'
        assert all(contains(interval(record['Jy'][i][j]), fresh_J[i][j]) for i in range(4) for j in range(4)), 'False Jacobian enclosure'
        assert all(contains(old, fresh) for old, fresh in zip(vector(record['Rp']), fresh_Rp)), 'False parameter derivative enclosure'
        count += 1
        if count % 500 == 0:
            print(f'  Arb replay {d["control"][:2]}: {count} witnesses', flush=True)
    Acount = 0
    for s in [*d['slabs'], *(d['endpoints'][e] for e in ('lo', 'hi'))]:
        record = s['w']
        c = vector(record['c'], 5, number)
        k = record['k']
        B = [None]*5
        B[k] = interval(record['P'])
        for j, y in zip([i for i in range(5) if i != k], vector(record['Y'])):
            B[j] = y
        assert contains(interval(s['A']), M.A_over(B)), 'False zero-mode enclosure'
        Acount += 1
    return dict(precision_bits=precision, witnesses=count, scalar_enclosures=24*count,
                A_boxes=Acount, seed_G_enclosures=2, symbolic_residual_models_equal=True,
                method='Fresh Arb replay of pinned generator model; independent rational checker; EXTERNAL, not Lean')


def negative_controls(d):
    rejected = []
    def reject(label, f):
        try:
            f()
        except (AssertionError, ValueError, ZeroDivisionError, IndexError, KeyError):
            rejected.append(label)
        else:
            raise AssertionError('Negative control accepted: '+label)
    bad = deepcopy(d)
    bad['script_sha256'][GENERATOR.name] = '0'*64
    reject('stale generator hash', lambda: metadata(bad))
    badw = deepcopy(d['slabs'][0]['w'])
    badw['f'][0] = ['1', '0']
    reject('reversed residual interval', lambda: witness(badw))
    badw2 = deepcopy(d['slabs'][0]['w'])
    unknown = next(i for i in range(5) if i != badw2['k'])
    badw2['c'][unknown] = str(interval(badw2['Y'][0])[1]+1)
    reject('center outside unknown box', lambda: witness(badw2))
    badw3 = deepcopy(d['slabs'][0]['w'])
    badw3['Jy'][0][0] = ['1000000', '1000001']
    reject('corrupted actual Jacobian interval', lambda: witness(badw3))
    for label, edit in [
        ('missing link', lambda x: x['links'].pop()),
        ('flipped endpoint sign', lambda x: x['endpoints']['hi'].__setitem__('A', ['1', '2'])),
        ('seed outside initial box', lambda x: x['seed']['enclosure'].__setitem__(2, ['1000000', '1000001'])),
        ('missing required A positivity', lambda x: x['slabs'][0].__setitem__('A', ['-1', '1']))]:
        modified = deepcopy(d)
        edit(modified)
        reject(label, lambda modified=modified: check_data(modified))
    if d['tau_switch'] is None:
        modified = deepcopy(d)
        lo = Q(d['bracket'][0])
        j = next(i for i, s in enumerate(modified['slabs']) if interval(s['w']['P'])[1] == lo)
        shifted = (lo+interval(modified['slabs'][j+1]['w']['P'])[1])/2
        modified['slabs'][j]['w']['P'][1] = str(shifted)
        modified['slabs'][j+1]['w']['P'][0] = str(shifted)
        reject('missing exact tau_lo break despite contiguous slabs', lambda: check_data(modified))
    return rejected


def main():
    p = ArgumentParser(description=__doc__)
    p.add_argument('--replay-arb', action='store_true')
    p.add_argument('--precision', type=int, default=320)
    p.add_argument('--negative-controls', action='store_true')
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    assert args.precision >= 320
    paths = [ROOT/f'results/two_tail/two_tail_py_chain_{name}.json.gz' for name in ('M1', 'M3')]
    inputs = [Path(__file__).resolve(), SOURCE, GENERATOR, MODEL, *LEAN, *paths,
              ROOT/'scripts/certificates/check_endpoint_witness_rational.py',
              ROOT/'scripts/certificates/codex_m1_parameter_monotonicity_arb.py']
    before = {str(f.relative_to(ROOT.parent)): digest(f) for f in inputs}
    results = {}
    for name, path in zip(('M1', 'M3'), paths):
        with gzip.open(path, 'rt') as f:
            data = json.load(f)
        assert data['control'].startswith(name)
        row = check_data(data)
        if args.replay_arb:
            row['arb_replay'] = replay_arb(data, args.precision)
        if args.negative_controls and name == 'M3':
            row['negative_controls_rejected'] = negative_controls(data)
            if args.replay_arb:
                modified = deepcopy(data)
                modified['slabs'][0]['w']['Rp'] = [['0', '0'] for _ in range(4)]
                try:
                    replay_arb(modified, args.precision)
                except AssertionError as error:
                    assert str(error) == 'False parameter derivative enclosure', str(error)
                    row['arb_negative_controls_rejected'] = ['zeroed parameter derivative enclosure']
                else:
                    raise AssertionError('Fresh Arb replay accepted a false parameter derivative')
        results[name] = row
        print(f'PASS {name}: {row["slabs"]} slabs, {row["links"]} links, weighted q<={row["max_weighted_q"]}', flush=True)
    assert before == {str(f.relative_to(ROOT.parent)): digest(f) for f in inputs}, 'Input changed during audit'
    report = dict(status='PASS_EXTERNAL_AUDIT', created_at_utc=datetime.now(timezone.utc).isoformat(),
                  label='EXTERNAL analytic certificate; independent rational arithmetic; NOT a Lean proof',
                  inputs_sha256=before, results=results,
                  scope='PY-seeded regular analytic root continuation and first zero-frequency zero bracket only; no first loss, all-wave canonicity, zero uniqueness or Taylor-radius conclusion.')
    if args.output:
        output = args.output.resolve()
        assert output.parent == ROOT/'results/certificates'
        output.write_text(json.dumps(report, indent=2)+'\n')
    print('PASS exact dimensions, interval order, centers, metadata pins, weighted self-maps, chain/seed/switch/endpoint matching.')


if __name__ == '__main__':
    main()
