"""Standard-library re-check of results/two_tail/two_tail_m3_arb_recheck.json (rational part only).

For every witness it recomputes, in exact Fraction intervals, I - C J from the stored C and the Arb
J enclosure (and checks the stored E covers it), the Krawczyk expression c - C f(c; T) + E (X - c)
(and checks the stored K covers it and lies strictly inside X), and the norm.  Against the
hash-checked endpoint certificate it checks that the re-checked witnesses use exactly the stored
center, C, X and tau, that the tiny endpoint boxes S lie strictly inside the parametric X at the
exact bracket ends, and the signs of A from its exact endpoints.  It does NOT check the Arb
enclosures (f, J, A) themselves.

Usage: python3 check_m3_arb_recheck_rational.py [JSON]
"""
import sys, json, hashlib
from fractions import Fraction as Q
from pathlib import Path

P0 = Path(__file__).resolve().parents[2]/'results'/'two_tail'/'two_tail_m3_arb_recheck.json'
def I(s): return (Q(s[0]), Q(s[1]))
def add(a, b): return (a[0] + b[0], a[1] + b[1])
def sub(a, b): return (a[0] - b[1], a[1] - b[0])
def mul(a, b):
    p = [a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1]]; return (min(p), max(p))
def pt(x): return (x, x)
def covers(big, small): return big[0] <= small[0] and small[1] <= big[1]
def strict_in(i, o): return o[0] < i[0] and i[1] < o[1]


def check(w):
    c = [Q(x) for x in w['center']]; C = [[Q(x) for x in r] for r in w['C_rational']]
    X = [I(v) for v in w['X']]; K = [I(v) for v in w['K']]; f = [I(v) for v in w['f_center_arb']]
    J = [[I(v) for v in r] for r in w['J_over_X_arb']]; E = [[I(v) for v in r] for r in w['I_minus_CJ']]
    ok = True
    for i in range(4):
        for j in range(4):
            acc = pt(Q(int(i == j)))
            for m in range(4):
                acc = sub(acc, mul(pt(C[i][m]), J[m][j]))
            ok &= covers(E[i][j], acc)
        acc = pt(c[i])
        for m in range(4):
            acc = sub(acc, mul(pt(C[i][m]), f[m]))
        for j in range(4):
            acc = add(acc, mul(E[i][j], sub(X[j], pt(c[j]))))
        ok &= covers(K[i], acc) and strict_in(K[i], X[i])
    rows = [sum(max(abs(e[0]), abs(e[1])) for e in row) for row in E]
    ok &= max(rows) <= Q(w['inf_norm_upper']) < 1
    return ok, float(max(rows))


def main():
    d = json.load(open(sys.argv[1] if len(sys.argv) > 1 else P0)); ok = True
    raw = Path(d['source']).read_bytes(); ok &= hashlib.sha256(raw).hexdigest() == d['source_sha256']
    c = next(c for c in json.loads(raw)['controls'] if c['name'].startswith('M3'))
    src = {f'runs.{k}': (c['runs'][k]['krawczyk'], c['runs'][k]['tau'], c['runs'][k]['tau']) for k in ('tau_hat', 'tau_lo', 'tau_hi')}
    src.update({f'rigorous_bracket.{k}': (c['rigorous_bracket'][k]['krawczyk'],) + (c['rigorous_bracket'][k]['tau'],)*2
                for k in ('lo', 'hi')})
    src['parametric'] = (c['parametric']['krawczyk'],) + tuple(c['parametric']['tau_interval_exact'])
    for name, (kw, t0, t1) in src.items():
        w = d['witnesses'][name]
        same = all(Q(a) == Q(b) for a, b in zip(w['center'], kw['center'])) and \
            all(Q(a) == Q(b) for ra, rb in zip(w['C_rational'], kw['C_rational']) for a, b in zip(ra, rb)) and \
            all(I(a) == I(b) for a, b in zip(w['X'], kw['X'])) and I(w['T']) == (Q(t0), Q(t1)) and \
            Q(w['tau_center']) == (Q(t0) + Q(t1))/2
        g, nrm = check(w); ok &= g and same
        print(f'{name}: same center/C/X/tau as the stored witness {same}; Krawczyk recomputed and covered, '
              f'K strictly in X, norm {nrm:.6f} < 1: {g}')
    PX = [I(v) for v in c['parametric']['krawczyk']['X']]
    signs = {}
    for e in ('lo', 'hi'):
        r = d['endpoints'][e]; w = r['witness']
        g, nrm = check(w)
        tau = Q(c['rigorous_bracket'][e]['tau'])
        g &= Q(r['tau']) == tau and I(w['T']) == (tau, tau) and Q(w['tau_center']) == tau
        g &= all(strict_in(I(s), x) for s, x in zip(w['X'], PX))
        A = I(r['A_over_S']); signs[e] = '+' if A[0] > 0 else '-' if A[1] < 0 else '0?'
        g &= signs[e] == r['detF0_sign']
        ok &= g
        print(f'endpoint {e}: tau = {float(tau)!r}; Krawczyk on S recomputed, norm {nrm:.3g}; S strictly inside the '
              f'parametric X; sign of A from exact endpoints {signs[e]}: {g}')
    ok &= set(signs.values()) == {'+', '-'}
    print('ALL RATIONAL CHECKS PASS' if ok else 'A CHECK FAILED')
    return 0 if ok else 1


if __name__ == '__main__':
    assert __debug__, 'run without -O'
    sys.exit(main())
