"""Standard-library re-check of results/two_tail/two_tail_m2_second_root.json (rational part only).

For the r2 box and for both window boxes Y1, Y2 it recomputes, in exact Fraction intervals, three
things: I - C J from the stored C and J (and checks the stored E covers it); the Krawczyk
expression c - C f(c) [- (C R_tau)(T - tau_c)] + E (X - c) (and checks the stored K covers it
and lies strictly inside X); and the norm.  It re-checks C R_tau against the stored R_tau.  It
re-checks, against the hash-checked Codex root box, that X2 and the Codex amplitude box are
disjoint, that Y1 contains the Codex box, that Y2 contains X2, and that Y1 and Y2 are disjoint.
It does NOT check the analytic enclosures (f, J), which come from the mpmath-AD calculation.

Usage: python3 check_m2_second_root_rational.py [JSON]
"""
import sys, json, hashlib
from fractions import Fraction as Q
from pathlib import Path

P0 = Path(__file__).resolve().parents[2]/'results'/'two_tail'/'two_tail_m2_second_root.json'
def I(s): return (Q(s[0]), Q(s[1]))
def add(a, b): return (a[0] + b[0], a[1] + b[1])
def sub(a, b): return (a[0] - b[1], a[1] - b[0])
def mul(a, b):
    p = [a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1]]; return (min(p), max(p))
def pt(x): return (x, x)
def covers(big, small): return big[0] <= small[0] and small[1] <= big[1]
def strict_in(i, o): return o[0] < i[0] and i[1] < o[1]
def disjoint(A, B): return any(a[1] < b[0] or b[1] < a[0] for a, b in zip(A, B))
def contains(Big, Small): return all(covers(b, s) for b, s in zip(Big, Small))


def check_witness(w):
    c = [Q(x) for x in w['center']]; C = [[Q(x) for x in r] for r in w['C_rational']]
    X = [I(v) for v in w['X']]; K = [I(v) for v in w['K']]; f = [I(v) for v in w['f_center']]
    J = [[I(v) for v in r] for r in w['J_over_X']]; E = [[I(v) for v in r] for r in w['I_minus_CJ']]
    ok = True
    for i in range(4):
        for j in range(4):
            acc = pt(Q(1) if i == j else Q(0))
            for m in range(4):
                acc = sub(acc, mul(pt(C[i][m]), J[m][j]))
            ok &= covers(E[i][j], acc)
    mv = 'C_R_tau' in w
    if mv:
        Rt = [I(v) for v in w['R_tau']]; CRt = [I(v) for v in w['C_R_tau']]; T = I(w['T']); tc = Q(w['tau_center'])
        for i in range(4):
            acc = pt(Q(0))
            for m in range(4):
                acc = add(acc, mul(pt(C[i][m]), Rt[m]))
            ok &= covers(CRt[i], acc)
    for i in range(4):
        acc = pt(c[i])
        for m in range(4):
            acc = sub(acc, mul(pt(C[i][m]), f[m]))
        if mv:
            acc = sub(acc, mul(CRt[i], sub(T, pt(tc))))
        for j in range(4):
            acc = add(acc, mul(E[i][j], sub(X[j], pt(c[j]))))
        ok &= covers(K[i], acc) and strict_in(K[i], X[i])
    rows = [sum(max(abs(E[i][j][0]), abs(E[i][j][1])) for j in range(4)) for i in range(4)]
    ok &= max(rows) <= Q(w['inf_norm_upper']) < 1
    return ok, float(max(rows)), mv


def main():
    d = json.load(open(sys.argv[1] if len(sys.argv) > 1 else P0)); ok = True
    raw = Path(d['root_box_source']).read_bytes(); ok &= hashlib.sha256(raw).hexdigest() == d['root_box_sha256']
    rb = json.loads(raw)['root_box']
    codex = [(Q(str(lo)), Q(str(hi))) for lo, hi in rb[:4]]
    ok &= [[str(a), str(b)] for a, b in codex] == d['data']['codex_amplitude_box']
    X2 = [I(v) for v in d['r2_box']['witness']['X']]
    for name, w in (('r2 box', d['r2_box']['witness']), ('Y1', d['window']['Y1']['witness']), ('Y2', d['window']['Y2']['witness'])):
        g, nrm, mv = check_witness(w); ok &= g
        print(f"{name}: Krawczyk recomputed {'(mean-value tau) ' if mv else ''}and covered, K strictly in X, norm {nrm:.6f} < 1: {g}")
    Y1 = [I(v) for v in d['window']['Y1']['witness']['X']]; Y2 = [I(v) for v in d['window']['Y2']['witness']['X']]
    checks = dict(X2_disjoint_codex=disjoint(X2, codex), Y1_contains_codex=contains(Y1, codex),
                  Y2_contains_X2=contains(Y2, X2), Y1_Y2_disjoint=disjoint(Y1, Y2))
    T = I(d['window']['T_iv']); Tc = (Q(d['data']['tau_box'][0]), Q(d['data']['tau_box'][1]))
    checks['window_covers_codex_tau_box'] = covers(T, Tc)
    ok &= all(checks.values())
    print('inclusion/disjointness (exact, recomputed):', checks)
    print('ALL RATIONAL CHECKS PASS' if ok else 'A CHECK FAILED')
    return 0 if ok else 1


if __name__ == '__main__':
    assert __debug__, 'run without -O'
    sys.exit(main())
