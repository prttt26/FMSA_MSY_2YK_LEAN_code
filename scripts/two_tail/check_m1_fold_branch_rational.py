"""Standard-library re-check of results/two_tail/two_tail_m1_fold_branch.json (rational part only).

For every slab it recomputes, in exact Fraction interval arithmetic, the Krawczyk expression
    c - C f(c; p~) - (C R_p)(P - p~) + E (Y - c)
from the stored center c, rational C, f_center, C_R_p, P, p~, I-CJ (E) and Y, and checks
that the stored K covers it and that K lies strictly inside Y.  It also checks that the stored
C_R_p covers C*R_p and that E covers I - C*J (both from the stored J/R_p enclosures), that
norm upper < 1, that each chain box Z lies strictly inside both neighbouring Y, and that the
endpoint roots lie in the first/last slab.  It does NOT check the analytic enclosures
(f, J, R_p, A), which come from the mpmath-AD calculation.

Usage: python3 check_m1_fold_branch_rational.py [JSON]
"""
import sys, json
from fractions import Fraction as Q
from pathlib import Path

P0 = Path(__file__).resolve().parents[2]/'results'/'two_tail'/'two_tail_m1_fold_branch.json'


def I(s): return (Q(s[0]), Q(s[1]))
def add(a, b): return (a[0] + b[0], a[1] + b[1])
def sub(a, b): return (a[0] - b[1], a[1] - b[0])
def mul(a, b):
    p = [a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1]]; return (min(p), max(p))
def pt(x): return (x, x)
def covers(big, small): return big[0] <= small[0] and small[1] <= big[1]
def strict_in(inner, outer): return outer[0] < inner[0] and inner[1] < outer[1]


def main():
    d = json.load(open(sys.argv[1] if len(sys.argv) > 1 else P0))
    ok = True
    for n, s in enumerate(d['slabs']):
        w = s['witness']
        c = [Q(x) for x in w['center']]; C = [[Q(x) for x in r] for r in w['C_rational']]
        Y = [I(v) for v in w['Y']]; K = [I(v) for v in w['K']]; f = [I(v) for v in w['f_center']]
        J = [[I(v) for v in r] for r in w['J_over_Y']]; E = [[I(v) for v in r] for r in w['I_minus_CJ']]
        Rp = [I(v) for v in w['R_p_over_box']]; CRp = [I(v) for v in w['C_R_p']]
        P = I(s['P_iv']); pc = Q(w['p_center'])
        # E covers I - C J, CRp covers C Rp
        for i in range(4):
            for j in range(4):
                acc = pt(Q(1) if i == j else Q(0))
                for m in range(4):
                    acc = sub(acc, mul(pt(C[i][m]), J[m][j]))
                ok &= covers(E[i][j], acc)
            acc = pt(Q(0))
            for m in range(4):
                acc = add(acc, mul(pt(C[i][m]), Rp[m]))
            ok &= covers(CRp[i], acc)
        # Krawczyk expression
        for i in range(4):
            acc = pt(c[i])
            for m in range(4):
                acc = sub(acc, mul(pt(C[i][m]), f[m]))
            acc = sub(acc, mul(CRp[i], sub(P, pt(pc))))
            for j in range(4):
                acc = add(acc, mul(E[i][j], sub(Y[j], pt(c[j]))))
            ok &= covers(K[i], acc) and strict_in(K[i], Y[i])
        # norm
        rows = [sum(max(abs(E[i][j][0]), abs(E[i][j][1])) for j in range(4)) for i in range(4)]
        ok &= max(rows) <= Q(w['inf_norm_upper']) < 1
        print(f"slab {n}: Krawczyk recomputed and covered, K strictly in Y, norm {float(max(rows)):.6f} < 1: {ok}")
    for ch, (s0, s1) in zip(d['chain'], zip(d['slabs'], d['slabs'][1:])):
        Z = [I(v) for v in ch['Z']]
        good = all(strict_in(z, I(y)) for z, y in zip(Z, s0['witness']['Y'])) and \
               all(strict_in(z, I(y)) for z, y in zip(Z, s1['witness']['Y'])) and Q(ch['p']) == Q(s0['P'][1]) == Q(s1['P'][0])
        ok &= good; print(f"chain p={float(Q(ch['p']))!r}: Z strictly inside both Y: {good}")
    # endpoints: recomputed from the endpoint-certificate JSON (hash-checked), not from stored booleans
    import hashlib
    src = Path(d['endpoint_source']); raw = src.read_bytes()
    ok &= hashlib.sha256(raw).hexdigest() == d['endpoint_source_sha256']
    ex = json.loads(raw); c = next(c for c in ex['controls'] if c['name'].startswith('M1')); rb = c['rigorous_bracket']
    k = d['parameter_coordinate']
    for e in ('lo', 'hi'):
        u = [I(b) for b in rb[e]['root_enclosure_after_shrink']]; tau = Q(rb[e]['tau'])
        A = I(rb[e]['A_over_root']); sign = '+' if A[0] > 0 else '-' if A[1] < 0 else '0?'
        y = [b for i, b in enumerate(u) if i != k] + [pt(tau)]
        hit = [s for s in d['slabs'] if covers(I(s['P_iv']), u[k])
               and all(strict_in(a, I(b)) for a, b in zip(y, s['witness']['Y']))]
        good = len(hit) >= 1 and sign == d['endpoints'][e]['detF0_sign'] and Q(d['endpoints'][e]['tau']) == tau
        ok &= good
        print(f"endpoint {e}: tau={float(tau)!r}, det F(0) sign {sign} from exact A; root inside a slab box "
              f"(p in P, (v, tau) strictly in Y): {good}")
    ok &= {d['endpoints'][e]['detF0_sign'] for e in ('lo', 'hi')} == {'+', '-'}
    print('ALL RATIONAL CHECKS PASS' if ok else 'A CHECK FAILED')
    return 0 if ok else 1


if __name__ == '__main__':
    assert __debug__, 'run without -O'
    sys.exit(main())
