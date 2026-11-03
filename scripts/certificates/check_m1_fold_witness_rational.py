#!/usr/bin/env python3
"""Independent rational audit of the M1 amplitude-parametrized branch witness.

Recomputes four mean-value Krawczyk slab witnesses AND all three point
Krawczyk witnesses joining them. Checks exact coverage, source pins, bridge
nesting, endpoint matching and the wide coupling hull. Analytic enclosures
and preservation of roots in the shrink iterations remain EXTERNAL evidence.
No monotonicity in tau or narrow tau zero bracket follows from this audit alone.
"""
from argparse import ArgumentParser
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

import check_endpoint_witness_rational as b

if not __debug__:
    raise RuntimeError('Certificate assertions must remain enabled; do not use python -O.')

ROOT = Path(__file__).resolve().parents[2]
DEFAULT = ROOT/'results/two_tail/two_tail_m1_fold_branch.json'


def point_view(w):
    return {**w, 'X': w['Y'], 'J_over_X': w['J_over_Y'],
            'exact_check_K_strictly_inside_X': w['exact_check_K_strictly_inside_Y']}


def slab_check(s):
    w = s['witness']
    center = list(map(Q, w['center']))
    assert len(center) == 4
    C = b.matrix(w['C_rational'], Q)
    Y, K, f = map(b.vector, (w['Y'], w['K'], w['f_center']))
    J, E = map(lambda x: b.matrix(x,b.interval), (w['J_over_Y'], w['I_minus_CJ']))
    Rp, CRp = map(b.vector,(w['R_p_over_box'],w['C_R_p']))
    P, exact_P = b.interval(s['P_iv']), b.interval(s['P'])
    assert exact_P[0] < exact_P[1] and b.contains(P,exact_P)
    pc = Q(w['p_center'])
    assert P[0] < pc < P[1]
    assert all(lo < c < hi for c,(lo,hi) in zip(center,Y))
    for i in range(4):
        for j in range(4):
            v = Q(i == j)
            exact = b.plus((v,v), b.negative(b.total(b.times((C[i][k],C[i][k]),J[k][j]) for k in range(4))))
            assert b.contains(E[i][j],exact), ('I-CJ',i,j)
        exact = b.total(b.times((C[i][k],C[i][k]),Rp[k]) for k in range(4))
        assert b.contains(CRp[i],exact), ('C*R_p',i)
    rows = [sum((max(abs(lo),abs(hi)) for lo,hi in row),Q(0)) for row in E]
    q = Q(w['inf_norm_upper'])
    assert max(rows) <= q < 1
    for i in range(4):
        exact = b.plus((center[i],center[i]), b.negative(b.total(b.times((C[i][k],C[i][k]),f[k]) for k in range(4))))
        exact = b.plus(exact,b.negative(b.times(CRp[i],b.plus(P,(-pc,-pc)))))
        exact = b.plus(exact,b.total(b.times(E[i][j],b.plus(Y[j],(-center[j],-center[j]))) for j in range(4)))
        assert b.contains(K[i],exact), ('mean-value Krawczyk expression',i)
        assert b.contains(Y[i],K[i],strict=True), ('strict K inclusion',i)
    assert w['exact_check_K_strictly_inside_Y'] is True and w['exact_check_norm_lt_1'] is True
    return q


def check_data(d):
    expected={'two_tail_m1_fold_branch.py','two_tail_endpoint_interval.py','two_tail_m2_jacobian_interval.py'}
    assert set(d['source_sha256']) == expected
    for name, h in d['source_sha256'].items():
        assert hashlib.sha256((ROOT/'scripts/two_tail'/name).read_bytes()).hexdigest() == h,name
    src = ROOT/'results/two_tail/two_tail_endpoint_interval_exact.json'
    assert Path(d['endpoint_source']).resolve() == src
    assert hashlib.sha256(src.read_bytes()).hexdigest() == d['endpoint_source_sha256']
    endpoint = json.loads(src.read_text())
    b.check_data(endpoint)
    c=next(c for c in endpoint['controls'] if c['name'].startswith('M1'))
    assert d['data'] == {'eta':c['eta'],'rho':'6*eta/pi','sigma':'1','z':c['z'],'f':c['f'],'w':c['w']}
    assert d['parameter_coordinate'] == 0
    slabs, chain = d['slabs'], d['chain']
    assert len(slabs) == 4 and len(chain) == len(slabs)-1
    hull=b.interval(d['p_hull'])
    assert Q(slabs[0]['P'][0]) == hull[0] and Q(slabs[-1]['P'][1]) == hull[1]
    bounds=[slab_check(s) for s in slabs]
    for i,ch in enumerate(chain):
        p=Q(ch['p'])
        assert p == Q(slabs[i]['P'][1]) == Q(slabs[i+1]['P'][0])
        # Recheck the INITIAL point existence/uniqueness witness, not just
        # the final bridge box's geometric nesting.
        b.check_krawczyk(point_view(ch['witness']))
        Z=b.vector(ch['Z'])
        assert all(lo < hi for lo,hi in Z)
        for box in [ch['witness']['Y'],slabs[i]['witness']['Y'],slabs[i+1]['witness']['Y']]:
            assert all(b.contains(y,z,strict=True) for y,z in zip(b.vector(box),Z))
        assert ch['exact_check_Z_inside_both'] is True
    rb=c['rigorous_bracket']
    for end, index in [('lo',0),('hi',len(slabs)-1)]:
        root=b.vector(rb[end]['root_enclosure_after_shrink']);tau=Q(rb[end]['tau'])
        assert b.interval(d['endpoints'][end]['p_box']) == root[0]
        assert b.contains(b.interval(slabs[index]['P_iv']),root[0])
        y=root[1:]+[(tau,tau)]
        assert all(b.contains(yy,yyroot,strict=True) for yy,yyroot in zip(b.vector(slabs[index]['witness']['Y']),y))
        A=b.interval(rb[end]['A_over_root'])
        sign='+' if A[0]>0 else '-' if A[1]<0 else '0?'
        assert sign == d['endpoints'][end]['detF0_sign'] == ('+' if end=='lo' else '-')
        assert tau == Q(d['endpoints'][end]['tau'])
        assert d['endpoints'][end]['p_inside_P'] is True and d['endpoints'][end]['root_inside_Y'] is True
    tau_hull=(min(Q(s['witness']['Y'][3][0]) for s in slabs),max(Q(s['witness']['Y'][3][1]) for s in slabs))
    assert b.interval(d['tau_hull']) == tau_hull
    assert d['passed'] is True
    return bounds,tau_hull


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('report',nargs='?',type=Path,default=DEFAULT)
    args=parser.parse_args()
    bounds,_=check_data(json.loads(args.report.read_text()))
    print(f'PASS four slab witnesses, max norm <= {b.upper_display(max(bounds))}; all three point bridge witnesses.')
    print('PASS exact cover, source pins, bridge/root matching, endpoint signs and wide tau hull.')
    print('Analytic enclosures and shrink-root preservation remain EXTERNAL; no tau monotonicity inferred.')


if __name__ == '__main__':
    main()
