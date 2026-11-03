#!/usr/bin/env python3
"""Independent RATIONAL PART check of M2 second-root/local-graph separation.

Checks all three Krawczyk witnesses, mean-value matrix products, source pins,
exact parameter windows and root-box disjointness/containment. Analytic
f/J/R_tau enclosures remain EXTERNAL mpmath-AD evidence. The PY-root-graph
identification uses the older 009/011 certificate; it is not re-proved here.
Global non-reconnection, first loss and Taylor radii are not inferred.
"""
from argparse import ArgumentParser
from decimal import Decimal
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

import check_endpoint_witness_rational as b
import check_m1_fold_witness_rational as fold

if not __debug__:
    raise RuntimeError('Certificate assertions must remain enabled; do not use python -O.')

ROOT=Path(__file__).resolve().parents[2]
DEFAULT=ROOT/'results/two_tail/two_tail_m2_second_root.json'
FROZEN=ROOT.parent/'MSA_and_1st_Truncation/results/coupling_singularities/codex_m2_zero_mode_firstness.json'
FROZEN_SHA='d75a89d83c0c5fb80c3bdcf243e04c9de906384f1a1da4e573a3c518dff0cbb9'


def disjoint(A,B):
    return any(a[1]<z[0] or z[1]<a[0] for a,z in zip(A,B))


def mean_value_view(w, exact_T):
    # Same exact parameter mean-value expression as the amplitude-slab
    # checker, with p renamed tau and the unknowns now the four amplitudes.
    transformed={**w,'Y':w['X'],'J_over_Y':w['J_over_X'],
                 'p_center':w['tau_center'],'R_p_over_box':w['R_tau'],
                 'C_R_p':w['C_R_tau'],
                 'exact_check_K_strictly_inside_Y':w['exact_check_K_strictly_inside_X']}
    return {'P':list(map(str,exact_T)),'P_iv':w['T'],'witness':transformed}


def check_data(d):
    names={'two_tail_m2_second_root.py','two_tail_endpoint_interval.py','two_tail_m2_jacobian_interval.py'}
    assert set(d['source_sha256'])==names
    for name,h in d['source_sha256'].items():
        assert hashlib.sha256((ROOT/'scripts/two_tail'/name).read_bytes()).hexdigest()==h,name
    assert Path(d['root_box_source']).resolve()==FROZEN
    assert d['root_box_sha256']==FROZEN_SHA==hashlib.sha256(FROZEN.read_bytes()).hexdigest()
    diag=ROOT/'results/two_tail/two_tail_fiber_diag.json'
    assert Path(d['diag_source']).resolve()==diag
    assert hashlib.sha256(diag.read_bytes()).hexdigest()==d['diag_sha256']
    raw=json.loads(FROZEN.read_text(),parse_float=Decimal)
    assert raw['model']=={'eta':'0.1','sigma':'1','z':['1.8','12']}
    boxes=[tuple(map(Q,p)) for p in raw['root_box'][:6]]
    amplitude=boxes[:4];tau,W=boxes[4:6]
    data=d['data']
    assert data['eta']=='1/10' and data['rho']=='6*eta/pi' and data['sigma']=='1' and data['z']==['9/5','12']
    assert b.vector(data['codex_amplitude_box'])==amplitude
    assert b.interval(data['tau_box'])==tau and b.interval(data['w_box'])==W
    q2,X2=b.check_krawczyk(d['r2_box']['witness'])
    assert disjoint(X2,amplitude)
    assert d['r2_disjoint_from_codex_box'] is True
    win=d['window'];delta=Q(win['delta'])
    assert delta==Q(1,10000)
    exact_T=(tau[0]-delta,tau[1]+delta)
    T=b.interval(win['T_iv']);assert b.contains(T,exact_T)
    bounds=[q2];Ys=[]
    for tag in ['Y1','Y2']:
        w=win[tag]['witness']
        assert w['T']==win['T_iv']
        assert b.interval(w['R_tau'][2])==b.interval(w['R_tau'][3])==(Q(0),Q(0))
        bounds.append(fold.slab_check(mean_value_view(w,exact_T)))
        Ys.append(b.vector(w['X']))
    Y1,Y2=Ys
    assert all(b.contains(y,a) for y,a in zip(Y1,amplitude))
    assert all(b.contains(y,x) for y,x in zip(Y2,X2))
    assert disjoint(Y1,Y2)
    assert win['checks']=={'Y1_contains_codex_box':True,'Y2_contains_X2':True,'Y1_Y2_disjoint':True}
    assert d['passed'] is True
    # Verify the inherited old cover is still the pinned artifact. Its
    # thousands of analytic slab enclosures are not replayed by this checker.
    cover=FROZEN.parent/raw['cover']['file']
    assert hashlib.sha256(cover.read_bytes()).hexdigest()==raw['cover']['sha256']
    return bounds


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('report',nargs='?',type=Path,default=DEFAULT)
    args=parser.parse_args()
    bounds=check_data(json.loads(args.report.read_text()))
    for label,q in zip(['r2','Y1','Y2'],bounds):
        print(f'PASS {label}: exact rational Krawczyk expression; norm <= {b.upper_display(q)}')
    print('PASS local root-box separation, window coverage, source hashes and old cover hash.')
    print('Analytic bounds/old PY-chain identification remain inherited EXTERNAL evidence; no global non-reconnection.')


if __name__=='__main__':
    main()
