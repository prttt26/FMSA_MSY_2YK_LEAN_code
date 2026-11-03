#!/usr/bin/env python3
"""Exact RATIONAL PART check of the new M1 parameter-derivative certificate.

Checks the existing fold witness, source pins, literal box/C/center matching,
component bounds from E,v and positive tau derivative on every slab. The
analytic E,v enclosures still rely on the external SymPy/Arb calculation.
"""
from argparse import ArgumentParser
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

import check_m1_fold_witness_rational as fold
import check_endpoint_witness_rational as b

if not __debug__:
    raise RuntimeError('Certificate assertions must remain enabled; do not use python -O.')

ROOT=Path(__file__).resolve().parents[2]
DEFAULT=ROOT/'results/certificates/codex_m1_parameter_monotonicity_arb.json'


def check_data(d):
    expected={
      'MSA_Convergence/scripts/certificates/codex_m1_parameter_monotonicity_arb.py',
      'MSA_Convergence/scripts/certificates/check_m1_fold_witness_rational.py',
      'MSA_Convergence/scripts/certificates/check_endpoint_witness_rational.py',
      'MSA_Convergence/scripts/certificates/codex_m2_jacobian_arb.py',
      'MSA_Convergence/scripts/certificates/check_m1_parameter_monotonicity_rational.py',
      'MSA_Convergence/results/two_tail/two_tail_m1_fold_branch.json',
      'MSA_Convergence/MSAConvergence/BHResidualPolynomials.lean',
      'MSA_and_1st_Truncation/LeanCode/YukawaOZMix/MSAMultiTailMixtureSystem.lean',
      'MSA_and_1st_Truncation/LeanCode/YukawaOZMix/MSAMixtureConcrete.lean',
      'MSA_and_1st_Truncation/LeanCode/YukawaOZMix/MSAMixtureCancellation.lean',
      'MSA_and_1st_Truncation/LeanCode/HSMixture/MatrixQ0.lean'}
    assert set(d['source_sha256'])==expected
    for p,h in d['source_sha256'].items():
        assert hashlib.sha256((ROOT.parent/p).read_bytes()).hexdigest()==h,p
    raw=(ROOT/'results/two_tail/two_tail_m1_fold_branch.json').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==d['fold_witness_source_sha256']
    original=json.loads(raw)
    fold.check_data(original)
    assert d['endpoint_source_sha256']==original['endpoint_source_sha256']
    assert d['data']==original['data']
    assert d['parameter']=='p=Dt1' and d['unknown_order']==['Dt2','G1','G2','tau']
    assert d['physical_amplitude_order']==['Dt1','Dt2','G1','G2']
    assert d['zero_frequency_identity']=={'phi_qp':'-1/2','phi_a':'1/6','phi_c':'1','symbolic_F0_equals_A_over_2pi':True}
    assert d['endpoint_tau_bracket']==[original['endpoints'][k]['tau'] for k in ['lo','hi']]
    lower,upper=Q(d['tau_derivative_strict_lower_rational']),Q(d['tau_derivative_strict_upper_rational'])
    assert 0<lower==Q(137,10**6)<upper==Q(176,10**6)
    assert len(d['slabs'])==len(original['slabs'])==4
    for i,(rec,s) in enumerate(zip(d['slabs'],original['slabs'])):
        w=s['witness']
        assert rec['slab_index']==i and rec['p_exact']==s['P'] and rec['p_interval']==s['P_iv']
        assert rec['Y']==w['Y'] and rec['C_rational']==w['C_rational']
        assert rec['amplitude_center_rational']==[w['p_center'],*w['center'][:3]]
        E=b.matrix(rec['E_rational_enclosure'],b.interval)
        v=b.vector(rec['v_rational_enclosure'])
        M=[[max(abs(a),abs(z)) for a,z in row] for row in E]
        V=[max(abs(a),abs(z)) for a,z in v]
        q=max(sum(row,Q(0)) for row in M)
        assert 0<=q==Q(rec['norm_upper_rational'])<1
        initial=max(V)/(1-q)
        assert initial==Q(rec['initial_norm_bound_rational'])
        assert rec['component_substitution_steps']==2
        B=[initial]*4
        for _ in range(2):
            B=[V[k]+sum((M[k][j]*B[j] for j in range(4)),Q(0)) for k in range(4)]
        assert B==list(map(Q,rec['component_bounds_rational']))
        computed=[]
        for k in range(4):
            error=sum((M[k][j]*B[j] for j in range(4)),Q(0))
            computed.append((v[k][0]-error,v[k][1]+error))
        assert computed==[b.interval(x) for x in rec['derivative_rational_enclosure']]
        assert lower<computed[3][0]<=computed[3][1]<upper
    assert d['status']=='PASS_EXTERNAL_M1_PARAMETER_MONOTONICITY'
    return lower,upper


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('report',nargs='?',type=Path,default=DEFAULT)
    args=parser.parse_args()
    check_data(json.loads(args.report.read_text()))
    print('PASS exact sources/boxes/C, all four component bounds and 0.000137 < d(tau)/d(p) < 0.000176.')
    print('Analytic E,v bounds and original root/shrink certificates remain EXTERNAL; NOT a Lean proof.')


if __name__=='__main__':
    main()
