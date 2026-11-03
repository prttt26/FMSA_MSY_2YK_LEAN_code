#!/usr/bin/env python3
"""EXTERNAL monotonicity certificate for the EXISTING four M1 parameter slabs.

No new roots or slabs are computed. Exact symbolic differentiation,
preconditioning BEFORE interval evaluation, and centered polynomial coefficients
avoid the raw AD dependency inflation. Arb bounds E=I-C*R_y and v=-C*R_p.
Exact rational component bounds then enclose d=-(R_y)^(-1)*R_p and prove its
last component d(tau)/d(p) positive. NOT a Lean proof.

Requires python-flint and SymPy; validated with 0.6.0 and 1.13.2. Example:
  PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/codex_m1_parameter_monotonicity_arb.py
"""
from argparse import ArgumentParser
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import sys

import flint
from flint import arb, ctx
import sympy as sp

from codex_m2_jacobian_arb import arb_evaluator, interval, enclosure
import check_m1_fold_witness_rational as fold_check

if not __debug__:
    raise RuntimeError('Certificate assertions must remain enabled; do not use python -O.')

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT/'results/two_tail/two_tail_m1_fold_branch.json'
OUTPUT = ROOT/'results/certificates/codex_m1_parameter_monotonicity_arb.json'


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def exact_residual(data):
    """Literal scalar two-tail residual in ORIGINAL D1,D2,G1,G2 coordinates."""
    amp = sp.symbols('D1 D2 G1 G2')
    tau = sp.Symbol('tau')
    ds, gs = amp[:2], amp[2:]
    eta = sp.Rational(49,100)
    rho, vac = 6*eta/sp.pi, 1-eta
    z = [sp.Rational(x) for x in data['z']]
    strength = [sp.Integer(1),sp.Rational(data['w'])]
    cs = [(1-2*sp.pi*rho*gs[i]*sp.exp(-z[i])/z[i])*ds[i] for i in range(2)]
    ws = [2*sp.pi/z[i]*rho*gs[i]*ds[i] for i in range(2)]
    ms = [-rho/z[i]*(ws[i]+(1+z[i])*cs[i]) for i in range(2)]
    ns = [rho*(ws[i]/z[i]**2+(1+z[i]+z[i]**2/2)*cs[i]/z[i]**2) for i in range(2)]
    a0 = 2*sp.pi/vac*(1+sp.pi*rho/(2*vac))
    qp0 = 2*sp.pi/vac*(1+sp.pi*rho/(4*vac))
    aa = a0+sum(a0*ms[i]+2*sp.pi**2*rho/vac**2*ns[i] for i in range(2))
    qp = qp0+sum(qp0*ms[i]+a0*ns[i] for i in range(2))
    # Honest zero-frequency moments of the finite transform, rather than
    # substituting s=0 into a formula with removable denominators.
    frequency=sp.Symbol('s',real=True)
    assert sp.limit((1-frequency-sp.exp(-frequency))/frequency**2,frequency,0)==-sp.Rational(1,2)
    assert sp.limit((1-frequency+frequency**2/2-sp.exp(-frequency))/frequency**3,frequency,0)==sp.Rational(1,6)
    assert sp.limit((1-sp.exp(-frequency))/frequency,frequency,0)==1
    qhat_zero=-qp/2+aa/6+sum((ws[j]+cs[j])/z[j]+cs[j] for j in range(2))
    assert sp.expand(1-rho*qhat_zero-aa/(2*sp.pi))==0
    first, second = [], []
    for i,s in enumerate(z):
        e = sp.exp(-s)
        qhat = ((1-s-e)/s**2*qp+(1-s+s**2/2-e)/s**3*aa
                +sum(ws[j]/(s+z[j])+cs[j]*(1-e)/s+cs[j]*e/(s+z[j]) for j in range(2)))
        factor = 1-rho*qhat
        source = (aa+s*qp+sum(s**2*z[j]/(s+z[j])*cs[j] for j in range(2)))/s**2
        first.append(ds[i]*factor-2*sp.pi*tau*strength[i]/s)
        second.append(2*sp.pi*gs[i]*factor-source)
    residual = sp.Matrix([sp.expand(x) for x in first+second])
    assert not any(expr.atoms(sp.Float) for expr in residual)
    assert all(sp.Poly(expr,*amp,tau).total_degree() <= 3 for expr in residual)
    return amp,tau,residual


def centered_evaluator(amp, centers, boxes):
    delta = sp.symbols('delta0 delta1 delta2 delta3')
    shifts = {amp[i]: delta[i]+sp.Rational(centers[i]) for i in range(4)}
    balls = [interval(Q(boxes[i][0])-centers[i],Q(boxes[i][1])-centers[i]) for i in range(4)]
    coefficient = arb_evaluator({})
    fingerprints = []

    def evaluate(expr):
        # Collect coefficients of each monomial BEFORE interval evaluation.
        # Each coefficient is constant and keeps exact pi/exp cancellations.
        poly = sp.Poly(sp.expand(sp.expand(expr).subs(shifts,simultaneous=True)),*delta)
        assert poly.total_degree() <= 2
        fingerprints.append(sp.srepr(poly.as_expr()))
        value = arb(0)
        for powers, coeff in poly.terms():
            assert not coeff.free_symbols and not coeff.atoms(sp.Float)
            term = coefficient(coeff)
            # Repeated multiplication encloses integer powers even for balls
            # crossing zero; no real-exponent/log branch is invoked.
            for i,power in enumerate(powers):
                for _ in range(power):
                    term = term*balls[i]
            value = value+term
        assert value.is_finite()
        return value
    return evaluate,fingerprints


def component_certificate(E, v):
    E = [[tuple(map(Q,enclosure(x))) for x in row] for row in E]
    v = [tuple(map(Q,enclosure(x))) for x in v]
    M = [[max(abs(lo),abs(hi)) for lo,hi in row] for row in E]
    V = [max(abs(lo),abs(hi)) for lo,hi in v]
    q = max(sum(row,Q(0)) for row in M)
    assert 0 <= q < 1
    initial = max(V)/(1-q)
    bounds = [initial]*4
    # Start with the ordinary infinity-norm bound, then use two component
    # substitutions |d| <= |v|+|E|*|d|. Every step remains a proved bound.
    for _ in range(2):
        bounds = [V[i]+sum((M[i][j]*bounds[j] for j in range(4)),Q(0)) for i in range(4)]
    derivative = []
    for i in range(4):
        error = sum((M[i][j]*bounds[j] for j in range(4)),Q(0))
        derivative.append((v[i][0]-error,v[i][1]+error))
    assert derivative[3][0] > Q(137,10**6)
    assert derivative[3][1] < Q(176,10**6)
    return dict(E_rational_enclosure=[[[str(q) for q in x] for x in row] for row in E],
                v_rational_enclosure=[[str(q) for q in x] for x in v],
                norm_upper_rational=str(q), initial_norm_bound_rational=str(initial),
                component_substitution_steps=2, component_bounds_rational=list(map(str,bounds)),
                derivative_rational_enclosure=[[str(q) for q in x] for x in derivative])


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--precision',type=int,default=256)
    parser.add_argument('--output',type=Path,default=OUTPUT)
    args=parser.parse_args()
    assert args.precision >= 192
    assert ROOT.parent/'MSA_and_1st_Truncation' not in args.output.resolve().parents
    assert args.output.resolve() != SOURCE
    ctx.prec=args.precision
    original=json.loads(SOURCE.read_text())
    fold_check.check_data(original)
    amp,tau,residual=exact_residual(original['data'])
    ys=(*amp[1:],tau)
    J,Rp=residual.jacobian(ys),residual.diff(amp[0])
    records=[]
    for n,slab in enumerate(original['slabs']):
        w=slab['witness']
        C=sp.Matrix([[sp.Rational(x) for x in row] for row in w['C_rational']])
        preE,prev=sp.eye(4)-C*J,-C*Rp
        assert all(not(tau in expr.free_symbols) for expr in [*preE,*prev])
        centers=[Q(w['p_center']),*map(Q,w['center'][:3])]
        boxes=[slab['P_iv'],*w['Y'][:3]]
        evaluate,prints=centered_evaluator(amp,centers,boxes)
        E=[[evaluate(preE[i,j]) for j in range(4)] for i in range(4)]
        v=[evaluate(prev[i]) for i in range(4)]
        rec=component_certificate(E,v)
        rec.update(slab_index=n,p_exact=slab['P'],p_interval=slab['P_iv'],Y=w['Y'],
                   C_rational=w['C_rational'],amplitude_center_rational=list(map(str,centers)),
                   centered_polynomials_srepr_sha256=hashlib.sha256('\n'.join(prints).encode()).hexdigest())
        records.append(rec)
        print(f'Slab {n}: exact component bound proves 137/1000000 < d(tau)/d(p) < 176/1000000',flush=True)
    sources=[Path(__file__).resolve(),ROOT/'scripts/certificates/check_m1_fold_witness_rational.py',
             ROOT/'scripts/certificates/check_endpoint_witness_rational.py',
             ROOT/'scripts/certificates/codex_m2_jacobian_arb.py',
             ROOT/'scripts/certificates/check_m1_parameter_monotonicity_rational.py',SOURCE,
             ROOT/'MSAConvergence/BHResidualPolynomials.lean',
             ROOT.parent/'MSA_and_1st_Truncation/LeanCode/YukawaOZMix/MSAMultiTailMixtureSystem.lean',
             ROOT.parent/'MSA_and_1st_Truncation/LeanCode/YukawaOZMix/MSAMixtureConcrete.lean',
             ROOT.parent/'MSA_and_1st_Truncation/LeanCode/YukawaOZMix/MSAMixtureCancellation.lean',
             ROOT.parent/'MSA_and_1st_Truncation/LeanCode/HSMixture/MatrixQ0.lean']
    result=dict(status='PASS_EXTERNAL_M1_PARAMETER_MONOTONICITY',label='EXTERNAL SymPy/Arb interval calculation; NOT a Lean proof',
                data=original['data'],parameter='p=Dt1',unknown_order=['Dt2','G1','G2','tau'],
                physical_amplitude_order=['Dt1','Dt2','G1','G2'],precision_bits=ctx.prec,
                zero_frequency_identity=dict(phi_qp='-1/2',phi_a='1/6',phi_c='1',symbolic_F0_equals_A_over_2pi=True),
                versions=dict(python=sys.version.split()[0],python_flint=flint.__version__,sympy=sp.__version__),
                method='Exact symbolic preconditioning and centered polynomial coefficients; Arb bounds; exact rational component substitutions',
                source_sha256={str(p.relative_to(ROOT.parent)):digest(p) for p in sources},
                fold_witness_source_sha256=digest(SOURCE),
                endpoint_source_sha256=original['endpoint_source_sha256'],
                tau_derivative_strict_lower_rational=str(Q(137,10**6)),
                tau_derivative_strict_upper_rational=str(Q(176,10**6)),slabs=records,
                endpoint_tau_bracket=[original['endpoints'][end]['tau'] for end in ['lo','hi']],
                scope='Positive d(tau)/d(p) over each existing M1 slab; with the externally certified root chain and endpoint signs, a zero lies strictly between the endpoint tau values. No PY-seed matching, first-loss, fold-location or Taylor-radius claim.')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('PASS EXTERNAL M1 coupling monotonicity on all four existing slabs; no new root search.')
    print(args.output.resolve())


if __name__ == '__main__':
    main()
