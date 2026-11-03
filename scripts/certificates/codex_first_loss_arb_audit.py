#!/usr/bin/env python3
"""Independently replay Claude173's compressed EXTERNAL M1/M3 all-wave certificates.

No two_tail implementation is imported. The six amplitude polynomials are
independently specialized from BHResidualPolynomials and the frozen Q0/Qpp
dictionary. They have support {1,D1,D2,D1*G1,D2*G2}. A separate bilinear
center/radius evaluator and independent Fourier coefficient/derivative code
recompute ALL stored m,d and coefficient bounds at higher precision.

The exact rational march, tail and slab coverage are checked independently.
The earlier hash-pinned PY-chain audit supplies its explicitly stated root
continuation scope; this tool does not replace that audit with a PASS flag.
This is an external numerical certificate, NOT a Lean proof or Taylor bound.

Example (python-flint 0.6.0):
  PYTHONPATH=/tmp/codex_fmsa_arb_deps /opt/anaconda3/bin/python3 \
    scripts/certificates/codex_first_loss_arb_audit.py --controls M3 M1 \
    --negative-controls --output results/certificates/codex_first_loss_arb_audit.json
"""
from argparse import ArgumentParser
from copy import deepcopy
from datetime import datetime, timezone
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial
from pathlib import Path
import gzip
import hashlib
import json
import sys
import time

import flint
from flint import acb, arb, ctx, fmpq
import sympy as sp

if not __debug__:
    raise RuntimeError('Assertions must remain enabled; do not use python -O.')

ROOT = Path(__file__).resolve().parents[2]
FOUNDATION = ROOT.parent/'MSA_and_1st_Truncation'
ENDPOINTS = ROOT/'results/two_tail/two_tail_endpoint_interval_exact.json'
PRIOR = ROOT/'results/certificates/codex_py_seeded_chain_audit.json'
LEAN = [ROOT/'MSAConvergence/BHResidualPolynomials.lean',
        FOUNDATION/'FMSAPaper/BaxterZeroMode.lean',
        ROOT/'MSAConvergence/CanonicalFirstLoss.lean',
        ROOT/'MSAConvergence/ScalarCanonicalSeed.lean',
        FOUNDATION/'LeanCode/HSMixture/MatrixQ0.lean',
        *[FOUNDATION/'LeanCode/YukawaOZMix'/f'{name}.lean' for name in (
            'MSAMultiTailMixtureBaxter', 'MSAMultiTailMixtureFourier',
            'MSAMultiTailMixtureSpectral', 'MSAMultiTailMixtureSystem',
            'MSAMixtureConcrete', 'MSAMixtureCancellation')]]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def number(s):
    assert isinstance(s, str)
    if 'p' in s:
        m, e = s.split('p')
        return Q(int(m))*Q(2)**int(e)
    return Q(s)


def pair(s):
    assert len(s) == 2
    lo, hi = map(number, s)
    assert lo <= hi, 'Reversed interval'
    return lo, hi


def point(q):
    q = Q(q)
    return arb(fmpq(q.numerator, q.denominator))


def endpoint(x):
    assert x.is_finite() and x.is_exact()
    m, e = map(int, x.man_exp())
    return Q(m)*Q(2)**e


def bounds(x):
    assert x.is_finite(), str(x)
    return endpoint(x.lower()), endpoint(x.upper())


def maxabs(p):
    return max(abs(p[0]), abs(p[1]))


def plus(a, b):
    return a[0]+b[0], a[1]+b[1]


def times(a, b):
    vals = [x*y for x in a for y in b]
    return min(vals), max(vals)


def amplitude_coefficients(eta, rates):
    """Rows in support order 1,D1,D2,D1*G1,D2*G2; no generator import.

    W_t = h_t D_t G_t, C_t = D_t - e_t D_t G_t.
    Linear M,N coefficients follow the literal scalar finite sums.
    """
    pi, eta = arb.pi(), point(eta)
    rho, vac = 6*eta/pi, 1-eta
    qp0 = 2*pi/vac*(1+pi*rho/(4*vac))
    a0 = 2*pi/vac*(1+pi*rho/(2*vac))
    nscale = 2*pi*pi*rho/(vac*vac)
    rows = [[arb(0) for _ in range(5)] for _ in range(6)]
    rows[0][0], rows[1][0] = qp0, a0
    for t, rate in enumerate(rates):
        z = point(rate)
        h, e = 2*pi*rho/z, 2*pi*rho*(-z).exp()/z
        md = -rho*(1+z)/z
        mx = -rho*(h-(1+z)*e)/z
        nd = rho*(1+z+z*z/2)/(z*z)
        nx = rho*(h-(1+z+z*z/2)*e)/(z*z)
        for row, d, x in ((rows[0], qp0*md+a0*nd, qp0*mx+a0*nx),
                          (rows[1], a0*md+nscale*nd, a0*mx+nscale*nx)):
            row[1+t], row[3+t] = d, x
        rows[2+t][3+t] = h
        rows[4+t][1+t], rows[4+t][3+t] = arb(1), -e
    return rows, rho


class Hull:
    """Exact midpoints, independent explicit centered bilinear expansion."""
    def __init__(self, U):
        assert len(U) == 4
        self.center = [(a+b)/2 for a,b in U]
        self.radius = [(b-a)/2 for a,b in U]
        self.c = list(map(point, self.center))
        self.r = list(map(point, self.radius))

    def centered(self, coeff):
        c, r = self.c, self.r
        value = coeff[0]
        linear, cross = [], []
        for t in range(2):
            a, b = coeff[1+t], coeff[3+t]
            value += c[t]*(a+b*c[2+t])
            linear.extend(((a+b*c[2+t], r[t]), (b*c[t], r[2+t])))
            cross.append((b, r[t]*r[2+t]))
        return value, linear+cross

    def enclose(self, coeff, exact=False):
        value, terms = self.centered(coeff)
        if exact:
            # Coefficient budgets are 32-bit, close to Arb's radius rounding.
            # Use exact Fraction endpoints here to avoid widening the result
            # solely because the two evaluators add their radii differently.
            lo, hi = bounds(value)
            err = sum((maxabs(bounds(a))*bounds(r)[1] for a,r in terms), Q(0))
            return lo-err, hi+err
        err = sum((abs(a)*r for a,r in terms), arb(0))
        # Adding a symmetric Arb ball gives an interval containing the true
        # centered value +/- the entire triangle radius.
        return value+arb(0, err.upper())


def combine(rows, weights):
    assert len(rows) == len(weights) == 6
    return [sum((w*row[j] for w,row in zip(weights,rows)), arb(0)) for j in range(5)]


def symbolic_checks(eta, rates, rows):
    """Exact literal-polynomial/zero-moment and kernel calculus checks.

    Numerical overlap below is only a consistency diagnostic; the actual
    enclosure computation uses the independently derived coefficient rows.
    The symbolic identities and source mapping are separate audit evidence,
    not a claimed Lean instantiation of the literal physical dictionaries.
    """
    D1,D2,G1,G2=V=sp.symbols('D1 D2 G1 G2')
    eta=sp.Rational(eta)
    z=list(map(sp.Rational,rates))
    rho=6*eta/sp.pi
    vac=1-eta
    q0=2*sp.pi/vac*(1+sp.pi*rho/(4*vac))
    app=2*sp.pi/vac*(1+sp.pi*rho/(2*vac))
    W=[2*sp.pi/z[t]*rho*V[2+t]*V[t] for t in range(2)]
    C=[(1-2*sp.pi*rho*sp.exp(-z[t])/z[t]*V[2+t])*V[t] for t in range(2)]
    M=[-rho/z[t]*(W[t]+(1+z[t])*C[t]) for t in range(2)]
    N=[rho*(W[t]+(1+z[t]+z[t]**2/2)*C[t])/z[t]**2 for t in range(2)]
    A=sp.expand(app+sum(app*M[t]+2*sp.pi**2*rho/vac**2*N[t] for t in range(2)))
    qp=sp.expand(q0+sum(q0*M[t]+app*N[t] for t in range(2)))
    polys=[sp.Poly(x,*V) for x in [qp,A,*W,*C]]
    support=[(0,0,0,0),(1,0,0,0),(0,1,0,0),(1,0,1,0),(0,1,0,1)]
    assert all(set(p.monoms())<=set(support) for p in polys)
    F0=1-rho*(-qp/2+A/6+sum(W[t]/z[t]+C[t]*(1+1/z[t]) for t in range(2)))
    assert sp.expand(F0-A/(2*sp.pi))==0, 'False literal zero-frequency identity'
    @lru_cache(None)
    def evaluate(expr):
        if expr.is_Rational:
            return point(Q(int(expr.p),int(expr.q)))
        if expr==sp.pi:
            return arb.pi()
        if expr.func==sp.exp:
            return evaluate(expr.args[0]).exp()
        if expr.is_Add:
            return sum(map(evaluate,expr.args),arb(0))
        if expr.is_Mul:
            value=arb(1)
            for t in expr.args:
                value*=evaluate(t)
            return value
        if expr.is_Pow and expr.args[1].is_Integer:
            return evaluate(expr.args[0])**int(expr.args[1])
        raise AssertionError('Unsupported symbolic coefficient: '+str(expr))
    for row,p in zip(rows,polys):
        for a,monomial in zip(row,support):
            assert a.overlaps(evaluate(p.coeff_monomial(monomial))), 'Bilinear dictionary mismatch'
    n=sp.Symbol('n',integer=True,nonnegative=True)
    assert sp.cancel(1/(n+2)-1/(n+1)+1/((n+1)*(n+2)))==0
    assert sp.cancel((1/(n+3)-2/(n+2)+1/(n+1))/2-1/((n+1)*(n+2)*(n+3)))==0
    # Closed-form derivatives of the three finite-core kernels.
    s=sp.Symbol('s',nonzero=True)
    E=sp.exp(-s)
    e=[(1-s-E)/s**2,(1-s+s**2/2-E)/s**3,(1-E)/s]
    ds=[(-1+E)/s**2-2*(1-s-E)/s**3,
        (-1+s+E)/s**3-3*(1-s+s**2/2-E)/s**4,E/s-(1-E)/s**2]
    assert all(sp.simplify(sp.diff(v,s)-d)==0 for v,d in zip(e,ds))
    assert [sp.limit(v,s,0) for v in e]==[-sp.Rational(1,2),sp.Rational(1,6),sp.Integer(1)]
    # Genuine second s-derivatives; F''(k)=rho*Phi''(i*k).
    zz=sp.Symbol('zz',positive=True)
    dd1=-E/s**2-(2+4*E)/s**3+6*(1-E)/s**4
    dd2=(1-E)/s**3-6*(1+E)/s**4+12*(1-E)/s**5
    hc=(1-E)/s+E/(s+zz)
    ddc=-zz*E/(s*(s+zz))-2*zz*E*(2*s+zz)/(s**2*(s+zz)**2)+2*E/(s+zz)**3+2*(1-E)/s**3
    assert sp.simplify(sp.diff(e[0],s,2)-dd1)==0
    assert sp.simplify(sp.diff(e[1],s,2)-dd2)==0
    assert sp.simplify(sp.diff(hc,s,2)-ddc)==0
    assert sp.simplify(sp.diff(1/(s+zz),s,2)-2/(s+zz)**3)==0
    # On s=i*k, |E|=1, |1-E|<=2, |s+z|>=k and |2s+z|<=2*k+z.
    # Triangle bounds therefore hold for ALL k,z>0, not sampled points.
    kk=sp.Symbol('kk',positive=True)
    cb=zz/kk**2+2*zz*(2*kk+zz)/kk**4+2/kk**3+4/kk**3
    assert sp.cancel(cb-(zz/kk**2+(6+4*zz)/kk**3+2*zz**2/kk**4))==0
    # The171 C budget and173 C budget need not be ordered globally.
    assert sp.cancel(cb-(zz/kk**2+(2+4*zz)/kk**3+6*zz/kk**4)
                     -(4*kk+2*zz**2-6*zz)/kk**4)==0
    # Core second absolute moments; tail moments follow integration by parts.
    r=sp.Symbol('r',real=True)
    assert sp.integrate(r**2*(1-r),(r,0,1))==sp.Rational(1,12)
    assert sp.integrate(r**2*(1-r)**2/2,(r,0,1))==sp.Rational(1,60)
    return dict(literal_polynomial_support_checked=True,literal_F0_equals_A_over_2pi=True,
                kernel_derivatives_and_zero_limits_checked=True,
                second_derivative_closed_forms_checked=True,
                decreasing_curvature_budget_triangle_identity_checked=True,H2_budget_order_not_assumed=True,
                small_frequency_series_moments_checked=True,core_L2_moments_checked=True,
                literal_polynomials_srepr_sha256=hashlib.sha256('\n'.join(sp.srepr(p.as_expr()) for p in polys).encode()).hexdigest())


def kernels(k, rates):
    """Independent e_j and actual k derivatives; including the honest k=0.

    For |k|<=1/2 integrate the exponential series termwise on [0,1].
    Truncate at n=99, with a common certified remainder 2^-500.
    For the first derivative n>=100 uses p_{n-1}; its absolute tail is
    <=2*(1/2)^99/99! < 2^-500 (checked with exact integers below).
    For larger k use the direct Fourier closed forms and k differentiation.
    """
    s = acb(0, point(k))
    E = (-s).exp()
    if k <= Q(1,2):
        value, deriv = [acb(0) for _ in range(3)], [acb(0) for _ in range(3)]
        power, previous = acb(1), acb(0)
        for n in range(100):
            coeff = [-Q(1,(n+1)*(n+2)), Q(1,(n+1)*(n+2)*(n+3)), Q(1,n+1)]
            for j in range(3):
                value[j] += power*point(coeff[j])
                if n:
                    deriv[j] -= acb(0,1)*previous*point(coeff[j])
            previous, power = power, power*(-s)/(n+1)
        err = acb(arb(0,point(Q(1,2**500))), arb(0,point(Q(1,2**500))))
        value = [v+err for v in value]
        deriv = [v+err for v in deriv]
        e1,e2,e3 = value
        k1,k2,k3 = deriv
    else:
        # Compute numerator derivatives directly with respect to k, rather
        # than importing the generator's d/ds dictionary and multiplying i.
        I = acb(0,1)
        n1, n2, n3 = 1-s-E, 1-s+s*s/2-E, 1-E
        e1,e2,e3 = n1/(s*s), n2/(s*s*s), n3/s
        k1 = I*((-1+E)/(s*s)-2*n1/(s*s*s))
        k2 = I*((-1+s+E)/(s*s*s)-3*n2/(s*s*s*s))
        k3 = I*(E/s-n3/(s*s))
    g = [1/(s+point(z)) for z in rates]
    I = acb(0,1)
    values = [e1,e2,*g,e3+E*g[0],e3+E*g[1]]
    derivatives = [k1,k2,*[-I*v*v for v in g],
                   *[k3-I*E*v-I*E*v*v for v in g]]
    return values, derivatives


def analytic_step(H, rows, rho, rates, k, m, d):
    a, da = kernels(k, rates)
    vr = combine(rows, [v.real for v in a])
    vi = combine(rows, [v.imag for v in a])
    dr = combine(rows, [v.real for v in da])
    di = combine(rows, [v.imag for v in da])
    # Multiply rho into coefficients BEFORE interval evaluation. This also
    # keeps the density/coefficients correlation, unlike treating rho as an
    # independent uncertain input after boxing the polynomial.
    fr = [-rho*v for v in vr]
    fr[0] += 1
    fi = [-rho*v for v in vi]
    re, im = H.enclose(fr), H.enclose(fi)
    reD, imD = H.enclose([-rho*v for v in dr]), H.enclose([-rho*v for v in di])
    def distance(b):
        lo, hi = bounds(b)
        return lo if lo>0 else (-hi if hi<0 else Q(0))
    assert m*m <= distance(re)**2+distance(im)**2, 'False |F| lower bound'
    # The Euclidean norm is bounded by the L1 norm. Exact endpoints prevent
    # floating comparison from deciding the acceptance of a stored budget.
    assert maxabs(bounds(reD))+maxabs(bounds(imD)) <= d, 'False |Fprime| upper bound'


def required_boxes(chain, control):
    tl = Q(control['rigorous_bracket']['lo']['tau'])
    pstar = number(chain['p_star']) if chain['p_star'] is not None else None
    boxes = {}
    for j, slab in enumerate(chain['slabs']):
        w = slab['w']
        k, P, Y = w['k'], pair(w['P']), list(map(pair,w['Y']))
        assert k in (0,4) and len(Y)==4
        assert pstar is not None or k==4
        need = P[1] <= (tl if k==4 else pstar)
        assert slab['A_required'] is need, 'Required-slab label mismatch'
        if need:
            B = dict(zip((i for i in range(5) if i!=k),Y))
            B[k] = P
            boxes[j] = [B[i] for i in range(4)]
    return boxes


def curvature_budget(k, up, rho_upper, rates):
    """Positive inverse-power coefficients give a decreasing true |F''| budget.

    This groups the derived triangle bound independently of the generator's
    per-tail implementation. Every coefficient is nonnegative; hence its
    value at k bounds every greater positive frequency. The analytic origin
    of all four basis derivative bounds is checked in symbolic_checks.
    """
    assert k>0 and rho_upper>=0 and len(up)==6 and len(rates)==2
    assert all(v>=0 for v in up) and all(z>0 for z in rates)
    qp,A,W1,W2,C1,C2=up
    zc=sum((z*C for z,C in zip(rates,(C1,C2))),Q(0))
    z2c=sum((z*z*C for z,C in zip(rates,(C1,C2))),Q(0))
    coeff=(qp+zc, 6*qp+2*A+2*(W1+W2)+6*(C1+C2)+4*zc,
           12*qp+12*A+2*z2c, 24*A)
    assert all(c>=0 for c in coeff)
    return rho_upper*sum((c/k**p for c,p in zip(coeff,(2,3,4,5))),Q(0))


def check_amplitude_budgets(H,rows,up):
    assert len(up)==len(rows)==6
    for row,budget in zip(rows,up):
        assert maxabs(H.enclose(row,exact=True))<=budget, 'False amplitude coefficient bound'


def check_structure(data, chain, control):
    assert data['passed'] is True
    assert data['control'] == chain['control'] == control['name']
    assert data['data'] == dict(eta=control['eta'],z=control['z'],w=control['w'],sigma='1',rho='6*eta/pi')
    boxes = required_boxes(chain,control)
    assert data['required_slabs']==list(boxes), 'Incomplete required slab set'
    rho = pair(data['rho_enclosure'])
    assert 0 < rho[0] <= rho[1]
    rates = list(map(Q,control['z']))
    assert len(rates)==2 and all(z>0 for z in rates)
    coverage = {j:[] for j in boxes}
    steps = 0
    for rec in data['records']:
        a,b = rec['slabs']
        assert isinstance(a,int) and isinstance(b,int) and 0<=a<=b<len(chain['slabs'])
        members = [j for j in boxes if a<=j<=b]
        U = list(map(pair,rec['U']))
        assert len(U)==4 and members, 'Empty slab membership'
        assert all(U[i][0]<=boxes[j][i][0]<=boxes[j][i][1]<=U[i][1] for j in members for i in range(4)), 'Hull misses member'
        up = list(map(number,rec['up']))
        assert len(up)==6 and all(x>=0 for x in up)
        qp,A,W1,W2,C1,C2 = up
        L2,B2,q0,K = [number(rec[key]) for key in ('L2','B2','q0','K')]
        assert q0>=0 and K>0
        budget = qp/12+A/60+sum((2*W/z**3+C*(Q(1,3)+1/z+2/z**2+2/z**3) for W,C,z in zip((W1,W2),(C1,C2),rates)),Q(0))
        assert L2>=rho[1]*budget and B2>=2*qp+A+sum((z*(W+C) for W,C,z in zip((W1,W2),(C1,C2),rates)),Q(0)), 'False moment/tail budget'
        ks,ms,ds = [list(map(number,rec[key])) for key in ('k','m','d')]
        assert len(ks)==len(ms)+1==len(ds)+1 and ks[0]>=0
        for k,nxt,m,d in zip(ks,ks[1:],ms,ds):
            h=nxt-k
            Li=L2 if k==0 else min(L2,curvature_budget(k,up,rho[1],rates))
            assert h>0 and m>0 and d>=0 and m-d*h-Li*h*h/2>0, 'Invalid march step'
        assert isinstance(rec['tail'],bool)
        if rec['tail']:
            assert ks[-1]>=K and rho[1]*(q0/K+B2/K**2+2*A/K**3)<Q(1,2), 'Invalid large-frequency tail'
        for j in members:
            coverage[j].append((ks[0],ks[-1],rec['tail']))
        steps+=len(ms)
    for pieces in coverage.values():
        pieces.sort()
        assert pieces and pieces[0][0]==0, 'Frequency coverage must start at zero'
        end,done=Q(0),False
        for a,b,t in pieces:
            assert done or a<=end, 'Frequency coverage gap'
            end=max(end,b)
            done=done or t
        assert done, 'Missing large-frequency coverage'
    assert steps==data['counts']['k_steps'] and len(data['records'])==data['counts']['records']
    return dict(required_slabs=len(boxes),records=len(data['records']),frequency_steps=steps)


def check_analytic(data, control, sample=False):
    rows,rho = amplitude_coefficients(Q(control['eta']),list(map(Q,control['z'])))
    checks=symbolic_checks(Q(control['eta']),list(map(Q,control['z'])),rows)
    rhol,rhou=pair(data['rho_enclosure'])
    l,h=bounds(rho)
    assert rhol<=l<=h<=rhou, 'False density enclosure'
    rates=list(map(Q,control['z']))
    count=0
    t0=time.monotonic()
    for n,rec in enumerate(data['records']):
        H=Hull(list(map(pair,rec['U'])))
        check_amplitude_budgets(H,rows,list(map(number,rec['up'])))
        q0row=combine(rows,[arb(-1),point(Q(1,2)),arb(1),arb(1),arb(1),arb(1)])
        assert maxabs(H.enclose(q0row,exact=True))<=number(rec['q0']), 'False q0 bound'
        ks,ms,ds=[list(map(number,rec[key])) for key in ('k','m','d')]
        indices=sorted(set((0,len(ms)//2,len(ms)-1))) if sample and ms else range(len(ms))
        for i in indices:
            try:
                analytic_step(H,rows,rho,rates,ks[i],ms[i],ds[i])
            except AssertionError as e:
                raise AssertionError(f'record {n}, step {i}, k={ks[i]}: {e}') from e
            count+=1
        if n%20==0 or n+1==len(data['records']):
            print(f'{control["name"][:2]} analytic {n+1}/{len(data["records"])} records; {count} steps; {time.monotonic()-t0:.1f}s',flush=True)
    return dict(analytic_steps_replayed=count,coefficient_hulls_replayed=len(data['records']),density_enclosure_replayed=True,
                symbolic_consistency_checks=checks)


def negative_controls(data,chain,control):
    rejected=[]
    def reject(label,f):
        try:
            f()
        except (AssertionError,ValueError,KeyError,IndexError,ZeroDivisionError):
            rejected.append(label)
        else:
            raise AssertionError('Negative control accepted: '+label)
    for label,edit in (
        ('missing required slab',lambda x:x['required_slabs'].pop()),
        ('missing final record',lambda x:x['records'].pop()),
        ('inflated march step',lambda x:x['records'][0]['k'].__setitem__(1,'1000000')),
        ('understated L2',lambda x:x['records'][0].__setitem__('L2','0')),
        ('negative q0 budget',lambda x:x['records'][0].__setitem__('q0','-1')),
        ('frequency coverage starts above zero',lambda x:x['records'][0]['k'].__setitem__(0,'1/1000000000000'))):
        bad=deepcopy(data)
        edit(bad)
        reject(label,lambda bad=bad:check_structure(bad,chain,control))
    rows,rho=amplitude_coefficients(Q(control['eta']),list(map(Q,control['z'])))
    rec=data['records'][0]
    H=Hull(list(map(pair,rec['U'])))
    k=number(rec['k'][0])
    m,d=number(rec['m'][0]),number(rec['d'][0])
    reject('inflated actual |F| lower bound',lambda:analytic_step(H,rows,rho,list(map(Q,control['z'])),k,m+1000,d))
    # At k=0 the derivative is generally nonzero; this tests the analytic
    # checker, not just an easy violation of the rational march inequality.
    reject('zero actual |Fprime| budget',lambda:analytic_step(H,rows,rho,list(map(Q,control['z'])),k,m,Q(0)))
    # Deliberately understate an analytic coefficient upper bound. A purely
    # rational step checker cannot detect this; fresh actual hulls must do so.
    rec=next(r for r in data['records'] if number(r['up'][4])>0)
    H=Hull(list(map(pair,rec['U'])))
    badup=list(map(number,rec['up']));badup[4]/=10
    reject('understated actual C1 upper bound',lambda:check_amplitude_budgets(H,rows,badup))
    # Select an H2-limited step whose tripled width violates its actual
    # quadratic budget, so rejection occurs before a later ordering check.
    found=False
    rates=list(map(Q,control['z']));rhou=pair(data['rho_enclosure'])[1]
    for j,rec in enumerate(data['records']):
        up=list(map(number,rec['up']));L2=number(rec['L2'])
        ks,ms,ds=[list(map(number,rec[key])) for key in ('k','m','d')]
        for i,(k,nxt,m,d) in enumerate(zip(ks,ks[1:],ms,ds)):
            if k==0:continue
            H2=curvature_budget(k,up,rhou,rates);h=nxt-k
            if H2<L2 and m-d*(3*h)-H2*(3*h)**2/2<=0:
                bad=deepcopy(data);bad['records'][j]['k'][i+1]=str(k+3*h)
                reject('tripled H2-limited step',lambda bad=bad:check_structure(bad,chain,control))
                found=True;break
        if found:break
    assert found, 'No effective H2 corruption control found'
    return rejected


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--controls',nargs='+',choices=('M1','M3'),default=['M3','M1'])
    parser.add_argument('--precision',type=int,default=384)
    parser.add_argument('--sample',action='store_true',help='diagnostic only; never writes a PASS receipt')
    parser.add_argument('--negative-controls',action='store_true')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    assert args.precision>=320 and len(set(args.controls))==len(args.controls)
    assert not(args.sample and args.output), 'Sampled runs cannot issue receipts'
    if args.output:
        assert args.output.resolve().parent==ROOT/'results/certificates'
        assert args.output.name.startswith('codex_first_loss_') and args.output.suffix=='.json'
    ctx.prec=args.precision
    # Exact tail proof for all six small-frequency series/derivative tails.
    assert 2*Q(1,2**99*factorial(99))<Q(1,2**500)
    paths=[Path(__file__).resolve(),ENDPOINTS,PRIOR,*LEAN,ROOT/'scripts/two_tail/check_first_loss_rational.py']
    for name in args.controls:
        paths.extend([ROOT/f'results/two_tail/two_tail_first_loss_{name}.json.gz',
                      ROOT/f'results/two_tail/two_tail_py_chain_{name}.json.gz'])
    prior=json.loads(PRIOR.read_text())
    assert prior['status']=='PASS_EXTERNAL_AUDIT'
    paths.extend(ROOT.parent/p for p in prior['inputs_sha256'])
    for p,h in prior['inputs_sha256'].items():
        assert digest(ROOT.parent/p)==h, 'Prior chain audit pin changed: '+p
    paths=list(dict.fromkeys(paths))
    before={str(p.relative_to(ROOT.parent)):digest(p) for p in paths}
    controls=json.loads(ENDPOINTS.read_text())['controls']
    results={}
    for name in args.controls:
        data=json.loads(gzip.decompress((ROOT/f'results/two_tail/two_tail_first_loss_{name}.json.gz').read_bytes()))
        chain_path=ROOT/f'results/two_tail/two_tail_py_chain_{name}.json.gz'
        chain=json.loads(gzip.decompress(chain_path.read_bytes()))
        assert data['chain_sha256']==digest(chain_path)
        assert data['source_sha256']==digest(ENDPOINTS)
        assert set(data['script_sha256'])=={'two_tail_first_loss.py','two_tail_py_chain.py','two_tail_m3_arb_recheck.py'}, 'Incomplete generator pins'
        assert set(data['lean_sha256'])=={'MSA_Convergence/MSAConvergence/BHResidualPolynomials.lean',
                                          'MSA_and_1st_Truncation/LeanCode/HSMixture/MatrixQ0.lean'}, 'Incomplete recorded Lean pins'
        for file,h in data['script_sha256'].items():
            p=ROOT/'scripts/two_tail'/file
            assert p.is_file() and digest(p)==h
            before[str(p.relative_to(ROOT.parent))]=h
        for file,h in data['lean_sha256'].items():
            p=ROOT.parent/file
            assert digest(p)==h
            before[str(p.relative_to(ROOT.parent))]=h
        control=next(c for c in controls if c['name']==chain['control'])
        row=check_structure(data,chain,control)
        row.update(check_analytic(data,control,args.sample))
        if args.negative_controls:
            row['negative_controls_rejected']=negative_controls(data,chain,control)
        results[name]=row
        print(f'PASS {name}: '+json.dumps(row),flush=True)
    assert all(digest(ROOT.parent/p)==h for p,h in before.items()), 'Input changed during audit'
    report=dict(status='PASS_EXTERNAL_FIRST_LOSS_AUDIT' if not args.sample else 'DIAGNOSTIC_SAMPLE_ONLY',
                created_at_utc=datetime.now(timezone.utc).isoformat(),
                label='EXTERNAL Arb/Fraction certificate; NOT a Lean proof',
                precision_bits=args.precision,versions=dict(python=sys.version.split()[0],python_flint=flint.__version__,sympy=sp.__version__),
                inputs_sha256=before,results=results,
                method='Independent bilinear amplitude dictionary, exact midpoint/radius evaluation, independently differentiated Fourier coefficients, full higher-precision analytic replay and independent exact rational coverage with the algebraically derived decreasing curvature budget',
                prior_chain_audit_sha256=digest(PRIOR),
                scope='All real Fourier-factor frequencies are nonzero on the saved required PY-chain slab boxes through tau_lo. Together with the separately audited continuous PY root chain, actual canonical HS seed and canonical_path_of_physical_factor_units, this localizes first full-canonicity loss to (tau_lo,tau_hi). The numerical instance is external, not Lean. No first-loss frequency, uniqueness or Taylor-radius claim.')
    if args.output:
        args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(report['status'],flush=True)


if __name__=='__main__':
    main()
