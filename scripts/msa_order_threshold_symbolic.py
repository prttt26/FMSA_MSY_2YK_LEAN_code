"""Exact scalar PY/BH derivation of the first two pressure-jet coefficients.

All rational identities are checked by SymPy. The exponential-kernel signs
and first-/second-order sign reentry are proved separately in Lean's
FiniteOrderThresholds module. This is a compressibility-route calculation;
it does not use energy-route HTE coefficients from the literature.
"""
from __future__ import annotations

import json
from pathlib import Path

import mpmath as mp
import numpy as np
import sympy as s

from msa_finite_order_thermo_check import ScalarSeries, PI

OUT=Path(__file__).resolve().parents[1]/'results'/'order_thresholds'


def derive():
    eta,z,E=s.symbols('eta z E',positive=True)
    d,w=s.symbols('d w')
    v=12*eta
    A0=(1+2*eta)/(1-eta)**2
    q0=(1+eta/2)/(1-eta)**2
    B0=-s.Rational(3,2)*eta/(1-eta)**2
    c=d-E*w
    M=-v*(w+(1+z)*c)/z
    Nc=v*(w+(1+z+z*z/2)*c)/z**2
    A=s.expand(A0*(1+M)-4*B0*Nc)
    q=s.expand(q0*(1+M)+A0*Nc)
    F=1-v*((1-z-E)/z**2*q+(1-z+z*z/2-E)/z**3*A+w/(2*z)
           +c*(E/(2*z)+(1-E)/z))
    U=(A+z*q)/z**2+c/2
    F0=s.factor(F.subs({d:0,w:0}))
    fd,fw=[s.factor(s.diff(F,x)) for x in [d,w]]
    ud,uw=[s.factor(s.diff(U,x)) for x in [d,w]]
    ad,aw=[s.factor(s.diff(A,x)) for x in [d,w]]
    g0=s.factor((A0+z*q0)/(z*z*F0))
    d1=s.factor(1/(z*F0))
    w1=s.factor(v/z*g0*d1)
    F1=s.factor(fd*d1+fw*w1)
    g1=s.factor((ud*d1+uw*w1-g0*F1)/F0)
    d2=s.factor(-d1*F1/F0)
    w2=s.factor(v/z*(g0*d2+g1*d1))
    F2=s.factor(fd*d2+fw*w2)
    g2=(ud*d2+uw*w2-g0*F2-g1*F1)/F0
    alpha1=s.factor(ad*d1+aw*w1)
    alpha2=s.factor(ad*d2+aw*w2)
    coefficients=[A0*A0,s.factor(2*A0*alpha1),s.factor(alpha1*alpha1+2*A0*alpha2)]
    print('Derived scalar coefficients',flush=True)
    # Verify both scalar amplitude residuals through order two.
    identities=[g0*F0-(A0+z*q0)/z**2,
                d1*F0-1/z,d2*F0+d1*F1,
                g1*F0+g0*F1-ud*d1-uw*w1,
                g2*F0+g1*F1+g0*F2-ud*d2-uw*w2]
    assert all(s.cancel(v)==0 for v in identities)
    print('Checked residual coefficient identities',flush=True)
    J=z-2+(z+2)*E
    K=2-(z*z+2*z+2)*E
    H0=z*z-2+2*(z+1)*E
    P=z**3*(1-eta)**2+6*eta*(1-eta)*H0+18*eta**2*J
    H=(1-eta)*H0+6*eta*J
    L=(1-eta)*z+1+2*eta
    expected=[A0*A0,-24*eta*z**4*(1+2*eta)*L/P**2,
              144*eta**2*z**11*(1-eta)**7*H/P**5]
    assert all(s.cancel(a-b)==0 for a,b in zip(coefficients,expected))
    assert s.cancel(F0-P/(z**3*(1-eta)**2))==0
    assert s.expand(H0-(z+2)*J-K)==0
    V0=z**3*(1+2*(z+1)*(1-E))
    V1=6*((3+5*z+2*z*z)*K+(z**3+7*z*z+9*z+4)*J)
    V2=9*((6+5*z)*H0+(2*z+2*z*z)*J)
    V3=54*(H0+2*(z+1)*J)
    V4=162*J
    V=sum(vi*eta**i*(1-eta)**(4-i) for i,vi in enumerate([V0,V1,V2,V3,V4]))
    assert s.expand(V-(L*L*P-z**3*(1-eta)**3*H))==0
    discriminant=expected[1]**2-4*expected[0]*expected[2]
    assert s.cancel(discriminant-576*eta**2*z**8*(1+2*eta)**2*V/P**5)==0
    # First-order spinodal temperature has one maximum, hence at most one loop.
    t=s.symbols('t',positive=True)
    aa=z+1; bb=z**3; cc=6*H0; dd=18*J
    RR=bb+cc*t+dd*t*t
    SS=(1+t)*(1+3*t)
    T1=24*z**4*t*(aa+3*t)/(SS*RR**2)
    assert s.cancel((-expected[1]/expected[0]).subs(eta,t/(1+t))-T1)==0
    QQ=s.expand((aa+6*t)*SS*RR-t*(aa+3*t)*(s.diff(SS,t)*RR+2*SS*s.diff(RR,t)))
    qcoef=[bb*aa,6*bb-cc*aa,-3*bb*aa+12*bb-8*cc*aa-3*dd*aa,
           -9*cc*aa-12*cc-16*dd*aa-6*dd,-3*(6*cc+5*dd*aa+12*dd),-36*dd]
    assert s.expand(QQ-sum(qi*t**i for i,qi in enumerate(qcoef)))==0
    assert s.cancel(s.diff(T1,t)-24*z**4*QQ/(SS**2*RR**3))==0
    assert s.expand(qcoef[2]-(3*z**3*(3-z)-48*(z+1)*H0-54*(z+1)*J))==0
    # Check the derivative used by Lean to obtain (z+1)H0 > 2z^3/3.
    kernel=(z+1)*H0-s.Rational(2,3)*z**3
    total_derivative=s.diff(kernel,z)-E*s.diff(kernel,E)
    assert s.expand(total_derivative-(H0+2*z*(1-(z+1)*E)))==0
    return dict(eta=eta,z=z,E=E,coefficients=expected,P=P,H=H,L=L,J=J,K=K,H0=H0,V=V,
                alpha1=alpha1,alpha2=alpha2,residual_identities=len(identities),
                first_order_T1=T1,first_order_derivative_numerator=QQ,
                first_order_derivative_coefficients=qcoef)


def main():
    symbolic=derive()
    OUT.mkdir(parents=True,exist_ok=True)
    names=['P','H','L','J','K','H0','V','alpha1','alpha2']
    report=dict(normalization='sigma=1; eta=pi*rho/6; tau multiplies unit attractive Yukawa amplitude',
                route='strict pressure derivative on the scalar PY/BH branch',
                formulas={k:str(symbolic[k]) for k in names},
                pressure_coefficients=list(map(str,symbolic['coefficients'])),
                checked_residual_identities=symbolic['residual_identities'],
                first_order_spinodal_T=str(symbolic['first_order_T1']),
                first_order_derivative_coefficients=list(map(str,symbolic['first_order_derivative_coefficients'])),
                proof_scope='SymPy checks exact identities; Lean proves signs and constructive reentry for '
                            'the displayed coefficient formulas. Physical OZ derivative identification '
                            'is not fully connected in Lean.',
                limitations='No global binodal, all-order positivity, or convergence-domain reentry claim')
    mp.mp.dps=70
    functions=[s.lambdify([symbolic['eta'],symbolic['z'],symbolic['E']],c,'mpmath')
               for c in symbolic['coefficients']]
    checks=[]
    for eta in ['.01','.1','.3','.5','.7']:
        for z in ['.2','1','1.8','5','12','30','100']:
            h=mp.mpf(eta);zz=mp.mpf(z)
            reference=[f(h,zz,mp.exp(-zz)) for f in functions]
            rho=np.longdouble(6)*np.longdouble(eta)/PI
            jet=ScalarSeries(rho,[float(z)],[1]).construct(2)['a']
            errors=[abs(float(c)-float(ref))/max(1,abs(float(ref))) for c,ref in zip(jet,reference)]
            checks.append(dict(eta=float(h),z=float(zz),maximum_scaled_coefficient_error=max(errors)))
    report['independent_series_checks']=checks
    report['maximum_scaled_coefficient_error']=max(c['maximum_scaled_coefficient_error'] for c in checks)
    if report['maximum_scaled_coefficient_error']>2e-9:
        raise RuntimeError('Symbolic coefficients disagree with independent series engine')
    (OUT/'symbolic_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print('All exact rational identities passed; maximum scaled coefficient discrepancy:',
          report['maximum_scaled_coefficient_error'],flush=True)


if __name__=='__main__':main()
