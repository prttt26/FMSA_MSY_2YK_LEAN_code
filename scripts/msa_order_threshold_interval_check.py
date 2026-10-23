"""Directed interval first-order counterexample for a normal two-Yukawa tail.

Long attraction / short repulsion, with net integrated attraction. This is a
single homogeneous state, not a Maxwell endpoint. Only the sign at k=5 is
certified; it makes an all-k search unnecessary for this negative example.
"""
from pathlib import Path
import json
import mpmath as mp
import numpy as np
from msa_maxwell_finite_k_check import Spectrum

OUT=Path(__file__).resolve().parents[1]/'results'/'order_thresholds'


def extra_loop_enclosures(dps):
    iv=mp.iv; iv.dps=dps
    z=iv.mpf(5); tau=1/iv.mpf('0.06259942900035')
    E=iv.exp(-z)
    J=z-2+(z+2)*E; H0=z*z-2+2*(z+1)*E
    records=[]
    for density,sign in [('0.01',1),('0.1',-1),('0.27',1),('0.5',-1),('1.3',1)]:
        eta=iv.pi*iv.mpf(density)/6; w=1-eta
        P=z**3*w**2+6*eta*w*H0+18*eta**2*J
        L=w*z+1+2*eta; H=w*H0+6*eta*J
        c0=((1+2*eta)/w**2)**2
        c1=-24*eta*z**4*(1+2*eta)*L/P**2
        c2=144*eta**2*z**11*w**7*H/P**5
        value=c0+tau*c1+tau**2*c2
        assert (sign*value>iv.mpf(0)) is True
        records.append(dict(rho=density,a2=str(value),certified_sign=sign))
    return dict(dps=dps,z=5,T='0.06259942900035',records=records,
                consequence='Continuity gives at least four distinct spinodal roots and two negative '
                            'pressure-slope intervals. No claim of two supporting binodals.')


def enclose(dps):
    iv=mp.iv
    iv.dps=dps
    rho=iv.mpf('0.3'); tau=iv.mpf(5)
    z=[iv.mpf('1.8'),iv.mpf(12)]
    K=[iv.mpf(1),iv.mpf(-6)]
    eta=iv.pi*rho/6; v=12*eta
    A0=(1+2*eta)/(1-eta)**2
    q0=(1+eta/2)/(1-eta)**2
    B0=-iv.mpf('1.5')*eta/(1-eta)**2

    def phi(s):
        em=iv.exp(-s)
        return (1-s-em)/s**2,(1-s+s*s/2-em)/s**3

    def Fhs(s):
        p1,p2=phi(s)
        return 1-v*(p1*q0+p2*A0)

    g0=[(A0+zz*q0)/(zz**2*Fhs(zz)) for zz in z]
    d1=[kk/(zz*Fhs(zz)) for kk,zz in zip(K,z)]
    w1=[v*gg*dd/zz for gg,dd,zz in zip(g0,d1,z)]
    c1=[dd-iv.exp(-zz)*ww for dd,ww,zz in zip(d1,w1,z)]
    M1=-v*sum((ww+(1+zz)*cc)/zz for ww,cc,zz in zip(w1,c1,z))
    N1=v*sum((ww+(1+zz+zz**2/2)*cc)/zz**2 for ww,cc,zz in zip(w1,c1,z))
    A1=A0*M1-4*B0*N1; q1=q0*M1+A0*N1
    D0=A0**2+2*tau*A0*A1
    s=iv.mpc(0,5); em=iv.exp(-s)
    p1,p2=phi(s)
    f0=Fhs(s)
    f1=-v*(p1*q1+p2*A1+sum(
        ww/(s+zz)+cc*(1/s-zz*em/(s*(s+zz))) for ww,cc,zz in zip(w1,c1,z)))
    D5=f0.real**2+f0.imag**2+2*tau*(f0.real*f1.real+f0.imag*f1.imag)
    integral=(1+z[0])/z[0]**2-6*(1+z[1])/z[1]**2
    # These wide rational bounds are checked directly in interval arithmetic.
    assert (D0>iv.mpf('2.805')) is True
    assert (D5<iv.mpf('-.202')) is True
    assert (integral>iv.mpf('.322')) is True
    return dict(dps=dps,D_at_zero=str(D0),D_at_five=str(D5),
                integrated_attraction=str(integral),
                certified_rational_bounds=['D1(0)>2.805','D1(5)<-0.202','integrated attraction>0.322'])


def main():
    checks=[enclose(30),enclose(60)]
    independent=Spectrum(.3,[1.8,12],[1,-6],.2,1).values(np.array([0.,5.]))
    assert independent[0]>2.805 and independent[1]<-.202
    report=dict(model=dict(rho=.3,z=[1.8,12],K=[1,-6],T=.2,order=1),
                normalization='sigma=1; exterior potential=-sum K_i exp[-z_i(r-1)]/(T r)',
                interval_checks=checks,independent_series_values=list(map(float,independent)),
                scope='Directed interval elementary arithmetic on explicit first-order PY/BH formulas; '
                      'not a Lean-certified transcendental evaluation or a coexistence endpoint',
                interpretation='Positive k=0 does not ensure an admissible homogeneous spectrum, '
                               'even with long attraction, short repulsion and net integrated attraction')
    report['pure_attraction_second_order_extra_loop']=[extra_loop_enclosures(30),extra_loop_enclosures(60)]
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/'first_order_normal_tail_interval.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
