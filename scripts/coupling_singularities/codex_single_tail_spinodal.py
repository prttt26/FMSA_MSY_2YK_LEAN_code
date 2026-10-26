"""Exact identities for the all-state single-tail spinodal-before-fold proof.

The inequalities are proved in the accompanying mathematical note / Lean
module; this script independently verifies their algebraic reductions.
"""
from pathlib import Path
import hashlib
import json
import time

import sympy as sp


def main():
    started=time.monotonic()
    eta,x,E,u=sp.symbols('eta x E u')
    v=1-eta
    J=E*(x+2)+x-2
    H=E*(2*x+2)+x*x-2
    Ht=2-2*x+E*(x*x-2)
    a=-(18*eta**2*J+6*eta*v*H+x**3*v*v)
    b=-18*eta**2*J+6*eta*v*Ht-E*x**3*v*v
    d=v*x*x*(1-E)+6*eta*J
    m=(1+2*eta)*d
    Dt=-sp.pi*u*(u-a)/(3*eta*x**3*v**3*d)
    G=x/(12*eta*d)*(eta*x*x+6*eta*x+12*eta-x*x-v**3*x**5/u)
    rho=6*eta/sp.pi
    W=2*sp.pi*rho*G*Dt/x
    C=(1-2*sp.pi*rho*G*E/x)*Dt
    M=-rho*(W+(1+x)*C)/x
    Nc=rho*(W+(1+x+x*x/2)*C)/x**2
    A=2*sp.pi*(1+2*eta)/v**2*(1+M)+12*sp.pi*eta/v**2*Nc
    num=2*u*u-2*(a+b+m)*u+2*a*b+m*(a+b)
    assert sp.cancel(A/(2*sp.pi)-num/(x*v**3*d*d))==0
    aa,bb,mm=sp.symbols('a b m')
    NN=2*u*u-2*(aa+bb+mm)*u+2*aa*bb+mm*(aa+bb)
    QQ=4*u*u-3*(aa+bb)*u+2*aa*bb
    assert sp.expand(NN-(u+mm)*(aa+bb-2*u)-QQ)==0
    assert sp.expand(QQ.subs(u,(aa+bb)/2)+(aa-bb)**2/2)==0
    R1=-2*J-3*x*x*(1-E)
    R0=4*(1-E)**2-3*x*(1-E*E)+2*E*x*x
    assert sp.expand(R0+3*(1-E)*J+2*((1-E)**2-E*x*x))==0
    q_at_m=4*m*m+3*(a+b)*m+2*a*b
    expansion=-36*eta**2*v**2*x*x*J*J+3*eta*v**3*x*x*J*R1+v**4*x**4*R0
    assert sp.expand(q_at_m-expansion)==0
    # The homogeneous identity is independent of eta+v=1 when m=(v+3eta)d.
    h,V=sp.symbols('h V')
    ah=-(18*h*h*J+6*h*V*H+V*V*x**3)
    bh=-18*h*h*J+6*h*V*Ht-E*V*V*x**3
    mh=(V+3*h)*(V*x*x*(1-E)+6*h*J)
    exph=-36*h*h*V*V*x*x*J*J+3*h*V**3*x*x*J*R1+V**4*x**4*R0
    assert sp.expand(4*mh*mh+3*(ah+bh)*mh+2*ah*bh-exph)==0
    result={'status':'PASS_EXACT_SPINODAL_IDENTITIES','sympy_version':sp.__version__,
            'domain':'x=z*sigma>0, 0<eta<1, E=exp(-x), u!=0; sigma=1 used for the independent scalar transcription, with general diameter obtained by the existing dimensionless parametrization.',
            'verified':['actual A/(2*pi)=N/(x*v^3*d^2)',
                        'N(u)=(u+m)*(a+b-2u)+criticalPolynomial(u)',
                        'criticalPolynomial((a+b)/2)=-(a-b)^2/2',
                        'criticalPolynomial(-m) homogeneous negative-coefficient decomposition',
                        'R0=-3*(1-E)*J-2*((1-E)^2-E*x^2)'],
            'inequality_argument':'sinh(x/2)>x/2 gives (1-E)^2>E*x^2. Existing J>0 and E<1 make R0,R1 negative; all density/vacuum factors in the critical polynomial decomposition have the required signs. Hence c1<-m and c1<(a+b)/2, so A(c1)<0. IVT from the positive HS seed gives a zero strictly before the quartic fold.',
            'scope':'Exact symbolic reduction and accompanying mathematical argument; this JSON is not a Lean proof or an exclusion of earlier finite-k loss.',
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'seconds':round(time.monotonic()-started,3)}
    p=Path(__file__).resolve().parents[2]/'results/coupling_singularities/codex_single_tail_spinodal.json'
    p.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: exact single-tail spinodal algebraic reductions')
    print(p)


if __name__=='__main__':
    main()
