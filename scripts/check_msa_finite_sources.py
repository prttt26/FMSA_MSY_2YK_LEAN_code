"""Check proved finite source formulas against the existing BH Python dictionary.
Symbolic checks and quadrature are verification, never Lean axioms.
Mixture values are off-root amplitude data; no phase claims are tested here.
"""
from pathlib import Path
import sys,json
import sympy as sp
import mpmath as mp
import numpy as np
BASE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(BASE.parents[1]))
from msa_exact_mix import HCYMix,_pieces
from check_msa_b_hierarchy_physical import data
mp.mp.dps=55
x,z,G,D,p,E=sp.symbols('xi z G D pi E',nonzero=True)
rho=6*x/p;a=2*p*(1+x/2)/(1-x)**2;b=2*p*(1+2*x)/(1-x)**2
B0=-3*p*x/(1-x)**2
c=1-2*p*rho*G*E/z
M=-rho/z*(c*(1+z)+2*p*rho*G/z)
N=rho/z**2*(2*p*rho*G/z+c*(1+z+z*z/2))
dA=D*(b*M-4*B0*N);dqp=D*(a*M+b*N);W=2*p*rho*G*D/z;C=c*D
h1=2*z*dA+rho*(dA*a*z-dqp*b*z+2*C*b*z+2*C*b+2*W*b)
h2=2*dqp*z*z+rho*(2*C*a*z*z+2*C*a*z-C*b*z*z-2*C*b*z-2*C*b+2*W*a*z-2*W*b)
assert sp.cancel(h1)==0 and sp.cancel(h2)==0
sd=data(mp.mpf('.15'),mp.mpf('2.45'))
old=json.loads((BASE/'results/msa_b_hierarchy_physical/physical_checks.json').read_text())
Ds=[mp.mpf(v) for v in old['Dt_coefficients']];Gs=[mp.mpf(v) for v in old['G_coefficients']]
dpoly=lambda t:sum(v*t**j for j,v in enumerate(Ds))
gpoly=lambda t:sum(v*t**j for j,v in enumerate(Gs))
def kap(d,g):
    A,b,W,C=sd['amps'](d,g)
    return sd['z']*C+b-sd['qp0']
shape=[]
probe=mp.mpc('.4','1.3')
for n in range(1,len(Ds)):
    theta=2*mp.pi*sd['rho']*mp.exp(-probe)*(sd['hsQ'](probe)*mp.diff(lambda t:sd['f'](probe,dpoly(t),gpoly(t)),0,n)/mp.factorial(n)
        -sd['f'](probe,0,Gs[0])*mp.diff(lambda t:sd['Q'](probe,dpoly(t),gpoly(t)),0,n)/mp.factorial(n))
    kn=kap(1,Gs[0])*Ds[n]+(kap(1,1)-kap(1,0))*sum(Ds[j]*Gs[n-j] for j in range(1,n))
    target=sd['rho']*mp.exp(-probe)*kn/(probe+sd['z'])
    err=abs(theta-target)
    assert err<mp.mpf('1e-48'),(n,err)
    shape.append({'order':n,'source_shape_residual':str(err),'kappa_coefficient':str(kn)})
# Unequal diameters, four tails, repeated rates, and a zero-density species.
sigma=np.array([.8,1.1,1.5]);rho_arr=np.array([.03,.08,0.]);rates=np.array([.6,2.45,2.45,9.])
st=HCYMix(sigma,rho_arr,rates,np.zeros((4,3,3)))
rng=np.random.default_rng(20261012)
Dt=rng.uniform(-.012,.025,(4,3,3));Gt=rng.uniform(.02,.08,(4,3,3))
parts=_pieces(st,Dt,Gt)
qA=list(map(lambda v:mp.mpf(str(v)),parts['A']))
qp=[[mp.mpf(str(v)) for v in row] for row in parts['qp']]
ws=np.vectorize(lambda v:mp.mpf(str(v)),otypes=[object])(parts['Wt'])
cs=np.vectorize(lambda v:mp.mpf(str(v)),otypes=[object])(parts['Ct'])
sig=list(map(lambda v:mp.mpf(str(v)),sigma));rs=list(map(lambda v:mp.mpf(str(v)),rates))
rd=list(map(lambda v:mp.mpf(str(v)),rho_arr))
def q(t,i,j):
    v=min(t,sig[i])-sig[i]
    return qp[i][j]*v+qA[j]*v*v/2+sum(ws[u,i,j]*mp.exp(-rs[u]*t)+cs[u,i,j]*mp.exp(-rs[u]*(max(t,sig[i])-sig[i])) for u in range(4))
def closed_bg(i,j,r,R):
    S=sig[i]
    if r<=S:
        bqp=r**3/6+(R-S)*r*r/2-S*R*r
        ba=r**4/24+(R-S)*r**3/6+(S*S/4-S*R/2)*r*r+S*S*R*r/2
    else:
        bqp=-(r+R)*S*S/2+S**3/6
        ba=(r+R)*S**3/6-S**4/24
    value=qp[i][j]*bqp+qA[j]*ba
    for u,zv in enumerate(rs):
        bw=(r+R)/zv-1/zv**2-mp.exp(-zv*r)*(R/zv-1/zv**2)
        bc=r*r/2+R*r if r<=S else (r+R)*(S+1/zv)-S*S/2-S/zv-1/zv**2-mp.exp(zv*S)*mp.exp(-zv*r)*(R/zv-1/zv**2)
        value+=ws[u,i,j]*bw+cs[u,i,j]*bc
    return value
checks=[]
for rv in ['0','.1','.8','1.1','1.5','3.4','4.5']:
    r=mp.mpf(rv)
    for i in range(3):
        for j in range(3):
            f=(qA[j]*r+qp[i][j]+sum(rs[u]*cs[u,i,j]*mp.exp(-rs[u]*r) for u in range(4)))/(2*mp.pi)
            direct=f-(r+(sig[i]+sig[j])/2)
            closed=direct
            for m in range(3):
                R=(sig[i]+sig[m])/2
                knots=[0,r] if r<=sig[m] else [0,sig[m],r]
                v=mp.quad(lambda t:q(t,m,j)*(r-t+R),knots) if r else mp.mpf(0)
                direct+=rd[m]*v
                closed+=rd[m]*closed_bg(m,j,r,R)
            err=abs(direct-closed)
            assert err<mp.mpf('1e-45'),(i,j,r,err)
            if r>=sum(sig):
                tail=sum((rs[u]*cs[u,i,j]/(2*mp.pi)-sum(rd[m]*(ws[u,m,j]+cs[u,m,j]*mp.exp(rs[u]*sig[m]))*((sig[i]+sig[m])/(2*rs[u])-1/rs[u]**2) for m in range(3)))*mp.exp(-rs[u]*r) for u in range(4))
                # Physical dictionary is supplied as machine-precision arrays.
                assert abs(closed-tail)<mp.mpf('1e-10'),(i,j,r,closed-tail)
            checks.append({'r':rv,'i':i,'j':j,'quadrature_residual':str(err)})
report={'status':'PASS','symbolic_background_checks':2,'scalar_source_shape_orders':shape,
        'mixture_parameters':{'sigma':sigma.tolist(),'rho':rho_arr.tolist(),'z':rates.tolist(),'eta':float(np.pi*np.sum(rho_arr*sigma**3)/6)},
        'mixture_amplitudes':'Off-root values from existing msa_exact_mix._pieces; repeated rates and zero density included.',
        'mixture_quadrature_checks':len(checks),'maximum_quadrature_residual':str(max(mp.mpf(v['quadrature_residual']) for v in checks)),
        'tail_check_tolerance':'1e-10 (machine-precision BH dictionary)',
        'proof_status':'Numerical/SymPy verification only; all corresponding formal claims use kernel-checked Lean theorems.'}
out=BASE/'results/msa_b_hierarchy_physical/finite_source_checks.json';out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
