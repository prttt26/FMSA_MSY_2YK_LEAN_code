"""Construct BH amplitude Taylor jets by linear solves at the HS Jacobian.

No nonlinear root solve is used to construct the jets. The residual is polynomial
in the amplitudes for fixed geometry and rates. mpmath works at 60 decimal digits.
"""
import json
import sys
from pathlib import Path

import mpmath as mp
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
from msa_exact_mix import HCYMix, solve_bh_mix

mp.mp.dps = 60
sigma = [mp.mpf('1'), mp.mpf('2')]
rho = [mp.mpf('.1'), mp.mpf('.04')]
z = mp.mpf('1.8')
K = mp.matrix([[mp.mpf('.5'), mp.mpf('.3')], [mp.mpf('.3'), mp.mpf('.4')]])
N = 2
def matrix(entry):
    return mp.matrix([[entry(i,j) for j in range(N)] for i in range(N)])
eye = mp.eye(N)
SIG = matrix(lambda i,j:(sigma[i]+sigma[j])/2)
LAM = matrix(lambda i,j:(sigma[i]-sigma[j])/2)
xi2 = mp.pi/6*sum(rho[i]*sigma[i]**2 for i in range(N))
xi3 = mp.pi/6*sum(rho[i]*sigma[i]**3 for i in range(N))
d = 2*mp.pi/(1-xi3)**2
A0 = [d*(1-xi3+3*sigma[i]*xi2) for i in range(N)]
B0 = [d*(-mp.mpf('1.5')*sigma[i]**2*xi2) for i in range(N)]
QP0 = matrix(lambda i,j:d*(mp.mpf('1.5')*sigma[i]*sigma[j]*xi2+SIG[i,j]*(1-xi3)))


def pieces(x):
    Dt = matrix(lambda i,j:x[i*N+j])
    Gt = matrix(lambda i,j:x[N*N+i*N+j])
    gam = matrix(lambda i,j:eye[i,j]-2*mp.pi*rho[j]*Gt[i,j]*mp.exp(-z*SIG[i,j])/z)
    Ct = matrix(lambda i,j:sum(gam[i,l]*mp.exp(-z*LAM[i,l])*Dt[l,j] for l in range(N)))
    Wt = matrix(lambda i,j:2*mp.pi/z*sum(rho[l]*Gt[i,l]*Dt[l,j] for l in range(N)))
    M = [-sum(rho[l]*(Wt[l,j]+(1+z*sigma[l])*Ct[l,j]) for l in range(N))/z for j in range(N)]
    Nc = [sum(rho[l]*((1+z*LAM[j,l])/z**2*Wt[l,j]+
          ((1+z*sigma[l]+(z*sigma[l])**2/2)/z**2+LAM[j,l]*(1+z*sigma[l])/z)*Ct[l,j])
          for l in range(N)) for j in range(N)]
    A = [A0[j]*(1+M[j])-4*B0[j]*Nc[j]/sigma[j]**2 for j in range(N)]
    qp = matrix(lambda i,j:QP0[i,j]*(1+M[j])+A0[i]*Nc[j])
    return Dt,Gt,Ct,Wt,A,qp


def qhat(p,s):
    Dt,Gt,Ct,Wt,A,qp=p
    def entry(i,j):
        v=s*sigma[i]
        phi1=(1-v-mp.exp(-v))/v**2
        phi2=(1-v+v**2/2-mp.exp(-v))/v**3
        core=sigma[i]**2*phi1*qp[i,j]+sigma[i]**3*phi2*A[j]
        core+=Wt[i,j]/(s+z)+Ct[i,j]*(mp.exp(-v)/(s+z)+(1-mp.exp(-v))/s)
        return mp.exp(-s*LAM[j,i])*core
    return matrix(entry)


def matrices(Q):
    Y=matrix(lambda i,j:mp.exp(-z*LAM[j,i])*(eye[i,j]-rho[i]*Q[j,i]))
    Z=matrix(lambda i,j:mp.exp(z*LAM[j,i])*(eye[i,j]-rho[i]*Q[i,j]))
    return Y,Z


def residual(t,x):
    Dt,Gt,Ct,Wt,A,qp=p=pieces(x)
    Y,Z=matrices(qhat(p,z))
    r1=Dt*Y-2*mp.pi*t*K/z
    src=matrix(lambda i,j:(A[j]+z*qp[i,j]+z**2*Ct[i,j]/2)/z**2)
    r2=2*mp.pi*Gt*Z-src
    return mp.matrix([r1[i,j] for i in range(N) for j in range(N)]+
                     [r2[i,j] for i in range(N) for j in range(N)])


Y0,Z0=matrices(qhat(pieces(mp.zeros(2*N*N,1)),z))
src0=matrix(lambda i,j:(A0[j]+z*QP0[i,j])/z**2)
G0=src0*Z0**-1/(2*mp.pi)
x0=mp.matrix([mp.mpf(0)]*(N*N)+[G0[i,j] for i in range(N) for j in range(N)])
J=mp.matrix(2*N*N)
for j in range(2*N*N):
    direction=mp.zeros(2*N*N,1)
    direction[j]=1
    column=mp.diff(lambda h:residual(0,x0+h*direction),0)
    for i in range(2*N*N):
        J[i,j]=column[i]

jets=[x0]
rows=[]
for n in range(1,6):
    def lower(t):
        return sum((x*t**k for k,x in enumerate(jets)),mp.zeros(2*N*N,1))
    rn=mp.diff(lambda t:residual(t,lower(t)),0,n)/mp.factorial(n)
    xn=mp.lu_solve(J,-rn)
    jets.append(xn)
    rows.append(dict(order=n,coefficient_norm=float(mp.norm(xn)),
                     linear_residual_norm=float(mp.norm(J*xn+rn))))

def truncated(t,n):
    return sum((jets[k]*t**k for k in range(n+1)),mp.zeros(2*N*N,1))

coefficient_defects=[float(mp.norm(mp.diff(lambda t:residual(t,truncated(t,5)),0,n)/mp.factorial(n)))
                     for n in range(6)]
checks=[]
for n in [2,3,5]:
    for t in [.08,.04,.02]:
        tt=mp.mpf(str(t))
        state=truncated(tt,n)
        sol=solve_bh_mix(HCYMix(np.array([1.,2.]),np.array([.1,.04]),[1.8],t*np.array([[.5,.3],[.3,.4]])),tol=5e-13)
        exact=np.r_[sol.Dt.ravel(),sol.Gt.ravel()]
        checks.append(dict(order=n,tau=t,residual_norm=float(mp.norm(residual(tt,state))),
                           root_difference_norm=float(np.linalg.norm(np.array(list(state),float)-exact))))

report=dict(precision_digits=mp.mp.dps,HS_residual_norm=float(mp.norm(residual(0,x0))),
            HS_jacobian_condition=float(np.linalg.cond(np.array(J.tolist(),float))),
            construction='HS seed plus the same linear Jacobian solve at each order; no nonlinear solve for jets',
            orders=rows,residual_taylor_coefficient_defects=coefficient_defects,
            validation_against_independent_nonlinear_roots=checks)
Path('/tmp/fmsa_amplitude_jet_check.json').write_text(json.dumps(report,indent=2))
print(json.dumps(report,indent=2))
