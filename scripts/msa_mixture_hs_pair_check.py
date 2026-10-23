#!/usr/bin/env python3
"""Numerical diagnostic of the actual pair-contact HS Volterra candidate.

Uses the actual left-density recentered kernel and the actual canonical
larger-diameter-row c0. This does not prove the remaining reference OZ/WT
identity or certify any interval inequalities in Lean.
"""
import argparse
import json
import warnings
from pathlib import Path
import numpy as np
from scipy.integrate import cumulative_trapezoid, quad
from math import pi
from numpy.polynomial import polynomial as poly
from msa_mixture_rdf_budget_check import weighted_kernel_budget

def probe(rho,sigma,step=.003):
 rho=np.array(rho);sigma=np.array(sigma);N=len(rho);R=(sigma[:,None]+sigma[None,:])/2;lam=(sigma[None,:]-sigma[:,None])/2
 vac=1-pi/6*np.sum(rho*sigma**3);xi2=np.sum(rho*sigma**2)
 qp=2*pi/vac*(R+pi*xi2*sigma[:,None]*sigma[None,:]/(4*vac));qpp=2*pi/vac*(1+pi*xi2*sigma/(2*vac))
 t=np.arange(0,6+step/2,step);w=np.maximum(sigma[None,:]-t[:,None],0)
 K=rho[None,:,None]*(qp[None,:,:]*(-w[:,:,None])+qpp[None,None,:]/2*w[:,:,None]**2)
 F=np.zeros((len(t),N,N))
 for i in range(N):
  for j in range(N):
   F[:,i,j]=sum(rho[m]*(qp[m,i]*(R[m,j]*w[:,m]**2/2-w[:,m]**3/6)+qpp[i]*(w[:,m]**4/24-R[m,j]*w[:,m]**3/6)) for m in range(N))
 Y=np.zeros_like(F);Y[0]=F[0];lhs=np.eye(N)-step/2*K[0].T
 for n in range(1,len(t)):
  rhs=F[n]+step*(np.einsum('tmi,tmj->ij',K[1:n][::-1],Y[1:n])+K[n].T@Y[0]/2)
  Y[n]=np.linalg.solve(lhs,rhs)
 CY=cumulative_trapezoid(Y,t,axis=0,initial=0)
 def psi(i,j,r):
  return -r if r<R[i,j] else float(np.interp(r-R[i,j],t,Y[:,i,j]))
 def prim(i,j,r):
  if r<=R[i,j]:return -r*r/2
  return -R[i,j]**2/2+float(np.interp(r-R[i,j],t,CY[:,i,j]))
 def c(i,j,r):
  if sigma[i]<sigma[j]:i,j=j,i
  if r>R[i,j]:return 0.
  p=qp[i,j]+qpp[j]*(r-R[i,j]) if lam[i,j]<=r else 0.
  s=0.
  for m in range(N):
   lo=max(lam[j,m],lam[i,m]-r);hi=min(R[j,m],R[i,m]-r)
   if hi<=lo:continue
   a=[qp[i,m]+qpp[m]*(r-R[i,m]),qpp[m]]
   b=[-qp[j,m]*R[j,m]+qpp[m]/2*R[j,m]**2,qp[j,m]-qpp[m]*R[j,m],qpp[m]/2]
   P=poly.polyint(poly.polymul(a,b));s+=rho[m]*(poly.polyval(hi,P)-poly.polyval(lo,P))
  return (-p+s)/(2*pi*r)
 maxerr=maxsym=0.;samples=[]
 for i in range(N):
  for j in range(N):
   for r in [.25,.7,1.1,1.7,2.5]:
    h=psi(i,j,r)/r
    sym=abs(h-psi(j,i,r)/r);maxsym=max(maxsym,sym)
    conv=0.
    for m in range(N):
     pts=sorted({0,R[i,m],abs(r-R[m,j]),r+R[m,j],abs(lam[i,m])})
     pts=[x for x in pts if 0<x<R[i,m]]
     val=quad(lambda v:v*c(i,m,v)*(prim(m,j,r+v)-prim(m,j,abs(r-v))),0,R[i,m],points=pts,epsabs=1e-8,epsrel=1e-8,limit=250)[0]
     conv+=rho[m]*2*pi/r*val
    err=abs(h-c(i,j,r)-conv);maxerr=max(maxerr,err)
    samples.append({'i':i,'j':j,'r':r,'h0':h,'canonical_c0':c(i,j,r),'OZ_convolution':conv,'absolute_OZ_residual':err,'absolute_reciprocity_residual':sym})
 return {'rho':rho.tolist(),'sigma':sigma.tolist(),'step':step,'maximum_OZ_residual':maxerr,'maximum_reciprocity_residual':maxsym,'numerical_budget':weighted_kernel_budget(rho.tolist(),sigma.tolist(),.2,[.6,1.8]),'samples':samples}
if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--output',type=Path)
 args=parser.parse_args()
 with warnings.catch_warnings(record=True) as caught:
  warnings.simplefilter('always')
  cases=[probe([.01,.015],[1.,1.6]),probe([.01,.015],[1.,1.6],.0015),probe([.0003,.0005,.0008],[1.,1.4,2.3])]
 result={'scope':'numerical definition and implementation diagnostic only; actual pairwise HS candidate global radius L1 is Lean-certified under the budget, actual canonical radial OZ remains unproved','not_a_formal_OZ_or_interval_certificate':True,'kernel':'Kc_mi=LEFT rho_m*Qc_mi; r=Rij+u, t=lambda_mi+v; per-pair contacts retained','source':'sum_m rho_m*[qp_mi*(Rmj*w^2/2-w^3/6)+qpp_i*(w^4/24-Rmj*w^3/6)], w=max(sigma_m-u,0); equivalent actual core tail integral','warnings':sorted({str(w.message) for w in caught}),'cases':cases}
 data=json.dumps(result,indent=2)+'\n'
 if args.output:args.output.write_text(data)
 print(data,end='')
