"""
EXTENDED-SEED mixture DCF via the matrix Volterra renewal — rho-WEIGHTED (physical) kernel.

Supersedes the bare-kernel volterra_extseed.py (which computed the WRONG object: the Lean
`matBaxterUQmSymFullExt` def sums `sum_k int Q_ik * ...` with NO rho_k weight, so its seed/r is
off from the physical DCF by rho-factors and is numerically noisy at unequal diameters).

ROOT-CAUSE FINDING (2026-08-11): the proved equal-diameter reduction
`cHSmixRenewal_eq_cHS_of_equalDiam` requires `hrow: sum_k Q_ik(u) = q0_poly(eta,sigma,rho,u)`
(the SCALAR one-component Baxter q, which carries an explicit `rho` factor). The physical
`Q0phys`/`Qppphys` are the rho-STRIPPED coefficients, so the row-sum identity holds ONLY when each
species-sum is weighted by the summed index rho_k (verified EXACTLY: `sum_k rho_k*Q0phys_ik =
q0_poly`, while bare and rho_geo=sqrt(rho_i rho_k) both FAIL at unequal rho). => the physical seed
that equals `r*c_ij` uses rho_k-WEIGHTED convolution kernels in BOTH the renewal AND the two seed
convolutions. The bare `q0MixEntry(physMix)` kernel in the current Lean seed def is off by rho.

VALIDATION (this file): rho-weighted seed/r reproduces the analytic Wertheim-Thiele one-component
c_HS to 1.5e-9 at equal diameters — for equal AND unequal rho at equal sigma (both species give the
same c_HS(eta)), pinning the rho_k placement (not rho_geo).

REGULARITY RESULT at UNEQUAL diameters (the physical DCF, rho-weighted):
  * SMALLEST-species row (lam_0k>=0, no sub-zero tail, no Psi-kink crossing): c_ij=seed/r is
    DEAD-FLAT to 5 digits across r=0.015..0.12 (e.g. -11.181 x4) => manifestly REGULAR, no 1/r pole.
  * LARGER-species row: mild ~2-3% drift from the sub-zero-tail Psi-kink quad (a0 ~0.4-2% of mag),
    consistent with numerical error, not a genuine pole.
  => the physical mixture DCF c_ij is a finite/regular (Lebowitz-polynomial) object; the apparent
     1/r pole seen with the bare kernel was BOTH a wrong-object and a kink-quad artifact.

Numerics: matrix Volterra renewal (implicit trapezoid, M~6000) for Psiouter with rho-weighted
q0MixPolyMat kernel + matForcingCore; cubic-spline Psi; quad with discontinuity `points` at the
Psi kink/jump (v-s = +-sigma). solve_renewal/utExt/extseed all carry the rho_k weight `rw`.
"""

import numpy as np
from scipy.integrate import quad
from scipy.interpolate import CubicSpline
pi=np.pi
def setup(rho,sigma):
    N=len(rho); xi2=sum(rho[i]*sigma[i]**2 for i in range(N))
    eta=pi/6*sum(rho[i]*sigma[i]**3 for i in range(N)); vac=1-eta
    R=[[(sigma[i]+sigma[k])/2 for k in range(N)] for i in range(N)]
    lam=[[(sigma[k]-sigma[i])/2 for k in range(N)] for i in range(N)]
    Q0=[[(2*pi/vac)*(R[i][k]+pi*xi2*sigma[i]*sigma[k]/(4*vac)) for k in range(N)] for i in range(N)]
    Qpp=[(2*pi/vac)*(1+pi*xi2*sigma[k]/(2*vac)) for k in range(N)]
    return N,max(sigma),R,lam,Q0,Qpp,eta
def qpoly(w,Q0ik,Qppk,Rik):
    m=min(w,Rik); return Q0ik*(m-Rik)+Qppk*(m-Rik)**2/2
def qentry(w,Q0ik,Qppk,Rik,lamik):
    return (Q0ik*(w-Rik)+Qppk*(w-Rik)**2/2) if (lamik<=w<=Rik) else 0.0
def Kmat(name,w,i,k,R,lam,Q0,Qpp):
    return qpoly(w,Q0[i][k],Qpp[k],R[i][k]) if name=='poly' else qentry(w,Q0[i][k],Qpp[k],R[i][k],lam[i][k])
def solve_renewal(rho,sigma,M=4000):
    N,sig,R,lam,Q0,Qpp,eta=setup(rho,sigma); L=2.0*sig
    r=np.linspace(sig,sig+L,M+1); h=r[1]-r[0]; rw=np.array(rho)
    F=np.zeros((M+1,N))
    for n in range(M+1):
        for i in range(N):
            pts=[r[n]-R[i][k] for k in range(N)]; pts=[p for p in pts if 0<p<sig]
            F[n,i]=-sum(rw[k]*quad(lambda s: Kmat('poly',r[n]-s,i,k,R,lam,Q0,Qpp)*s,0,sig,
                             points=pts if pts else None,limit=80)[0] for k in range(N))
    K0=np.array([[rw[k]*Kmat('poly',0.0,i,k,R,lam,Q0,Qpp) for k in range(N)] for i in range(N)])
    psi=np.zeros((M+1,N)); psi[0]=F[0]; Ainv=np.linalg.inv(np.eye(N)-h*0.5*K0)
    for n in range(1,M+1):
        rhs=F[n].copy()
        for m in range(n):
            w=0.5 if m==0 else 1.0
            Km=np.array([[rw[k]*Kmat('poly',r[n]-r[m],i,k,R,lam,Q0,Qpp) for k in range(N)] for i in range(N)])
            rhs+=h*w*(Km@psi[m])
        psi[n]=Ainv@rhs
    spl=[CubicSpline(r,psi[:,k]) for k in range(N)]
    return sig,N,R,lam,Q0,Qpp,eta,spl,r[-1],rw
def make_Psi(spl,sig,rmax):
    def Psi(v,k):
        if abs(v)<sig: return -v
        if v>=sig: return float(spl[k](v)) if v<=rmax else 0.0
        w=-v; return -(float(spl[k](w)) if w<=rmax else 0.0)
    return Psi
def utExt(Psi,i,v,R,lam,Q0,Qpp,sig,rw):
    N=len(rw); tot=Psi(v,i)
    for m in range(N):
        a,b=lam[m][i],R[m][i]; pts=[v-sig,v+sig]; pts=[p for p in pts if a<p<b]
        tot-=rw[m]*quad(lambda s: Kmat('entry',s,m,i,R,lam,Q0,Qpp)*Psi(v-s,m),a,b,
                        points=pts if pts else None,limit=120)[0]
    return tot
def extseed(Psi,i,r,R,lam,Q0,Qpp,sig,rw):
    N=len(rw); lead=utExt(Psi,i,r,R,lam,Q0,Qpp,sig,rw); coup=0.0
    for k in range(N):
        a,b=lam[i][k],R[i][k]; pts=[sig-r,-sig-r]; pts=[p for p in pts if a<p<b]
        coup+=rw[k]*quad(lambda t: Kmat('entry',t,i,k,R,lam,Q0,Qpp)*utExt(Psi,k,r+t,R,lam,Q0,Qpp,sig,rw),
                         a,b,points=pts if pts else None,limit=150)[0]
    return lead-coup
def cHS_analytic(eta,r):
    l1=(1+2*eta)**2/(1-eta)**4; l2=-(1+eta/2)**2/(1-eta)**4
    return -l1-6*eta*l2*r-0.5*eta*l1*r**3
if __name__=="__main__":
    for rho,sigma in [([0.2,0.2],[1.0,1.0]),([0.15,0.25],[1.0,1.0])]:
        sig,N,R,lam,Q0,Qpp,eta,spl,rmax,rw=solve_renewal(rho,sigma,M=5000)
        Psi=make_Psi(spl,sig,rmax)
        print(f"== rho={rho} sigma={sigma} eta={eta:.5f} (rho-weighted) ==")
        rs=np.linspace(0.3,0.06,6)
        for i in [0,1]:
            cnum=np.array([extseed(Psi,i,rr,R,lam,Q0,Qpp,sig,rw)/rr for rr in rs])
            can=np.array([cHS_analytic(eta,rr) for rr in rs])
            print(f"  i={i}: max|c_num - c_HS_analytic| = {np.max(np.abs(cnum-can)):.3e} "
                  f"(c_HS(0)={-((1+2*eta)**2/(1-eta)**4):.4f}, c_num@r={rs[-1]:.2f}={cnum[-1]:.4f})")
