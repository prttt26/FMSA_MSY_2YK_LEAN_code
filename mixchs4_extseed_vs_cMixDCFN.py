"""
MIXCHS.4 VERIFICATION (2026-08-14): does the EXTENDED seed matBaxterUQmSymFullExt[phys]
equal r * cMixDCFN (the value-route MIXCHS.7-N pair Lebowitz DCF) at UNEQUAL diameters?

RESULT: NO — the target `matBaxterUQmSymFullExt = r*c_ij` (c_ij = cMixDCFN) is REFUTED at unequal σ.

  * CONTROL (equal σ=1.0): seed/r == c_HS == cMixDCFN to 6e-10  => the numerical machinery
    (Volterra renewal + extseed from volterra_extseed.py, calibrated at σ_max=1.0) is sound.
  * UNEQUAL σ=[1.0,0.7], ρ=[0.3,0.25]:
      - smaller-species row (i=1): seed/r == cMixDCFN(1,0) EXACTLY in the lower piece (−3.4416),
        smooth solver drift in the upper piece  -> matches the ORDERED pair (smaller,larger).
      - larger-species row  (i=0): seed/r = −5.42, matches NEITHER cMixDCFN(0,0)=−4.57 NOR
        cMixDCFN(0,1)=−3.44 (18–58% off, vs the 6e-10 baseline — not solver error).

STRUCTURAL PROOF (independent of numerics): the physical Baxter renewal has Ψ_ij = ψ_i
(j-INDEPENDENT — it is the outer q-function, not the OZ h_ij), and matBaxterUtExt_core is
j-independent, so the extended seed is a j-INDEPENDENT, ROW object; numerically it is
ROW-ASYMMETRIC (seed_0=−5.42 ≠ seed_1=−3.44). The pair DCF c_ij is SYMMETRIC (c_01=c_10). A
j-independent, row-asymmetric object CANNOT equal the symmetric pair DCF.  => the extended seed
route computes a DIFFERENT object from the value route's cMixDCFN; MIXCHS.4-unequal as
"= r*c_ij" is the wrong statement.  The pair Lebowitz DCF is fully established by MIXCHS.7-N.
"""
import numpy as np, sys
sys.path.insert(0,'/home/rpan/YK_tail_FMSA/Lean_code')
from volterra_extseed import solve_renewal, make_Psi, extseed, cHS_analytic
pi=np.pi
def cMixDCFN(rho,sigma,i,k,r):
    si,sk=sigma[i],sigma[k]
    D=1-pi/6*sum(rho[l]*sigma[l]**3 for l in range(len(rho))); xi=sum(rho[l]*sigma[l]**2 for l in range(len(rho)))
    if abs(si-sk)<1e-14: return cHS_analytic(pi/6*sum(rho[l]*sigma[l]**3 for l in range(len(rho))),r)
    if si>sk: return cMixDCFN(rho,sigma,k,i,r)
    lam=(sk-si)/2; R=(si+sk)/2
    if r>=R: return 0.0
    def A(sl,rl): return (-64*D**2*pi*rl*si**3-192*D**2*pi*rl*si**2*sl-192*D**2*pi*rl*si*sl**2-64*D**2*pi*rl*sk**3-192*D**2*pi*rl*sk**2*sl+192*D**2*pi*rl*sk*sl**2-64*D*pi**2*rl*si**3*sl*xi-96*D*pi**2*rl*si**2*sl**2*xi-64*D*pi**2*rl*sk**3*sl*xi-96*D*pi**2*rl*sk**2*sl**2*xi-16*pi**3*rl*si**3*sl**2*xi**2-16*pi**3*rl*sk**3*sl**2*xi**2)
    def B(sl,rl): return (12*D**2*pi*rl*si**4+48*D**2*pi*rl*si**3*sl-24*D**2*pi*rl*si**2*sk**2-48*D**2*pi*rl*si**2*sk*sl+48*D**2*pi*rl*si**2*sl**2-48*D**2*pi*rl*si*sk**2*sl-96*D**2*pi*rl*si*sk*sl**2+12*D**2*pi*rl*sk**4+48*D**2*pi*rl*sk**3*sl-144*D**2*pi*rl*sk**2*sl**2+12*D*pi**2*rl*si**4*sl*xi+24*D*pi**2*rl*si**3*sl**2*xi-24*D*pi**2*rl*si**2*sk**2*sl*xi-24*D*pi**2*rl*si**2*sk*sl**2*xi-24*D*pi**2*rl*si*sk**2*sl**2*xi+12*D*pi**2*rl*sk**4*sl*xi+24*D*pi**2*rl*sk**3*sl**2*xi+3*pi**3*rl*si**4*sl**2*xi**2-6*pi**3*rl*si**2*sk**2*sl**2*xi**2+3*pi**3*rl*sk**4*sl**2*xi**2)
    def C2(sl,rl): return (96*D**2*pi*rl*si**2+192*D**2*pi*rl*si*sl+96*D**2*pi*rl*sk**2+192*D**2*pi*rl*sk*sl+192*D**2*pi*rl*sl**2+96*D*pi**2*rl*si**2*sl*xi+96*D*pi**2*rl*si*sl**2*xi+96*D*pi**2*rl*sk**2*sl*xi+96*D*pi**2*rl*sk*sl**2*xi+24*pi**3*rl*si**2*sl**2*xi**2+24*pi**3*rl*sk**2*sl**2*xi**2)
    def E(sl,rl): return (-64*D**2*pi*rl-64*D*pi**2*rl*sl*xi-16*pi**3*rl*sl**2*xi**2)
    re=lam if r<lam else r; den=768*D**4
    aA=-768*D**3-384*D**2*pi*sk*xi+sum(A(sigma[l],rho[l]) for l in range(len(rho)))
    aB=192*D**2*pi*sk**2*xi+sum(B(sigma[l],rho[l]) for l in range(len(rho)))
    aC=sum(C2(sigma[l],rho[l]) for l in range(len(rho))); aE=sum(E(sigma[l],rho[l]) for l in range(len(rho)))
    return (aA+aB/re+aC*re+aE*re**3)/den
if __name__=="__main__":
    print("CONTROL equal σ=1.0:")
    sig,N,R,lam,Q0,Qpp,eta,spl,rmax,rw=solve_renewal([0.3,0.25],[1.0,1.0],M=6000); Psi=make_Psi(spl,sig,rmax)
    for i in [0,1]:
        e=max(abs(extseed(Psi,i,rr,R,lam,Q0,Qpp,sig,rw)/rr-cHS_analytic(eta,rr)) for rr in [0.1,0.3,0.5])
        print(f"  i={i}: max|seed/r - c_HS| = {e:.2e}")
    print("UNEQUAL σ=[1.0,0.7] ρ=[0.3,0.25]:")
    sig,N,R,lam,Q0,Qpp,eta,spl,rmax,rw=solve_renewal([0.3,0.25],[1.0,0.7],M=6000); Psi=make_Psi(spl,sig,rmax)
    for i in [0,1]:
        for rr in [0.08,0.30]:
            cs=extseed(Psi,i,rr,R,lam,Q0,Qpp,sig,rw)/rr
            print(f"  i={i} r={rr}: seed/r={cs:+.4f}  cMixDCFN(i,0)={cMixDCFN([0.3,0.25],[1.0,0.7],i,0,rr):+.4f}  cMixDCFN(i,1)={cMixDCFN([0.3,0.25],[1.0,0.7],i,1,rr):+.4f}")
