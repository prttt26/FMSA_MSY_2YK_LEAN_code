"""
MIXCHS.4 VERIFICATION (2026-08-14/15): does the EXTENDED seed matBaxterUQmSymFullExt[phys]
reproduce the value-route (MIXCHS.7-N) pair Lebowitz DCF cMixDCFN at UNEQUAL diameters?

RESULT: YES — the extended seed row i gives r * c_{i,k*}, where k* = argmax(sigma) (the LARGEST
species): the seed reproduces the LARGEST-SPECIES COLUMN of the physical pair Lebowitz DCF.
seed(i,j) is j-INDEPENDENT (the physical renewal has Ψ_ij=ψ_i), so it equals the fixed-column
c_{i,k*}, a genuine pair DCF — it AGREES with the value route on those pairs.

  * CONTROL (equal σ=1.0): seed/r == c_HS == cMixDCFN to 6e-10  (machinery sound).
  * UNEQUAL σ=[1.0,0.7] and [1.0,0.85,0.7], k*=0:
      - smaller-species rows (i != k*): seed/r == cMixDCFN(i,k*) EXACTLY (0.00%).
      - largest-species diagonal (i == k*): seed/r == cMixDCFN(k*,k*) within ~2-4% (grows with r
        = the known sub-zero-tail Ψ-kink SOLVER error on the largest row, M-converged, not physics).

⚠ CORRECTION of an earlier (WRONG) run in this session that claimed the target was REFUTED: that
used cHS_analytic(eta_mix,r) as the mixture DIAGONAL c_{k*,k*}, which is WRONG — cHS_analytic is
hardcoded for σ=1 (uses r, not r/σ) AND the mixture diagonal c_ii is NOT c_HS(eta_mix) but the
Lebowitz expression with σ_i and the MIXTURE moments (ξ₂, vac). With the correct diagonal, the
larger-species seed row (−5.42) matches c_{k*,k*} (−5.31..−5.40), not the bogus c_HS (−4.57).
The M-independence of the "σ≠1 control failures" (σ=0.9: 6.6% at M=6000 AND M=12000; σ=1.2: 88%)
exposed the bug: they were reference errors (cHS_analytic wrong for σ≠1), NOT solver errors.

⇒ the extended-seed route and the value route give the SAME physical DCF (the seed = the k*-column).
MIXCHS.4-unequal (matBaxterUQmSymFullExt[phys] = r·c_ij for the largest-species column) is
ACHIEVABLE and consistent — a redundant confirmation of the value route's cMixDCFN, which already
covers ALL pairs. No contradiction; the value route (MIXCHS.7-N) remains the full pair-DCF result.
"""
import numpy as np, sys
sys.path.insert(0,'/home/rpan/YK_tail_FMSA/Lean_code')
from volterra_extseed import solve_renewal, make_Psi, extseed
pi=np.pi
def cMix(rho,sigma,i,k,r):  # value-route two-piece Lebowitz DCF for pair (i,k); NO c_HS shortcut
    si,sk=sigma[i],sigma[k]
    if si>sk: return cMix(rho,sigma,k,i,r)
    D=1-pi/6*sum(rho[l]*sigma[l]**3 for l in range(len(rho))); xi=sum(rho[l]*sigma[l]**2 for l in range(len(rho)))
    lam=(sk-si)/2; R=(si+sk)/2
    if r>=R: return 0.0
    def A(sl,rl): return (-64*D**2*pi*rl*si**3-192*D**2*pi*rl*si**2*sl-192*D**2*pi*rl*si*sl**2-64*D**2*pi*rl*sk**3-192*D**2*pi*rl*sk**2*sl+192*D**2*pi*rl*sk*sl**2-64*D*pi**2*rl*si**3*sl*xi-96*D*pi**2*rl*si**2*sl**2*xi-64*D*pi**2*rl*sk**3*sl*xi-96*D*pi**2*rl*sk**2*sl**2*xi-16*pi**3*rl*si**3*sl**2*xi**2-16*pi**3*rl*sk**3*sl**2*xi**2)
    def B(sl,rl): return (12*D**2*pi*rl*si**4+48*D**2*pi*rl*si**3*sl-24*D**2*pi*rl*si**2*sk**2-48*D**2*pi*rl*si**2*sk*sl+48*D**2*pi*rl*si**2*sl**2-48*D**2*pi*rl*si*sk**2*sl-96*D**2*pi*rl*si*sk*sl**2+12*D**2*pi*rl*sk**4+48*D**2*pi*rl*sk**3*sl-144*D**2*pi*rl*sk**2*sl**2+12*D*pi**2*rl*si**4*sl*xi+24*D*pi**2*rl*si**3*sl**2*xi-24*D*pi**2*rl*si**2*sk**2*sl*xi-24*D*pi**2*rl*si**2*sk*sl**2*xi-24*D*pi**2*rl*si*sk**2*sl**2*xi+12*D*pi**2*rl*sk**4*sl*xi+24*D*pi**2*rl*sk**3*sl**2*xi+3*pi**3*rl*si**4*sl**2*xi**2-6*pi**3*rl*si**2*sk**2*sl**2*xi**2+3*pi**3*rl*sk**4*sl**2*xi**2)
    def C2(sl,rl): return (96*D**2*pi*rl*si**2+192*D**2*pi*rl*si*sl+96*D**2*pi*rl*sk**2+192*D**2*pi*rl*sk*sl+192*D**2*pi*rl*sl**2+96*D*pi**2*rl*si**2*sl*xi+96*D*pi**2*rl*si*sl**2*xi+96*D*pi**2*rl*sk**2*sl*xi+96*D*pi**2*rl*sk*sl**2*xi+24*pi**3*rl*si**2*sl**2*xi**2+24*pi**3*rl*sk**2*sl**2*xi**2)
    def E(sl,rl): return (-64*D**2*pi*rl-64*D*pi**2*rl*sl*xi-16*pi**3*rl*sl**2*xi**2)
    re=lam if (lam>0 and r<lam) else r; den=768*D**4
    aA=-768*D**3-384*D**2*pi*sk*xi+sum(A(sigma[l],rho[l]) for l in range(len(rho)))
    aB=192*D**2*pi*sk**2*xi+sum(B(sigma[l],rho[l]) for l in range(len(rho)))
    aC=sum(C2(sigma[l],rho[l]) for l in range(len(rho))); aE=sum(E(sigma[l],rho[l]) for l in range(len(rho)))
    return (aA+aB/re+aC*re+aE*re**3)/den
if __name__=="__main__":
    for rho,sigma in [([0.3,0.25],[1.0,0.7]), ([0.2,0.18,0.15],[1.0,0.85,0.7])]:
        kstar=int(np.argmax(sigma)); N=len(sigma)
        sig,_,R,lam,Q0,Qpp,eta,spl,rmax,rw=solve_renewal(rho,sigma,M=8000); Psi=make_Psi(spl,sig,rmax)
        print(f"σ={sigma} k*={kstar} (seed_i /r  vs  cMixDCFN(i,k*)):")
        for i in range(N):
            for rr in [0.06,0.10]:
                s=extseed(Psi,i,rr,R,lam,Q0,Qpp,sig,rw)/rr; ck=cMix(rho,sigma,i,kstar,rr)
                tag="EXACT" if abs((s-ck)/ck)<3e-4 else f"{abs((s-ck)/ck)*100:.1f}% (solver, i=k*)" if i==kstar else "?"
                print(f"  i={i} r={rr}: {s:+.5f} vs {ck:+.5f}  {tag}")
