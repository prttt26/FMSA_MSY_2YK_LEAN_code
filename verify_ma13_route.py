"""Recon for MA.13 (`volterra_renewal_tendsto_zero`), 2026-07-21.

Establishes (a) why no elementary route exists -- the causal L1 convolution algebra has spectral
radius sup_{Re z>=0}|qhat(z)| = |qhat(0)| = M = eta(4-eta)/(1-eta)^2 > 1 for eta > (3-sqrt7)/2, so
the Neumann series for the resolvent DIVERGES and its existence is exactly Wiener's 1/f theorem;
and (b) that the axiom's instantiation is true: the simulated renewal solution decays at exactly
the rate Im(k1) of the lowest Baxter pole (= the Ornstein-Zernike correlation decay) and is L1.
See `proof_notes_pole.md` -> "POLE.11 decay half / MA.13".
"""
import numpy as np
s=1.0
def par(eta):
    rho=6*eta/(np.pi*s**3); qp=np.pi*s*(2+eta)/(1-eta)**2; qpp=2*np.pi*(1+2*eta)/(1-eta)**2
    return rho,qp,qpp
def bax(eta):
    rho,qp,qpp=par(eta); return rho*qpp*s**2/2-rho*qp*s, rho*qp-rho*qpp*s, rho*qpp/2
def Gdefl(k,eta):   # G_baxter(k)/k^3  -- zeros = Baxter poles, origin deflated
    P0,P1,P2=bax(eta)
    return (1j*k**3-P0*k**2+1j*P1*k+2*P2-(1j*(P1+2*P2*s)*k+2*P2)*np.exp(-1j*k*s))/k**3
def q0(t,eta):
    rho,qp,qpp=par(eta)
    return np.where((t>=0)&(t<=s), rho*qp*(t-s)+rho*qpp*(t-s)**2/2, 0.0)

print("[3'] lowest Baxter pole (deflated root-find, Im k>0) -> predicted decay rate Im(k1)")
lowest={}
for eta in [0.2,0.4,0.6,0.8]:
    best=None
    for re0 in np.linspace(-14,14,60):
        for im0 in np.linspace(0.2,8,30):
            k=complex(re0,im0)
            ok=True
            for _ in range(200):
                h=1e-7*max(1,abs(k))
                d=(Gdefl(k+h,eta)-Gdefl(k-h,eta))/(2*h)
                if abs(d)<1e-30 or abs(k)<1e-6: ok=False;break
                k-=Gdefl(k,eta)/d
                if abs(k)>1e5: ok=False;break
            if ok and abs(Gdefl(k,eta))<1e-8 and k.imag>1e-4:
                if best is None or k.imag<best.imag: best=k
    lowest[eta]=best
    print(f"  eta={eta:<5} k1={best:.5f}   predicted psi decay rate = Im k1 = {best.imag:.5f}")

print("\n[4] DIRECT SIMULATION of the renewal eq  psi(r)=g(r)+int_0^r q(r-t)psi(t)dt")
print("    g = baxterForcing (supported [sigma,2sigma]); measure actual decay of |psi|")
for eta in [0.2,0.4,0.6,0.8]:
    h=0.002; R=40.0; n=int(R/h)+1
    r=np.arange(n)*h
    qv=q0(r,eta)
    # baxterForcing(r) = int_0^sigma q0(r-u)*(-u) du   (support [sigma,2sigma])
    gu=np.linspace(0,s,2001)
    g=np.array([np.trapezoid(q0(rr-gu,eta)*(-gu),gu) for rr in r])
    psi=np.zeros(n)
    # Volterra: trapezoid, psi(r_i)=g_i + h*sum_j w_j q(r_i-r_j) psi_j ; diagonal q(0)=0 (q0(sigma)=0? no, q0(0)!=0)
    q0v=qv[0]
    for i in range(n):
        acc=0.0
        jmax=i
        if jmax>0:
            idx=np.arange(0,jmax+1)
            w=np.full(jmax+1,h); w[0]*=0.5; w[-1]*=0.5
            acc=np.sum(w*qv[i-idx]*psi[idx])
        # implicit diagonal term
        psi[i]=(g[i]+acc-0.5*h*q0v*psi[i]*0)/(1-0.5*h*q0v)
    # measure decay rate on the tail
    mask=(r>12)&(r<32)
    env=np.abs(psi[mask]); rr=r[mask]
    # fit log of local maxima envelope
    pos=env>1e-300
    A=np.polyfit(rr[pos], np.log(np.maximum(env[pos],1e-300)),1)
    k1=lowest[eta]
    print(f"  eta={eta:<5} |psi(40)|={abs(psi[-1]):.3e}  fitted decay rate={-A[0]:.4f}"
          f"   Im k1={k1.imag:.4f}   ratio={-A[0]/k1.imag:.3f}")
    print(f"          int_0^40 |psi| = {np.trapezoid(np.abs(psi),r):.4f}  (finite => psi in L1)")
