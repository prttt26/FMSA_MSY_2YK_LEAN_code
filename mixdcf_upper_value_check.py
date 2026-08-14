import numpy as np
sig=np.array([1.0,0.7]); rho=np.array([0.30,0.25]); N=2
xi2=np.sum(rho*sig**2); eta=(np.pi/6)*np.sum(rho*sig**3); D=1-eta
R=np.array([[(sig[a]+sig[b])/2 for b in range(N)] for a in range(N)])
lam=np.array([[(sig[b]-sig[a])/2 for b in range(N)] for a in range(N)])
sq=np.sqrt(np.outer(rho,rho))
def Q0(a,b): return (2*np.pi/D)*(R[a,b]+np.pi*xi2*sig[a]*sig[b]/(4*D))
def Qpp(b):  return (2*np.pi/D)*(1+np.pi*xi2*sig[b]/(2*D))
def q0(a,b,r):
    r=np.asarray(r,float); x=r-R[a,b]
    return np.where((r>=lam[a,b])&(r<=R[a,b]), sq[a,b]*(Q0(a,b)*x+Qpp(b)*x*x/2),0.0)
L=R.max()+0.05; ns=1600001; xs=np.linspace(-L,L,ns); dx=xs[1]-xs[0]
def matDCFre_grid(i,k):
    fwd=q0(i,k,xs); refl=q0(k,i,-xs); corr=np.zeros(ns)
    for m in range(N):
        C=np.fft.irfft(np.fft.rfft(q0(i,m,xs))*np.conj(np.fft.rfft(q0(k,m,xs))),ns)*dx
        corr+=np.fft.fftshift(C)
    return fwd+refl-corr
import sys; sys.path.insert(0,'/home/rpan/YK_tail_FMSA/Lean_code')
from mixdcf_lebowitz_cij import c_upper_coeffs
i,k=1,0  # pair with lower piece; upper piece v in (0.15, 0.85)
# c_upper for pair (1,0): relabel smaller=species1(0.7)=s0, larger=species0(1.0)=s1, r0=rho1=.25,r1=rho0=.30
a,b,c2,e = c_upper_coeffs(0.7,1.0,0.25,0.30)
Rik=R[i,k]
def shell_antideriv(v):  # 2pi * int_v^R s c_upper(s) ds ;  s c_upper = a s + b + c2 s^2 + e s^4
    F=lambda s: a*s**2/2 + b*s + c2*s**3/3 + e*s**5/5
    return 2*np.pi*(F(Rik)-F(v))
Mg=matDCFre_grid(i,k)
print("upper piece: matDCFreCore_ik(v) / rg   vs   2pi int_v^R s c_upper(s) ds :")
for v in [0.25,0.45,0.65,0.80]:
    mval=np.interp(v,xs,Mg)/sq[i,k]
    print(f"  v={v}: matDCFre/rg={mval:+.5f}   2pi-antideriv={shell_antideriv(v):+.5f}   diff={mval-shell_antideriv(v):+.1e}")
# also check boundary matDCFreCore(R)=0
print(f"  matDCFre(R={Rik})/rg =", np.interp(Rik,xs,Mg)/sq[i,k], "(should be ~0)")
