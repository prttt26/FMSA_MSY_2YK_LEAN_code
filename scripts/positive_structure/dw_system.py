"""N = 1, T tails, sigma = 1.  The BH system in X = (D_mu, W_mu):
     D_nu = tau k_nu / f_nu(X),  W_nu = tau kap_nu S_nu(X) / f_nu(X)^2
with f_nu = 1 - rho Qhat(z_nu), S_nu = A + z_nu q' + sum_mu z_nu^2 z_mu/(z_nu+z_mu) Ct_mu, both affine in X."""
import sys, numpy as np
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[4]))
import msa_exact_mix as Mx

def affine(st):
    T = st.T; z = st.z; rho = float(st.rho[0]); e = np.exp(-z)
    def fS(D, W):
        Ct = D - e*W
        M = -np.sum((rho/z)*(W + (1+z)*Ct))
        Nc = np.sum(rho*(W/z**2 + ((1+z+z**2/2)/z**2)*Ct))
        A = st.A0[0]*(1+M) - 4*st.B0[0]*Nc
        qp = st.QP0[0, 0]*(1+M) + st.A0[0]*Nc
        p = dict(A=np.array([A]), qp=np.array([[qp]]), Wt=W.reshape(T, 1, 1), Ct=Ct.reshape(T, 1, 1))
        f = np.array([1 - rho*Mx.qhat(st, p, zn)[0, 0].real for zn in z])
        S = np.array([A + zn*qp + np.sum(zn**2*z/(zn+z)*Ct) for zn in z])
        return f, S
    f0, S0 = fS(np.zeros(T), np.zeros(T))
    dfD = np.empty((T, T)); dfW = np.empty((T, T)); dSD = np.empty((T, T)); dSW = np.empty((T, T))
    for m in range(T):
        u = np.zeros(T); u[m] = 1.0
        f1, S1 = fS(u, np.zeros(T)); dfD[:, m] = f1-f0; dSD[:, m] = S1-S0
        f1, S1 = fS(np.zeros(T), u); dfW[:, m] = f1-f0; dSW[:, m] = S1-S0
    return f0, S0, dfD, dfW, dSD, dSW

def series(st, nmax, scale):
    """Taylor coefficients of D, W by the fixed point X = tau R(X) (power series arithmetic)."""
    T = st.T; z = st.z; rho = float(st.rho[0])
    K = st.K[:, 0, 0]; k = 2*np.pi*K/z; kap = rho*k/z**3
    f0, S0, dfD, dfW, dSD, dSW = affine(st)
    D = np.zeros((nmax+1, T)); W = np.zeros((nmax+1, T))
    def mul(a, b): return np.array([sum(a[i]*b[n-i] for i in range(n+1)) for n in range(len(a))])
    for it in range(nmax+1):
        f = D@dfD.T + W@dfW.T; f[0] += f0      # series in tau (rows = orders)
        S = D@dSD.T + W@dSW.T; S[0] += S0
        inv = np.zeros_like(f)
        for t in range(T):  # series reciprocal
            inv[0, t] = 1/f[0, t]
            for n in range(1, nmax+1):
                inv[n, t] = -sum(f[i, t]*inv[n-i, t] for i in range(1, n+1))/f[0, t]
        inv2 = np.array([mul(inv[:, t], inv[:, t]) for t in range(T)]).T
        Dn = np.zeros_like(D); Wn = np.zeros_like(W)
        Dn[1:] = (k*inv[:-1])*scale
        SW = np.array([mul(S[:, t], inv2[:, t]) for t in range(T)]).T
        Wn[1:] = (kap*SW[:-1])*scale
        D, W = Dn, Wn
    return D, W, (f0, S0, dfD, dfW, dSD, dSW)

if __name__ == "__main__":
    eta = lambda e: 6*e/np.pi
    for name, st in (("1 tail z=1.8 eta=0.2", Mx.HCYMix([1.0], [eta(0.2)], [1.8], [[[1.0]]])),
                     ("2 attr z=(1.8,4) eta=0.3", Mx.HCYMix([1.0], [eta(0.3)], [1.8, 4.0], np.array([1.0, .5]).reshape(2, 1, 1))),
                     ("2 attr z=(1.8,.8) eta=0.3", Mx.HCYMix([1.0], [eta(0.3)], [1.8, 0.8], np.array([1.0, .3]).reshape(2, 1, 1))),
                     ("2YK eta=0.25", Mx.HCYMix([1.0], [eta(0.25)], [2.9637, 14.0167], np.array([2.1714, -2.1714]).reshape(2, 1, 1))),
                     ("F5 eta=0.3", Mx.HCYMix([1.0], [eta(0.3)], [1.8, 12.0], np.array([1.0, -6.0]).reshape(2, 1, 1)))):
        f0, S0, dfD, dfW, dSD, dSW = affine(st)
        print(f"{name}: f0={f0.round(4)} S0={S0.round(4)}\n  -df/dD={(-dfD).round(5).tolist()} -df/dW={(-dfW).round(5).tolist()}\n  dS/dD={dSD.round(5).tolist()} dS/dW={dSW.round(5).tolist()}")
        # cross-check against the BH solution at a small tau via the traced branch
        tr = Mx.trace_coupling_mix(st, lam_max=0.3); l, s = tr[-1]
        D, W, _ = series(st, 30, 1.0)
        Dsum = sum(D[n]*l**n for n in range(31)); Wsum = sum(W[n]*l**n for n in range(31))
        Wbh = (2*np.pi/st.z)*float(st.rho[0])*s.Gt[:, 0, 0]*s.Dt[:, 0, 0]
        print(f"  check at tau={l:.3f}: |D-D_BH|={np.max(np.abs(Dsum-s.Dt[:,0,0])):.1e} |W-W_BH|={np.max(np.abs(Wsum-Wbh)):.1e}", flush=True)
