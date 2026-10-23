"""Taylor coefficients of the BH physical branch u(tau), P(u) = tau b, by
u_n = J0^{-1}(b delta_{n1} - [P(U_{n-1})]_n) with exact FFT extraction (P is cubic)."""
import sys, numpy as np
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[3]))
import msa_exact_mix as M

def residual_c(u, st):
    """_residuals without the tau term, complex-capable (same formulas)."""
    N, T = st.N, st.T; n2 = N*N
    Dt = u[:T*n2].reshape(T, N, N); Gt = u[T*n2:].reshape(T, N, N)
    sig, rho, z, SIG, LAM = st.sigma, st.rho, st.z, st.SIG, st.LAM; eye = np.eye(N)
    gam = np.empty((T, N, N), complex); Ct = np.empty_like(gam); Wt = np.empty_like(gam)
    for t in range(T):
        zt = z[t]
        gam[t] = eye - 2*np.pi*rho[None, :]*Gt[t]*np.exp(-zt*SIG)/zt
        Ct[t] = (gam[t]*np.exp(-zt*LAM)) @ Dt[t]
        Wt[t] = (2*np.pi/zt)*((Gt[t]*rho[None, :]) @ Dt[t])
    Mv = np.zeros(N, complex); Nc = np.zeros(N, complex)
    for t in range(T):
        zt = z[t]
        Mv -= (1/zt)*np.einsum('l,lj->j', rho, Wt[t] + (1+zt*sig)[:, None]*Ct[t])
        lam_jl = LAM.T
        Nc += np.einsum('l,lj->j', rho, ((1+zt*lam_jl)/zt**2)*Wt[t]
                        + (((1+zt*sig+0.5*(zt*sig)**2)/zt**2)[:, None] + lam_jl*((1+zt*sig)/zt)[:, None])*Ct[t])
    A = st.A0*(1+Mv) - 4*st.B0*Nc/sig**2
    qp = st.QP0*(1+Mv)[None, :] + st.A0[:, None]*Nc[None, :]
    p = dict(A=A, qp=qp, Wt=Wt, Ct=Ct)
    r1 = np.empty((T, N, N), complex); r2 = np.empty_like(r1)
    for t in range(T):
        zt = z[t]
        Q = M.qhat(st, p, zt)
        Y = np.exp(-zt*LAM.T)*(eye - rho[:, None]*Q.T)
        r1[t] = Dt[t] @ Y
        Z = np.exp(zt*LAM.T)*(eye - rho[:, None]*Q)
        src = A[None, :] + zt*qp
        for m in range(T):
            src = src + (zt**2*z[m]/(zt+z[m]))*Ct[m]
        r2[t] = 2*np.pi*(Gt[t] @ Z) - src/zt**2
    return np.concatenate([r1.ravel(), r2.ravel()]), A

def series(st, nmax, scale):
    """coefficients of u(scale*s) in s; also of A_j."""
    T, N = st.T, st.N; n2 = N*N; n = 2*T*n2
    st0 = M.HCYMix(st.sigma, st.rho, st.z, 0*st.K)
    _, G0 = M.seed_zero_K(st0)
    u0 = np.concatenate([np.zeros(T*n2), G0.ravel()]).astype(complex)
    b = np.concatenate([(2*np.pi*st.K/st.z[:, None, None]).ravel(), np.zeros(T*n2)])*scale
    def cd(e, h):
        return (residual_c(u0 + h*e, st)[0] - residual_c(u0 - h*e, st)[0])/(2*h)
    J0 = np.empty((n, n), complex)
    for j in range(n):
        e = np.zeros(n, complex); e[j] = 1.0
        J0[:, j] = (4*cd(e, 1e-3) - cd(e, 2e-3))/3      # exact for a cubic
    U = [u0]; Acoef = None
    for k in range(1, nmax+1):
        m = 3*k + 1; w = np.exp(2j*np.pi*np.arange(m)/m)
        vals = np.array([residual_c(sum(U[i]*wk**i for i in range(k)), st)[0] for wk in w])
        ck = (vals*(w**(-k))[:, None]).mean(axis=0)
        rhs = (b if k == 1 else 0) - ck
        U.append(np.linalg.solve(J0, rhs))
    U = np.array(U).real
    m = 3*nmax+1; w = np.exp(2j*np.pi*np.arange(m)/m)
    Avals = np.array([residual_c(sum(U[i]*wk**i for i in range(nmax+1)), st)[1] for wk in w])
    Ac = np.array([(Avals*(w**(-k))[:, None]).mean(axis=0).real for k in range(nmax+1)])
    return U, Ac

def report(name, st, nmax=40, scale=None):
    tr = M.trace_coupling_mix(st, lam_max=8.0); lend = tr[-1][0]
    fold = lend < 8.0 - 1e-9
    sc = lend if scale is None else scale
    U, Ac = series(st, nmax, sc)
    allc = np.concatenate([U, Ac], axis=1)[1:]          # orders 1..nmax in s = tau/sc
    last_flip = []
    for c in range(allc.shape[1]):
        col = allc[:, c]
        if np.max(np.abs(col)) < 1e-14: continue
        s = np.sign(col)
        flips = [i+2 for i in range(len(s)-1) if s[i] != s[i+1] and abs(col[i+1]) > 1e-12*np.max(np.abs(col))]
        last_flip.append(flips[-1] if flips else 0)
    # Domb-Sykes on the largest component: c_{n}/c_{n-1} = (1/R)(1 - (1+g)/n), extrapolate in 1/n
    j = int(np.argmax(np.abs(allc[-1]))); col = allc[:, j]; n = np.arange(1, nmax+1)
    r = col[1:]/col[:-1]; x = 1/n[1:]
    a, b0 = np.polyfit(x[-12:], r[-12:], 1)
    print(f"{name}: {'fold' if fold else 'no fold<=8'} tau_end={lend:.6f} scale={sc:.4f} "
          f"components={len(last_flip)} last sign flip order: max={max(last_flip)} "
          f"(n with flips: {sum(1 for f in last_flip if f)})  DombSykes R/scale={1/b0:.5f} exponent g={-a/b0-1:.3f}", flush=True)
    return allc

if __name__ == "__main__":
    eta = lambda e: 6*e/np.pi
    report("1 tail z=1.8 eta=0.2", M.HCYMix([1.0], [eta(0.2)], [1.8], [[[1.0]]]))
    report("2 attractive z=(1.8,4) K=(1,.5) eta=0.3", M.HCYMix([1.0], [eta(0.3)], [1.8, 4.0], np.array([1.0, .5]).reshape(2,1,1)))
    report("2 attractive z=(1.8,.8) K=(1,.3) eta=0.3", M.HCYMix([1.0], [eta(0.3)], [1.8, 0.8], np.array([1.0, .3]).reshape(2,1,1)))
    report("2YK eta=0.25", M.HCYMix([1.0], [eta(0.25)], [2.9637, 14.0167], np.array([2.1714, -2.1714]).reshape(2,1,1)))
    report("F5 z=(1.8,12) w=(1,-6) eta=0.3", M.HCYMix([1.0], [eta(0.3)], [1.8, 12.0], np.array([1.0, -6.0]).reshape(2,1,1)), scale=2.0)
    s = np.array([1.0, 1.3]); e = np.array([[1.0, .9], [.9, .8]]); SIG = .5*(s[:, None]+s[None, :])
    rho = np.array([.5, .5]); rho *= .3/((np.pi/6)*np.sum(rho*s**3))
    report("binary Berthelot eta=0.3", M.HCYMix(s, rho, [1.8], (e*SIG)[None]))
    report("binary equal-sigma K12=0.2", M.HCYMix([1.0, 1.0], np.array([.5, .5])*eta(0.3), [1.8], np.array([[1, .2], [.2, 1]])[None]))
    report("binary K12=-0.3 (repulsive cross)", M.HCYMix([1.0, 1.0], np.array([.5, .5])*eta(0.3), [1.8], np.array([[1, -.3], [-.3, 1]])[None]))
