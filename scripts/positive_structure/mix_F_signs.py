import sys, numpy as np
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent)); sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[1]))
import msa_coupling_series_sign_probe as SP
M = SP.M

def p_of(u, st):
    T, N = st.T, st.N; n2 = N*N
    Dt = u[:T*n2].reshape(T, N, N); Gt = u[T*n2:].reshape(T, N, N)
    # reuse the real pieces (complex u allowed through residual_c's formulas)
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
    return dict(A=A, qp=qp, Wt=Wt, Ct=Ct)

def run(name, st, nmax=30):
    tr = M.trace_coupling_mix(st, lam_max=8.0); sc = min(tr[-1][0], 2.0)
    U, _ = SP.series(st, nmax, sc)
    m = 3*nmax+1; w = np.exp(2j*np.pi*np.arange(m)/m)
    us = [sum(U[i]*wk**i for i in range(nmax+1)) for wk in w]
    rr = np.sqrt(np.outer(st.rho, st.rho)); res = []
    for s in (1e-9, 1.0, 1.8, 4.0, 12.0):
        vals = np.array([np.eye(st.N) - rr*M.qhat(st, p_of(u, st), s) for u in us])   # symmetrised F~
        dets = np.array([np.linalg.det(v) for v in vals])
        Fc = np.array([(vals*(w**(-k))[:, None, None]).mean(axis=0).real for k in range(1, nmax+1)])
        dc = np.array([(dets*w**(-k)).mean().real for k in range(1, nmax+1)])
        pats = []
        for i in range(st.N):
            for j in range(st.N):
                c = Fc[:, i, j]; big = np.abs(c) > 1e-10*np.max(np.abs(c)); sg = np.sign(c[big])
                pats.append('-' if np.all(sg < 0) else ('+' if np.all(sg > 0) else '~'))
        big = np.abs(dc) > 1e-10*np.max(np.abs(dc)); sg = np.sign(dc[big])
        res.append(f"s={s:g}: F~ entries[{''.join(pats)}] det[{'-' if np.all(sg<0) else ('+' if np.all(sg>0) else '~')}]")
    print(f"{name}: " + "  ".join(res), flush=True)

eta = lambda e: 6*e/np.pi
s = np.array([1.0, 1.3]); e = np.array([[1.0, .9], [.9, .8]]); SIG = .5*(s[:, None]+s[None, :])
rho = np.array([.5, .5]); rho *= .3/((np.pi/6)*np.sum(rho*s**3))
run("binary Berthelot", M.HCYMix(s, rho, [1.8], (e*SIG)[None]))
run("equal-sigma K12=0.2", M.HCYMix([1.0, 1.0], np.array([.5, .5])*eta(0.3), [1.8], np.array([[1, .2], [.2, 1]])[None]))
run("equal-sigma K12=-0.3", M.HCYMix([1.0, 1.0], np.array([.5, .5])*eta(0.3), [1.8], np.array([[1, -.3], [-.3, 1]])[None]))
run("binary 2 attr tails", M.HCYMix(s, rho, [1.8, 4.0], np.stack([e*SIG, 0.5*e*SIG])))
