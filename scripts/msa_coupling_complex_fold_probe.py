import sys, numpy as np
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent))
from msa_coupling_series_sign_probe import series, residual_c, M
from scipy.linalg import toeplitz

def pade_poles(c, L, Mm):
    # denominator q (q0=1) from c_{L+1..L+M} = -sum q_k c_{L+1-k...}
    A = np.array([[c[L+i-k] if L+i-k >= 0 else 0 for k in range(1, Mm+1)] for i in range(1, Mm+1)])
    q = np.linalg.solve(A, -c[L+1:L+Mm+1])
    return np.roots(np.r_[q[::-1], 1.0])

def jac(u, st):
    n = len(u); J = np.empty((n, n), complex)
    for j in range(n):
        e = np.zeros(n, complex); e[j] = 1
        cd = lambda h: (residual_c(u+h*e, st)[0]-residual_c(u-h*e, st)[0])/(2*h)
        J[:, j] = (4*cd(1e-3)-cd(2e-3))/3
    return J

def refine(st, u, tau, b, it=60):
    v = np.r_[u, tau].astype(complex); n = len(u)
    def F(v):
        u, t = v[:n], v[n]
        return np.r_[residual_c(u, st)[0] - t*b, np.linalg.det(jac(u, st))]
    for _ in range(it):
        f = F(v); Jv = np.empty((n+1, n+1), complex); h = 1e-6
        for j in range(n+1):
            e = np.zeros(n+1, complex); e[j] = h
            Jv[:, j] = (F(v+e)-F(v-e))/(2*h)
        dv = np.linalg.solve(Jv, -f); v = v + dv
        if np.linalg.norm(dv) < 1e-13*(1+np.linalg.norm(v)): break
    return v, np.linalg.norm(F(v))

for e in (0.2, 0.3, 0.4):
    st = M.HCYMix([1.0], [6*e/np.pi], [1.8, 12.0], np.array([1.0, -6.0]).reshape(2, 1, 1))
    SC = 2.0
    U, Ac = series(st, 44, SC)
    U = U*SC**(-np.arange(U.shape[0]))[:, None]          # back to coefficients in tau
    j = int(np.argmax(np.abs(U[-1]*SC**44))); c = U[:, j]*SC**np.arange(U.shape[0])
    for (L, Mm) in ((24, 14), (26, 16), (22, 18)):
        pp = sorted(SC*pade_poles(c, L, Mm), key=abs)[:3]
        print(f"eta={e}: Pade[{L}/{Mm}] nearest poles: {[complex(round(p.real,5), round(p.imag,5)) for p in pp]}", flush=True)
    P1 = SC*pade_poles(c, 24, 14); P2 = SC*pade_poles(c, 22, 18)
    stable = [p for p in P1 if abs(p.imag) > 1e-3 and min(abs(P2-p)) < 0.02*abs(p)]
    poles = sorted(stable, key=abs)
    # seed u at the nearest pole from the series evaluated slightly inside, then refine
    tp = poles[0]; ts = 0.97*tp
    u = sum(U[k]*ts**k for k in range(len(U)))
    b = np.concatenate([(2*np.pi*st.K/st.z[:, None, None]).ravel(), np.zeros(st.T)])
    v, res = refine(st, u, tp, b)
    print(f"   seed {tp:.5f} -> complex fold tau*={v[-1]:.8f} |tau*|={abs(v[-1]):.8f} residual={res:.1e}", flush=True)
    # root test on the scaled coefficients: |c_n|^(-1/n) * SC
    cs = np.abs(U*SC**np.arange(U.shape[0])[:, None]).max(axis=1)
    print("   root test R(n=30,36,40,44):", [round(SC*cs[k]**(-1/k), 4) for k in (30, 36, 40, 44)], flush=True)
