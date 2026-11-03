"""Taylor series of an all-attractive pure fluid, certified independently of root tracking
(EXTERNAL multiprecision arithmetic, NOT a Lean proof).

Takes (z1, z2, w = K2/K1, eta) and computes the coefficients c_n of u(tau) = (D1, D2, G1, G2) with
mpmath, from a port of the residual that does not call the float code: the residual is cubic in
u, so with v = u - u0 it is R0 + L v + Q[v,v] + C[v,v,v], and the tensors come from exact
polarisation. The series recursion is then an exact Cauchy recursion.

Nothing here follows a root path, so these checks are independent of the Newton and tracer runs:
  * every sign change of every component;
  * the singularity read off the coefficients alone: linear prediction on n^{3/2} c_n
    (c_n ~ A n^{-3/2} rho^{-n} cos(n theta + phi) gives a two-term recurrence with roots
    exp(+-i theta)/rho), and the plain root test;
  * partial sums at real tau on both sides of the predicted radius. Partial sums blowing up at
    real tau < tau_f, where the real branch still exists, is the failure itself.
Two precisions must agree.

Usage: attractive_pair_series_mp.py z1 z2 w eta N dps [tau_test ...]   (tau in units K1 = 1)
"""
import sys
import numpy as np
import mpmath as mp


def pure_state(z, K, eta):
    """N = 1, sigma = 1: the BH constants of the hard-sphere reference, in exact form."""
    eta = mp.mpf(eta); rho = 6*eta/mp.pi
    d = 2*mp.pi/(1 - eta)**2
    xi2 = eta
    return dict(T=len(z), z=[mp.mpf(v) for v in z], K=[mp.mpf(v) for v in K], rho=rho,
                A0=d*((1 - eta) + 3*xi2), B0=d*(-mp.mpf(3)/2*xi2), QP0=d*(mp.mpf(3)/2*xi2 + (1 - eta)))


def phi1(x): return (1 - x - mp.exp(-x))/x**2
def phi2(x): return (1 - x + x*x/2 - mp.exp(-x))/x**3
def exprel(x): return (1 - mp.exp(-x))/x


def residual(u, st):
    """Blum-Hoye residual without the tau term, N = 1. u = (D_t, G_t)."""
    T, z, rho = st['T'], st['z'], st['rho']
    D, G = u[:T], u[T:]
    Ct = [(1 - 2*mp.pi*rho*G[t]*mp.exp(-z[t])/z[t])*D[t] for t in range(T)]
    Wt = [(2*mp.pi/z[t])*G[t]*rho*D[t] for t in range(T)]
    Mv = -sum(rho*(Wt[t] + (1 + z[t])*Ct[t])/z[t] for t in range(T))
    Nc = sum(rho*(Wt[t]/z[t]**2 + (1 + z[t] + z[t]**2/2)/z[t]**2*Ct[t]) for t in range(T))
    A = st['A0']*(1 + Mv) - 4*st['B0']*Nc
    qp = st['QP0']*(1 + Mv) + st['A0']*Nc
    r1, r2 = [], []
    for t in range(T):
        x = z[t]
        Q = phi1(x)*qp + phi2(x)*A + sum(Wt[m]/(x + z[m]) + Ct[m]*(mp.exp(-x)/(x + z[m]) + exprel(x)) for m in range(T))
        F = 1 - rho*Q
        src = A + x*qp + sum((x**2*z[m]/(x + z[m]))*Ct[m] for m in range(T))
        r1.append(D[t]*F)
        r2.append(2*mp.pi*G[t]*F - src/x**2)
    return r1 + r2


def seed(n, st, res=residual):
    """D = 0 makes the second block linear in G. n is the length of u."""
    m = n//2
    zero = [mp.mpf(0)]*n
    r0 = res(zero, st)
    LG = mp.matrix(m, m)
    for k in range(m):
        e = list(zero); e[m + k] = mp.mpf(1)
        rk = res(e, st)
        for i in range(m): LG[i, k] = rk[m + i] - r0[m + i]
    g = mp.lu_solve(LG, mp.matrix([-r0[m + i] for i in range(m)]))
    return [mp.mpf(0)]*m + [g[i] for i in range(m)]


class Cubic:
    """R(u0 + v) as an explicit cubic, assembled from values on a finite-difference stencil."""
    def __init__(self, st, u0, res=residual):
        self.n = n = len(u0); self.st = st; self.u0 = u0
        def R(v): return res([u0[i] + v[i] for i in range(n)], st)
        def e(*ks):
            v = [mp.mpf(0)]*n
            for k, a in ks: v[k] += a
            return v
        R0 = R(e()); self.R0 = R0
        one = mp.mpf(1)
        self.L = [[mp.mpf(0)]*n for _ in range(n)]
        self.Q = [[[mp.mpf(0)]*n for _ in range(n)] for _ in range(n)]         # symmetric, Q[v,v] = sum Q_ijk v_j v_k
        self.C = [[[[mp.mpf(0)]*n for _ in range(n)] for _ in range(n)] for _ in range(n)]  # symmetric
        P1 = [R(e((k, one))) for k in range(n)]; M1 = [R(e((k, -one))) for k in range(n)]; P2 = [R(e((k, 2*one))) for k in range(n)]
        for k in range(n):
            for i in range(n):
                self.Q[i][k][k] = (P1[k][i] + M1[k][i] - 2*R0[i])/2
                ckkk = (P2[k][i] - 2*P1[k][i] + 2*M1[k][i] - R(e((k, -2*one)))[i])/12
                self.C[i][k][k][k] = ckkk
                self.L[i][k] = (P1[k][i] - M1[k][i])/2 - ckkk
        # mixed second and third derivatives: inclusion-exclusion on the pure parts, exact for a cubic
        for j in range(n):
            for k in range(j + 1, n):
                Rpp = R(e((j, one), (k, one))); Rmm = R(e((j, -one), (k, -one)))
                Rpm = R(e((j, one), (k, -one)))
                for i in range(n):
                    # f(+,+) + f(-,-) - 2 f0 = 2 (Qjj + Qkk + 2 Qjk)
                    qjk = ((Rpp[i] + Rmm[i] - 2*R0[i])/2 - self.Q[i][j][j] - self.Q[i][k][k])/2
                    self.Q[i][j][k] = self.Q[i][k][j] = qjk
                    # f(+,+) - f(-,-) = 2 (Lj + Lk + Cjjj + Ckkk + 3 Cjjk + 3 Cjkk)
                    # f(+,-) - f(-,+) = 2 (Lj - Lk + Cjjj - Ckkk - 3 Cjjk + 3 Cjkk)
                    Rmp = R(e((j, -one), (k, one)))
                    a = (Rpp[i] - Rmm[i])/2 - self.L[i][j] - self.L[i][k] - self.C[i][j][j][j] - self.C[i][k][k][k]   # 3 Cjjk + 3 Cjkk
                    b = (Rpm[i] - Rmp[i])/2 - self.L[i][j] + self.L[i][k] - self.C[i][j][j][j] + self.C[i][k][k][k]   # -3 Cjjk + 3 Cjkk
                    cjkk = (a + b)/6; cjjk = (a - b)/6
                    for s in ((j, j, k), (j, k, j), (k, j, j)): self.C[i][s[0]][s[1]][s[2]] = cjjk
                    for s in ((j, k, k), (k, j, k), (k, k, j)): self.C[i][s[0]][s[1]][s[2]] = cjkk
        for j in range(n):
            for k in range(j + 1, n):
                for l in range(k + 1, n):
                    Rppp = R(e((j, one), (k, one), (l, one))); Rmmm = R(e((j, -one), (k, -one), (l, -one)))
                    for i in range(n):
                        # odd part along (1,1,1) = L sum + all cubic terms with multiplicity
                        t = (Rppp[i] - Rmmm[i])/2 - self.L[i][j] - self.L[i][k] - self.L[i][l]
                        for a, b, c, mult in ((j, j, j, 1), (k, k, k, 1), (l, l, l, 1), (j, j, k, 3), (j, k, k, 3),
                                              (j, j, l, 3), (j, l, l, 3), (k, k, l, 3), (k, l, l, 3)):
                            t -= mult*self.C[i][a][b][c]
                        val = t/6
                        for s in ((j, k, l), (j, l, k), (k, j, l), (k, l, j), (l, j, k), (l, k, j)):
                            self.C[i][s[0]][s[1]][s[2]] = val

    def __call__(self, v):
        n = self.n; out = []
        for i in range(n):
            s = self.R0[i]
            for j in range(n):
                s += self.L[i][j]*v[j]
                for k in range(n):
                    s += self.Q[i][j][k]*v[j]*v[k]
                    for l in range(n):
                        s += self.C[i][j][k][l]*v[j]*v[k]*v[l]
            out.append(s)
        return out


def coefficients(st, N, res=residual, b=None):
    """c[1..N] of v(tau), R(u0 + v) = tau b, by the exact Cauchy recursion."""
    if b is None:
        T = st['T']; b = [2*mp.pi*st['K'][t]/st['z'][t] for t in range(T)] + [mp.mpf(0)]*T
    u0 = seed(len(b), st, res); cub = Cubic(st, u0, res); n = cub.n
    # the polynomial must reproduce the residual away from the stencil
    test = [mp.mpf(1)/(3 + i) - mp.mpf(1)/7 for i in range(n)]
    ex = res([u0[i] + test[i] for i in range(n)], st); ap = cub(test)
    defect = max(abs(ex[i] - ap[i]) for i in range(n))
    L = mp.matrix(cub.L)
    Lfac = mp.inverse(L)
    Qf = [[[cub.Q[i][j][k] for k in range(n)] for j in range(n)] for i in range(n)]
    c = [None, [sum(Lfac[i, k]*b[k] for k in range(n)) for i in range(n)]]
    W = [None, None]    # W[m][j][k] = sum_{a+b=m} c_a[j] c_b[k]
    for m in range(2, N + 1):
        # order m needs W[m-1] for the cubic term; W[m] is the quadratic convolution at m
        Wm = [[sum(c[a][j]*c[m - a][k] for a in range(1, m)) for k in range(n)] for j in range(n)]
        W.append(Wm)
        rhs = []
        for i in range(n):
            s = mp.mpf(0)
            for j in range(n):
                for k in range(n):
                    s += Qf[i][j][k]*Wm[j][k]
                    for l in range(n):
                        cc = cub.C[i][j][k][l]
                        if cc != 0:
                            s += cc*sum(c[a][j]*W[m - a][k][l] for a in range(1, m - 1))
            rhs.append(-s)
        c.append([sum(Lfac[i, k]*rhs[k] for k in range(n)) for i in range(n)])
    return u0, c, defect


def linear_prediction(seq, nmin, nmax):
    """Least-squares two-term recurrence for n^{3/2} c_n on orders [nmin, nmax]; returns tau* = r e^{i th}."""
    a = [[], []]; y = []
    for m in range(nmin + 2, nmax + 1):
        f = lambda q: mp.mpf(q)**mp.mpf('1.5')*seq[q]
        a[0].append(f(m - 1)); a[1].append(f(m - 2)); y.append(f(m))
    A = mp.matrix([[a[0][i], a[1][i]] for i in range(len(y))]); Y = mp.matrix(y)
    sol = mp.lu_solve(A.T*A, A.T*Y)
    p, q = sol[0], sol[1]                                     # x^2 = p x + q, roots x = 1/tau*
    disc = mp.mpc(p*p + 4*q)
    x1 = (p + mp.sqrt(disc))/2
    return 1/x1


def main(argv):
    z1, z2, w, eta, N, dps = argv[0], argv[1], argv[2], argv[3], int(argv[4]), [int(d) for d in argv[5].split(',')]
    tests = [mp.mpf(t) for t in argv[6:]]
    print('cmd:', ' '.join(sys.argv), '(EXTERNAL multiprecision arithmetic, NOT a Lean proof)', flush=True)
    results = {}
    for d in dps:
        mp.mp.dps = d
        st = pure_state([mp.mpf(z1), mp.mpf(z2)], [1, mp.mpf(w)], mp.mpf(eta))
        u0, c, defect = coefficients(st, N)
        results[d] = c
        print(f'== mp.dps={d}: cubic reproduction defect {mp.nstr(defect, 3)}; seed G=({mp.nstr(u0[2], 12)},{mp.nstr(u0[3], 12)})', flush=True)
        names = ['D1', 'D2', 'G1', 'G2']
        for i, nm in enumerate(names):
            flips = [m for m in range(2, N + 1) if (c[m][i] > 0) != (c[m - 1][i] > 0)]
            print(f'  {nm}: c1={mp.nstr(c[1][i], 8)} c2={mp.nstr(c[2][i], 8)}; {len(flips)} sign changes at orders {flips[:30]}', flush=True)
            rt = abs(c[N][i])**(-mp.mpf(1)/N)
            print(f'    root test at N: {mp.nstr(rt, 8)}; smallest over last 20 orders: {mp.nstr(min(abs(c[m][i])**(-mp.mpf(1)/m) for m in range(N-20, N+1)), 8)}', flush=True)
            if N >= 60:
                for nmin in (N//2, 3*N//4):
                    t = linear_prediction([None] + [c[m][i] for m in range(1, N + 1)], nmin, N)
                    print(f'    linear prediction on [{nmin},{N}]: tau* = {mp.nstr(t.real, 10)} +- {mp.nstr(abs(t.imag), 10)}i, |tau*| = {mp.nstr(abs(t), 10)}', flush=True)
        for t in tests:
            line = f'  partial sums at tau={mp.nstr(t, 8)} of G2 - G2(0):'
            s = mp.mpf(0); out = []
            for m in range(1, N + 1):
                s += c[m][3]*t**m
                if m in (N//4, N//2, 3*N//4, N): out.append(f' S_{m}={mp.nstr(s, 6)}')
            print(line + ''.join(out), flush=True)
    if len(dps) > 1:
        a, b = results[dps[0]], results[dps[-1]]
        mp.mp.dps = dps[0]
        dmax = max(abs(a[m][i] - b[m][i])/abs(b[m][i]) for m in range(1, N + 1) for i in range(4))
        print(f'largest relative difference between the two precisions: {mp.nstr(dmax, 3)}', flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
