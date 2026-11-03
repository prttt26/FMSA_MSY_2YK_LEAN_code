"""Explicit rational parametrization of the multi-tail MSA branch, pure fluid (EXTERNAL multiprecision evidence, NOT a Lean proof).

F(x) = P(x) + e^(-x) Shat(x), with P and Shat = rho S(x)/x rational. With Lambda_t = rho tau_t/F_t^2 (tau_t the right side of D_t F_t = tau_t):
    Shat(x) = a/x^3 + q/x^2 + c/x - sum_t Lambda_t P_t/(x + z_t),
    P(x) = 1 - a/x^3 + (a - q)/x^2 + (q - a/2 - c)/x - sum_t Lambda_t Shat_t/(x + z_t),
    c = sum_t Lambda_t P_t,   a = a0 (1 + Mv) + b4 Nc,   q = q0 (1 + Mv) + a0 Nc,
    Mv = -sum_t Lambda_t (Shat_t + (1 + z_t) P_t)/z_t,   Nc = sum_t Lambda_t (Shat_t + (1 + z_t + z_t^2/2) P_t)/z_t^2.
This is linear in (P_t, Shat_t, a, q, c) for given Lambda, so the branch is tau_t = Lambda_t F_t(Lambda)^2/rho, D_t = Lambda_t F_t/rho, G_s = z_s Shat_s/(2 pi rho F_s).
Lagrange: if rho/F_t^2 has nonnegative Taylor coefficients in Lambda, so has Lambda(tau), and so has 1/F_t(Lambda(tau)). The script
  * checks the parametrization against the residual of the BH system (attractive_tie_limit.Affine);
  * reads the signs of the Taylor coefficients in Lambda of F0 - F, of 1/F^2, of G - G0, of a, q, c, in multiprecision.

Usage: lambda_parametrization.py --check | --signs S --order N --T T [--seed S] [--workers W]
"""
import sys, itertools
import numpy as np
import mpmath as mp
from multiprocessing import Pool
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_Convergence/scripts/two_tail')


def constants(eta):
    a0 = 12*eta*(1 + 2*eta)/(1 - eta)**2; q0 = 12*eta*(1 + eta/2)/(1 - eta)**2; b4 = 72*eta*eta/(1 - eta)**2
    return a0, q0, b4


def system(z, eta):
    """M0 X + sum_t Lambda_t M_t X = X0, X = (P_1..T, Shat_1..T, a, q, c)."""
    T = len(z); n = 2*T + 3; ia, iq, ic = 2*T, 2*T + 1, 2*T + 2
    a0, q0, b4 = constants(eta)
    M0 = mp.zeros(n, n); Mt = [mp.zeros(n, n) for _ in range(T)]; X0 = mp.zeros(n, 1)
    for s in range(T):
        x = z[s]
        M0[s, s] = 1; M0[s, ia] = 1/x**3 - 1/x**2 + 1/(2*x); M0[s, iq] = 1/x**2 - 1/x; M0[s, ic] = 1/x; X0[s] = 1
        M0[T + s, T + s] = 1; M0[T + s, ia] = -1/x**3; M0[T + s, iq] = -1/x**2; M0[T + s, ic] = -1/x
        for t in range(T):
            Mt[t][s, T + t] += 1/(x + z[t]); Mt[t][T + s, t] += 1/(x + z[t])
    M0[ia, ia] = 1; M0[iq, iq] = 1; M0[ic, ic] = 1; X0[ia] = a0; X0[iq] = q0
    for t in range(T):
        zt = z[t]; Mt[t][ic, t] += -1
        mvS, mvP = -1/zt, -(1 + zt)/zt; ncS, ncP = 1/zt**2, (1 + zt + zt*zt/2)/zt**2
        Mt[t][ia, T + t] += -(a0*mvS + b4*ncS); Mt[t][ia, t] += -(a0*mvP + b4*ncP)
        Mt[t][iq, T + t] += -(q0*mvS + a0*ncS); Mt[t][iq, t] += -(q0*mvP + a0*ncP)
    return M0, Mt, X0


def solve_at(z, eta, Lam):
    M0, Mt, X0 = system(z, eta); M = M0.copy()
    for t, l in enumerate(Lam): M = M + l*Mt[t]
    return mp.lu_solve(M, X0)


def check():
    import attractive_tie_limit as L
    for z, eta, Lam in [([1.8], .3, [.05]), ([1, 10], .3, [.02, .3]), ([1.0722, 56.33], .5, [1e-3, 2.0]), ([.7, 3.0, 40.0], .4, [.05, .05, .5])]:
        zm = [mp.mpf(v) for v in z]; e = mp.mpf(eta); X = solve_at(zm, e, [mp.mpf(v) for v in Lam]); T = len(z); rho = 6*e/mp.pi
        F = [X[s] + mp.exp(-zm[s])*X[T + s] for s in range(T)]; S = [zm[s]*X[T + s]/rho for s in range(T)]
        tau = [Lam[t]*F[t]**2/rho for t in range(T)]; D = [Lam[t]*F[t]/rho for t in range(T)]; G = [S[s]/(2*mp.pi*F[s]) for s in range(T)]
        f = L.Affine(np.array(z, float), float(eta))
        Fa, Sa = f.fs(np.r_[[float(d) for d in D], [float(d*g) for d, g in zip(D, G)]])
        print(f'z={z} eta={eta} Lambda={Lam}: tau {[mp.nstr(v, 8) for v in tau]}; F from Lambda {[mp.nstr(v, 12) for v in F]}, F from the affine BH factors {np.array2string(Fa, precision=12)}; S from Lambda {[mp.nstr(v, 12) for v in S]}, affine {np.array2string(Sa, precision=12)}', flush=True)


def series(z, eta, N):
    T = len(z); M0, Mt, X0 = system(z, eta); n = M0.rows; Mi = M0**-1
    X = {tuple([0]*T): Mi*X0}
    for d in range(1, N + 1):
        for al in itertools.product(range(d + 1), repeat=T):
            if sum(al) != d: continue
            r = mp.zeros(n, 1)
            for t in range(T):
                if al[t]:
                    b = tuple(v - (1 if i == t else 0) for i, v in enumerate(al))
                    r = r - Mt[t]*X[b]
            X[al] = Mi*r
    return X


def mul(a, b, N):
    out = {}
    for x, u in a.items():
        for y, v in b.items():
            k = tuple(i + j for i, j in zip(x, y))
            if sum(k) <= N: out[k] = out.get(k, mp.mpf(0)) + u*v
    return out


def inv(a, N, T):
    O = tuple([0]*T); out = {O: 1/a[O]}
    for d in range(1, N + 1):
        for al in itertools.product(range(d + 1), repeat=T):
            if sum(al) != d: continue
            s = mp.mpf(0)
            for b, v in a.items():
                if sum(b) == 0: continue
                g = tuple(i - j for i, j in zip(al, b))
                if min(g) >= 0: s += v*out[g]
            out[al] = -s/a[O]
    return out


def read(z, eta, N):
    T = len(z); X = series(z, eta, N); rho = 6*eta/mp.pi; res = {}
    def tally(name, p, sg):
        neg = tot = 0; first = None
        for k, v in p.items():
            if sum(k) == 0 or v == 0: continue
            tot += 1
            if sg*v < 0:
                neg += 1
                if first is None or sum(k) < sum(first): first = k
        r = res.setdefault(name, [0, 0, None]); r[0] += neg; r[1] += tot
        if first is not None and (r[2] is None or sum(first) < sum(r[2])): r[2] = first
    for s in range(T):
        F = {k: X[k][s] + mp.exp(-z[s])*X[k][T + s] for k in X}; Sh = {k: X[k][T + s] for k in X}
        iF = inv(F, N, T); iF2 = mul(iF, iF, N); G = mul({k: z[s]*v/(2*mp.pi*rho) for k, v in Sh.items()}, iF, N)
        tally('F0-F', F, -1); tally('1/F', iF, 1); tally('1/F^2', iF2, 1); tally('G-G0', G, 1); tally('P', {k: X[k][s] for k in X}, -1); tally('Shat', Sh, 1)
    ia, iq, ic = 2*T, 2*T + 1, 2*T + 2
    tally('a', {k: X[k][ia] for k in X}, 1); tally('q', {k: X[k][iq] for k in X}, 1); tally('c', {k: X[k][ic] for k in X}, 1)
    return res


def run(job):
    i, seed, N, T = job; rng = np.random.default_rng([seed, i])
    if i % 3 == 0:
        zw = float(np.exp(rng.uniform(np.log(.3), np.log(5)))); zz = [zw] + [zw*float(np.exp(rng.uniform(np.log(10), np.log(300)))) for _ in range(T - 1)]
    elif i % 3 == 1:
        z0 = float(np.exp(rng.uniform(np.log(.2), np.log(30)))); zz = [z0*float(np.exp(rng.uniform(0, .2))) for _ in range(T)]
    else:
        zz = np.exp(rng.uniform(np.log(.1), np.log(300), T)).tolist()
    e = float(rng.uniform(.005, .79)); mp.mp.dps = 80
    return zz, e, read([mp.mpf(v) for v in zz], mp.mpf(e), N)


if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(EXTERNAL multiprecision evidence, NOT a Lean proof)', flush=True)
    mp.mp.dps = 80
    val = lambda f, d: type(d)(sys.argv[sys.argv.index(f) + 1]) if f in sys.argv else d
    if '--check' in sys.argv: check()
    if '--signs' in sys.argv:
        S, N, T, seed, W = val('--signs', 30), val('--order', 12), val('--T', 2), val('--seed', 1), val('--workers', 8)
        with Pool(W) as ex: res = ex.map(run, [(i, seed, N, T) for i in range(S)], chunksize=1)
        tot = {}
        for z, e, r in res:
            for k, v in r.items():
                a = tot.setdefault(k, [0, 0, 0, None]); a[0] += v[0]; a[1] += v[1]; a[2] += v[0] > 0
                if v[2] is not None and (a[3] is None or sum(v[2]) < sum(a[3])): a[3] = v[2]
        print(f'== {S} states, T={T}, order {N}, Taylor coefficients in Lambda: (negative monomials, total, states with any, lowest monomial)', flush=True)
        for k, v in tot.items(): print(f'   {k}: {v}', flush=True)
        for z, e, r in res[:6]:
            print(f'   z={np.round(z, 4).tolist()} eta={e:.4f}: ' + ', '.join(f'{k} {v[0]}/{v[1]}' for k, v in r.items()), flush=True)
