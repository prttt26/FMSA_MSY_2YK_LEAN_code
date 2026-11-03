"""Chandrasekhar H-function form of the pure multi-tail MSA branch: every step of the positivity argument, checked at high precision
(EXTERNAL multiprecision evidence, NOT a Lean proof).

Given theta_t >= 0, with C_st = 1/(z_s + z_t):
    w_s U_s = theta_s,   U(x) = 1 - sum_t w_t/(x + z_t),   U_s = U(z_s),                      [H(x) = 1/U(x) is Chandrasekhar's H-function]
    r_s - sum_t w_t (r_s - r_t)/(z_s + z_t) = sum_t w_t z_t/(z_s + z_t),                       [linear in r]
    kappa_s = (1 - omega_s)/z_s,  omega_s = e^(-z_s) F0(-z_s)/F0(z_s),
    rho D_s = F0_s w_s (1 - kappa_s r_s),   F_s = F0_s U_s (1 - kappa_s r_s),
    rho tau_s = F0_s^2 theta_s (1 - kappa_s r_s)^2,   2 pi rho F0_s^2 (G_s - G0_s) = r_s/(1 - kappa_s r_s).
Checks:
 1. REPRESENTATION: these D, G satisfy the BH system through the exact factors of the frozen probe's formulas, D_s F_s(D, DG) = tau_s, 2 pi G_s F_s(D, DG) = S_s(D, DG), T = 1...5.
 2. INTEGRALS: with theta(k) = sum_t 2 z_t theta_t/(z_t^2 + k^2),  U(x)U(-x) = 1 - theta(k) at x = ik, and
       r(x) = (1/pi) int_0^inf k^2/(x^2 + k^2) (1/(1 - theta(k)) - 1) dk,   -ln U(x) = (x/pi) int_0^inf -ln(1 - theta(k))/(x^2 + k^2) dk.
 3. SIGNS: Taylor coefficients in theta of r_s and of 1/U_s, and in tau of D, G - G0 from the Picard iteration, compared with the independent recursion of multivariate_sign_mp.
 4. KAPPA: F0(z) - e^(-z) F0(-z) = (1 - e^-z) + A (z (1 + e^-z) - 2 (1 - e^-z))/z^2, A = 6 eta/(1 - eta), and F0 > 1 for real argument.

Usage: h_function_representation.py --check [--seed S]
"""
import sys, itertools
import numpy as np
import mpmath as mp
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_Convergence/scripts/two_tail')
import shifted_affine_closed_form as CF
import multivariate_sign_mp as MS
mp.mp.dps = 60


def F0fun(x, eta):
    rho = 6*eta/mp.pi; d = 2*mp.pi/(1 - eta)**2
    A0, QP0 = d*((1 - eta) + 3*eta), d*(mp.mpf(3)/2*eta + (1 - eta))
    phi1 = (1 - x - mp.exp(-x))/x**2; phi2 = (1 - x + x*x/2 - mp.exp(-x))/x**3
    return 1 - rho*(phi1*QP0 + phi2*A0)


def S0fun(x, eta):
    d = 2*mp.pi/(1 - eta)**2
    return (d*((1 - eta) + 3*eta) + x*d*(mp.mpf(3)/2*eta + (1 - eta)))/x**2


def H_solve(z, theta):
    """w from w_s (1 - (C w)_s) = theta_s, the branch with w -> 0."""
    T = len(z); w = list(theta)
    for _ in range(4000):
        new = [theta[s]/(1 - sum(w[t]/(z[s] + z[t]) for t in range(T))) for s in range(T)]
        d = max(abs(new[s] - w[s]) for s in range(T)); w = new
        if d < mp.mpf(10)**(-mp.mp.dps + 5): break
    return w


def r_solve(z, w):
    T = len(z); A = mp.zeros(T, T); b = mp.zeros(T, 1)
    for s in range(T):
        b[s] = sum(w[t]*z[t]/(z[s] + z[t]) for t in range(T)); A[s, s] += 1
        for t in range(T):
            A[s, s] -= w[t]/(z[s] + z[t]); A[s, t] += w[t]/(z[s] + z[t])
    x = mp.lu_solve(A, b)
    return [x[i] for i in range(T)]


def state(z, eta, theta):
    T = len(z); rho = 6*eta/mp.pi; F0 = [F0fun(v, eta) for v in z]; kap = [(1 - mp.exp(-v)*F0fun(-v, eta)/F0fun(v, eta))/v for v in z]
    w = H_solve(z, theta); U = [1 - sum(w[t]/(z[s] + z[t]) for t in range(T)) for s in range(T)]; r = r_solve(z, w)
    D = [F0[s]*w[s]*(1 - kap[s]*r[s])/rho for s in range(T)]; tau = [F0[s]**2*theta[s]*(1 - kap[s]*r[s])**2/rho for s in range(T)]
    G0 = [S0fun(z[s], eta)/(2*mp.pi*F0[s]) for s in range(T)]; G = [G0[s] + r[s]/(1 - kap[s]*r[s])/(2*mp.pi*rho*F0[s]**2) for s in range(T)]
    return dict(D=D, G=G, tau=tau, w=w, U=U, r=r, kap=kap, F0=F0, Fpred=[F0[s]*U[s]*(1 - kap[s]*r[s]) for s in range(T)])


def check_representation(rng):
    worst = 0; n = 0
    for T in (1, 2, 3, 4, 5):
        for _ in range(12):
            z = [mp.mpf(float(v)) for v in np.exp(rng.uniform(np.log(.1), np.log(100), T))]; eta = mp.mpf(float(rng.uniform(.01, .79)))
            lim = 1/sum(2/v for v in z)      # theta(k=0) < 1
            th = [mp.mpf(float(rng.uniform(0, 1)))*lim*mp.mpf(float(rng.uniform(.05, .9))) for _ in z]
            st = state(z, eta, th); v = st['D'] + [d*g for d, g in zip(st['D'], st['G'])]
            F, S = CF.fs(z, eta, v)
            for s in range(T):
                e1 = abs(st['D'][s]*F[s]/st['tau'][s] - 1); e2 = abs(2*mp.pi*st['G'][s]*F[s]/S[s] - 1); e3 = abs(F[s]/st['Fpred'][s] - 1)
                worst = max(worst, e1, e2, e3); n += 1
    print(f'1. REPRESENTATION: {n} tail equations, T = 1...5, largest relative residual of D F = tau, 2 pi G F = S, F = F0 U (1 - kappa r): {mp.nstr(worst, 4)}', flush=True)


def check_integrals(rng):
    w1 = w2 = w3 = 0; n = 0
    for T in (1, 2, 3):
        for _ in range(4):
            z = [mp.mpf(float(v)) for v in np.exp(rng.uniform(np.log(.2), np.log(30), T))]
            lim = 1/sum(2/v for v in z); th = [mp.mpf(float(rng.uniform(.1, .8)))*lim for _ in z]
            w = H_solve(z, th); r = r_solve(z, w); vt = lambda k: sum(2*z[t]*th[t]/(z[t]**2 + k*k) for t in range(T))
            U = lambda x: 1 - sum(w[t]/(x + z[t]) for t in range(T))
            for x in z + [mp.mpf('.77')]:
                k0 = mp.mpf('1.3'); w1 = max(w1, abs(U(1j*k0)*U(-1j*k0) - (1 - vt(k0))))
                pts = [0, 1, 10, 100, mp.inf]
                ri = mp.quad(lambda k: k*k/(x*x + k*k)*(1/(1 - vt(k)) - 1), pts)/mp.pi
                li = x*mp.quad(lambda k: -mp.log(1 - vt(k))/(x*x + k*k), pts)/mp.pi
                rx = sum(w[t]*(z[t] - r[t])/(x + z[t]) for t in range(T))/U(x)
                w2 = max(w2, abs(ri/rx - 1)); w3 = max(w3, abs(li + mp.log(U(x)))/max(abs(li), mp.mpf(10)**-30)); n += 1
    print(f'2. INTEGRALS: {n} evaluations; largest |U(ik)U(-ik) - (1 - theta(k))| {mp.nstr(w1, 3)}; relative error of the r(x) integral {mp.nstr(w2, 3)}; of the ln H(x) integral {mp.nstr(w3, 3)}', flush=True)


def taylor_theta(z, N):
    """Taylor coefficients in theta of w, U, r (exact recursion)."""
    T = len(z); O = tuple([0]*T); w = [{} for _ in range(T)]; invU = [{O: mp.mpf(1)} for _ in range(T)]; U = [{O: mp.mpf(1)} for _ in range(T)]; r = [{} for _ in range(T)]
    for d in range(1, N + 1):
        ks = [a for a in itertools.product(range(d + 1), repeat=T) if sum(a) == d]
        for s in range(T):
            for a in ks:
                if a[s] >= 1:
                    b = tuple(x - (1 if i == s else 0) for i, x in enumerate(a)); w[s][a] = invU[s].get(b, mp.mpf(0))
        for s in range(T):
            for a in ks: U[s][a] = -sum(w[t].get(a, 0)/(z[s] + z[t]) for t in range(T))
            pr = MS.mul({k: v for k, v in U[s].items() if sum(k) > 0}, invU[s], d)
            for a in ks: invU[s][a] = -pr.get(a, mp.mpf(0))
        for s in range(T):                 # r_s U_s + sum_t w_t r_t/(z_s + z_t) = sum_t w_t z_t/(z_s + z_t), order by order
            for a in ks:
                rhs = sum(w[t].get(a, 0)*z[t]/(z[s] + z[t]) for t in range(T))
                for t in range(T):
                    pr = MS.mul(w[t], r[t], d); rhs -= pr.get(a, 0)/(z[s] + z[t])
                pr = MS.mul({k: v for k, v in U[s].items() if sum(k) > 0}, r[s], d); rhs -= pr.get(a, 0)
                r[s][a] = rhs
    return w, invU, r


def check_signs(rng):
    tot = {'r': [0, 0], '1/U': [0, 0], 'w': [0, 0]}; lowest = None
    for T, N, cnt in ((1, 40, 6), (2, 14, 10), (3, 8, 5)):
        for _ in range(cnt):
            z = [mp.mpf(float(v)) for v in np.exp(rng.uniform(np.log(.1), np.log(300), T))]
            w, iU, r = taylor_theta(z, N)
            for name, ps in (('r', r), ('1/U', iU), ('w', w)):
                for p in ps:
                    for k, v in p.items():
                        if sum(k) == 0: continue
                        tot[name][1] += 1
                        if v < -mp.mpf(10)**-40*(1 + abs(v)): tot[name][0] += 1
    print(f'3. SIGNS in theta, T = 1, 2, 3, exact recursion: (negative, total) {tot}', flush=True)
    # against the independent recursion, in tau, at one state
    z = [mp.mpf(1), mp.mpf(10)]; eta = mp.mpf('.3'); N = 8; D, G, St, dF, invF = MS.series([1.0, 10.0], .3, N, 2)
    lam = [mp.mpf('.004'), mp.mpf('.03')]
    st = state(z, eta, lam)
    t = st['tau']
    # the tau of MS.series is the right side of D_t F_t = tau_t, as here
    Dser = [sum(v*t[0]**k[0]*t[1]**k[1] for k, v in D[s].items()) for s in range(2)]; Gser = [sum(v*t[0]**k[0]*t[1]**k[1] for k, v in G[s].items()) for s in range(2)]
    G0 = [S0fun(z[s], eta)/(2*mp.pi*st['F0'][s]) for s in range(2)]
    print(f'   independent recursion at theta = {[mp.nstr(v, 3) for v in lam]}, order {N}: D {[mp.nstr(v, 12) for v in Dser]} vs representation {[mp.nstr(v, 12) for v in st["D"]]}; G - G0 {[mp.nstr(v, 12) for v in Gser]} vs {[mp.nstr(st["G"][s] - G0[s], 12) for s in range(2)]}', flush=True)


def check_kappa(rng):
    w = 0; lo = mp.inf; f0 = mp.inf
    for _ in range(3000):
        z = mp.mpf(float(np.exp(rng.uniform(np.log(1e-3), np.log(1e3))))); eta = mp.mpf(float(rng.uniform(1e-4, .9999))); A = 6*eta/(1 - eta); e = mp.exp(-z)
        lhs = F0fun(z, eta) - e*F0fun(-z, eta); rhs = (1 - e) + A*(z*(1 + e) - 2*(1 - e))/z**2
        w = max(w, abs(lhs/rhs - 1)); lo = min(lo, rhs); f0 = min(f0, F0fun(z, eta), F0fun(-z, eta))
    print(f'4. KAPPA: 3000 states, largest relative difference from the closed form {mp.nstr(w, 3)}; smallest closed form {mp.nstr(lo, 4)}; smallest F0(+-z) {mp.nstr(f0, 6)} (must exceed 1)', flush=True)


if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(EXTERNAL multiprecision evidence, NOT a Lean proof)', flush=True)
    seed = int(sys.argv[sys.argv.index('--seed') + 1]) if '--seed' in sys.argv else 1; rng = np.random.default_rng(seed)
    check_representation(rng); check_kappa(rng); check_integrals(rng); check_signs(rng)
