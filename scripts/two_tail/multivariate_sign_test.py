"""Are all mixed Taylor coefficients of u(tau_1, ..., tau_T) nonnegative? All-attractive pure fluids (float64 evidence, NOT a Lean proof).

The all-order sign in one coupling asks that sum_alpha c_alpha K^alpha has one sign at each order, for every K > 0. A stronger statement is
c_alpha >= 0 monomial by monomial, which is what a Picard induction would prove. Exact recursion for the cubic residual in T variables:
J0 c_alpha = delta_{|alpha| = 1} e_t - Qt[c, c]_alpha - C[c, c, c]_alpha, with tau_t measured so that the right side is tau_t e_t.
Each component is read against the largest |c| of that component at the same total order; a negative entry above 1e-9 of it is reported.

Usage: multivariate_sign_test.py --states S --order N --T T [--seed S] [--workers W]
"""
import sys, warnings, itertools
import numpy as np
from multiprocessing import Pool
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_Convergence/scripts/two_tail')
import attractive_pair_fast as AF
warnings.simplefilter('ignore')


def coefficients(z, eta, T, N):
    cub = AF.Cubic(z, eta); n = cub.n; u0 = cub.u0; C = cub.C
    Qt = cub.Q + 3*(C @ u0); J0 = cub.J(u0); Ji = np.linalg.inv(J0)
    alphas = [a for d in range(1, N + 1) for a in itertools.product(range(d + 1), repeat=T) if sum(a) == d]
    c = {}; E = {}
    for a in alphas:
        d = sum(a); rhs = np.zeros(n)
        if d == 1: rhs[a.index(1)] = 1.0
        for b, cb in c.items():
            g = tuple(x - y for x, y in zip(a, b))
            if min(g) < 0 or sum(g) == 0 or g not in c: continue
            rhs -= Qt @ c[g] @ cb
        for b, Eb in E.items():
            g = tuple(x - y for x, y in zip(a, b))
            if min(g) < 0 or sum(g) == 0 or g not in c: continue
            rhs -= np.einsum('ijkl,jk,l->i', C, Eb, c[g], optimize=True)
        c[a] = Ji @ rhs
        Ea = np.zeros((n, n))
        for b, cb in c.items():
            g = tuple(x - y for x, y in zip(a, b))
            if min(g) < 0 or sum(g) == 0 or g not in c: continue
            Ea += np.outer(cb, c[g])
        E[a] = Ea
    return c, n


def run(job):
    seed, T, N = job; rng = np.random.default_rng(seed)
    z = np.sort(np.exp(rng.uniform(np.log(.2), np.log(200), T))); e = float(rng.uniform(.01, .79))
    if rng.random() < .3:   # near-equal rates, where earlier false alarms sat
        z[1] = z[0]*np.exp(rng.uniform(.01, .2))
    c, n = coefficients(z, e, T, N); worst = 0.0; where = None; negs = 0; total = 0; first = None
    for d in range(1, N + 1):
        ks = [a for a in c if sum(a) == d]; A = np.array([c[a] for a in ks]); mx = np.max(np.abs(A), axis=0)
        for i, a in enumerate(ks):
            for k in range(n):
                total += 1; v = A[i, k]/mx[k] if mx[k] > 0 else 0.0
                if v < -1e-9:
                    negs += 1
                    if first is None: first = (a, k, float(v))
                    if v < worst: worst, where = v, (a, k)
    return z.tolist(), e, negs, total, worst, where, first


if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(float64 evidence, NOT a Lean proof)', flush=True)
    val = lambda f, d: type(d)(sys.argv[sys.argv.index(f) + 1]) if f in sys.argv else d
    S, N, T, seed, W = val('--states', 200), val('--order', 16), val('--T', 2), val('--seed', 1), val('--workers', 16)
    with Pool(W) as ex: res = ex.map(run, [(seed*100000 + i, T, N) for i in range(S)], chunksize=1)
    bad = [r for r in res if r[2]]
    for r in sorted(bad, key=lambda r: r[4])[:25]:
        print(f'z={np.round(r[0], 5).tolist()} eta={r[1]:.5f}: {r[2]}/{r[3]} negative; worst {r[4]:.3e} at (alpha, comp)={r[5]}; first {r[6]}', flush=True)
    print(f'== {S} states, T={T}, order {N}: {len(bad)} states with a negative mixed coefficient above 1e-9', flush=True)
