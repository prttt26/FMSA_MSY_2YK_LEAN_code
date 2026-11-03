"""Direct search for Lam = ln(rho)/theta < sqrt 3, all-attractive pure fluids (float64 evidence, NOT a Lean proof).

normal_form_sign shows that sqrt 3 is the edge of the sign protection at a near tie: t = y^2 + a y + beta/y has Lam >= sqrt 3
exactly for a >= 0, where its scaling function has only positive terms, while for a < 0 the strong-tail component
changes sign. So a principal-sheet pair with Lam < sqrt 3 near a fold would be a counterexample candidate for the
all-order sign. attractive_sign_margin only recorded Lam along another objective; here it is the objective.
Each state below sqrt 3 gets the recursion, to order min(20000, 60/gap). Rates are kept >= 0.2, since float tensors
lose the sign at rates near 0.05 (attractive_margin_mp_{1,2}.log).

Usage: attractive_lam_bound.py --minutes M [--workers W] [--seed S]
"""
import sys, time, warnings
import numpy as np
from multiprocessing import Pool
from scipy.optimize import minimize
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_Convergence/scripts/two_tail')
import attractive_pair_fast as AF
import attractive_sign_margin as SM
warnings.simplefilter('ignore')
R3 = np.sqrt(3.0)


def worker(args):
    wid, seed, minutes, starts = args
    rng = np.random.default_rng([seed, wid]); end = time.time() + 60*minutes; cache = {}
    nstates = npair = 0; best = (np.inf, None); floor = [R3]
    def f(q):
        nonlocal nstates, npair, best
        if time.time() > end: raise TimeoutError
        q = np.asarray(q); T = len(q)//2
        z, K, eta = np.exp(q[:T]), np.r_[1.0, np.exp(q[T:2*T - 1])], float(q[-1])
        if not (0.005 < eta < 0.8) or np.any(z < 0.2) or np.any(z > 500) or np.any(K < 1e-6) or np.any(K > 1e10): return 9.0
        try: A = AF.analyse(z, K, eta, cache)
        except np.linalg.LinAlgError: return 9.0
        nstates += 1
        if A['tf'] is None: return 9.0
        tf = A['tf']; L = [(np.log(p[0])/abs(np.angle(p[1])), p) for p in A['pts'] if abs(p[1].imag) > 1e-12*abs(p[1])]
        if not L: return 9.0
        npair += 1
        lam, p = min(L, key=lambda v: v[0]); gap = abs(1 - p[1]/tf)
        msg = f'Lam {lam:.6f} (sqrt 3 {lam - R3:+.6f}) ratio {p[0]:.7f} gap {gap:.4e} direction {np.degrees(np.angle(p[1]/tf - 1)):+.4f} deg, sheet d(1e-2)={p[2]:.2e} d(1e-8)={p[3]:.2e}, turning points {len(A["folds"])} at {AF.fmt(z, K, eta)}'
        if lam < best[0]: best = (lam, msg)
        if lam < floor[0]:
            floor[0] = lam - 0.002
            cub = AF.Cubic(z, eta); N = int(min(20000, 60/gap))
            c = SM.series(cub, AF.rhs(cub, K), tf, N)
            print(f'BELOW sqrt 3: {msg}; recursion to order {N}, sign changes {[int(np.sum(np.sign(c[2:, k]) != np.sign(c[1:-1, k]))) for k in range(cub.n)]}', flush=True)
        return lam
    try:
        for s in starts:
            minimize(f, s, method='Nelder-Mead', options=dict(maxiter=500, xatol=1e-5, fatol=1e-6))
        while True:
            T = 2 if rng.random() < 0.7 else 3
            q = np.r_[rng.uniform(np.log(.2), np.log(500), T), rng.uniform(np.log(1e-6), np.log(1e10), T - 1), rng.uniform(.02, .8)]
            if f(q) < 3.0:
                minimize(f, q, method='Nelder-Mead', options=dict(maxiter=500, xatol=1e-5, fatol=1e-6))
    except TimeoutError:
        pass
    print(f'worker {wid}: {nstates} states, {npair} with a complex pair; smallest {best[1]}', flush=True)
    return nstates, npair, best


if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(float64 evidence, NOT a Lean proof)', flush=True)
    val = lambda f, d: type(d)(sys.argv[sys.argv.index(f) + 1]) if f in sys.argv else d
    minutes, W, seed = val('--minutes', 45.0), val('--workers', 20), val('--seed', 1)
    pool = [np.r_[np.log([2.7636, 58.2749, 6.812e7]), .7981], np.r_[np.log([1.0482, 47.9458, 9.913e7]), .3040],
            np.r_[np.log([1.7922, 60.0411, 4.032e7]), .2731], np.r_[np.log([.9374, 29.4236, 4.397e7]), .1169],
            np.r_[np.log([3.167849233194492, 23.880787678883983, 6.23157446e+01/3.77257994e-02]), 0.19032415340471848]]
    jobs = [(i, seed, minutes, [pool[i]] if i < len(pool) else []) for i in range(W)]
    with Pool(W) as ex:
        res = ex.map(worker, jobs, chunksize=1)
    b = min(res, key=lambda r: r[2][0])[2]
    print(f'== total {sum(r[0] for r in res)} states, {sum(r[1] for r in res)} with a complex pair; smallest {b[1]}', flush=True)
