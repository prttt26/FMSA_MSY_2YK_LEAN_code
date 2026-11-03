"""Can a complex branch pair change the sign of a pure fluid's coefficients at some high order?
(float64 evidence, NOT a Lean proof)

A pair outside the fold still enters c_n. With u = u_s + a_s sqrt(1 - tau/tau_s) at each principal-sheet
branch point s, Darboux gives, for each component k,
    -2 sqrt(pi) n^{3/2} tau_f^n c_{n,k} -> a_{f,k} y_k(n),   y_k(n) = 1 + 2 Re[(a_{p,k}/a_{f,k}) (tau_f/tau*)^n],
over the pairs p (a real negative tau* counts once). y_k(n) < 0 is a sign change at order n. Near-tie
pairs have |tau*|/tau_f - 1 ~ 1e-5 and arg tau* ~ 1e-5, so their sign change, if any, would come near order 1e5,
far beyond any series computed so far, while y_k costs no series at all. Controls compare y_k with the
coefficients themselves. It holds only for n >> 1/gap, gap = |1 - tau*/tau_f|: at ratio 1.0069 it reads 0.97 at
order 600 against 0.98, but -0.69 at order 30 against +0.17. So the objective reads the coefficients where
the terms are not separated:
    y = y_direct(n) for n <= 1000, y_k(n) for n >= max(1000, 20/gap),
with y_direct = -2 sqrt(pi) n^{3/2} tau_f^n c_{n,k} / a_{f,k}, so y < 0 is a sign change, and f is the depth of its
deepest dip (see dip), 1 for monotone y; a small y at n = 1 is only the power law. For a near tie the orders
between 1000 and 20/gap are not read by either; Lam = min ln(rho)/theta bounds what a pair can do there,
since between one phase turn of the pair its weight falls by exp(-pi Lam). States with f < 0.2 get the
recursion as far as order 20000. Random states and Nelder-Mead, T = 2, 3, eta < 0.8.
Parameters are printed in full.

Usage: attractive_sign_margin.py --minutes M [--workers W] [--seed S] [--controls-only]
"""
import sys, time, warnings
import numpy as np
from multiprocessing import Pool
from scipy.optimize import minimize
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_Convergence/scripts/two_tail')
import attractive_pair_fast as AF
warnings.simplefilter('ignore')
ND = 1000


def series(cub, b, tf, N):
    """Coefficients of u(tf s) by the exact Cauchy recursion: c[m] has units of u, m = 1..N."""
    n = cub.n; u0 = cub.u0; L = cub.J(u0); Qs = cub.Q + 3*(cub.C @ u0); C = cub.C
    Li = np.linalg.inv(L); c = np.zeros((N + 1, n)); W = np.zeros((N + 1, n, n))
    c[1] = Li @ (tf*b)
    for m in range(2, N + 1):
        W[m] = np.einsum('aj,ak->jk', c[1:m], c[m - 1:0:-1], optimize=True)
        r = np.einsum('ijk,jk->i', Qs, W[m])
        if m > 2:
            T3 = np.einsum('aj,akl->jkl', c[1:m - 1], W[m - 1:1:-1], optimize=True)
            r = r + np.einsum('ijkl,jkl->i', C, T3)
        c[m] = -Li @ r
    return c


def amplitude(cub, b, us, ts, tf):
    """a in u = u* + a sqrt(1 - tau/tau*), read at 1 - tau/tau* = 1e-6 and 1e-8. Returns (a, relative disagreement)."""
    r = abs(ts); marks = [r*(1 - 1e-6), r*(1 - 1e-8)]
    _, got = AF.ray(cub, b, ts/r, marks[-1], tf, marks=marks)
    if len(got) < 2: return None, np.inf
    a1 = (got[0] - us)/1e-3; a2 = (got[1] - us)/1e-4
    return a2, np.linalg.norm(a1 - a2)/np.linalg.norm(a2)


def dip(ns, y):
    """Depth of the deepest dip: min y(n) / min(largest y before n, largest y after n), so a monotone y gives 1.
    A low y at n = 1 is only the power law, not a dip. y <= 0 is a sign change, and is returned as it stands."""
    if np.min(y) <= 0:
        i, k = np.unravel_index(np.argmin(y), y.shape)
        return float(y[i, k]), int(ns[i]), int(k)
    r = y/np.minimum(np.maximum.accumulate(y, axis=0), np.maximum.accumulate(y[::-1], axis=0)[::-1])
    i, k = np.unravel_index(np.argmin(r), r.shape)
    return float(r[i, k]), int(ns[i]), int(k)


def margin(z, K, eta, cache=None):
    """f = min of y over all orders: coefficients to ND, then Darboux from max(ND, 20/gap).
    Returns dict with f, its order n and component k, Lam = min ln(rho)/theta, and amplitude consistency."""
    A = AF.analyse(z, K, eta, cache); tf = A['tf']
    if tf is None: return None
    cub = (cache or {}).get((tuple(z), eta)) or AF.Cubic(z, eta); b = AF.rhs(cub, K)
    h = AF.ray(cub, b, 1.0, tf*(1 - 1e-4), tf)[0]
    uf, tc, ok = AF.branch_point(cub, b, h[-1][2], tf)
    if not ok or abs(tc - tf) > 1e-6*tf: return None
    af, cons = amplitude(cub, b, uf, tc.real + 0j, tf)
    if af is None: return None
    af = af.real
    c = series(cub, b, tf, ND); ns = np.arange(1, ND + 1.0)
    yd = -2*np.sqrt(np.pi)*c[1:]*(ns**1.5)[:, None]/af
    out = dict(tf=tf, folds=A['folds'], pts=A['pts'], af=af, cons=cons, terms=[], Lam=np.inf, ratio=None, gap=None, direct_f=float(np.min(yd)))
    out.update(zip(('f', 'n', 'k'), dip(ns, yd)))
    terms = []
    for p in A['pts']:
        ap, c1 = amplitude(cub, b, p[4], p[1], tf)
        if ap is None: continue
        out['cons'] = max(out['cons'], c1); terms.append((p[1], ap))
    if not terms: return out
    out['terms'] = terms
    gap = min(abs(1 - t/tf) for t, _ in terms); lr = min(np.log(abs(t)/tf) for t, _ in terms)
    t0 = min(terms, key=lambda q: abs(q[0]))[0]
    out.update(gap=gap, ratio=abs(t0)/tf)
    cplx = [np.log(abs(t)/tf)/abs(np.angle(t)) for t, _ in terms if abs(t.imag) > 1e-12*abs(t)]
    if cplx: out['Lam'] = min(cplx)
    lo = max(ND, 20/gap); hi = min(1e9, 40/max(lr, 1e-9))
    if hi > lo:
        ng = np.unique(np.geomspace(lo, hi, 20000).astype(np.int64)).astype(float)
        y = np.ones((cub.n, len(ng)))
        for t, ap in terms:
            w = np.exp(ng*(np.log(tf) - np.log(complex(t))))
            y += (1.0 if abs(t.imag) < 1e-12*abs(t) else 2.0)*np.real((ap/af)[:, None]*w[None, :])
        out.update(zip(('f', 'n', 'k'), dip(np.r_[ns, ng], np.vstack([yd, y.T]))))
    return out


def direct(z, K, eta, tf, N):
    cub = AF.Cubic(z, eta); c = series(cub, AF.rhs(cub, K), tf, N)
    flips = [(np.where(np.sign(c[2:, k]) != np.sign(c[1:-1, k]))[0] + 2).tolist() for k in range(cub.n)]
    return c, flips


def fmt(z, K, eta): return AF.fmt(z, K, eta)


def worker(args):
    wid, seed, minutes, starts = args
    rng = np.random.default_rng([seed, wid]); end = time.time() + 60*minutes; cache = {}
    nstates = 0; best = (9.0, None); checked = [0.2]; lam = [np.inf, None]
    def f(q):
        nonlocal nstates, best
        if time.time() > end: raise TimeoutError
        q = np.asarray(q); T = len(q)//2
        z, K, eta = np.exp(q[:T]), np.r_[1.0, np.exp(q[T:2*T - 1])], float(q[-1])
        if not (0.005 < eta < 0.8) or np.any(z < 0.05) or np.any(z > 500) or np.any(K < 1e-6) or np.any(K > 1e8): return 9.0
        try: M = margin(z, K, eta, cache)
        except np.linalg.LinAlgError: return 9.0
        nstates += 1
        if M is None: return 3.0
        if M['Lam'] < lam[0]:
            lam[0] = M['Lam']; lam[1] = f'Lam {M["Lam"]:.5f} ratio {M["ratio"]} gap {M["gap"]} direct y {M["direct_f"]:.5f} at {fmt(z, K, eta)}'
        if M['f'] < best[0]:
            best = (M['f'], f'dip f={M["f"]:.5f} at n={M["n"]} comp {M["k"]} (smallest direct y to {ND}: {M["direct_f"]:.5f}), nearest ratio {M["ratio"]}, gap {M["gap"]}, Lam {M["Lam"]:.4f}, amplitude consistency {M["cons"]:.2e}, tf={M["tf"]} at {fmt(z, K, eta)}')
        if M['f'] < checked[0]:
            checked[0] = M['f'] - 0.05
            c, fl = direct(z, K, eta, M['tf'], min(20000, 3*M['n'] + 200))
            msg = f'recursion to order {len(c) - 1}, sign changes per component, first 8: {[x[:8] for x in fl]}'
            print(f'LOW f: {best[1]}; {msg}', flush=True)
        return M['f']
    try:
        for s in starts:
            minimize(f, s, method='Nelder-Mead', options=dict(maxiter=400, xatol=1e-4, fatol=1e-6))
        while True:
            T = 2 if rng.random() < 0.7 else 3
            q = np.r_[rng.uniform(np.log(.05), np.log(500), T), rng.uniform(np.log(1e-6), np.log(1e8), T - 1), rng.uniform(.02, .8)]
            if f(q) < 0.98:
                minimize(f, q, method='Nelder-Mead', options=dict(maxiter=400, xatol=1e-4, fatol=1e-6))
    except TimeoutError:
        pass
    print(f'worker {wid}: {nstates} states; best {best[1]}; smallest {lam[1]}', flush=True)
    return nstates, best, lam


if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(float64 evidence, NOT a Lean proof)', flush=True)
    val = lambda f, d: type(d)(sys.argv[sys.argv.index(f) + 1]) if f in sys.argv else d
    minutes, W, seed = val('--minutes', 60.0), val('--workers', 20), val('--seed', 1)
    for name, z, K, e in [('CONTROL pair ratio 1.29866', [3.167849233194492, 23.880787678883983], [3.77257994e-02, 6.23157446e+01], 0.19032415340471848),
                          ('CONTROL pair ratio 1.49786', [.53, 20.81], [.023, 89.431], .103),
                          ('CONTROL pair ratio 1.00690', [1.3208, 8.0950], [1, 29203], .5847)]:
        t0 = time.time(); M = margin(z, K, e); tf = M['tf']
        print(f'{name}: dip f={M["f"]:.5f} at n={M["n"]} comp {M["k"]}, Lam {M["Lam"]:.4f}, gap {M["gap"]}, amplitude consistency {M["cons"]:.2e}, turning points {M["folds"]} [{time.time() - t0:.2f} s]', flush=True)
        c, fl = direct(z, K, e, tf, 1200)
        print(f'  direct sign changes to order 1200: {[len(x) for x in fl]}', flush=True)
        for n in (30, 60, 120, 300, 600, 1200):
            d = c[n]*n**1.5*(-2*np.sqrt(np.pi))
            y = np.ones(len(d))
            for t, ap in M['terms']:
                fac = 1.0 if abs(t.imag) < 1e-12*abs(t) else 2.0
                y = y + fac*np.real((ap/M['af'])*np.exp(n*(np.log(tf) - np.log(complex(t)))))
            print(f'  n={n}: direct/a_f {np.round(d/M["af"], 5).tolist()}; predicted y {np.round(y, 5).tolist()}', flush=True)
    if '--controls-only' in sys.argv: sys.exit(0)
    pool = [np.r_[np.log([3.167849233194492, 23.880787678883983, 6.23157446e+01/3.77257994e-02]), 0.19032415340471848],
            np.r_[np.log([.53, 20.81, 89.431/.023]), .103], np.r_[np.log([1.3208, 8.0950, 29203.]), .5847],
            np.r_[np.log([.6243310037229898, .5784146503602097, 10.509884121001777, .0013074019495375904, 41012424.22405669]), .7953290066261736],
            np.r_[np.log([2.2647359032816383, 16.56245035231241, 99314273.83694799]), .7965845874346712]]
    jobs = [(i, seed, minutes, [pool[i]] if i < len(pool) else []) for i in range(W)]
    with Pool(W) as ex:
        res = ex.map(worker, jobs, chunksize=1)
    b = min(res, key=lambda r: r[1][0])[1]
    l = min(res, key=lambda r: r[2][0])[2]
    print(f'== total {sum(r[0] for r in res)} states evaluated; smallest f: {b[1]}; smallest {l[1]}', flush=True)
