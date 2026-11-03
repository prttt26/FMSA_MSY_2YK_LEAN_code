"""Global search for a principal-sheet singularity inside the first fold, all-attractive pure fluids
(float64 evidence, NOT a Lean proof).

The residual is an explicit cubic, R(u) = R0 + L u + Q[u,u] + C[u,u,u], with K only in the right side
tau b, so one state costs milliseconds and no warm start is needed: every evaluation finds the branch
points from nothing.
  * first fold tau_f: pseudo-arclength from tau = 0, which does not jump folds; the trace goes on to
    tau < 0 and counts turning points, so an S-curve shows up directly as more than one;
  * branch points: the root tracked along rays arg tau = theta, each local minimum of |det J| and each
    point where the step collapses seeds Newton on R(u) = tau b, J(u) v = 0, c.v = 1;
  * principal sheet: the root tracked along the ray through tau* must reach u*. |u - u*| is read at
    1 - |tau|/|tau*| = 1e-2, 1e-4, 1e-6, 1e-8 and must end in the square-root law, the last two
    differing by about 10. A root on another sheet leaves |u - u*| saturated at the gap between roots,
    however small, so this test has no tolerance for a descent to sit under. A real tau* in (0, tau_f)
    is excluded outright: the real branch is analytic there, the arclength trace having no turning point.
Two weaker tests failed in exactly the way a descent exploits. attractive_pair_ratio accepted a pair if
|u - u*|/|u*| < 0.1 at one radius; its descents ended at 0.09 - 0.098 with ratios as low as 0.99634 that
order-1000 coefficients did not confirm. A first version of this script asked for d(1e-4)/d(1e-2) < 0.25;
its descents ended at exactly 0.25 on real tau* (attractive_pair_fast_two_radii.log, 656 false hits).

Objective: ratio = min |tau*| / tau_f over principal-sheet branch points other than the fold. ratio < 1
would give R < tau_f. Random states (eta < 0.8) and Nelder-Mead descents from the good ones, T = 2, 3.
Parameters are printed in full, since a rounded state may not reproduce a near-degenerate one.

Usage: attractive_pair_fast.py --minutes M [--workers W] [--seed S] [--controls-only] [--retest LOG]
"""
import sys, time, warnings, re, json
import numpy as np
from itertools import product
from multiprocessing import Pool
from scipy.optimize import minimize
warnings.simplefilter('ignore')
THETAS = (0.02, 0.05, 0.1, 0.3, 1.0, 2.0, 4.0, 8.0, 15.0, 25.0, 40.0, 60.0, 90.0, 120.0, 150.0, 180.0)


def phi1(x): return (1 - x - np.exp(-x))/x**2
def phi2(x): return (1 - x + x*x/2 - np.exp(-x))/x**3
def exprel(x): return (1 - np.exp(-x))/x


class Cubic:
    """R(u) as explicit tensors, from exact polarisation at unit stencil points."""
    def __init__(self, z, eta):
        self.z = z = np.asarray(z, float); self.eta = eta; self.T = T = len(z); self.n = n = 2*T
        self.rho = 6*eta/np.pi
        d = 2*np.pi/(1 - eta)**2
        self.A0 = d*((1 - eta) + 3*eta); self.B0 = d*(-1.5*eta); self.QP0 = d*(1.5*eta + (1 - eta))
        I = np.eye(n)
        self.R0 = self.res(np.zeros(n))
        self.C = C = np.zeros((n, n, n, n)); self.Q = Q = np.zeros((n, n, n)); self.L = L = np.zeros((n, n))
        for j in range(n):
            for k in range(j, n):
                for l in range(k, n):
                    s = sum(a*b*c*self.res(a*I[j] + b*I[k] + c*I[l]) for a, b, c in product((1, -1), repeat=3))/48
                    for p in {(j, k, l), (j, l, k), (k, j, l), (k, l, j), (l, j, k), (l, k, j)}: C[:, p[0], p[1], p[2]] = s
        for j in range(n):
            for k in range(j, n):
                s = sum(a*b*self.res(a*I[j] + b*I[k]) for a, b in product((1, -1), repeat=2))/8
                Q[:, j, k] = s; Q[:, k, j] = s
        for j in range(n):
            L[:, j] = (self.res(I[j]) - self.res(-I[j]))/2 - C[:, j, j, j]
        m = T
        G = np.linalg.solve(L[m:, m:], -self.R0[m:])
        self.u0 = np.r_[np.zeros(m), G]

    def res(self, u):
        T, z, rho = self.T, self.z, self.rho
        D, G = u[:T], u[T:]
        Ct = (1 - 2*np.pi*rho*G*np.exp(-z)/z)*D
        Wt = (2*np.pi/z)*G*rho*D
        Mv = -np.sum(rho*(Wt + (1 + z)*Ct)/z)
        Nc = np.sum(rho*(Wt/z**2 + (1 + z + z**2/2)/z**2*Ct))
        A = self.A0*(1 + Mv) - 4*self.B0*Nc
        qp = self.QP0*(1 + Mv) + self.A0*Nc
        r1, r2 = np.zeros(T), np.zeros(T)
        for t in range(T):
            x = z[t]
            Q = phi1(x)*qp + phi2(x)*A + np.sum(Wt/(x + z) + Ct*(np.exp(-x)/(x + z) + exprel(x)))
            F = 1 - rho*Q
            src = A + x*qp + np.sum((x**2*z/(x + z))*Ct)
            r1[t] = D[t]*F; r2[t] = 2*np.pi*G[t]*F - src/x**2
        return np.r_[r1, r2]

    def RJ(self, u):
        Qu = self.Q @ u; Cuu = (self.C @ u) @ u
        return self.R0 + (self.L + Qu + Cuu) @ u, self.L + 2*Qu + 3*Cuu

    def J(self, u): return self.RJ(u)[1]


def rhs(cub, K): return np.r_[2*np.pi*np.asarray(K, float)/cub.z, np.zeros(cub.T)]


def branch_point(cub, b, u, tau, iters=30):
    """Newton on (R(u) - tau b, J(u) v, c.v - 1), exact derivatives. Returns (u, tau, ok)."""
    n = cub.n; u = np.asarray(u, complex); _, _, Vh = np.linalg.svd(cub.J(u)); v = Vh[-1].conj(); c = v.conj(); v = v/(c @ v)
    tau = complex(tau); bc = b.astype(complex)
    for _ in range(iters):
        R, J = cub.RJ(u); g = np.r_[R - tau*bc, J @ v, c @ v - 1]
        M = 2*(cub.Q @ v) + 6*((cub.C @ u) @ v)
        A = np.zeros((2*n + 1, 2*n + 1), complex)
        A[:n, :n] = J; A[:n, n] = -bc; A[n:2*n, :n] = M; A[n:2*n, n + 1:] = J; A[2*n, n + 1:] = c
        try: dx = np.linalg.solve(A, -g)
        except np.linalg.LinAlgError: return u, tau, False
        u = u + dx[:n]; tau = tau + dx[n]; v = v + dx[n + 1:]
        if not np.all(np.isfinite(dx)): return u, tau, False
        if np.linalg.norm(dx[:n]) < 1e-11*(1 + np.linalg.norm(u)) and abs(dx[n]) < 1e-12*abs(tau): return u, tau, True
    return u, tau, False


def arclength(cub, b, max_steps=6000):
    """Returns (real turning points in order, tau scale). Stops at tau < 0, at 3 turning points, or at max_steps."""
    n = cub.n; u0 = cub.u0; u1 = np.linalg.solve(cub.J(u0), b)
    tm = 1.0/np.max(np.abs(u1)/(1 + np.abs(u0)))
    us = np.maximum(np.abs(u1)*tm, 1e-3*(1 + np.abs(u0)))
    def FA(x):
        R, J = cub.RJ(u0 + us*x[:n])
        return R - x[n]*tm*b, np.column_stack([J*us, -tm*b])
    def tangent(A, t):
        s = np.linalg.solve(np.vstack([A, t]), np.r_[np.zeros(n), 1.0]); return s/np.linalg.norm(s)
    x = np.zeros(n + 1); e = np.zeros(n + 1); e[n] = 1.0
    t = tangent(FA(x)[1], e); ds = 1e-3; folds = []; steps = 0
    while steps < max_steps and ds > 1e-11:
        steps += 1; y = x + ds*t; ok = False
        for _ in range(8):
            r, A = FA(y)
            try: dy = np.linalg.solve(np.vstack([A, t]), np.r_[-r, -(t @ (y - x) - ds)])
            except np.linalg.LinAlgError: break
            y = y + dy
            if not np.all(np.isfinite(y)): break
            if np.linalg.norm(dy) < 1e-10*(1 + np.linalg.norm(y)): ok = True; break
        if not ok: ds /= 2; continue
        tn = tangent(FA(y)[1], t)
        if t @ tn < 0.97: ds /= 2; continue
        if tn[n]*t[n] < 0:
            a = t[n]/(t[n] - tn[n]); xa = x + a*(y - x); ua = u0 + us*xa[:n]; ta = xa[n]*tm
            ub, tb, good = branch_point(cub, b, ua, ta)
            folds.append(float(tb.real) if good and abs(tb.imag) < 1e-9*abs(tb) and abs(tb - ta) < 0.05*abs(ta) else float(ta))
        x, t = y, tn; ds = min(ds*1.3, 0.2)
        if x[n] < 0 or len(folds) >= 3: break
    return folds, tm


def ray(cub, b, ph, rmax, tf, dmax=1e-2, marks=()):
    """Root along tau = r ph from r = 0 to rmax. Returns (hist of (r, |det J|, u), root at each mark)."""
    u = cub.u0.astype(complex); r = 0.0; prev = None; dr = tf*1e-3; hist = []; bc = b*ph; got = []; marks = list(marks)
    while r < rmax and dr > tf*1e-13:
        rn = min(r + dr, rmax)
        if marks and rn > marks[0]: rn = marks[0]
        pred = u if prev is None else u + (u - prev[0])*(rn - r)/(r - prev[1])
        un = pred; ok = False
        for _ in range(6):
            R, J = cub.RJ(un)
            try: du = np.linalg.solve(J, rn*bc - R)
            except np.linalg.LinAlgError: break
            un = un + du
            if not np.all(np.isfinite(un)): break
            if np.linalg.norm(du) < 1e-11*(1 + np.linalg.norm(un)): ok = True; break
        if ok and np.linalg.norm(un - pred) > 2e-3*(1 + np.linalg.norm(u)): ok = False
        if not ok: dr /= 2; continue
        prev = (u, r); u, r = un, rn; dr = min(dr*1.25, tf*dmax)
        hist.append((r, abs(np.linalg.det(cub.J(u))), u))
        if marks and r >= marks[0]: got.append(u); marks.pop(0)
    return hist, got


def on_sheet(cub, b, us, ts, tf):
    """|u - u*|/|u*| along the ray through tau*, at the four radii; None if the root stops short of them."""
    r = abs(ts); marks = [r*(1 - g) for g in (1e-2, 1e-4, 1e-6, 1e-8)]
    hist, got = ray(cub, b, ts/r, marks[-1], tf, marks=marks)
    if len(got) < 4: return None
    return [np.linalg.norm(g - us)/np.linalg.norm(us) for g in got]


def analyse(z, K, eta, cache=None):
    """Returns dict with tau_f, turning points, and the principal-sheet branch points other than the fold."""
    key = (tuple(z), eta)
    cub = cache.get(key) if cache is not None else None
    if cub is None:
        cub = Cubic(z, eta)
        if cache is not None:
            if len(cache) > 2000: cache.clear()
            cache[key] = cub
    b = rhs(cub, K)
    folds, tm = arclength(cub, b)
    if not folds: return dict(tf=None, folds=[], pts=[])
    tf = folds[0]; found = {}
    for th in THETAS:
        ph = np.exp(1j*np.deg2rad(th))
        hist, _ = ray(cub, b, ph, 1.25*tf, tf)
        if len(hist) < 3: continue
        ds = np.array([h[1] for h in hist]); seeds = list(np.where((ds[1:-1] < ds[:-2]) & (ds[1:-1] < ds[2:]))[0] + 1)
        if hist[-1][0] < 1.25*tf*(1 - 1e-9): seeds.append(len(hist) - 1)
        for i in seeds:
            us, ts, ok = branch_point(cub, b, hist[i][2], hist[i][0]*ph)
            if not ok or abs(ts) < 1e-6*tf or abs(ts - tf) < 1e-7*tf: continue
            ts = complex(ts.real, abs(ts.imag))
            if abs(ts) > 1.5*tf: continue
            k = (round(ts.real/tf, 7), round(ts.imag/tf, 7))
            if k not in found: found[k] = (ts, us if ts.imag == 0 or np.isclose(ts, complex(ts.real, abs(ts.imag))) else us.conj())
    pts = []
    for ts, us in found.values():
        _, tc, ok = branch_point(cub, b, us, ts)           # the conjugate root belongs to the conjugate tau*
        if not ok or abs(tc - ts) > 1e-6*abs(ts): us = us.conj()
        if abs(ts.imag) < 1e-12*abs(ts) and 0 < ts.real < tf: continue
        chk = on_sheet(cub, b, us, ts, tf)
        if chk is None: continue
        if 0.05 < chk[3]/chk[2] < 0.2: pts.append((abs(ts)/tf, ts, chk[0], chk[3], us))
    pts.sort(key=lambda p: p[0])
    return dict(tf=tf, folds=folds, pts=pts)


def fmt(z, K, eta): return f'z={[float(v) for v in z]} K={[float(v) for v in K]} eta={eta!r}'


def retest(line):
    """Run a state printed by an earlier search through the current test."""
    m = re.search(r'z=(\[.*?\]) K=(\[.*?\]) eta=([0-9.e-]+)', line)
    A = analyse(json.loads(m.group(1)), json.loads(m.group(2)), float(m.group(3)))
    return A['pts'][0][0] if A['pts'] else None


def worker(args):
    wid, seed, minutes, starts = args
    rng = np.random.default_rng([seed, wid]); end = time.time() + 60*minutes; cache = {}
    nstates = nsc = 0; best = (9.0, None); record = [9.0]
    def unpack(q):
        T = len(q)//2
        return np.exp(q[:T]), np.r_[1.0, np.exp(q[T:2*T - 1])], float(q[-1])
    def f(q):
        nonlocal nstates, nsc, best
        if time.time() > end: raise TimeoutError
        z, K, eta = unpack(np.asarray(q))
        if not (0.005 < eta < 0.8) or np.any(z < 0.05) or np.any(z > 500) or np.any(K < 1e-6) or np.any(K > 1e8): return 9.0
        try: A = analyse(z, K, eta, cache)
        except np.linalg.LinAlgError: return 9.0
        nstates += 1
        if A['tf'] is None: return 9.0
        if len(A['folds']) > 1:
            nsc += 1
            print(f'S-CURVE turning points {A["folds"]} at {fmt(z, K, eta)}', flush=True)
        if not A['pts']: return 3.0
        p = A['pts'][0]
        if p[0] < best[0]:
            best = (p[0], f'ratio {p[0]:.6f} tau*={p[1]} tf={A["tf"]} sheet d(1e-2)={p[2]:.3e} d(1e-8)={p[3]:.3e} at {fmt(z, K, eta)}')
        if p[0] < 1 and p[0] < record[0]:
            record[0] = p[0]; print(f'BELOW 1: {best[1]}', flush=True)
        return p[0]
    try:
        for s in starts:
            minimize(f, s, method='Nelder-Mead', options=dict(maxiter=400, xatol=1e-4, fatol=1e-7))
        while True:
            T = 2 if rng.random() < 0.7 else 3
            q = np.r_[rng.uniform(np.log(.05), np.log(500), T), rng.uniform(np.log(1e-6), np.log(1e8), T - 1), rng.uniform(.02, .8)]
            if f(q) < 1.5:
                minimize(f, q, method='Nelder-Mead', options=dict(maxiter=400, xatol=1e-4, fatol=1e-7))
    except TimeoutError:
        pass
    print(f'worker {wid}: {nstates} states, {nsc} with an S-curve; best {best[1]}', flush=True)
    return nstates, nsc, best


if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(float64 evidence, NOT a Lean proof)', flush=True)
    val = lambda f, d: type(d)(sys.argv[sys.argv.index(f) + 1]) if f in sys.argv else d
    minutes, W, seed = val('--minutes', 60.0), val('--workers', 20), val('--seed', 1)
    for name, z, K, e in [('CONTROL one tail z=1.8, fold 1.3070', [1.8], [1.0], .3),
                          ('CONTROL z=(1,10) K=(1,1), fold 0.5642', [1, 10], [1, 1], .3),
                          ('CONTROL pair ratio 1.29866', [3.167849233194492, 23.880787678883983], [3.77257994e-02, 6.23157446e+01], 0.19032415340471848),
                          ('CONTROL pair ratio 1.49786', [.53, 20.81], [.023, 89.431], .103),
                          ('search ending 1.00690 dist .012', [1.3208, 8.0950], [1, 29203], .5847),
                          ('search ending 1.01275 dist .0098', [.7561, 6.3195], [1, 9444.2], .5744),
                          ('search ending 0.99634 dist .0975', [.4505, 3.6718], [1, 91367], .5633),
                          ('search ending 0.99978 dist .0925', [.5266, 4.0853], [1, 39499], .5422)]:
        t0 = time.time(); A = analyse(z, K, e)
        print(f'{name}: tau_f={A["tf"]}, turning points {A["folds"]}; ' + ('; '.join(f'|tau*|/tf={p[0]:.6f} tau*/tf={p[1]/A["tf"]:.6f} sheet {p[2]:.2e} -> {p[3]:.2e}' for p in A['pts']) or 'no other principal-sheet branch point within 1.5 tau_f') + f' [{time.time() - t0:.2f} s]', flush=True)
    if '--controls-only' in sys.argv: sys.exit(0)
    if '--retest' in sys.argv:
        hits = [l for l in open(sys.argv[sys.argv.index('--retest') + 1]) if l.startswith(('BELOW 1', 'worker')) and ' at z=' in l]
        with Pool(W) as ex: out = ex.map(retest, hits, chunksize=4)
        print(f'== retest: {len(out)} hits of the earlier test; survive the four-radius test with ratio < 1: {sum(o is not None and o < 1 for o in out)}; '
              f'smallest surviving ratio {min((o for o in out if o is not None), default=None)}; no principal-sheet point within 1.5 tau_f: {sum(o is None for o in out)}', flush=True)
        sys.exit(0)
    pool = [np.r_[np.log([1.3208, 8.0950, 29203.]), .5847], np.r_[np.log([.7561, 6.3195, 9444.2]), .5744],
            np.r_[np.log([1.0096, 11.0453, 21545.]), .5887], np.r_[np.log([.5444, 6.1583, 3534.4]), .5801],
            np.r_[np.log([3.5200, 14.1067, 1623.2]), .5734], np.r_[np.log([2.2852, 71.5302, 99980.]), .6]]
    jobs = [(i, seed, minutes, [pool[i]] if i < len(pool) else []) for i in range(W)]
    with Pool(W) as ex:
        res = ex.map(worker, jobs, chunksize=1)
    tot = sum(r[0] for r in res); sc = sum(r[1] for r in res); b = min(res, key=lambda r: r[2][0])[2]
    print(f'== total {tot} states evaluated, {sc} with more than one turning point; smallest ratio: {b[1]}', flush=True)
