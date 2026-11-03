"""How close can the complex branch pair of an all-attractive two-tail fluid come to the fold?
(float64 evidence, NOT a Lean proof)

Superseded by attractive_pair_fast. The sheet test here, distance < 0.1 at one radius, is loose: the
ratios below 1 in attractive_pair_ratio.log sit at distance 0.09 - 0.098 and are not on the principal sheet.

From a known pair tau*, parameters (z1, z2, w = K2/K1, eta) are continued with the augmented Newton
solve warm-started from the previous solution. The objective is ratio = |tau*| / tau_f with tau_f
the FIRST real fold, taken from a fresh pseudo-arclength trace at every evaluation. Two earlier
denominators were wrong: a warm-started fold solve converged to a later fold, and the tau-stepping
msa_exact_mix.trace_coupling_mix jumped over the first fold on strong short-range tails. The second
produced ratios down to 0.31 that attractive_pair_series_mp refuted (no sign change through order 400,
real singularity at the arclength fold). A new minimum is only kept if the root tracked along the
ray 0 -> tau* lands on the pair. ratio < 1 means R <= |tau*| < tau_f: a counterexample to R = tau_f
for all-attractive tails, once tau* is verified to be on the principal sheet (the root tracked along
the straight ray 0 -> tau* approaches u*). Nelder-Mead in log-parameters from several starts.
"""
import sys, warnings, signal
import numpy as np
from scipy.optimize import minimize
from concurrent.futures import ProcessPoolExecutor, as_completed
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_Convergence/scripts/two_tail')
import herglotz_test as H
import attractive_branch_points as A
import attractive_real_branch as RB
Mx = H.Mx
warnings.simplefilter('ignore')

def state(p):
    z1, z2, w, e = np.exp(p[0]), np.exp(p[1]), np.exp(p[2]), p[3]
    return Mx.HCYMix([1.0], [6*e/np.pi], [z1, z2], np.array([1.0, w]).reshape(2, 1, 1))

def first_fold(p, tau_scale):
    """First real fold of the HS branch at parameters p, below 8 |tau*|; None if there is none."""
    return RB.first_fold(state(p), 8.0*float(tau_scale))

class Tracker:
    """Warm-started pair along a parameter path, in steps small enough to stay on the same solution."""
    def __init__(self, p0, tau_guess):
        self.p = np.array(p0, float); B = H.Branch(state(self.p))
        ph = np.exp(1j*np.angle(tau_guess)); self.us = self._ray(B, ph, abs(tau_guess)*0.98)
        self.us, self.taus, ok = A.augmented_newton(B, self.us, tau_guess)
        if not ok: raise RuntimeError('start failed')
    def _ray(self, B, ph, r):
        u = B.u0.copy(); rr = 0.0; prev = None; dr = r*2e-3
        while rr < r and dr > r*1e-8:
            rn = min(rr+dr, r); pred = u if prev is None else u+(u-prev[0])*(rn-rr)/(rr-prev[1])
            un, ok = B.newton(pred, rn*ph)
            if ok and np.linalg.norm(un-pred) > 2e-4*(1+np.linalg.norm(u)): ok = False
            if not ok: dr /= 2; continue
            prev = (u, rr); u, rr = un, rn; dr = min(dr*1.25, r*5e-3)
        return u
    def move(self, q, nsteps=4):
        """Continue the pair to parameters q. Returns False if it is lost."""
        p0 = self.p.copy(); us, ts = self.us, self.taus
        for a in np.linspace(0, 1, nsteps+1)[1:]:
            B = H.Branch(state(p0+a*(np.asarray(q)-p0)))
            us2, ts2, ok = A.augmented_newton(B, us, ts)
            if not ok or abs(ts2.imag) < 1e-4*abs(ts2) or abs(ts2-ts) > 0.3*abs(ts): return False
            us, ts = us2, ts2
        self.p = np.array(q, float); self.us, self.taus = us, ts
        return True
    def ratio(self):
        tf = first_fold(self.p, abs(self.taus))
        return (0.125 if tf is None else abs(self.taus)/tf), tf

def verify(p, us, taus):
    B = H.Branch(state(p)); ph = np.exp(1j*np.angle(taus)); r = abs(taus)
    u = B.u0.copy(); rr = 0.0; prev = None; dr = r*1e-3; target = 0.9995*r
    while rr < target and dr > r*1e-9:
        rn = min(rr+dr, target); pred = u if prev is None else u+(u-prev[0])*(rn-rr)/(rr-prev[1])
        un, ok = B.newton(pred, rn*ph)
        if ok and np.linalg.norm(un-pred) > 2e-4*(1+np.linalg.norm(u)): ok = False
        if not ok: dr /= 2; continue
        prev = (u, rr); u, rr = un, rn; dr = min(dr*1.25, r*2e-3)
    return rr/r, np.linalg.norm(u-us)/np.linalg.norm(us)

class Slow(Exception): pass
def _alarm(*_): raise Slow()
BUDGET = 4800     # s per start; a start out of budget still reports its best so far

def descend(start):
    name, p0, tau0 = start
    try:
        Tr = Tracker(p0, tau0)
    except Exception as e:
        return f'{name}: start failed {e!r}'
    r0, tf0 = Tr.ratio()
    best = [r0, Tr.p.copy(), Tr.taus, tf0, Tr.us]
    def f(q):
        q = np.array(q)
        if not (0.01 <= q[3] <= 0.6) or np.exp(q[1]) > 200 or np.exp(q[0]) < 0.1 or not (1e-3 <= np.exp(q[2]) <= 1e5): return 9.0
        if not Tr.move(q): return 9.0
        r, tf = Tr.ratio()
        if r < best[0] and verify(Tr.p, Tr.us, Tr.taus)[1] < 0.1: best[:] = [r, Tr.p.copy(), Tr.taus, tf, Tr.us]
        return r
    signal.signal(signal.SIGALRM, _alarm); signal.alarm(BUDGET)
    try:
        minimize(f, Tr.p, method='Nelder-Mead', options=dict(maxiter=200, xatol=1e-3, fatol=1e-5,
                 initial_simplex=[Tr.p+d for d in np.vstack([np.zeros(4), 0.15*np.eye(4)])]))
    except Slow:
        name += ' (budget reached)'
    finally:
        signal.alarm(0)
    r, p, ts, tf, us = best
    frac, dist = verify(p, us, ts)
    return (f'{name}: ratio {r0:.4f} -> {r:.5f} at z=({np.exp(p[0]):.4f},{np.exp(p[1]):.4f}) w=K2/K1={np.exp(p[2]):.5g} eta={p[3]:.4f}; '
            f'tau*={ts.real:+.5f}{ts.imag:+.5f}i first fold={tf}; principal-sheet check: reached {frac:.4f} of the ray, |u-u*|/|u*|={dist:.2e}')

if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(float64 evidence, NOT a Lean proof)', flush=True)
    s1 = np.log([3.167849233194492, 23.880787678883983]).tolist()+[np.log(6.23157446e+01/3.77257994e-02), 0.19032415340471848]
    t1 = (0.639123+0.080379j)*3.77257994e-02
    s2 = np.log([0.53, 20.81]).tolist()+[np.log(89.431/0.023), 0.103]
    t2 = (0.3224+0.057499j)*0.023
    # states the earlier, wrong denominator pushed to: their true ratios are 1.06 - 1.10
    s3 = np.log([1.9399, 76.3415, 99996.]).tolist()+[0.537]; t3 = 0.000716037-2.15193e-05j
    s4 = np.log([0.5596, 20.6266, 9212.2]).tolist()+[0.5033]; t4 = 0.00201918+9.37081e-05j
    s5 = np.log([0.4164, 13.6545, 8815.4]).tolist()+[0.6]; t5 = 0.00210103+5.20517e-05j
    s6 = np.log([0.2733, 34.862, 99987.]).tolist()+[0.5953]; t6 = 0.000335746+7.72443e-06j
    pool = [(s1, t1), (s2, t2), (s3, t3), (s4, t4), (s5, t5), (s6, t6)]
    starts = [(f'from {i}', b, t) for i, (b, t) in enumerate(pool)]
    rng = np.random.default_rng(3)
    for i in range(18):
        base, tb = pool[i % len(pool)]
        starts.append((f'perturbed {i}', (np.array(base)+np.r_[rng.normal(0, 0.05, 3), 0.0]).tolist(), tb))
    with ProcessPoolExecutor(24) as ex:
        for fut in as_completed([ex.submit(descend, c) for c in starts]):
            print(fut.result(), flush=True)
