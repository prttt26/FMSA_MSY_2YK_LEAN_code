"""FLOAT evidence only: pseudo-arclength continuation in (u, tau), at fixed w, of the two real M2 roots.
r1 is the certified root; r2 is the homotopy root at relative distance 0.04 (two_tail_fiber_diag).
It records where each branch goes, its folds (sign changes of dtau/ds), and the closest approach of
r2's branch to r1.  Literal Lean residual (two_tail_fiber_diag.make_residual); finite-difference
Jacobian.  Not a certificate.

Usage: two_tail_m2_branch_explore.py
"""
import sys, json, numpy as np
print('#', ' '.join(sys.orig_argv))
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from two_tail_fiber_diag import make_residual
d = json.load(open(Path(__file__).resolve().parents[2]/'results'/'two_tail'/'two_tail_fiber_diag.json'))
c = d['controls'][0]; tb = c['beta']
from two_tail_margin import state
st0 = state(c['z'][0], c['z'][1], c['w'], c['eta'])
rho, sig, z, K0 = float(st0.rho[0]), float(st0.sigma[0]), st0.z, st0.K[:, 0, 0]
def R(x):  # x = (u0..u3, tau)
    return make_residual(rho, sig, z, x[4]*K0)(x[:4].astype(complex)).real
def Jx(x, h=1e-7):
    J = np.empty((4, 5))
    for j in range(5):
        e = np.zeros(5); e[j] = h*(1 + abs(x[j])); J[:, j] = (R(x + e) - R(x - e))/(2*e[j])
    return J
def tangent(x, prev=None):
    t = np.linalg.svd(Jx(x))[2][-1]
    if prev is not None and t @ prev < 0: t = -t
    return t
def trace(x, t, ds=0.05, n=4000, tau_rng=(-1, 3*tb), umax=1e4):
    pts = [x.copy()]; folds = []
    for it in range(n):
        xp = x + ds*t; y = xp.copy()
        for _ in range(12):
            F = np.concatenate([R(y), [t @ (y - xp)]]); A = np.vstack([Jx(y), t])
            dy = np.linalg.solve(A, -F); y += dy
            if np.linalg.norm(dy) < 1e-12*(1 + np.linalg.norm(y)): break
        else:
            ds *= 0.5
            if ds < 1e-8: break
            continue
        tn = tangent(y, t)
        if np.sign(tn[4]) != np.sign(t[4]) and abs(t[4]) > 0: folds.append(y.copy())
        x, t = y, tn; pts.append(x.copy()); ds = min(ds*1.3, 0.5)
        if not (tau_rng[0] < x[4] < tau_rng[1]) or np.max(np.abs(x[:4])) > umax: break
    return np.array(pts), folds
r1 = np.array(c['u_traced'] + [tb])
r2u = next(g for g in c['distinct_roots'] if g['real'] and g['dist_to_traced'] > 1e-3 and g['dist_to_traced'] < 0.1)['u']
r2 = np.array([a for a, b in r2u] + [tb])
print('r1', r1, '|R|', np.abs(R(r1)).max()); print('r2', r2, '|R|', np.abs(R(r2)).max())
for name, x0 in (('r1', r1), ('r2', r2)):
    t0 = tangent(x0)
    print(f"\n{name}: tangent {np.round(t0, 4)}; sv(J_u) = {np.round(np.linalg.svd(Jx(x0)[:, :4], compute_uv=False), 5)}")
    for sgn in (+1, -1):
        pts, folds = trace(x0, sgn*t0)
        dist_r1 = None
        print(f"  dir {sgn:+d}: {len(pts)} pts, tau range [{pts[:,4].min():.5f}, {pts[:,4].max():.5f}], end tau {pts[-1,4]:.5f}, "
              f"end u {np.round(pts[-1,:4], 4)}; folds at tau {[round(f[4], 6) for f in folds]}")
        if name == 'r2':
            dd = np.min(np.max(np.abs(pts[:, :4] - r1[:4])/np.maximum(1, np.abs(r1[:4])), axis=1) + np.abs(pts[:, 4] - tb)/tb)
            print(f"     closest approach of r2's branch to r1 in (u,tau): {dd:.3e}")
