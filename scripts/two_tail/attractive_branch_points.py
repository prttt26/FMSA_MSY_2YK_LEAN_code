"""Locate branch points tau* of all-attractive pure fluids near the positive real axis
(float64 evidence, NOT a Lean proof).

Tracks the HS root along rays tau = r e^{i theta}, theta small, watching |det J(u)| relative to its
value at the seed. Each local minimum seeds a Newton solve of the augmented system
    R(u) - tau b = 0,   J(u) v = 0,   c.v = 1
for (u, tau, v). A converged solution with the tracked root as seed is a branch point on, or next
to, the sheet of the HS branch. Reported: tau*, |tau*| / tau_f, arg tau*. The real fold is the
theta -> 0 solution. |tau*| < tau_f in an all-attractive state would contradict R = tau_f.
"""
import sys, warnings
import numpy as np
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_Convergence/scripts/two_tail')
import herglotz_test as H
Mx = H.Mx
warnings.simplefilter('ignore')

def augmented_newton(B, u, tau, iters=40):
    n = B.n
    J = B.J(u); _, s, Vh = np.linalg.svd(J); v = Vh[-1].conj(); c = v.conj()
    x = np.r_[u, tau, v/(c@v)]
    def G(x):
        uu, t, vv = x[:n], x[n], x[n+1:]
        Jv = (B.R(uu+1e-4*vv) - B.R(uu-1e-4*vv))/2e-4     # central difference: O(h^2 C(v,v,v)), corrected below
        Jv2 = (B.R(uu+2e-4*vv) - B.R(uu-2e-4*vv))/4e-4
        return np.r_[B.R(uu)-t*B.b, (4*Jv-Jv2)/3, c@vv-1]
    for _ in range(iters):
        g = G(x)
        if np.linalg.norm(g) < 1e-10*(1+np.linalg.norm(x)): return x[:n], x[n], True
        m = len(x); A = np.empty((m, m), complex)
        for j in range(m):
            e = np.zeros(m, complex); e[j] = 1e-6*(1+abs(x[j]))
            A[:, j] = (G(x+e)-G(x-e))/(2*e[j])
        x = x - np.linalg.solve(A, g)
        if not np.all(np.isfinite(x)): return None, None, False
    return x[:n], x[n], np.linalg.norm(G(x)) < 1e-8*(1+np.linalg.norm(x))

def scan(name, st, tf, thetas=(0.5, 1, 2, 3, 5, 8, 12, 16, 20, 30, 45, 60, 90), rmax=3.0):
    B = H.Branch(st); d0 = abs(np.linalg.det(B.J(B.u0))); found = {}
    for th in thetas:
        ph = np.exp(1j*np.deg2rad(th)); u = B.u0.copy(); r = 0.0; prev = None; dr = tf*2e-3; hist = []
        while r < rmax*tf and dr > tf*1e-7:
            rn = min(r+dr, rmax*tf); pred = u if prev is None else u+(u-prev[0])*(rn-r)/(r-prev[1])
            un, ok = B.newton(pred, rn*ph)
            if ok and np.linalg.norm(un-pred) > 2e-4*(1+np.linalg.norm(u)): ok = False
            if not ok: dr /= 2; continue
            prev = (u, r); u, r = un, rn; dr = min(dr*1.25, tf*5e-3)
            hist.append((r, abs(np.linalg.det(B.J(u)))/d0, u.copy()))
        ds = np.array([h[1] for h in hist])
        for i in np.where((ds[1:-1] < ds[:-2]) & (ds[1:-1] < ds[2:]))[0]+1:
            uu, tt, ok = augmented_newton(B, hist[i][2], hist[i][0]*ph)
            if ok and tt is not None and abs(tt) > 1e-6*tf:
                key = (round(tt.real/tf, 5), round(abs(tt.imag)/tf, 5))
                found[key] = tt
    print(f'{name} (tau_f={tf:.5f})', flush=True)
    for k, t in sorted(found.items(), key=lambda kv: abs(kv[1])):
        print(f'   tau* = {t.real:+.6f} {abs(t.imag):+.6f}i  |tau*|/tau_f = {abs(t)/tf:.5f}  arg = {np.degrees(np.angle(t)):+.3f} deg', flush=True)
    if not found: print('   no branch point found in the scanned sector', flush=True)

if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(float64 evidence, NOT a Lean proof)')
    eta = lambda e: 6*e/np.pi
    pure = lambda z, K, e: Mx.HCYMix([1.0], [e*6/np.pi], list(z), np.array(K, float).reshape(len(z), 1, 1))
    for name, z, K, e in [('CONTROL one tail z=1.8', [1.8], [1.0], 0.3),
                          ('two attr z=(3.1678,23.8808)', [3.167849233194492, 23.880787678883983], [3.77257994e-02, 6.23157446e+01], 0.19032415340471848),
                          ('two attr z=(0.53,20.81)', [0.53, 20.81], [0.023, 89.431], 0.103),
                          ('two attr z=(1,10) K=(1,1)', [1, 10], [1, 1], 0.3)]:
        st = pure(z, K, e); tf = Mx.trace_coupling_mix(st, lam_max=8.0)[-1][0]
        scan(name, st, tf)
