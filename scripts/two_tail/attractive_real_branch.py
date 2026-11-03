"""Real HS branch of an all-attractive pure fluid by pseudo-arclength (float64 evidence, NOT a Lean proof).

msa_exact_mix.trace_coupling_mix steps in tau, so at a strong short-range tail it can jump over a
fold onto a later part of the curve: at z=(1.94,76.3), K2/K1=1e5, eta=.537 it reports its end at
tau=.0023 while the coefficients, computed without any tracking, show a real singularity at
tau=.000679. Arclength steps through folds and returns all of them, in order along the curve:
tau_1 > tau_2 < tau_3 ... is an S-curve. The first canonicity loss det F(0) = 0 is read along the same
curve. Stops at tau_max, at tau < 0, or after max_folds folds. Controls: one tail z=1.8, eta=.3 has its
known fold 1.3070; z=(1,10), K=(1,1), eta=.3 has 0.5642.

Why this matters: when the first two folds of an S-curve merge as a parameter moves, they become a
complex pair sitting on the principal sheet, near the real axis, ahead of the surviving fold, so
R = |tau*| < tau_f there unless another mechanism intervenes.
"""
import sys, warnings
import numpy as np
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_Convergence/scripts/two_tail')
import herglotz_test as H
Mx = H.Mx
warnings.simplefilter('ignore')


def state(z, K, eta):
    return Mx.HCYMix([1.0], [6*eta/np.pi], list(z), np.array(K, float).reshape(len(z), 1, 1))


def detF0(st, u):
    T, N = st.T, st.N; n2 = N*N
    Dt = u[:T*n2].reshape(T, N, N).real; Gt = u[T*n2:].reshape(T, N, N).real
    s = Mx.SolutionMix(st, Dt, Gt, Mx._pieces(st, Dt, Gt), 0.0)
    return float(np.real(s.detF(0.0)))


def arclength(st, tau_max, max_folds=4, max_steps=8000, ds0=1e-3, dsmax=0.1):
    """Returns (folds, crossings, pts). pts = list of (tau, detF0). tau is measured in units of the scale
    given by the first-order tangent, so that steps are comparable across very different K."""
    B = H.Branch(st); n = B.n; b = B.b.real; u = B.u0.real.copy()
    J0 = B.J(B.u0).real; u1 = np.linalg.solve(J0, b)
    # scales: tau_s from where the first-order change is comparable to the state; u_s per component
    us = np.maximum(np.abs(u1)*tau_max, 1e-3*(1+np.abs(u)))

    def rhs(x):
        return B.R((u_base + us*x[:n]).astype(complex)).real - x[n]*tau_max*b
    def jac(x):
        Ju = B.J((u_base + us*x[:n]).astype(complex)).real
        return np.column_stack([Ju*us, -tau_max*b])
    u_base = u.copy(); x = np.zeros(n+1)
    t = np.zeros(n+1); t[n] = 1.0
    A = jac(x); t = np.linalg.solve(np.vstack([A, t]), np.r_[np.zeros(n), 1.0]); t /= np.linalg.norm(t)
    folds, cross, pts = [], [], [(0.0, detF0(st, u))]
    ds = ds0; steps = 0
    while steps < max_steps and ds > 1e-11:
        steps += 1
        y = x + ds*t; ok = False
        for it in range(8):
            r = rhs(y); M = np.vstack([jac(y), t])
            dy = np.linalg.solve(M, np.r_[-r, -(t @ (y-x) - ds)])
            y = y + dy
            if not np.all(np.isfinite(y)): break
            if np.linalg.norm(dy) < 1e-10*(1+np.linalg.norm(y)):
                ok = True; break
        if not ok:
            ds /= 2; continue
        A = jac(y); tn = np.linalg.solve(np.vstack([A, t]), np.r_[np.zeros(n), 1.0]); tn /= np.linalg.norm(tn)
        if t @ tn < 0.97:                                    # turned too far: may have jumped a fold
            ds /= 2; continue
        if np.sign(tn[n]) != np.sign(t[n]) and t[n] != 0:
            # a turning point in tau between the two points: secant on dtau/ds
            a = t[n]/(t[n]-tn[n]); folds.append(float((x[n] + a*(y[n]-x[n]))*tau_max))
        d0 = detF0(st, u_base + us*y[:n])
        if pts[-1][1]*d0 < 0:
            cross.append(float((x[n] + pts[-1][1]/(pts[-1][1]-d0)*(y[n]-x[n]))*tau_max))
        pts.append((float(y[n]*tau_max), d0))
        x, t = y, tn
        ds = min(ds*1.3, dsmax)
        if x[n] > 1.0 or x[n] < 0.0 or len(folds) >= max_folds: break     # past the cap, or the curve left tau > 0
    return folds, cross, pts


def first_fold(st, tau_max, polish=True):
    """First fold along the arclength curve, Newton-polished on the fold system; None if no fold below tau_max."""
    import attractive_branch_points as A
    B = H.Branch(st); n = B.n; b = B.b.real; u = B.u0.real.copy()
    J0 = B.J(B.u0).real; u1 = np.linalg.solve(J0, b)
    us = np.maximum(np.abs(u1)*tau_max, 1e-3*(1+np.abs(u)))
    def rhs(x): return B.R((u + us*x[:n]).astype(complex)).real - x[n]*tau_max*b
    def jac(x): return np.column_stack([B.J((u + us*x[:n]).astype(complex)).real*us, -tau_max*b])
    x = np.zeros(n+1); t = np.zeros(n+1); t[n] = 1.0
    t = np.linalg.solve(np.vstack([jac(x), t]), np.r_[np.zeros(n), 1.0]); t /= np.linalg.norm(t)
    ds = 1e-3; steps = 0
    while steps < 4000 and ds > 1e-11:
        steps += 1
        y = x + ds*t; ok = False
        for it in range(8):
            dy = np.linalg.solve(np.vstack([jac(y), t]), np.r_[-rhs(y), -(t @ (y-x) - ds)]); y = y + dy
            if not np.all(np.isfinite(y)): break
            if np.linalg.norm(dy) < 1e-10*(1+np.linalg.norm(y)): ok = True; break
        if not ok: ds /= 2; continue
        tn = np.linalg.solve(np.vstack([jac(y), t]), np.r_[np.zeros(n), 1.0]); tn /= np.linalg.norm(tn)
        if t @ tn < 0.97: ds /= 2; continue
        if tn[n] < 0:
            a = t[n]/(t[n]-tn[n]); tau = (x[n] + a*(y[n]-x[n]))*tau_max
            if polish:
                _, ts, ok = A.augmented_newton(B, (u + us*(x[:n]+a*(y[:n]-x[:n]))).astype(complex), complex(tau))
                if ok and abs(ts.imag) < 1e-8*abs(ts) and abs(ts.real-tau) < 0.05*abs(tau): return float(ts.real)
            return float(tau)
        x, t = y, tn; ds = min(ds*1.3, 0.1)
        if x[n] > 1.0: return None
    return None


if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(float64 evidence, NOT a Lean proof)', flush=True)
    for name, z, K, e, tm in [('CONTROL one tail z=1.8', [1.8], [1.0], .3, 3.0),
                              ('z=(1,10) K=(1,1)', [1, 10], [1, 1], .3, 3.0),
                              ('z=(3.1678,23.8808) K=(.0377,62.3)', [3.167849233194492, 23.880787678883983], [3.77257994e-02, 6.23157446e+01], 0.19032415340471848, 2.0),
                              ('z=(1.9399,76.3415) w=99996', [1.9399, 76.3415], [1, 99996], .537, .004),
                              ('z=(.5596,20.6266) w=9212.2', [.5596, 20.6266], [1, 9212.2], .5033, .006)]:
        st = state(z, K, e)
        f, c, p = arclength(st, tm, max_steps=6000)
        t = np.array([q[0] for q in p]); i = int(np.argmax(t))
        after = t[i:]
        print(f'{name}: first fold (polished) {first_fold(st, tm)}; turning points on the curve {[round(v, 7) for v in f]}; det F(0) crossings {[round(v, 7) for v in c]}; '
              f'{len(p)} points; after the first fold tau is monotone decreasing: {bool(np.all(np.diff(after) < 0))}, from {after[0]:.6g} to {after[-1]:.6g}', flush=True)
