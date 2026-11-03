"""Nearest singularity of the exact-MSA physical branch u(tau), P(u) = tau b, in complex tau.

Candidates: stable Pade poles of the Taylor series (several orders, scaled coefficients).
Each candidate is refined on the augmented system {P(u) = tau b, det DP(u) = 0} and tested
for membership of the PHYSICAL sheet: the branch is continued from tau = 0 along the
straight path to (1 - d) tau* and its distance to the fold point u* must shrink like
sqrt(d) (square-root branch point reached on this sheet).  Float64; evidence, not proof.
"""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

_HERE = Path(__file__).resolve().parent
_FOUNDATION = _HERE.parents[2]/'MSA_and_1st_Truncation'/'scripts'   # frozen 1.0.17, imported read-only
sys.path[:0] = [str(_HERE), str(_FOUNDATION/'coupling_singularities'), str(_FOUNDATION)]
from msa_coupling_series_sign_probe import residual_c, series, M  # noqa: E402


def bvec(st):
    T, N = st.T, st.N
    return np.concatenate([(2*np.pi*st.K/st.z[:, None, None]).ravel(), np.zeros(T*N*N)]).astype(complex)


def u_seed(st):
    T, N = st.T, st.N
    _, G0 = M.seed_zero_K(M.HCYMix(st.sigma, st.rho, st.z, 0*st.K))
    return np.concatenate([np.zeros(T*N*N), G0.ravel()]).astype(complex)


def jac(u, st):
    n = len(u); J = np.empty((n, n), complex)
    for j in range(n):
        e = np.zeros(n, complex); e[j] = 1.0
        cd = lambda h: (residual_c(u + h*e, st)[0] - residual_c(u - h*e, st)[0])/(2*h)
        J[:, j] = (4*cd(1e-3) - cd(2e-3))/3                  # exact: P is cubic
    return J


def newton(u, tau, st, b, tol=1e-13, it=30):
    for _ in range(it):
        r = residual_c(u, st)[0] - tau*b
        du = np.linalg.solve(jac(u, st), -r); u = u + du
        if np.linalg.norm(du) < tol*(1 + np.linalg.norm(u)):
            return u, True
    return u, np.linalg.norm(residual_c(u, st)[0] - tau*b) < 1e-9


def continue_path(st, taus, u0=None):
    """Predictor (tangent J^{-1} b) - corrector along a polyline of complex taus, adaptive."""
    b = bvec(st); u = u_seed(st) if u0 is None else u0
    t = taus[0]
    for t1 in taus[1:]:
        h = t1 - t; s = 0.0; ds = 1.0
        while s < 1.0 - 1e-15:
            ds = min(ds, 1.0 - s)
            tn = t + (s + ds)*h
            v = np.linalg.solve(jac(u, st), b)
            un, ok = newton(u + v*(tn - (t + s*h)), tn, st, b)
            if ok and np.linalg.norm(un - u) < 0.2*(1 + np.linalg.norm(u)):
                u, s = un, s + ds; ds = min(2*ds, 1.0)
            else:
                ds /= 2
                if ds < 1e-10:
                    raise RuntimeError(f"continuation stalled at tau={t + s*h}")
        t = t1
    return u


def pade_poles(c, L, Mm):
    A = np.array([[c[L + i - k] if L + i - k >= 0 else 0 for k in range(1, Mm + 1)] for i in range(1, Mm + 1)])
    q = np.linalg.solve(A, -c[L + 1:L + Mm + 1])
    return np.roots(np.r_[q[::-1], 1.0])


def candidates(st, scale, nmax=56, orders=((30, 18), (28, 22), (34, 16), (26, 24))):
    U, _ = series(st, nmax, scale)                       # coefficients in s = tau/scale
    out = []
    for j in range(U.shape[1]):
        c = U[:, j]
        if np.max(np.abs(c[1:])) < 1e-12:
            continue
        sets = [scale*pade_poles(c, L, Mm) for L, Mm in orders]
        for p in sets[0]:
            if abs(p) < 3*scale and all(min(abs(S - p)) < 0.01*abs(p) for S in sets[1:]):
                if not any(abs(p - q) < 0.01*abs(p) for q in out):
                    out.append(p)
    return sorted(out, key=abs)


def refine_fold(st, u, tau, it=60):
    b = bvec(st); n = len(u)
    def F(v):
        return np.r_[residual_c(v[:n], st)[0] - v[n]*b, np.linalg.det(jac(v[:n], st))]
    v = np.r_[u, tau].astype(complex)
    for _ in range(it):
        f = F(v); Jv = np.empty((n + 1, n + 1), complex)
        for j in range(n + 1):
            e = np.zeros(n + 1, complex); e[j] = 1e-6
            Jv[:, j] = (F(v + e) - F(v - e))/2e-6
        dv = np.linalg.solve(Jv, -f); v = v + dv
        if np.linalg.norm(dv) < 1e-13*(1 + np.linalg.norm(v)):
            break
    return v[:n], v[n], float(np.linalg.norm(F(v)))


def on_sheet(st, tau_star, u_star, ds=(1e-2, 3e-3, 1e-3)):
    """Continue along the ray 0 -> (1-d) tau*; return distances |u - u*| and their sqrt-d slopes."""
    dist = []
    for d in ds:
        u = continue_path(st, [0.0, (1 - d)*tau_star])
        dist.append(float(np.linalg.norm(u - u_star)))
    slopes = [np.log(dist[i]/dist[i + 1])/np.log(ds[i]/ds[i + 1]) for i in range(len(ds) - 1)]
    return dist, slopes


SHEET_RETRY_DS = (1e-3, 3e-4, 1e-4, 3e-5, 1e-5, 3e-6, 1e-6)


def nearest_singularity(st, scale, verbose=True, res_rel=False, sheet_retry=False):
    """Return (tau*, info) for the nearest physical-sheet singularity among Pade candidates.

    res_rel: True accepts the refined fold at residual < 1e-7*max(1, |det J|) at the seed (det J
    is O(100) at high packing, where the absolute 1e-7 rejects true folds); 'hadamard' requires
    the BH residual < 1e-9 relative to 1 + |tau||b| and |det J| < 1e-6 of the Hadamard bound
    (large amplitudes: Hadamard ~ 1e10 rejected a true on-sheet fold under True); default off.
    sheet_retry: a candidate whose sqrt-d slopes miss 1/2 at d = 1e-2..1e-3 but still approach
    (last slope > 1/4) is retried at d = 1e-3..1e-6; default off.
    """
    for p in candidates(st, scale):
        if abs(p.imag) < 1e-8*abs(p):
            kind = 'real'
        else:
            kind = 'complex'
        try:
            useed = continue_path(st, [0.0, 0.97*p])
        except RuntimeError as e:
            if verbose:
                print(f"   candidate {p:.5f}: continuation failed ({e})")
            continue
        u_s, t_s, res = refine_fold(st, useed, p)
        if res_rel == 'hadamard':
            # per-block relative residuals: BH part against 1 + |tau||b|, det J against Hadamard
            Js = jac(u_s, st)
            rP = np.linalg.norm(residual_c(u_s, st)[0] - t_s*bvec(st))/(1 + abs(t_s)*np.linalg.norm(bvec(st)))
            rD = abs(np.linalg.det(Js))/np.prod(np.linalg.norm(Js, axis=0))
            bad = rP > 1e-9 or rD > 1e-6     # rD: refine_fold's FD Jacobian floors it near 1e-8
        else:
            tol = 1e-7*max(1.0, abs(np.linalg.det(jac(useed, st)))) if res_rel else 1e-7
            bad = res > tol
        if bad or abs(t_s - p) > 0.05*abs(p):
            if verbose:
                print(f"   candidate {p:.5f}: no fold nearby (res {res:.1e}, tau {t_s:.4f})")
            continue
        try:
            dist, slopes = on_sheet(st, t_s, u_s)
        except RuntimeError as e:
            if verbose:
                print(f"   candidate {p:.5f}: ray continuation failed ({e})")
            continue
        ok = all(abs(s - 0.5) < 0.1 for s in slopes)
        if not ok and sheet_retry and slopes[-1] > 0.25:
            # near-real complex folds are not yet asymptotic at d >= 1e-3 (handoff 015: slopes
            # .669, .596 -> .503 at d = 1e-6); retry closer, require the last two slopes near 1/2
            try:
                dist2, slopes2 = on_sheet(st, t_s, u_s, ds=SHEET_RETRY_DS)
                if all(np.diff(dist2) < 0) and all(abs(s - 0.5) < 0.05 for s in slopes2[-2:]):
                    ok, dist, slopes = True, dist2, slopes2
            except RuntimeError:
                pass
        if verbose:
            print(f"   candidate {p:.5f} -> fold tau*={t_s:.6f} |tau*|={abs(t_s):.6f} res={res:.1e} "
                  f"dist(d)={np.round(dist, 5)} slopes={np.round(slopes, 3)} {'ON SHEET' if ok else 'not reached'}")
        if ok:
            return t_s, dict(kind=kind, pade=p, u=u_s, dist=dist, slopes=slopes, residual=res)
    return None, None
