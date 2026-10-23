#!/usr/bin/env python3
"""F7, state B: the physical real branch reaches a real fold, and the fold lies beyond R_c.

Real Arb arithmetic (python-flint), constants and residual of `f5_competing_tails.Model`.

1. tau-chain on [0, a]: real pieces T = [t_k, t_{k+1}], Krawczyk boxes X_k (K in int X; Rump's
   theorem gives a unique real root in X_k and an invertible Jacobian for every tau in T),
   linked by a tight box at each shared end point; the first box holds the PY seed.
2. Arclength chain on the curve {(u, tau) : P(u) = tau b} through (u(a), a): unknown
   x = (u, tau), H(x; s) = [P(u) - tau b ; t.(x - x_c) - s] with a unit vector t and centre x_c,
   s in [s_k, s_{k+1}]; again Krawczyk boxes with tight links. (t, x_c) are re-anchored at the
   current point when the curve tangent turns away from t; the first piece after a re-anchor
   takes its s-range from the enclosure of t.(Y - x_c) of the last link box Y, so the link is
   kept. The curve is regular (rank [J, -b] = n) wherever the boxes are certified, also at a fold.
3. The tau-components of the arclength boxes go above tau_hi and later below tau_lo < tau_hi
   while starting at a: so tau has an interior maximum on the certified curve segment, where
   d tau / ds = 0, i.e. J(u) is singular: a fold, at tau_f >= tau_hi. The segment before the
   maximum is the continuation of the physical branch (the two chains share the root at a, and
   while d tau/ds > 0 the curve is a graph over tau).

    python3 f7_fold_turning.py <w> <a> <tau_hi> <tau_lo>
"""
from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import mpmath
import numpy as np
from flint import arb

sys.path.insert(0, str(Path(__file__).resolve().parent))
from f5_competing_tails import D, Model  # noqa: E402
import os
DEBUG = bool(os.environ.get('F7_DEBUG'))


def mp_arb(x, rel=mpmath.mpf(2)**-180):
    return arb(mpmath.nstr(x, 70), mpmath.nstr(abs(x)*rel + mpmath.mpf(2)**-1000, 5))


class RealModel:
    def __init__(self, model: Model):
        self.m = model
        self.n = 2*model.n
        self.k = Model._map(model.mpk, mp_arb)
        self.seed = [mp_arb(x, mpmath.mpf(2)**-150) for x in model.seed_mp]
        self.b = [self.k["kt"][i] for i in range(model.n)] + [arb(0)]*model.n
        self.bf = np.array(list(model.kf["kt"]) + [0.0]*model.n)

    def P(self, u):                         # residual without the tau term
        return self.m.residual(u, 0, self.k)

    def PJ(self, X):
        n = self.n
        vars_ = [D(X[i], [arb(1) if j == i else arb(0) for j in range(n)]) for i in range(n)]
        r = self.m.residual(vars_, 0, self.k)
        return [ri.v if isinstance(ri, D) else ri for ri in r], \
               [[ri.g[j] if isinstance(ri, D) else arb(0) for j in range(n)] for ri in r]

    # float helpers
    def Pf(self, u):
        return np.array(self.m.residual(list(u.astype(complex)), 0, self.m.kf), dtype=complex).real

    def Jf(self, u):
        return self.m.jac_float(u.astype(complex), 0j).real


def iv(x, r):
    return arb(float(x), float(r))


def contains_int(X, K):
    return all(X[i].contains_interior(K[i]) for i in range(len(X)))


def need(K, c):
    return np.array([max(abs(float(K[i].upper()) - c[i]), abs(float(K[i].lower()) - c[i])) for i in range(len(c))])


def krawczyk_H(rm: RealModel, xc, rad, H, HJ):
    """Generic real Krawczyk for x -> H(x) given interval evaluations H(point box), HJ(X)."""
    m = len(xc)
    X = [iv(xc[i], rad[i]) for i in range(m)]
    y = [arb(float(xc[i])) for i in range(m)]
    Jx = HJ(X)
    Cm = np.linalg.inv(np.array([[float(Jx[i][j].mid()) for j in range(m)] for i in range(m)]))
    Hy = H(y)
    K = []
    for i in range(m):
        s = y[i]
        for k in range(m):
            s -= arb(float(Cm[i, k]))*Hy[k]
        for j in range(m):
            e = arb(1 if i == j else 0)
            for k in range(m):
                e -= arb(float(Cm[i, k]))*Jx[k][j]
            s += e*(X[j] - y[j])
        K.append(s)
    return contains_int(X, K), X, K


def certify_H(rm, xc, rad, H, HJ, tries=14):
    for _ in range(tries):
        ok, X, K = krawczyk_H(rm, xc, rad, H, HJ)
        if ok:
            return X
        nd = need(K, xc)
        if not np.all(np.isfinite(nd)) or np.max(nd/(1 + np.abs(xc))) > 0.5:
            return None
        rad = np.maximum(rad, 1.3*nd)
    return None


def tau_chain(rm: RealModel, a: float, h0=1/256, log=print):
    """u-boxes for tau in [0, a]; returns the tight end box at a and the float root there."""
    n = rm.n
    u = rm.m.seed_f.real.copy()
    t, h = 0.0, h0*a
    Yprev = rm.seed
    pieces = 0
    while t < a:
        t1 = min(a, t + h)
        T = arb(0.5*(t + t1), 0.5*(t1 - t)) if t1 > t else arb(t)
        tm = 0.5*(t + t1)
        um = newton_tau(rm, u, tm); ub = newton_tau(rm, u, t1)
        ok = False
        if um is not None and ub is not None:
            v = np.linalg.solve(rm.Jf(um), rm.bf)
            rad = 3.0*np.abs(v)*(t1 - t)/2 + 2*np.abs(ub - um) + 1e-12*(1 + np.abs(um))
            Hf = lambda y: [p - T*bi for p, bi in zip(rm.P(y), rm.b)]
            HJ = lambda X: rm.PJ(X)[1]
            X = None
            for _ in range(14):
                okk, X, K = krawczyk_H(rm, um, rad, Hf, HJ)
                if okk and all(X[i].contains(Yprev[i]) for i in range(n)):
                    break
                nd = need(K, um)
                nd = np.maximum(nd, [max(abs(float(Yprev[i].upper()) - um[i]), abs(float(Yprev[i].lower()) - um[i])) for i in range(n)])
                if not np.all(np.isfinite(nd)) or np.max(nd/(1 + np.abs(um))) > 0.5:
                    X = None
                    break
                rad = np.maximum(rad, 1.3*nd)
                X = None
            if X is not None:
                Tb = arb(t1)
                Hb = lambda y: [p - Tb*bi for p, bi in zip(rm.P(y), rm.b)]
                Y = certify_H(rm, ub, 1e-10*(1 + np.abs(ub)), Hb, HJ)
                if Y is not None and all(X[i].contains(Y[i]) for i in range(n)):
                    ok = True
        if not ok:
            h /= 2
            if h < 1e-9:
                raise RuntimeError(f"tau chain: underflow at tau={t}")
            continue
        Yprev, u, t = Y, ub, t1
        pieces += 1
        h = min(h*1.5, h0*a*8)
        if log and pieces % 2000 == 0:
            log(f"  tau chain: tau={t:.5f}, pieces={pieces}")
    return Yprev, u, pieces


def newton_tau(rm, u, tau, it=30):
    for _ in range(it):
        du = np.linalg.solve(rm.Jf(u), -(rm.Pf(u) - tau*rm.bf))
        u = u + du
        if np.max(np.abs(du)) < 1e-12*(1 + np.max(np.abs(u))):
            return u
    return u if np.max(np.abs(rm.Pf(u) - tau*rm.bf)) < 1e-9 else None


def arc_chain(rm: RealModel, Y0, u0, a, tau_hi, tau_lo, ds0=2e-3, log=print, max_pieces=200000):
    """Arclength chain through (u0, a) until the tau-box drops below tau_lo after exceeding tau_hi."""
    n = rm.n
    x = np.r_[u0, a]
    # tangent of the curve: [J, -b] t = 0, oriented so that tau increases at the start
    Jf = rm.Jf(u0)
    tdir = np.r_[np.linalg.solve(Jf, rm.bf), 1.0]
    tdir /= np.linalg.norm(tdir)
    xc = x.copy()
    tdir_a = [arb(float(c)) for c in tdir]          # exact floats
    xc_a = [arb(float(c)) for c in xc]

    anchor = {"t": tdir, "xc": xc, "ta": tdir_a, "xa": xc_a}

    def H_of(S):
        ta, xa = anchor["ta"], anchor["xa"]
        def H(y):
            p = rm.P(y[:n])
            out = [p[i] - y[n]*rm.b[i] for i in range(n)]
            s = arb(0)
            for i in range(n + 1):
                s += ta[i]*(y[i] - xa[i])
            out.append(s - S)
            return out
        return H

    def HJ(X):
        _, J = rm.PJ(X[:n])
        rows = [J[i] + [-rm.b[i]] for i in range(n)]
        rows.append(list(anchor["ta"]))
        return rows

    def newton_s(xg, s):
        t, c = anchor["t"], anchor["xc"]
        # float centring only (rigour comes from Krawczyk): accept the iterate once the step
        # stalls at round-off, which near a fold is ~cond * eps, not 1e-14
        for _ in range(30):
            Jm = np.vstack([np.c_[rm.Jf(xg[:n]), -rm.bf], t])
            f = np.r_[rm.Pf(xg[:n]) - xg[n]*rm.bf, t @ (xg - c) - s]
            dx = np.linalg.solve(Jm, -f); xg = xg + dx
            if np.max(np.abs(dx)) < 1e-12*(1 + np.max(np.abs(xg))):
                return xg
        f = np.r_[rm.Pf(xg[:n]) - xg[n]*rm.bf, t @ (xg - c) - s]
        return xg if np.max(np.abs(f)) < 1e-9 else None

    def curve_tangent(xg):
        Jb = np.c_[rm.Jf(xg[:n]), -rm.bf]
        _, _, Vt = np.linalg.svd(Jb)
        v = Vt[-1]
        return v if v @ anchor["t"] > 0 else -v

    # link: the start box must contain (Y0, a) at s = 0
    prev = list(Y0) + [arb(a)]
    s, ds = 0.0, ds0
    s_lo = 0.0                     # lower end of the next piece's s-range
    reanchors = 0
    seen_hi = False
    tau_max_lower = -math.inf
    tau_max_upper = -math.inf
    pieces = 0
    while True:
        s1 = s + ds
        S = arb(0.5*(s_lo + s1), 0.5*(s1 - s_lo))
        xm = newton_s(x, 0.5*(s + s1)); xb = newton_s(x, s1)
        ok = False
        if xm is not None and xb is not None:
            Jm = np.vstack([np.c_[rm.Jf(xm[:n]), -rm.bf], tdir])
            Jm = np.vstack([np.c_[rm.Jf(xm[:n]), -rm.bf], anchor["t"]])
            v = np.linalg.solve(Jm, np.r_[np.zeros(n), 1.0])
            rad = 3.0*np.abs(v)*ds/2 + 2*np.abs(xb - xm) + 1e-12*(1 + np.abs(xm))
            X = None
            for _ in range(14):
                okk, X, K = krawczyk_H(rm, xm, rad, H_of(S), HJ)
                if okk and all(X[i].contains(prev[i]) for i in range(n + 1)):
                    break
                nd = need(K, xm)
                nd = np.maximum(nd, [max(abs(float(prev[i].upper()) - xm[i]), abs(float(prev[i].lower()) - xm[i])) for i in range(n + 1)])
                if not np.all(np.isfinite(nd)) or np.max(nd/(1 + np.abs(xm))) > 0.5:
                    X = None
                    break
                rad = np.maximum(rad, 1.3*nd)
                X = None
            if X is not None:
                Yb = certify_H(rm, xb, 1e-10*(1 + np.abs(xb)), H_of(arb(s1)), HJ)
                if Yb is not None and all(X[i].contains(Yb[i]) for i in range(n + 1)):
                    ok = True
        if not ok:
            if DEBUG:
                stage = 'newton' if (xm is None or xb is None) else ('X' if X is None else 'Y')
                print(f"    fail s={s:.6f} ds={ds:.2e} stage={stage} s_lo={s_lo:.3e} reanchors={reanchors}")
            ds /= 2
            if ds < 1e-10:
                raise RuntimeError(f"arc chain: underflow at s={s}")
            continue
        pieces += 1
        tau_box = X[n]
        tau_max_upper = max(tau_max_upper, float(tau_box.upper()))
        if float(tau_box.lower()) > tau_hi:
            seen_hi = True
            tau_max_lower = max(tau_max_lower, float(tau_box.lower()))
        if seen_hi and float(tau_box.upper()) < tau_lo:
            return dict(pieces=pieces, reanchors=reanchors, tau_hi=tau_hi, tau_lo=tau_lo,
                        tau_max_lower_bound=tau_max_lower, tau_max_upper_bound=tau_max_upper,
                        turning_point_certified=True)
        prev, x, s = Yb, xb, s1
        s_lo = s1
        ds = min(ds*1.5, ds0*8)
        tc = curve_tangent(x)
        if abs(tc @ anchor["t"]) < 0.98:         # re-anchor at the current point
            anchor["t"] = tc; anchor["xc"] = x.copy()
            anchor["ta"] = [arb(float(c)) for c in tc]; anchor["xa"] = [arb(float(c)) for c in x]
            sig = arb(0)
            for i in range(n + 1):
                sig += anchor["ta"][i]*(prev[i] - anchor["xa"][i])
            s = 0.0; s_lo = float(sig.lower()); reanchors += 1
            if float(sig.upper()) >= ds:
                raise RuntimeError("arc chain: re-anchor link wider than a step")
        if pieces > max_pieces:
            raise RuntimeError("arc chain: too many pieces")
        if log and pieces % 2000 == 0:
            log(f"  arc chain: s={s:.5f}, tau~{x[n]:.6f}, pieces={pieces}")


def main(argv):
    w, a, tau_hi, tau_lo = argv[1], float(argv[2]), float(argv[3]), float(argv[4])
    rm = RealModel(Model("0.3", ["1.8", "12"], ["1", w]))
    t0 = time.time()
    Y, u, p1 = tau_chain(rm, a)
    rec = dict(w=w, tau_chain=dict(interval=[0.0, a], pieces=p1))
    rec["arc"] = arc_chain(rm, Y, u, a, tau_hi, tau_lo)
    rec["seconds"] = round(time.time() - t0, 1)
    print(json.dumps(rec), flush=True)
    res = Path(__file__).resolve().parent/"results"
    (res/f"f7_fold_turning_w{w}.json").write_text(json.dumps(rec, indent=1) + "\n")
    return 0 if rec["arc"]["turning_point_certified"] else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
