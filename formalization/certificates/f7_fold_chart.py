#!/usr/bin/env python3
"""F7, state A: the Taylor radius equals the real fold exactly, R_c = tau_f, in Arb (python-flint).

`f7_cover_arb.py` brackets R_c and `f7_fold_turning.py` brackets tau_f; this script closes the
gap with a certified chart of the solution curve at the fold.

Chart.  With a float fold point u_c, a float null vector v and c = v, write
u = u_c + s v + y with c.y = 0. The unknowns Z = (y, tau) solve

    H(Z; s) = (P(u_c + s v + y) - tau b, c.y) = 0,   dH/dZ = [[J(u), -b], [c^T, 0]],

which stays regular through the fold. A grid of s-squares (plus a ring of squares on the circle
|s| = sigma) covers the closed disc |s| <= sigma; each square gets a Krawczyk box (Rump: unique
root, dH/dZ invertible), and every two overlapping squares are glued. This gives one analytic
chart (U(s), tau(s)) on a neighbourhood of the disc, with P(U(s)) = tau(s) b and c.U'(s) = c.v != 0.
Squares on the real axis are symmetric, so tau is real for real s.

Certified facts, then the argument:

(a) On |s| = sigma, tau(s) - tau_c (tau_c the float fold value) winds twice round 0, and
    |tau(s) - tau_c| >= m_c there. tau'(s) winds once. So tau' has exactly one zero s* (real, by
    symmetry), tau_f := tau(s*) is real, and for every tau in D(tau_c, m_c), tau(s) = tau has
    exactly two roots in the disc (Rouche), simple unless tau = tau_f.
(b) tau' changes sign between two real points s_a < s_b: s* lies in [s_a, s_b], and
    tau_f lies in tau([s_a, s_b]).
(c) A tau-cover (f7_cover_arb.cover) of the closed upper half disc |tau| <= r with r >= tau_f,
    minus the open disc D_ex = D(tau_c, rho_ex): the PY branch f is analytic on a neighbourhood
    of (closed disc) minus D_ex (Schwarz reflection for the lower half).
(d) Link: at the real point tau_0 with rho_ex < tau_c - tau_0 < rho_g, the root f(tau_0) of the
    covering leaf equals U(s_0) for some s_0 in the chart (its (y, tau) decomposition lies in the
    Krawczyk box of the chart square holding s_0).

Lower bound. Let V = D(0, tau_f) and L = D(tau_c, rho_g) cap V with rho_ex < rho_g <= m_c. L is
convex and misses tau_f, so by (a) the root s(tau) of tau(s) = tau continued from s_0 is a
single-valued analytic function on L, and g = U(s(.)) is an analytic root there. The overlap
(V minus D_ex) cap L is connected (a half-annulus about tau_c) and g = f near tau_0 by (d), so
f and g glue to one analytic function on V, equal to the PY branch near 0: R_c >= tau_f.

Upper bound. If f were analytic at tau_f, then f(tau(s)) - U(s) would vanish on the open set
s(L) accumulating at s*, hence near s*, so U'(s*) = f'(tau_f) tau'(s*) = 0, contradicting
c.U'(s*) = c.v != 0. So R_c <= tau_f.

Hence R_c = tau_f, with tau_f enclosed by (b).

Run from this directory:  python3 f7_fold_chart.py [w tau_a [sigma hs rho_g rho_ex]]
(default -2.5 4.40 0.4 1/64 0.038 0.028, state A). Negative control: state B, whose fold does
not bind, must FAIL at the tau-cover: `-2.636 7.6 0.015 0.00048828125 0.0018 0.0012` (B sits near a
cusp, so its chart needs a small sigma).
"""
from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import numpy as np
from flint import acb, acb_mat, arb

sys.path.insert(0, str(Path(__file__).resolve().parent))
from f5_competing_tails import Model                       # noqa: E402
from f7_cover_arb import ArbModel, Rect, box, certify, cover, mid_matrix  # noqa: E402


# ---------------------------------------------------------------------------------- floats
def float_fold(m: Model, tau_a: float):
    """Float fold point by Newton on (P(u) - tau b, J(u) v, c0.v - 1) from the real branch."""
    n = 2*m.n
    F, J = (lambda u, t: m.f_float(u, t)), (lambda u: m.jac_float(u, 0j))
    u = m.seed_f.copy()
    for t in np.linspace(0, tau_a, int(tau_a/0.01) + 1):
        for _ in range(30):
            du = np.linalg.solve(J(u), -F(u, t)); u = u + du
            if np.max(np.abs(du)) < 1e-13*(1 + np.max(np.abs(u))):
                break
    ev, V = np.linalg.eig(J(u))
    v = V[:, np.argmin(abs(ev))].real
    c0 = v/np.linalg.norm(v)
    x = np.concatenate([u, c0, [tau_a]]).astype(complex)

    def G(x):
        return np.concatenate([F(x[:n], x[2*n]), J(x[:n]) @ x[n:2*n], [c0 @ x[n:2*n] - 1]])
    for _ in range(60):
        D = np.zeros((2*n + 1, 2*n + 1), complex)
        for i in range(2*n + 1):
            e = np.zeros(2*n + 1, complex); e[i] = 1e-6
            D[:, i] = (G(x + e) - G(x - e))/2e-6
        dx = np.linalg.solve(D, -G(x)); x = x + dx
        if np.max(abs(dx)) < 1e-14:
            break
    uf, vf = x[:n].real.copy(), x[n:2*n].real.copy()
    return uf, vf/np.linalg.norm(vf), float(x[2*n].real)


# ----------------------------------------------------------------------------------- chart
class Chart:
    def __init__(self, am: ArbModel, uc, v):
        self.am, self.n = am, am.n
        self.ucf, self.vf = np.array(uc, complex), np.array(v, complex)
        self.uc = [acb(float(x)) for x in uc]
        self.v = [acb(float(x)) for x in v]
        self.c = self.v
        self.kappa = sum((a*b for a, b in zip(self.c, self.v)), acb(0))
        self.b = [acb(x) for x in am.k["kt"]] + [acb(0)]*(am.n//2)
        self.bf = np.array(list(am.m.kf["kt"]) + [0.0]*(am.n//2), dtype=complex)

    def u_of(self, Z, S):
        return [self.uc[i] + S*self.v[i] + Z[i] for i in range(self.n)]

    def H(self, Z, S):
        n = self.n
        r = self.am.F(self.u_of(Z, S), Z[n])
        return list(r) + [sum((self.c[i]*Z[i] for i in range(n)), acb(0))]

    def H_mv(self, y, S, smid):
        """H(y, S) in mean-value form in s: H(y, smid) + J(U) v (S - smid), U = u(y, S); the
        natural extension over S is ~|J||v||S| wide, while J v is nearly 0 at the fold."""
        n = self.n
        H0 = self.H(y, smid)
        J = self.am.Jc(self.u_of(y, S), self.u_of(y, smid))
        dS = S - smid
        return [H0[i] + sum((J[i][j]*self.v[j] for j in range(n)), acb(0))*dS for i in range(n)] + [H0[n]]

    def M(self, X, S, y, smid):
        """dH/dZ over the box X (and S), centred at the point y (and smid)."""
        n = self.n
        J = self.am.Jc(self.u_of(X, S), self.u_of(y, smid))
        return [list(J[i]) + [-self.b[i]] for i in range(n)] + [list(self.c) + [acb(0)]]

    # floats
    def Hf(self, z, s):
        u = self.ucf + s*self.vf + z[:self.n]
        return np.concatenate([self.am.m.f_float(u, z[self.n]), [self.vf @ z[:self.n]]])

    def Mf(self, z, s):
        n = self.n
        u = self.ucf + s*self.vf + z[:n]
        out = np.zeros((n + 1, n + 1), complex)
        out[:n, :n] = self.am.m.jac_float(u, 0j); out[:n, n] = -self.bf; out[n, :n] = self.vf
        return out

    def newton(self, z, s):
        for _ in range(40):
            d = np.linalg.solve(self.Mf(z, s), -self.Hf(z, s)); z = z + d
            if np.max(np.abs(d)) < 1e-13*(1 + np.max(np.abs(z))):
                break
        return z

    def tangent(self, z, s):
        n = self.n
        u = self.ucf + s*self.vf + z[:n]
        rhs = np.concatenate([self.am.m.jac_float(u, 0j) @ self.vf, [0]])
        return -np.linalg.solve(self.Mf(z, s), rhs)

    # Krawczyk on Z with parameter ball S
    def K(self, zm, X, S, smid, sym):
        n1 = self.n + 1
        y = [acb(float(zm[i].real)) if sym else acb(complex(zm[i])) for i in range(n1)]
        Mx = self.M(X, S, y, acb(smid))
        Cm = np.linalg.inv(mid_matrix(Mx))
        Ca = [[acb(complex(Cm[i, j])) for j in range(n1)] for i in range(n1)]
        Hy = self.H_mv(y, S, acb(smid))
        out = []
        for i in range(n1):
            t = y[i]
            for k in range(n1):
                t -= Ca[i][k]*Hy[k]
            for j in range(n1):
                e = acb(1 if i == j else 0)
                for k in range(n1):
                    e -= Ca[i][k]*Mx[k][j]
                t += e*(X[j] - y[j])
            out.append(t)
        return out

    def certify(self, zm, S, smid, span, sym, tries=8):
        v = self.tangent(zm, smid)
        rad = 3.0*np.abs(v)*span + 1e-12*(1 + np.abs(zm))
        for _ in range(tries):
            X = box(zm, rad, sym)
            Kx = self.K(zm, X, S, smid, sym)
            if all(X[i].contains_interior(Kx[i]) for i in range(len(X))):
                return X, Kx
            nd = np.array([max(abs(float(k.real.upper()) - zm[i].real), abs(float(k.real.lower()) - zm[i].real),
                               abs(float(k.imag.upper()) - zm[i].imag), abs(float(k.imag.lower()) - zm[i].imag))
                           for i, k in enumerate(Kx)])
            if not np.all(np.isfinite(nd)):
                return None, None
            rad = np.maximum(rad, 1.3*nd)
        return None, None

    def tight(self, zm, X, S, smid, sym, its=3):
        """Shrink an enclosure: every root in X lies in K(X)."""
        for _ in range(its):
            X = self.K(zm, X, S, smid, sym)
        return X

    def dtau(self, X, S, smid, zm, sym):
        """Enclosure of tau'(s) over S from the root box X: (y', tau') = -M^-1 (J v, 0)."""
        n = self.n
        y = [acb(float(zm[i].real)) if sym else acb(complex(zm[i])) for i in range(n + 1)]
        Mx = self.M(X, S, y, acb(smid))
        J = self.am.Jc(self.u_of(X, S), self.u_of(y, acb(smid)))
        rhs = [sum((J[i][j]*self.v[j] for j in range(n)), acb(0)) for i in range(n)] + [acb(0)]
        sol = acb_mat(Mx).solve(acb_mat([[-r] for r in rhs]))
        return sol[n, 0]


def sq(cx, cy, h, sym=False):
    return Rect(cx - h, cx + h, -h, h) if sym else Rect(cx - h, cx + h, cy - h, cy + h)


def sball(r: Rect):
    return acb(arb(0.5*(r.x0 + r.x1), 0.5*(r.x1 - r.x0)), arb(0.5*(r.y0 + r.y1), 0.5*(r.y1 - r.y0)))


def winding(encl):
    """Winding number round 0 of a closed chain of enclosures (consecutive ones share a point
    of the curve and the curve between them lies in their union). Returns (W, ok)."""
    arcs = []
    for e in encl:
        if e.contains(acb(0)):
            return None, False
        c = complex(float(e.real.mid()), float(e.imag.mid()))
        ca = acb(c)
        rot = e*acb(c.conjugate())
        if not float(rot.real.lower()) > 0:
            return None, False
        th = ca.arg() + rot.arg()
        arcs.append((float(th.lower()), float(th.upper())))
    tot, prev = 0.0, arcs[0]
    lo0 = arcs[0][0]
    cur_lo, cur_hi = arcs[0]
    for lo, hi in arcs[1:] + [arcs[0]]:
        # unwrap the new interval next to the current one; they must overlap
        k = round(((cur_lo + cur_hi) - (lo + hi))/2/(2*math.pi))
        lo, hi = lo + 2*math.pi*k, hi + 2*math.pi*k
        if hi < cur_lo or lo > cur_hi or max(hi, cur_hi) - min(lo, cur_lo) > math.pi:
            return None, False
        cur_lo, cur_hi = lo, hi
    W = (cur_lo - lo0)/(2*math.pi)
    Wr = round(W)
    return Wr, abs(W - Wr) < 0.25


def main(argv):
    w = argv[1] if len(argv) > 1 else "-2.5"
    tau_a = float(argv[2]) if len(argv) > 2 else 4.40        # real-branch start for the float fold
    sigma, hs, rho_g, rho_ex = (0.4, 1/64, 0.038, 0.028) if len(argv) < 7 else map(float, argv[3:7])
    t0 = time.time()
    am = ArbModel(Model("0.3", ["1.8", "12"], ["1", w]))
    uc, v, tau_c = float_fold(am.m, tau_a)
    ch = Chart(am, uc, v)
    n1 = am.n + 1
    rec = dict(w=w, eta="0.3", z=["1.8", "12"], tau_c=tau_c, u_c=list(uc), v=list(v),
               sigma=sigma, grid_half_size=hs, rho_g=rho_g, rho_ex=rho_ex)
    kap = ch.kappa
    rec["c_dot_v"] = [float(kap.real.lower()), float(kap.real.upper())]
    assert not kap.contains(acb(0))
    print(f"fold (float) tau_c = {tau_c:.12f}; c.v = {kap}", flush=True)

    # ---- chart pieces: grid squares meeting the closed disc, plus a ring on |s| = sigma
    pieces = []
    N = int(math.ceil(sigma/(2*hs))) + 1
    for j in range(-N, N + 1):
        for i in range(-N, N + 1):
            r = sq((2*i + 1)*hs, 2*j*hs, hs, sym=(j == 0))
            dx = 0.0 if r.x0 <= 0 <= r.x1 else min(abs(r.x0), abs(r.x1))
            dy = 0.0 if r.y0 <= 0 <= r.y1 else min(abs(r.y0), abs(r.y1))
            if math.hypot(dx, dy) <= sigma:
                pieces.append(r)
    ngrid = len(pieces)
    Nc = 256
    pts = [sigma*complex(math.cos(2*math.pi*k/Nc), math.sin(2*math.pi*k/Nc)) for k in range(Nc)]
    pts[0], pts[Nc//2] = complex(sigma, 0.0), complex(-sigma, 0.0)
    hc = 1.01*abs(pts[1] - pts[0])
    ring = []
    for k, p in enumerate(pts):
        r = sq(p.real, p.imag, hc, sym=(k in (0, Nc//2)))
        ring.append(r); pieces.append(r)
    # certify, centres by continuation from s = 0 outwards
    order = sorted(range(len(pieces)), key=lambda k: abs(pieces[k].mid))
    zf = {}
    z0 = np.concatenate([np.zeros(am.n), [tau_c]]).astype(complex)
    for k in order:
        r = pieces[k]
        s = r.mid
        near = min(zf, key=lambda q: abs(pieces[q].mid - s)) if zf else None
        start = z0 if near is None else zf[near]
        zm = ch.newton(start.copy(), s)
        if r.sym:
            zm = zm.real + 0j
        X, Kx = ch.certify(zm, sball(r), s, r.span, r.sym)
        if X is None:
            raise SystemExit(f"FAIL: chart square at s = {s:.4f}")
        r.u, r.X = zm, X
        zf[k] = zm
    print(f"chart: {len(pieces)} squares certified ({ngrid} grid, {Nc} ring), {time.time() - t0:.0f}s", flush=True)

    # ---- glue every two overlapping squares
    pairs = fb = 0
    for a in range(len(pieces)):
        for bb in range(a + 1, len(pieces)):
            s_, t_ = pieces[a], pieces[bb]
            lx, hx = max(s_.x0, t_.x0), min(s_.x1, t_.x1)
            ly, hy = max(s_.y0, t_.y0), min(s_.y1, t_.y1)
            if lx > hx or ly > hy:
                continue
            Sint = acb(arb(0.5*(lx + hx), 0.5*(hx - lx)), arb(0.5*(ly + hy), 0.5*(hy - ly)))
            Ks = ch.K(s_.u, s_.X, Sint, s_.mid, s_.sym)
            pairs += 1
            if all(t_.X[i].contains(Ks[i]) for i in range(n1)):
                continue
            fb += 1
            sp = complex(0.5*(lx + hx), 0.5*(ly + hy))
            zp = ch.newton(s_.u.copy(), sp)
            Y, _ = ch.certify(zp, acb(sp), sp, 0.0, False)
            if Y is None or not all(s_.X[i].contains(Y[i]) and t_.X[i].contains(Y[i]) for i in range(n1)):
                raise SystemExit(f"FAIL: chart gluing between {s_.mid:.4f} and {t_.mid:.4f}")
    rec["chart"] = dict(squares=len(pieces), grid=ngrid, ring=Nc, ring_half_size=hc, glued_pairs=pairs,
                        glued_by_point=fb)
    print(f"chart glued: {pairs} pairs ({fb} by point), {time.time() - t0:.0f}s", flush=True)

    # ---- (a) windings on the ring
    et, ed = [], []
    for r in ring:
        Xt = ch.tight(r.u, r.X, sball(r), r.mid, r.sym)
        et.append(Xt[am.n] - acb(tau_c))
        ed.append(ch.dtau(Xt, sball(r), r.mid, r.u, r.sym))
    W_tau, ok1 = winding(et)
    W_dtau, ok2 = winding(ed)
    m_c = min(float((abs(e)).lower()) for e in et)
    rec["ring"] = dict(winding_tau_minus_tau_c=W_tau, winding_dtau=W_dtau, m_c=m_c)
    print(f"ring: winding(tau - tau_c) = {W_tau} ({ok1}), winding(tau') = {W_dtau} ({ok2}), m_c = {m_c:.5f}",
          flush=True)
    if not (ok1 and ok2 and W_tau == 2 and W_dtau == 1 and rho_ex < rho_g <= m_c):
        raise SystemExit("FAIL: ring conditions")

    # ---- (b) s* and tau_f
    def real_piece(sa, sb):
        mid = 0.5*(sa + sb)
        # every symmetric grid square meeting [sa, sb]; the box must lie in each of their boxes,
        # so the root on the piece is the chart root (uniqueness in each host box)
        hosts = [r for r in pieces[:ngrid] if r.sym and r.x0 <= sb and sa <= r.x1]
        if not hosts:
            return None
        zm = ch.newton(hosts[0].u.copy(), mid).real + 0j
        S = acb(arb(mid, 0.5*(sb - sa)), arb(0))
        X, _ = ch.certify(zm, S, mid, 0.5*(sb - sa), True)
        if X is None or not all(h.X[i].contains(X[i]) for h in hosts for i in range(n1)):
            return None
        return ch.tight(zm, X, S, mid, True), zm, S
    # float s*: secant on the real tau'
    def dtf(s):
        z = ch.newton(np.concatenate([np.zeros(am.n), [tau_c]]).astype(complex), s)
        return ch.tangent(z, s)[am.n].real
    sa_, sb_ = -0.05, 0.05
    for _ in range(80):
        sm = 0.5*(sa_ + sb_)
        if dtf(sa_)*dtf(sm) <= 0:
            sb_ = sm
        else:
            sa_ = sm
    s_star = 0.5*(sa_ + sb_)
    dlt = 2.0**-24
    sa, sb = math.floor(s_star/dlt)*dlt - dlt, math.floor(s_star/dlt)*dlt + 2*dlt
    Pa, Pb, Pab = real_piece(sa, sa), real_piece(sb, sb), real_piece(sa, sb)
    if Pa is None or Pb is None or Pab is None:
        raise SystemExit("FAIL: real pieces at s*")
    da = ch.dtau(Pa[0], Pa[2], sa, Pa[1], True)
    db = ch.dtau(Pb[0], Pb[2], sb, Pb[1], True)
    sign_ok = (float(da.real.lower()) > 0 and float(db.real.upper()) < 0) or \
              (float(da.real.upper()) < 0 and float(db.real.lower()) > 0)
    tf = Pab[0][am.n].real
    tf_lo, tf_hi = float(tf.lower()), float(tf.upper())
    rec["fold"] = dict(s_a=sa, s_b=sb, dtau_a=str(da), dtau_b=str(db), sign_change=sign_ok,
                       tau_f=[tf_lo, tf_hi])
    print(f"s* in [{sa:.9f}, {sb:.9f}]: tau'(s_a) = {da}, tau'(s_b) = {db}; tau_f in [{tf_lo:.12f}, {tf_hi:.12f}]",
          flush=True)
    if not sign_ok:
        raise SystemExit("FAIL: no sign change of tau'")
    if not abs(tf_hi - tau_c) + rho_ex < rho_g:
        raise SystemExit("FAIL: tau_f too far from tau_c")

    # ---- (c) tau-cover of the half disc |tau| <= r minus D(tau_c, rho_ex)
    r_lo = math.nextafter(tf_hi, math.inf)
    leaves = []
    try:
        crec = cover(am, r_lo, exclude=(complex(tau_c, 0.0), rho_ex), leaves_out=leaves)
    except RuntimeError as e:
        raise SystemExit(f"FAIL: tau cover: {e}")
    rec["tau_cover"] = crec
    print(f"tau cover r = {r_lo:.12f} minus D(tau_c, {rho_ex}): certified = {crec['certified']}, "
          f"{crec['rectangles']} leaves, {time.time() - t0:.0f}s", flush=True)
    if not crec["certified"]:
        raise SystemExit("FAIL: tau cover")

    # ---- (d) link at tau_0
    tau0 = tau_c - 0.5*(rho_ex + rho_g)
    T = [L for L in leaves if L.sym and L.x0 <= tau0 <= L.x1][0]
    u0 = am.m.newton(T.u, complex(tau0, 0))
    if u0 is None:
        u0 = T.u
    Y, _ = certify(am, u0.real + 0j, acb(tau0), np.zeros(am.n), 0.0, True)
    if Y is None or not all(T.X[i].contains(Y[i]) for i in range(am.n)):
        raise SystemExit("FAIL: link box at tau_0")
    s0 = sum((ch.c[i]*(Y[i] - ch.uc[i]) for i in range(am.n)), acb(0))/kap
    y0 = [Y[i] - ch.uc[i] - s0*ch.v[i] for i in range(am.n)]
    Z0 = y0 + [acb(tau0)]
    host = [r for r in pieces if r.x0 < float(s0.real.lower()) and float(s0.real.upper()) < r.x1
            and r.y0 < float(s0.imag.lower()) and float(s0.imag.upper()) < r.y1]
    linked = any(all(r.X[i].contains(Z0[i]) for i in range(n1)) for r in host)
    rec["link"] = dict(tau_0=tau0, s_0=str(s0), leaf=[T.x0, T.x1, T.y0, T.y1], linked=linked)
    print(f"link at tau_0 = {tau0:.6f}: s_0 = {s0}, in chart box: {linked}", flush=True)
    if not linked:
        raise SystemExit("FAIL: link")

    rec["R_c_equals_tau_f"] = True
    rec["R_c"] = [tf_lo, tf_hi]
    rec["seconds"] = round(time.time() - t0, 1)
    out = Path(__file__).resolve().parent/"results"/f"f7_fold_chart_w{w}.json"
    out.write_text(json.dumps(rec, indent=1) + "\n")
    print(f"PASS: R_c = tau_f in [{tf_lo:.12f}, {tf_hi:.12f}]  ({rec['seconds']} s)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
