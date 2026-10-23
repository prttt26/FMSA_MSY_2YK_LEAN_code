#!/usr/bin/env python3
"""F5 certificate: real solvability does not imply convergence of the coupling series.

System: exact MSA (Blum-Hoye) for one hard-sphere species with n Yukawa tails, in the
unknowns u = (Dt_1..Dt_n, G_1..G_n), coupling K = tau * kv:

    R1_u = Dt_u F_u - 2 pi tau kv_u / z_u,     R2_u = 2 pi G_u F_u - src_u,

exactly the unnormalised residual of `release/fmsa_mixture/paper/msa_series_radius.py`
(`residuals`), re-implemented here independently. R is a polynomial of degree 3 in u and
affine in tau, hence entire in (u, tau). The PY seed is u(0) = (0, G0) with
G0 = (A0 + z qp0) / (2 pi z^2 F0).

Two validated continuations (rigorous outward-rounded interval arithmetic; complex
numbers as rectangles; Krawczyk operator with explicit contraction bound):

1. Real segment tau in [0, tau_max]. Each piece [a, b] gets a box X, symmetric about the
   real axis, with K(X) inside int X and ||I - C J(X)|| < 1 for all tau in [a, b]. Hence
   exactly one root in X for every such tau; by conjugation symmetry it is real; the
   Jacobian is invertible there (no fold). Consecutive pieces are linked through the
   shared end point tau_b: a small box Y_b, itself Krawczyk-certified at tau_b alone, lies
   inside both X_k and X_{k+1}, so the two unique roots coincide at tau_b. The first box
   contains an enclosure of the PY seed. So the PY-seeded branch
   extends as a real regular branch over [0, tau_max].

2. Monodromy loop: the same chain from 0 to r, then around |tau| = r. If the Krawczyk
   enclosure at the end of the loop is disjoint from the one at the start, the analytic
   continuation of the branch around the circle does not return to its start. If the
   Taylor radius R_c of the branch at 0 exceeded r, the series sum S would be analytic on
   a disc containing the closed disc |tau| <= r, would solve R (identity theorem; R is
   entire), and by a clopen argument would coincide with the unique root in every box of
   the chain; it is single-valued, a contradiction. Hence R_c <= r.

With r < tau_max = 3: the branch is real at tau = 3, yet the Taylor series diverges there.

    python3 f5_competing_tails.py            # writes results/f5_competing_tails.json
"""
from __future__ import annotations

import cmath
import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path

import mpmath
import numpy as np

mpmath.mp.prec = 200
INF = math.inf


def dn(x):
    return math.nextafter(x, -INF)


def up(x):
    return math.nextafter(x, INF)


# ----------------------------------------------------------------------------- intervals
class I:
    """Closed real interval with outward rounding after every float operation."""
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo = lo
        self.hi = lo if hi is None else hi
        assert self.lo <= self.hi, (lo, hi)

    @staticmethod
    def of(x):
        return x if isinstance(x, I) else I(x, x)

    def __add__(self, o):
        if isinstance(o, (C, D)):
            return NotImplemented
        o = I.of(o)
        return I(dn(self.lo + o.lo), up(self.hi + o.hi))

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, o):
        if isinstance(o, (C, D)):
            return NotImplemented
        return self + (-I.of(o))

    def __rsub__(self, o):
        return I.of(o) + (-self)

    def __mul__(self, o):
        if isinstance(o, (C, D)):
            return NotImplemented
        o = I.of(o)
        p = (self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi)
        return I(dn(min(p)), up(max(p)))

    __rmul__ = __mul__

    def inv(self):
        assert self.lo > 0 or self.hi < 0, "division by an interval containing 0"
        return I(dn(1.0 / self.hi), up(1.0 / self.lo))

    def __truediv__(self, o):
        return self * I.of(o).inv()

    def mag(self):
        return max(abs(self.lo), abs(self.hi))

    def mid(self):
        return 0.5 * (self.lo + self.hi)

    def rad(self):
        return up(max(up(self.hi - self.mid()), up(self.mid() - self.lo)))

    def inside(self, o):            # self strictly inside o
        return o.lo < self.lo and self.hi < o.hi

    def disjoint(self, o):
        return self.hi < o.lo or o.hi < self.lo

    def hull(self, o):
        return I(min(self.lo, o.lo), max(self.hi, o.hi))


def iv_from_mp(lo, hi):
    """Float interval containing the mpmath reals [lo, hi] (computed at 200 bits)."""
    return I(dn(float(lo)), up(float(hi)))


def exact(dec: str) -> I:
    """Enclosure of an exact decimal constant such as '1.8'."""
    f = Fraction(dec)
    x = float(f)
    return I(dn(x), up(x)) if Fraction(x) != f else I(x, x)


def mp_exact(dec: str):
    return mpmath.mpf(Fraction(dec).numerator) / Fraction(dec).denominator


class C:
    """Complex rectangle re + i im."""
    __slots__ = ("re", "im")

    def __init__(self, re, im=None):
        self.re = I.of(re)
        self.im = I.of(0.0) if im is None else I.of(im)

    @staticmethod
    def of(x):
        if isinstance(x, C):
            return x
        if isinstance(x, complex):
            return C(x.real, x.imag)
        return C(x)

    def __add__(self, o):
        o = C.of(o)
        return C(self.re + o.re, self.im + o.im)

    __radd__ = __add__

    def __neg__(self):
        return C(-self.re, -self.im)

    def __sub__(self, o):
        return self + (-C.of(o))

    def __rsub__(self, o):
        return C.of(o) + (-self)

    def __mul__(self, o):
        o = C.of(o)
        return C(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)

    __rmul__ = __mul__

    def mag(self):                  # upper bound of |x| over the rectangle
        return up(math.hypot(self.re.mag(), self.im.mag()) * (1 + 4e-16))

    def mid(self):
        return complex(self.re.mid(), self.im.mid())

    def inside(self, o):
        return self.re.inside(o.re) and self.im.inside(o.im)

    def disjoint(self, o):
        return self.re.disjoint(o.re) or self.im.disjoint(o.im)

    def hull(self, o):
        return C(self.re.hull(o.re), self.im.hull(o.im))


def ball(c: complex, rre: float, rim: float) -> C:
    return C(I(dn(c.real - rre), up(c.real + rre)), I(dn(c.imag - rim), up(c.imag + rim)))


# ------------------------------------------------------------------- forward-mode AD
class D:
    """Value plus gradient over a ring of scalars (complex floats or rectangles)."""
    __slots__ = ("v", "g")

    def __init__(self, v, g):
        self.v, self.g = v, g

    def __add__(self, o):
        if isinstance(o, D):
            return D(self.v + o.v, [a + b for a, b in zip(self.g, o.g)])
        return D(self.v + o, self.g)

    __radd__ = __add__

    def __neg__(self):
        return D(-self.v, [-a for a in self.g])

    def __sub__(self, o):
        return self + (-o)

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, o):
        if isinstance(o, D):
            return D(self.v * o.v, [self.v * b + o.v * a for a, b in zip(self.g, o.g)])
        return D(self.v * o, [a * o for a in self.g])

    __rmul__ = __mul__


# --------------------------------------------------------------------- the BH system
class Model:
    """Constants of the n-tail Blum-Hoye system, as float values and as enclosures."""

    def __init__(self, eta: str, z: list[str], kv: list[str]):
        self.label = dict(eta=eta, z=z, kv=kv)
        self.n = len(z)
        mp = mpmath
        e, zs, ks = mp_exact(eta), [mp_exact(s) for s in z], [mp_exact(s) for s in kv]
        rho = 6 * e / mp.pi
        d = 2 * mp.pi / (1 - e) ** 2
        A0, B0, qp0 = d * (1 + 2 * e), d * (-mp.mpf(3) / 2 * e), d * (mp.mpf(3) / 2 * e + 1 - e)
        ez = [mp.exp(-zz) for zz in zs]
        phi1 = [(1 - zz - mp.exp(-zz)) / zz ** 2 for zz in zs]
        phi2 = [(1 - zz + zz * zz / 2 - mp.exp(-zz)) / zz ** 3 for zz in zs]
        n = self.n
        # every constant coefficient of the polynomial residual, at 200 bits
        k = {}
        k["rho"] = rho
        k["A0"], k["B0"], k["qp0"] = A0, B0, qp0
        k["cg"] = [2 * mp.pi * rho * ez[t] / zs[t] for t in range(n)]          # gam = 1 - cg G
        k["mA"] = [rho / zs[t] * (1 + zs[t]) for t in range(n)]               # M terms
        k["mB"] = [rho / zs[t] * 2 * mp.pi * rho / zs[t] for t in range(n)]
        k["nA"] = [rho / zs[t] ** 2 * (1 + zs[t] + zs[t] ** 2 / 2) for t in range(n)]
        k["nB"] = [rho / zs[t] ** 2 * 2 * mp.pi * rho / zs[t] for t in range(n)]
        k["phi1"], k["phi2"] = phi1, phi2
        k["xA"] = [[2 * mp.pi * rho / zs[t] / (zs[u] + zs[t]) for t in range(n)] for u in range(n)]
        k["xB"] = [[mp.exp(-zs[u]) / (zs[u] + zs[t]) + (1 - mp.exp(-zs[u])) / zs[u]
                    for t in range(n)] for u in range(n)]
        k["sA"] = [1 / zs[u] ** 2 for u in range(n)]
        k["sQ"] = [1 / zs[u] for u in range(n)]
        k["sD"] = [[zs[t] / (zs[u] + zs[t]) for t in range(n)] for u in range(n)]
        k["kt"] = [2 * mp.pi * ks[u] / zs[u] for u in range(n)]
        k["twopi"] = 2 * mp.pi
        F0 = [1 - rho * (phi1[u] * qp0 + phi2[u] * A0) for u in range(n)]
        G0 = [(A0 + zs[u] * qp0) / (2 * mp.pi * zs[u] ** 2 * F0[u]) for u in range(n)]
        self.mpk = k
        self.seed_mp = [mp.mpf(0)] * n + G0
        # Each 200-bit constant is within 2^-190 relative of its true value; widen to a
        # float interval that certainly contains the true value.
        self.ki = self._map(k, lambda x: iv_from_mp(x - abs(x) * mp.mpf(2) ** -180 - mp.mpf(2) ** -1000,
                                                     x + abs(x) * mp.mpf(2) ** -180 + mp.mpf(2) ** -1000))
        self.kf = self._map(k, float)
        self.seed_f = np.array([complex(float(x)) for x in self.seed_mp])
        self.seed_i = [C(iv_from_mp(x - abs(x) * mp.mpf(2) ** -150, x + abs(x) * mp.mpf(2) ** -150))
                       for x in self.seed_mp]

    @staticmethod
    def _map(k, f):
        out = {}
        for key, val in k.items():
            if isinstance(val, list):
                out[key] = [[f(x) for x in v] if isinstance(v, list) else f(v) for v in val]
            else:
                out[key] = f(val)
        return out

    def residual(self, u, tau, k):
        """Generic residual: u a list of 2n scalars (complex, C or D), tau a scalar."""
        n = self.n
        Dt, G = u[:n], u[n:]
        gam = [1 - k["cg"][t] * G[t] for t in range(n)]
        M = 0
        N = 0
        for t in range(n):
            M = M - Dt[t] * (gam[t] * k["mA"][t] + G[t] * k["mB"][t])
            N = N + Dt[t] * (G[t] * k["nB"][t] + gam[t] * k["nA"][t])
        A = (1 + M) * k["A0"] - N * (k["B0"] * 4.0)
        qp = (1 + M) * k["qp0"] + N * k["A0"]
        out1, out2 = [], []
        for uu in range(n):
            Qh = qp * k["phi1"][uu] + A * k["phi2"][uu]
            sD = 0
            for t in range(n):
                Qh = Qh + Dt[t] * (G[t] * k["xA"][uu][t] + gam[t] * k["xB"][uu][t])
                sD = sD + gam[t] * Dt[t] * k["sD"][uu][t]
            F = 1 - Qh * k["rho"]
            src = A * k["sA"][uu] + qp * k["sQ"][uu] + sD
            out1.append(Dt[uu] * F - tau * k["kt"][uu])
            out2.append(G[uu] * F * k["twopi"] - src)
        return out1 + out2

    # float helpers -------------------------------------------------------------
    def f_float(self, u, tau):
        return np.array(self.residual(list(u), tau, self.kf), dtype=complex)

    def jac_float(self, u, tau):
        m = 2 * self.n
        vars_ = [D(complex(u[i]), [1.0 + 0j if j == i else 0j for j in range(m)]) for i in range(m)]
        r = self.residual(vars_, tau, self.kf)
        return np.array([[ri.g[j] for j in range(m)] for ri in r], dtype=complex)

    def newton(self, u, tau, tol=1e-14, itmax=50):
        u = np.array(u, dtype=complex)
        for _ in range(itmax):
            r = self.f_float(u, tau)
            du = np.linalg.solve(self.jac_float(u, tau), -r)
            u = u + du
            if np.max(np.abs(du)) < tol * (1 + np.max(np.abs(u))):
                return u
        return None

    # interval helpers ----------------------------------------------------------
    def f_box(self, u: list[C], T: C):
        return self.residual(u, T, self.ki)

    def jac_box(self, X: list[C], T: C):
        m = 2 * self.n
        z0 = C(0.0)
        one = C(1.0)
        vars_ = [D(X[i], [one if j == i else z0 for j in range(m)]) for i in range(m)]
        r = self.residual(vars_, T, self.ki)
        return [[C.of(ri.g[j]) if isinstance(ri, D) else z0 for j in range(m)] for ri in r]


# ----------------------------------------------------------------------- Krawczyk
def cmatvec(Cm, v):
    m = len(v)
    return [sum((C.of(complex(Cm[i][j])) * v[j] for j in range(m)), C(0.0)) for i in range(m)]


def krawczyk(model: Model, ut: np.ndarray, T: C, rad: np.ndarray, tau_mid: complex):
    """Krawczyk test on X = ut +- rad (per component, same radius re and im).

    Returns (ok, X, K, contraction) where contraction is an upper bound of
    ||I - C J(X, T)||_inf (complex modulus row sums).
    """
    m = 2 * model.n
    Cm = np.linalg.inv(model.jac_float(ut, tau_mid))
    X = [ball(complex(ut[i]), rad[i], rad[i]) for i in range(m)]
    y = [C.of(complex(ut[i])) for i in range(m)]
    Fy = model.f_box(y, T)
    J = model.jac_box(X, T)
    CF = cmatvec(Cm, Fy)
    # I - C J
    E = []
    for i in range(m):
        row = []
        for j in range(m):
            s = C(1.0 if i == j else 0.0)
            for k in range(m):
                s = s - C.of(complex(Cm[i][k])) * J[k][j]
            row.append(s)
        E.append(row)
    contraction = max(sum(E[i][j].mag() * 1.0 for j in range(m)) for i in range(m))
    dX = [X[j] - y[j] for j in range(m)]
    K = []
    for i in range(m):
        s = y[i] - CF[i]
        for j in range(m):
            s = s + E[i][j] * dX[j]
        K.append(s)
    ok = contraction < 1.0 and all(K[i].inside(X[i]) for i in range(m))
    return ok, X, K, contraction, CF


def box_inside(A: list[C], B: list[C]):
    return all(a.inside(b) for a, b in zip(A, B))


def box_disjoint(A: list[C], B: list[C]):
    return any(a.disjoint(b) for a, b in zip(A, B))


def run_chain(model: Model, pieces_fn, u_start, K_prev, label, h0, hmin=1e-6, log=None,
              real=False):
    """Generic validated continuation along a path parameterised by s in [0, 1].

    pieces_fn(sa, sb) -> (T, tau_a, tau_b, tau_mid): an enclosure T of the path image of
    [sa, sb], the points at sa, sb and the midpoint, and an enclosure of the point at sb.
    Returns the certified pieces and the end-point box Y of the last piece.
    """
    s, h = 0.0, h0
    u = np.array(u_start, dtype=complex)
    pieces = []
    worst = 0.0
    while s < 1.0:
        sb = min(1.0, s + h)
        T, ta, tb, tm, Tb = pieces_fn(s, sb)
        um = model.newton(u, tm)
        ub = model.newton(u, tb) if um is not None else None
        if real and um is not None and ub is not None:
            # boxes symmetric about the real axis: the unique root is then real
            um, ub = um.real + 0j, ub.real + 0j
        accepted = False
        if um is not None and ub is not None:
            # radius: drift across the piece plus a floor
            drift = np.maximum(np.abs(ub - um), np.abs(um - u))
            rad = 2.0 * drift + 1e-11 * (1.0 + np.abs(um))
            for _ in range(8):
                ok, X, K, q, CF = krawczyk(model, um, T, rad, tm)
                link = K_prev is None or box_inside(K_prev, X)
                if ok and link:
                    accepted = True
                    break
                if q >= 1.0:
                    break
                # inflate each component to cover its Krawczyk image and the previous
                # enclosure (epsilon-inflation); the test is re-run on the new box
                need = np.array([max(abs(K[i].re.lo - um[i].real), abs(K[i].re.hi - um[i].real),
                                     abs(K[i].im.lo - um[i].imag), abs(K[i].im.hi - um[i].imag))
                                 for i in range(len(um))])
                if K_prev is not None:
                    need = np.maximum(need, [max(abs(K_prev[i].re.lo - um[i].real),
                                                 abs(K_prev[i].re.hi - um[i].real),
                                                 abs(K_prev[i].im.lo - um[i].imag),
                                                 abs(K_prev[i].im.hi - um[i].imag))
                                             for i in range(len(um))])
                rad = np.maximum(rad, 1.3 * need)
        if accepted:
            # tight enclosure of the root at the piece's end point: a box Y around the
            # Newton root, certified at tau_b alone, and contained in X (so it is the
            # same root as the unique one in X)
            accepted = False
            ry = 1e-9 * (1.0 + np.abs(ub))
            for _ in range(6):
                oky, Y, KY, qy, _ = krawczyk(model, ub, Tb, ry, tb)
                if oky and box_inside(Y, X):
                    accepted = True
                    break
                ry = ry * 4.0
        if not accepted:
            h = h / 2.0
            if h < hmin:
                raise RuntimeError(f"{label}: step underflow at s={s}")
            continue
        pieces.append({"s": [s, sb], "contraction": q})
        worst = max(worst, q)
        K_prev = Y
        s, u = sb, ub
        h = min(h * 1.5, h0 * 8)
        if log is not None and len(pieces) % 200 == 0:
            log(f"  {label}: s={s:.4f}, pieces={len(pieces)}, worst contraction={worst:.3f}")
    return pieces, K_prev, u, worst


def seg_pieces(a: float, b: float):
    """Real segment tau = a + s (b - a); a, b exact floats."""
    def f(sa, sb):
        ta = a + (b - a) * sa
        tb = a + (b - a) * sb
        lo, hi = (dn(min(ta, tb)), up(max(ta, tb)))
        # ta, tb are the float images; the true path points a+(b-a)s are within 1 ulp,
        # and every piece shares its float endpoint with the next, so the union of the
        # widened rectangles covers the segment.
        T = C(I(dn(lo), up(hi)), I(0.0, 0.0))
        Tb = C(I(tb, tb), I(0.0, 0.0))
        return T, complex(ta), complex(tb), complex(0.5 * (ta + tb)), Tb
    return f


def circle_pieces(r: float):
    """tau = r exp(2 pi i s): rectangle centred at the arc midpoint, half-width r*dtheta/2."""
    two_pi = iv_from_mp(2 * mpmath.pi * (1 - mpmath.mpf(2) ** -150), 2 * mpmath.pi * (1 + mpmath.mpf(2) ** -150))

    def f(sa, sb):
        sm = 0.5 * (sa + sb)
        th = mpmath.mpf(sm) * 2 * mpmath.pi
        c, si = mpmath.cos(th), mpmath.sin(th)
        eps = mpmath.mpf(2) ** -150
        cr = iv_from_mp(r * c - eps, r * c + eps)
        ci = iv_from_mp(r * si - eps, r * si + eps)
        half = up(up(r * up(two_pi.hi * (sb - sa))) * 0.5 * (1 + 1e-15))
        T = C(I(dn(cr.lo - half), up(cr.hi + half)), I(dn(ci.lo - half), up(ci.hi + half)))
        ta = r * cmath.exp(2j * math.pi * sa)
        tb = r * cmath.exp(2j * math.pi * sb)
        tm = complex(float(r * c), float(r * si))
        thb = mpmath.mpf(sb) * 2 * mpmath.pi
        cb, sbn = mpmath.cos(thb), mpmath.sin(thb)
        Tb = C(iv_from_mp(r * cb - eps, r * cb + eps), iv_from_mp(r * sbn - eps, r * sbn + eps))
        return T, ta, tb, tm, Tb
    return f


def certify_state(eta: str, z, kv, tau_max: float, r: float | None, log):
    model = Model(eta, z, kv)
    rec = {"model": model.label, "tau_max": tau_max}
    t0 = time.time()
    # seed check is folded into the first link: K_prev = enclosure of the PY seed
    seed_box = model.seed_i
    if r is not None and r < tau_max:
        p1, K_r, u_r, w1 = run_chain(model, seg_pieces(0.0, r), model.seed_f, seed_box,
                                     f"eta={eta} real [0,{r}]", h0=1 / 64, log=log, real=True)
        p2, K_t, u_t, w2 = run_chain(model, seg_pieces(r, tau_max), u_r, K_r,
                                     f"eta={eta} real [{r},{tau_max}]", h0=1 / 64, log=log, real=True)
        pc, K_c, u_c, wc = run_chain(model, circle_pieces(r), u_r, K_r,
                                     f"eta={eta} circle r={r}", h0=1 / 256, log=log)
        disjoint = box_disjoint(K_c, K_r)
        rec.update({
            "real_pieces": len(p1) + len(p2), "real_worst_contraction": max(w1, w2),
            "real_branch_certified": True,
            "root_at_tau_max": [[k.re.lo, k.re.hi] for k in K_t],
            "circle_radius": r, "circle_pieces": len(pc), "circle_worst_contraction": wc,
            "start_enclosure": [[[k.re.lo, k.re.hi], [k.im.lo, k.im.hi]] for k in K_r],
            "end_enclosure": [[[k.re.lo, k.re.hi], [k.im.lo, k.im.hi]] for k in K_c],
            "end_float": [[float(x.real), float(x.imag)] for x in u_c],
            "monodromy_nontrivial": disjoint,
            "conclusion": (f"R_c <= {r} < {tau_max}: the Taylor series diverges at tau={tau_max} "
                           f"although the PY-seeded branch is real and regular on [0,{tau_max}]")
            if disjoint else "monodromy NOT certified",
        })
    else:
        p, K_t, u_t, w = run_chain(model, seg_pieces(0.0, tau_max), model.seed_f, seed_box,
                                   f"eta={eta} real [0,{tau_max}]", h0=1 / 64, log=log, real=True)
        rec.update({"real_pieces": len(p), "real_worst_contraction": w,
                    "real_branch_certified": True,
                    "root_at_tau_max": [[k.re.lo, k.re.hi] for k in K_t]})
    rec["seconds"] = round(time.time() - t0, 1)
    return rec


def main(argv):
    z, kv = ["1.8", "12"], ["1", "-6"]
    states = [("0.2", 2.75), ("0.3", 2.75), ("0.4", 2.75)]
    if len(argv) > 1 and argv[1] == "--quick":
        states = states[:1]
    out = {"description": __doc__.split("\n")[0], "z": z, "kv": kv, "states": []}
    for eta, r in states:
        rec = certify_state(eta, z, kv, 3.0, r, log=lambda s: print(s, flush=True))
        print(json.dumps({k: v for k, v in rec.items() if "enclosure" not in k}), flush=True)
        out["states"].append(rec)
    # negative control: at eta = 0.1 the radius is about 3.97 > 2.75, so the same loop
    # must close (start and end enclosures overlap) and the test must NOT certify
    ctrl = certify_state("0.1", z, kv, 3.0, 2.75, log=lambda s: None)
    out["negative_control"] = {"eta": "0.1", "circle_radius": 2.75,
                               "monodromy_nontrivial": ctrl["monodromy_nontrivial"],
                               "expected": False}
    print("negative control eta=0.1:", ctrl["monodromy_nontrivial"], flush=True)
    res = Path(__file__).resolve().parent / "results"
    res.mkdir(exist_ok=True)
    (res / "f5_competing_tails.json").write_text(json.dumps(out, indent=1) + "\n")
    ok = all(s.get("monodromy_nontrivial") and s["real_branch_certified"] for s in out["states"])
    ok = ok and not ctrl["monodromy_nontrivial"]
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
