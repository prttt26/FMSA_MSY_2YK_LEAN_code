#!/usr/bin/env python3
"""Disc-cover lower bound R_c >= r_lo for F7, in Arb ball arithmetic (python-flint).

Same system and constants as `f5_competing_tails.Model` (the generic residual is evaluated
on acb balls; the 200-bit constants become acb balls with an explicit radius). Argument as
in `f7_fold_binding.py`:

* the closed upper half disc {|tau| <= r_lo, Im tau >= 0} is covered by dyadic rectangles
  (exact in binary), refined on failure, and every rectangle T gets a box X with
  K(X, T) in int X (Krawczyk; by Rump's theorem this alone gives a unique root in X for every
  tau in T and nonsingular Jacobians, for any preconditioner);
* rectangles meeting the real axis are symmetric about it and get boxes symmetric about it,
  so the unique root is real for real tau; the glued function is then real on the real axis
  and extends by Schwarz reflection to the whole disc;
* the Jacobian over a box is enclosed in centred form, J(y) + sum_k dJ/du_k(y) d_k +
  1/2 sum_kl d2J d_k d_l with d = X - y (exact, since the residual is a cubic polynomial in u),
  with the derivative tensors taken from step-1 differences at points; the natural interval
  extension J(X) is 7-15x wider here, which cost ~250x more rectangles;
* the rectangles are the leaves of a quadtree over coarse cells (default h0 = 1/8);
* for every pair of leaves s, t sharing an edge segment (found by walking the right and top
  edges of each leaf; edge pairs suffice, see `cover`): either the Krawczyk image
  K(X_s, T_s ∩ T_t) (which
  contains the root of s for every tau in the intersection, by the mean-value form and
  convexity of rectangles) lies in X_t, so there the root of s lies in X_t and equals the root
  of t; or (fallback) a box Y,
  certified at one exact common point, lies in both X boxes, so the two root functions agree
  there and, by local uniqueness, on the whole connected intersection;
* the square holding tau = 0 contains the PY seed ball.

The roots then glue to one analytic function on a neighbourhood of the closed disc, equal to
the PY-seeded branch near 0, so its Taylor radius at 0 is at least r_lo.  Midpoint roots come
from a tangent predictor off a certified neighbour plus chord corrections (float); they only
centre the boxes and need no accuracy guarantee.

Requires python-flint (Arb). Run from this directory:

    python3 f7_cover_arb.py <w> <r_lo> [h0] [hmin]
"""
from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import mpmath
import numpy as np
from flint import acb, arb

sys.path.insert(0, str(Path(__file__).resolve().parent))
from f5_competing_tails import D, Model  # noqa: E402


def mp_ball(x, rel=mpmath.mpf(2)**-180):
    r = abs(x)*rel + mpmath.mpf(2)**-1000
    return acb(arb(mpmath.nstr(x, 70), mpmath.nstr(r, 5)))


class ArbModel:
    def __init__(self, model: Model):
        self.m = model
        self.n = 2*model.n
        self.k = Model._map(model.mpk, mp_ball)
        self.seed = [mp_ball(x, mpmath.mpf(2)**-150) for x in model.seed_mp]

    def F(self, u, T):
        return self.m.residual(u, T, self.k)

    def J(self, X, T):
        n = self.n
        z0, one = acb(0), acb(1)
        vars_ = [D(X[i], [one if j == i else z0 for j in range(n)]) for i in range(n)]
        r = self.m.residual(vars_, T, self.k)
        return [[ri.g[j] if isinstance(ri, D) else z0 for j in range(n)] for ri in r]

    def _quadratic_parts(self):
        """The residual is a cubic polynomial in u (only + - x), so J is quadratic and these
        step-1 differences are exact identities, evaluated at points (no dependency growth):
        Dk[k] = dJ/du_k at 0 = (J(e_k) - J(-e_k))/2, Tq[k][l] = d2J/du_k du_l (constant)."""
        n, T0 = self.n, acb(0)
        e = lambda *ks: [acb(sum(1 for k in ks if k == i) - sum(1 for k in ks if k == -i - 1))
                         for i in range(n)]
        J0 = self.J([acb(0)]*n, T0)
        Jp = [self.J(e(k), T0) for k in range(n)]
        Jm = [self.J(e(-k - 1), T0) for k in range(n)]
        self.Dk = [[[(Jp[k][i][j] - Jm[k][i][j])/2 for j in range(n)] for i in range(n)] for k in range(n)]
        self.Tq = [[None]*n for _ in range(n)]
        for k in range(n):
            for l in range(k, n):
                Jkl = self.J(e(k, l), T0)
                self.Tq[k][l] = self.Tq[l][k] = [[Jkl[i][j] - Jp[k][i][j] - Jp[l][i][j] + J0[i][j]
                                                  for j in range(n)] for i in range(n)]

    def Jc(self, X, y):
        """Centred enclosure of J over the box X around the point y (exact Taylor form of a
        quadratic): J(y) + sum_k dJ/du_k(y) d_k + 1/2 sum_kl Tq[k][l] d_k d_l, d = X - y.
        The natural extension J(X) overestimates the spread 7-15x here (cancellations inside
        the residual); this form gives the true first-order width."""
        if not hasattr(self, "Tq"):
            self._quadratic_parts()
        n = self.n
        d = [X[k] - y[k] for k in range(n)]
        out = [row[:] for row in self.J(y, acb(0))]
        for k in range(n):
            Gk = [[self.Dk[k][i][j] + sum((self.Tq[k][l][i][j]*y[l] for l in range(n)), acb(0))
                   for j in range(n)] for i in range(n)]
            for l in range(n):
                c = d[k]*d[l]/2
                for i in range(n):
                    for j in range(n):
                        out[i][j] += self.Tq[k][l][i][j]*c
            for i in range(n):
                for j in range(n):
                    out[i][j] += Gk[i][j]*d[k]
        return out


def box(u, rad, sym=False):
    if sym:
        return [acb(arb(float(u[i].real), float(rad[i])), arb(0.0, float(rad[i]))) for i in range(len(u))]
    return [acb(arb(float(u[i].real), float(rad[i])), arb(float(u[i].imag), float(rad[i]))) for i in range(len(u))]


def mid_matrix(Ja):
    return np.array([[complex(float(x.real.mid()), float(x.imag.mid())) for x in row] for row in Ja])


def krawczyk(am: ArbModel, um, T, rad, sym=False):
    """K(X, T) in int X with C = inverse of the midpoint of J(X).  Returns ok, X, K, C."""
    n = am.n
    X = box(um, rad, sym)
    y = [acb(float(um[i].real)) if sym else acb(complex(um[i])) for i in range(n)]
    J = am.Jc(X, y)
    Cm = np.linalg.inv(mid_matrix(J))
    Ca = [[acb(complex(Cm[i, j])) for j in range(n)] for i in range(n)]
    Fy = am.F(y, T)
    K = []
    for i in range(n):
        s = y[i]
        for k in range(n):
            s -= Ca[i][k]*Fy[k]
        for j in range(n):
            e = acb(1 if i == j else 0)
            for k in range(n):
                e -= Ca[i][k]*J[k][j]
            s += e*(X[j] - y[j])
        K.append(s)
    ok = all(X[i].contains_interior(K[i]) for i in range(n))
    return ok, X, K, Cm


def krawczyk_on(am: ArbModel, um, X, T, sym=False):
    """K(X, T) for a given box X (no acceptance test): encloses the unique root of X for every
    tau in T whenever X was certified on a rectangle containing T."""
    n = am.n
    y = [acb(float(um[i].real)) if sym else acb(complex(um[i])) for i in range(n)]
    J = am.Jc(X, y)
    Cm = np.linalg.inv(mid_matrix(J))
    Ca = [[acb(complex(Cm[i, j])) for j in range(n)] for i in range(n)]
    Fy = am.F(y, T)
    K = []
    for i in range(n):
        s = y[i]
        for k in range(n):
            s -= Ca[i][k]*Fy[k]
        for j in range(n):
            e = acb(1 if i == j else 0)
            for k in range(n):
                e -= Ca[i][k]*J[k][j]
            s += e*(X[j] - y[j])
        K.append(s)
    return K


def need(K, um):
    out = []
    for i, k in enumerate(K):
        re, im = k.real, k.imag
        out.append(max(abs(float(re.upper()) - um[i].real), abs(float(re.lower()) - um[i].real),
                       abs(float(im.upper()) - um[i].imag), abs(float(im.lower()) - um[i].imag)))
    return np.array(out)


def certify(am: ArbModel, um, T, v, span, sym=False, tries=6, fac=3.0, withK=False):
    rad = fac*np.abs(v)*span + 1e-12*(1 + np.abs(um))
    for _ in range(tries):
        ok, X, K, Cm = krawczyk(am, um, T, rad, sym)
        if ok:
            return (X, Cm, K) if withK else (X, Cm)
        nd = need(K, um)
        if not np.all(np.isfinite(nd)) or np.max(nd/(1 + np.abs(um))) > 0.5:
            return (None, None, None) if withK else (None, None)
        rad = np.maximum(rad, 1.3*nd)
    return (None, None, None) if withK else (None, None)


class Rect:
    __slots__ = ("x0", "x1", "y0", "y1", "u", "X", "C", "sub", "nb", "ok")

    def __init__(self, x0, x1, y0, y1, nb=None):
        self.x0, self.x1, self.y0, self.y1 = x0, x1, y0, y1
        self.sub, self.nb, self.ok = None, nb, False

    def has(self, x, y):
        return self.x0 <= x < self.x1 and self.y0 <= y < self.y1

    @property
    def sym(self):
        return self.y0 == -self.y1

    @property
    def mid(self):
        return complex(0.5*(self.x0 + self.x1), 0.0 if self.sym else 0.5*(self.y0 + self.y1))

    @property
    def span(self):
        return math.hypot(self.x1 - self.x0, self.y1 - self.y0)/2

    def T(self):
        return acb(arb(0.5*(self.x0 + self.x1), 0.5*(self.x1 - self.x0)),
                   arb(0.5*(self.y0 + self.y1), 0.5*(self.y1 - self.y0)))

    def dist0(self):            # lower bound of |tau| over the part with Im >= 0
        y0 = max(self.y0, 0.0)
        dx = 0.0 if self.x0 <= 0 <= self.x1 else min(abs(self.x0), abs(self.x1))
        dy = 0.0 if y0 <= 0 <= self.y1 else y0
        return math.hypot(dx, dy)*(1 - 1e-12)

    def kids(self):
        xm = 0.5*(self.x0 + self.x1)
        if self.sym:
            ym = 0.5*self.y1
            return [Rect(self.x0, xm, -ym, ym), Rect(xm, self.x1, -ym, ym),
                    Rect(self.x0, xm, ym, self.y1), Rect(xm, self.x1, ym, self.y1)]
        ym = 0.5*(self.y0 + self.y1)
        return [Rect(a, b, c, d) for a, b in ((self.x0, xm), (xm, self.x1)) for c, d in ((self.y0, ym), (ym, self.y1))]


def predict(am, nb, tau, steps=3):
    """Tangent predictor from a certified neighbour plus chord corrections with its C."""
    b = np.array(list(am.m.kf["kt"]) + [0.0]*am.m.n, dtype=complex)
    v = nb.C @ b
    u = nb.u + v*(tau - nb.mid)
    for _ in range(steps):
        u = u - nb.C @ am.m.f_float(u, tau)
    return u, v


def cover(am: ArbModel, r_lo: float, h0: float = 2.0**-3, hmin: float = 2.0**-20, log=print,
          max_rects=6_000_000, check_pairs=False):
    """Quadtree cover of the closed upper half disc, then gluing of every pair of leaves that
    share an edge segment.  Edge pairs suffice: every point of the closed disc is interior to
    the union, so the leaves holding it go round it in a cycle in which neighbours share an
    edge segment through it, and the roots agree there pairwise."""
    t0 = time.time()
    n_x = int(math.ceil(r_lo*1.0001/h0)) + 1
    cells = {}                    # (i, j) -> top-level cell; row j = 0 straddles the real axis
    for j in range(0, n_x + 1):
        y0, y1 = (-h0/2, h0/2) if j == 0 else (h0/2 + (j - 1)*h0, h0/2 + j*h0)
        for i in range(-n_x, n_x):
            r = Rect(i*h0, (i + 1)*h0, y0, y1)
            if r.dist0() <= r_lo:
                cells[(i, j)] = r
    eps = hmin/8                  # every coordinate is a multiple of hmin/2: probes never sit on an edge

    def locate(x, y):
        """Leaf holding (x, y), or (None, (x1, y1)): upper-right corner of the missing region."""
        i, j = int(math.floor(x/h0)), int(math.floor((y + h0/2)/h0))
        r = cells.get((i, j)) if y >= -h0/2 else None
        if r is None:
            return None, ((i + 1)*h0, h0/2 + j*h0)
        while r.sub is not None:
            for k in r.sub:
                if k[1] is not None and k[1].has(x, y):
                    r = k[1]
                    break
            else:
                for k in r.sub:
                    if k[0].has(x, y):
                        return None, (k[0].x1, k[0].y1)
                return None, (r.x1, r.sub[0][0].y0)    # reflected lower part of a symmetric cell
        return r, None

    def around(r):
        cx, cy = r.mid.real, max(r.mid.imag, 0.0)
        pts = [(r.x1 + eps, cy), (r.x0 - eps, cy), (cx, r.y1 + eps), (cx, r.y0 - eps),
               (r.x1 + eps, r.y1 + eps), (r.x0 - eps, r.y1 + eps), (r.x1 + eps, r.y0 - eps), (r.x0 - eps, r.y0 - eps)]
        out = [locate(x, y)[0] for x, y in pts]
        return [t for t in out if t is not None and t.ok]

    todo = sorted(cells.values(), key=lambda r: abs(r.mid))
    first = todo.pop(0)
    J0 = am.m.jac_float(am.m.seed_f, 0j)
    b = np.array(list(am.m.kf["kt"]) + [0.0]*am.m.n, dtype=complex)
    v0 = np.linalg.solve(J0, b)
    import collections
    queue, splits = collections.deque(todo), 0
    while True:                   # refine the cell at 0 until it certifies off the PY seed
        u0 = am.m.newton(am.m.seed_f, first.mid)
        X, Cm = certify(am, u0, first.T(), v0, first.span, first.sym)
        if X is not None:
            break
        if (first.x1 - first.x0)/2 < hmin:
            raise RuntimeError("cover: the rectangle at 0 failed")
        splits += 1
        kids = first.kids()
        first.sub = [(k, k if k.dist0() <= r_lo else None) for k in kids]
        kids = sorted([k for k in kids if k.dist0() <= r_lo], key=lambda s: abs(s.mid))
        first = kids[0]
        queue.extendleft(kids[1:])
    first.u, first.X, first.C, first.ok = u0, X, Cm, True
    leaves = [first]
    stalls = 0
    while queue:
        r = queue.popleft()
        near = around(r)
        if r.nb is not None:
            near.append(r.nb)
        if not near:
            queue.append(r); stalls += 1
            if stalls > len(queue) + 10:
                raise RuntimeError("cover: disconnected rectangle set")
            continue
        stalls = 0
        nb = min(near, key=lambda s: abs(s.mid - r.mid))
        u, v = predict(am, nb, r.mid)
        if r.sym:
            u = u.real + 0j
        X, Cm = certify(am, u, r.T(), v, r.span, r.sym)
        if X is not None:
            r.u, r.X, r.C, r.ok = u, X, Cm, True
            leaves.append(r)
            if log and len(leaves) % 20000 == 0:
                log(f"  cover r_lo={r_lo}: {len(leaves)} certified, {len(queue)} pending, {time.time() - t0:.0f}s")
        else:
            if (r.x1 - r.x0)/2 < hmin:
                raise RuntimeError(f"cover: rectangle at {r.mid:.5f} (w={r.x1 - r.x0:.2e}) failed at min size")
            splits += 1
            kids = r.kids()
            r.sub = [(k, k if k.dist0() <= r_lo else None) for k in kids]
            for k in sorted([k for k in kids if k.dist0() <= r_lo], key=lambda s: abs(s.mid - nb.mid), reverse=True):
                k.nb = nb
                queue.appendleft(k)
        if len(leaves) + len(queue) > max_rects:
            raise RuntimeError("cover: too many rectangles")
    seed_ok = all(first.X[i].contains(am.seed[i]) for i in range(am.n))
    t1 = time.time()
    log(f"  cover done: {len(leaves)} leaves, {splits} splits, {t1 - t0:.0f}s; gluing")

    def glue(s, t):
        lx, hx = max(s.x0, t.x0), min(s.x1, t.x1)
        ly, hy = max(s.y0, t.y0), min(s.y1, t.y1)
        assert lx <= hx and ly <= hy and (lx < hx or ly < hy), "not an edge pair"
        Tint = acb(arb(0.5*(lx + hx), 0.5*(hx - lx)), arb(0.5*(ly + hy), 0.5*(hy - ly)))
        Ks = krawczyk_on(am, s.u, s.X, Tint, s.sym)
        if all(t.X[i].contains(Ks[i]) for i in range(am.n)):
            return False
        tau0 = complex(0.5*(lx + hx), 0.5*(ly + hy))          # dyadic midpoint: exact
        sym0 = (ly == -hy)
        if sym0:
            tau0 = complex(tau0.real, 0.0)
        u0 = s.u + (s.C @ b)*(tau0 - s.mid)
        for _ in range(3):
            u0 = u0 - s.C @ am.m.f_float(u0, tau0)
        if sym0:
            u0 = u0.real + 0j
        Y, _ = certify(am, u0, acb(tau0), np.zeros(am.n), 0.0, sym0)
        if Y is None or not all(s.X[i].contains(Y[i]) and t.X[i].contains(Y[i]) for i in range(am.n)):
            raise RuntimeError(f"cover: gluing failed between {s.mid:.5f} and {t.mid:.5f}")
        return True

    pairs = fallback = 0
    seen = set() if check_pairs else None
    for a, s in enumerate(leaves):
        # right edge (upward from the axis for a symmetric leaf), then top edge
        y = max(s.y0, 0.0) + eps
        while y < s.y1:
            t, gap = locate(s.x1 + eps, y)
            if t is None:
                y = gap[1] + eps
                continue
            if not t.ok:
                raise RuntimeError(f"cover: uncertified leaf at {t.mid:.5f}")
            fallback += glue(s, t); pairs += 1
            if seen is not None:
                seen.add((id(s), id(t)))
            y = t.y1 + eps
        x = s.x0 + eps
        while x < s.x1:
            t, gap = locate(x, s.y1 + eps)
            if t is None:
                x = gap[0] + eps
                continue
            if not t.ok:
                raise RuntimeError(f"cover: uncertified leaf at {t.mid:.5f}")
            fallback += glue(s, t); pairs += 1
            if seen is not None:
                seen.add((id(s), id(t)))
            x = t.x1 + eps
        if log and a % 50000 == 0 and a:
            log(f"  gluing: {a}/{len(leaves)} leaves, {pairs} pairs ({fallback} by point), {time.time() - t1:.0f}s")
    if seen is not None:            # self-test (small covers): brute-force list of edge pairs
        want = set()
        for s in leaves:
            for t in leaves:
                lx, hx = max(s.x0, t.x0), min(s.x1, t.x1)
                ly, hy = max(s.y0, t.y0), min(s.y1, t.y1)
                if s is not t and lx <= hx and ly <= hy and (lx < hx or ly < hy) and (id(t), id(s)) not in want:
                    want.add((id(s), id(t)))
        norm = lambda S: {tuple(sorted(p)) for p in S}
        if norm(want) != norm(seen):
            raise RuntimeError(f"cover: edge walk found {len(seen)} pairs, brute force {len(want)}")
        log(f"  pair self-test: {len(seen)} edge pairs, all found")
    widths = [r.x1 - r.x0 for r in leaves]
    hist = collections.Counter(int(round(-math.log2(wd))) for wd in widths)
    return dict(r_lo=r_lo, half_disc=True, rectangles=len(leaves), splits=splits, min_width=min(widths),
                width_histogram={f"2^-{k}": hist[k] for k in sorted(hist)}, glued_edge_pairs=pairs,
                glued_by_point_fallback=fallback, h0=h0, hmin=hmin,
                seed_in_zero_rectangle=seed_ok, certified=seed_ok, seconds=round(time.time() - t0, 1))


def main(argv):
    w, r_lo = argv[1], float(argv[2])
    h0 = float(argv[3]) if len(argv) > 3 else 2.0**-3
    hmin = float(argv[4]) if len(argv) > 4 else 2.0**-20
    am = ArbModel(Model("0.3", ["1.8", "12"], ["1", w]))
    try:
        rec = cover(am, r_lo, h0, hmin)
    except RuntimeError as e:
        rec = dict(r_lo=r_lo, certified=False, failure=str(e))
    rec.update(w=w, eta="0.3", z=["1.8", "12"])
    print(json.dumps(rec), flush=True)
    res = Path(__file__).resolve().parent/"results"
    res.mkdir(exist_ok=True)
    (res/f"f7_cover_w{w}_r{r_lo}.json").write_text(json.dumps(rec, indent=1) + "\n")
    return 0 if rec.get("certified") else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
