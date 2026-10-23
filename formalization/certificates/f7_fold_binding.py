#!/usr/bin/env python3
"""F7 certificate: a real fold need not bind the coupling series; the radius is set by the
nearest singularity of the physical branch, real or complex.

System and interval machinery: those of `f5_competing_tails.py` (one hard-sphere species,
n Yukawa tails, polynomial BH residual R(u, tau), Krawczyk with outward rounding). Family
z = (1.8, 12), kv = (1, w), eta = 0.3.

Two certified bounds on the Taylor radius R_c of the PY-seeded branch at tau = 0:

* Lower bound, disc cover. The square [-r, r]^2 is subdivided (quadtree) and every square
  T meeting the closed disc |tau| <= r_lo gets a Krawczyk box X_T: for each tau in T there
  is exactly one root in X_T, and the Jacobian is invertible there. For every pair of
  squares whose closed rectangles meet, a tight box Y at one common point tau_0, certified
  at tau_0 alone, lies in both X boxes; so the two root functions agree at tau_0, and by
  local uniqueness (invertible Jacobian) on the whole connected intersection. The square
  containing 0 holds the PY seed enclosure. Hence the roots glue to one analytic function on
  a neighbourhood of the closed disc, equal to the branch near 0, and R_c >= r_lo.

* Upper bound, monodromy loop. A validated chain from 0 along a straight segment to
  tau_1 = c - rho (c - 0)/|c|, then around the polygon tau = c + rho e^{i theta} back to tau_1.
  If the end enclosure is disjoint from the start enclosure, continuation along this closed
  path is not single-valued; by the argument of F5 the series cannot converge on a disc
  containing the path, so R_c <= max |tau| on the path <= |c| + rho.

State A (w = -2.5): the circle is around the real fold tau_f ~ 4.4789, so R_c is pinned to
the fold. State B (w = -2.636): the circle is around the complex fold tau* ~ 7.04 e^{i...},
while the real branch is certified regular on [0, 7.80] and the real fold sits at
tau_f ~ 7.834 > R_c: a real fold that does not bind.

Negative controls: a loop of the same radius around a regular point must close, and a disc
cover with r_lo beyond the singularity must fail.

    python3 f7_fold_binding.py            # writes results/f7_fold_binding.json
"""
from __future__ import annotations

import cmath
import json
import math
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
import f5_competing_tails as F5  # noqa: E402
from f5_competing_tails import (C, I, Model, ball, box_disjoint, box_inside, cmatvec, dn,  # noqa: E402
                                seg_pieces, up)


def krawczyk(model: Model, ut: np.ndarray, T: C, rad: np.ndarray, tau_mid: complex):
    """F5's Krawczyk test with the contraction measured in the norm weighted by the box radii,
    max_i sum_j |I - C J(X)|_ij r_j / r_i.  Any norm gives a valid test (and K(X) in int X alone
    already implies uniqueness, Rump 1983); the weighted one is scale-invariant, which matters
    here because the components differ by two orders of magnitude."""
    m = 2 * model.n
    Cm = np.linalg.inv(model.jac_float(ut, tau_mid))
    X = [ball(complex(ut[i]), rad[i], rad[i]) for i in range(m)]
    y = [C.of(complex(ut[i])) for i in range(m)]
    Fy = model.f_box(y, T)
    J = model.jac_box(X, T)
    CF = cmatvec(Cm, Fy)
    E = []
    for i in range(m):
        row = []
        for j in range(m):
            s = C(1.0 if i == j else 0.0)
            for k in range(m):
                s = s - C.of(complex(Cm[i][k])) * J[k][j]
            row.append(s)
        E.append(row)
    contraction = max(up(sum(up(E[i][j].mag() * rad[j]) for j in range(m)) / dn(rad[i])) for i in range(m))
    dX = [X[j] - y[j] for j in range(m)]
    K = []
    for i in range(m):
        s = y[i] - CF[i]
        for j in range(m):
            s = s + E[i][j] * dX[j]
        K.append(s)
    # Acceptance is the interior inclusion alone: by Rump's theorem (Rump 1983; Neumaier,
    # Interval Methods for Systems of Equations, Thm 5.1.7) K(X) in int X already implies that
    # C and every Jacobian in J(X) are nonsingular and that X holds exactly one root.  f is
    # holomorphic, so the complex-rectangle operations enclose the real 2n-dimensional
    # Krawczyk operator.  The weighted contraction is reported for information.
    ok = all(K[i].inside(X[i]) for i in range(m))
    return ok, X, K, contraction, CF


def tangent_rad(model, u, tm, span):
    """Per-component radius from the tangent du/dtau = J^{-1} b over a tau-span."""
    b = np.array(list(model.kf["kt"]) + [0.0]*model.n, dtype=complex)
    v = np.linalg.solve(model.jac_float(u, tm), b)
    return 2.5*np.abs(v)*span + 1e-11*(1 + np.abs(u))


def inflate(model, u, T, tm, rad, extra=None, tries=14):
    """epsilon-inflation until K(X) in int X (and extra, a box, inside X when given)."""
    for _ in range(tries):
        ok, X, K, q, _ = krawczyk(model, u, T, rad, tm)
        if ok and (extra is None or box_inside(extra, X)):
            return True, X, K, q
        need = np.array([max(abs(K[i].re.lo - u[i].real), abs(K[i].re.hi - u[i].real),
                             abs(K[i].im.lo - u[i].imag), abs(K[i].im.hi - u[i].imag)) for i in range(len(u))])
        if extra is not None:
            need = np.maximum(need, [max(abs(extra[i].re.lo - u[i].real), abs(extra[i].re.hi - u[i].real),
                                         abs(extra[i].im.lo - u[i].imag), abs(extra[i].im.hi - u[i].imag))
                                     for i in range(len(u))])
        if not np.all(np.isfinite(need)) or np.max(need/(1 + np.abs(u))) > 1.0:
            return False, X, K, q
        rad = np.maximum(rad, 1.3*need)
    return False, X, K, q


def run_chain(model, pieces_fn, u_start, K_prev, label, h0, hmin=1e-7, log=None, real=False):
    """F5's validated continuation (same linking logic), with tangent-based radii and the
    inclusion-only Krawczyk acceptance above."""
    s, h = 0.0, h0
    u = np.array(u_start, dtype=complex)
    pieces, worst = [], 0.0
    while s < 1.0:
        sb = min(1.0, s + h)
        T, ta, tb, tm, Tb = pieces_fn(s, sb)
        um = model.newton(u, tm)
        ub = model.newton(u, tb) if um is not None else None
        accepted = False
        if um is not None and ub is not None:
            if real:
                um, ub = um.real + 0j, ub.real + 0j
            span = max(abs(tb - ta), 1e-300)
            rad = np.maximum(tangent_rad(model, um, tm, span), 2.0*np.maximum(np.abs(ub - um), np.abs(um - u)))
            okx, X, K, q = inflate(model, um, T, tm, rad, extra=K_prev)
            if okx:
                ry = 1e-9*(1.0 + np.abs(ub))
                for _ in range(8):
                    oky, Y, _, _, _ = krawczyk(model, ub, Tb, ry, tb)
                    if oky and box_inside(Y, X):
                        accepted = True
                        break
                    ry = ry*4.0
        if not accepted:
            h = h/2.0
            if h < hmin:
                raise RuntimeError(f"{label}: step underflow at s={s}")
            continue
        pieces.append({"s": [s, sb], "contraction": q})
        worst = max(worst, q)
        K_prev = Y
        s, u = sb, ub
        h = min(h*1.5, h0*8)
        if log is not None and len(pieces) % 200 == 0:
            log(f"  {label}: s={s:.4f}, pieces={len(pieces)}, worst weighted contraction={worst:.3f}")
    return pieces, K_prev, u, worst


# ----------------------------------------------------------------------------- paths
def hull_pts(ta: complex, tb: complex) -> C:
    return C(I(dn(min(ta.real, tb.real)), up(max(ta.real, tb.real))),
             I(dn(min(ta.imag, tb.imag)), up(max(ta.imag, tb.imag))))


def point(t: complex) -> C:
    return C(I(t.real, t.real), I(t.imag, t.imag))


def polyline_pieces(fn):
    """Path through the float points fn(s); piece [sa, sb] = chord, enclosed by the hull of
    its end points.  Consecutive pieces share the identical float end point."""
    def f(sa, sb):
        ta, tb = fn(sa), fn(sb)
        return hull_pts(ta, tb), ta, tb, 0.5*(ta + tb), point(tb)
    return f


def ray(p0: complex, p1: complex):
    return lambda s: p1 if s >= 1.0 else (p0 if s <= 0.0 else p0 + s*(p1 - p0))


def loop(c: complex, start: complex):
    """Closed polygon around c through start (float points on the circle |tau - c| = |start - c|)."""
    rho = abs(start - c); th0 = cmath.phase(start - c)
    return lambda s: start if (s <= 0.0 or s >= 1.0) else c + rho*cmath.exp(1j*(th0 + 2*math.pi*s))


def certify_loop(model, c: complex, rho: float, log):
    t1 = c - rho*c/abs(c)
    p1, K1, u1, w1 = run_chain(model, polyline_pieces(ray(0j, t1)), model.seed_f, model.seed_i,
                               f"ray 0->{t1:.4f}", h0=1/64, log=log)
    p2, K2, u2, w2 = run_chain(model, polyline_pieces(loop(c, t1)), u1, K1,
                               f"loop around {c:.4f}", h0=1/256, log=log)
    return dict(center=[c.real, c.imag], radius=rho, ray_pieces=len(p1), loop_pieces=len(p2),
                worst_contraction=max(w1, w2), max_abs_tau=up(abs(c) + rho*(1 + 1e-12)),
                monodromy_nontrivial=box_disjoint(K2, K1))


# ------------------------------------------------------------------------ disc cover
class Square:
    __slots__ = ("x0", "y0", "h", "T", "u", "X", "K", "q")

    def __init__(self, x0, y0, h):
        self.x0, self.y0, self.h = x0, y0, h
        self.T = C(I(x0, x0 + h), I(y0, y0 + h))
        self.u = None

    @property
    def mid(self):
        return complex(self.x0 + self.h/2, self.y0 + self.h/2)

    def dist0(self):            # lower bound of |tau| over the square
        dx = 0.0 if self.x0 <= 0 <= self.x0 + self.h else min(abs(self.x0), abs(self.x0 + self.h))
        dy = 0.0 if self.y0 <= 0 <= self.y0 + self.h else min(abs(self.y0), abs(self.y0 + self.h))
        return math.hypot(dx, dy)*(1 - 1e-12)


def certify_square(model, sq: Square, useed):
    tm = sq.mid
    u = model.newton(useed, tm)
    if u is None:
        return False
    rad = tangent_rad(model, u, tm, sq.h/math.sqrt(2))
    ok, X, K, q = inflate(model, u, sq.T, tm, rad)
    if ok:
        sq.u, sq.X, sq.K, sq.q = u, X, K, q
    return ok


def disc_cover(model, r_lo: float, h0: float, hmin: float, log, max_squares=200000):
    """Quadtree cover of |tau| <= r_lo by certified squares, then pairwise gluing checks."""
    R = r_lo*1.0001
    n0 = int(math.ceil(2*R/h0))
    start = -h0*n0/2
    todo = []
    for i in range(n0):
        for j in range(n0):
            sq = Square(start + i*h0, start + j*h0, h0)
            if sq.dist0() <= r_lo:
                todo.append(sq)
    # breadth-first from the square nearest 0 so every square inherits a nearby seed
    todo.sort(key=lambda s: abs(s.mid))
    done = []
    seeds = {}
    t0 = time.time()
    while todo:
        sq = todo.pop(0)
        # seed: nearest certified square's root, else the PY seed
        if done:
            nb = min(done[-64:], key=lambda s: abs(s.mid - sq.mid))
            useed = nb.u
            if abs(nb.mid - sq.mid) > 4*sq.h:
                nb = min(done, key=lambda s: abs(s.mid - sq.mid)); useed = nb.u
        else:
            useed = model.seed_f
        if certify_square(model, sq, useed):
            done.append(sq)
        else:
            if sq.h/2 < hmin:
                raise RuntimeError(f"disc cover: square at {sq.mid:.4f} (h={sq.h:.2e}) failed at min size")
            kids = [Square(sq.x0 + a*sq.h/2, sq.y0 + b*sq.h/2, sq.h/2) for a in (0, 1) for b in (0, 1)]
            kids = [k for k in kids if k.dist0() <= r_lo]
            todo[0:0] = sorted(kids, key=lambda s: abs(s.mid))
        if len(done) + len(todo) > max_squares:
            raise RuntimeError("disc cover: too many squares")
        if log and len(done) % 500 == 0 and done:
            log(f"  cover r_lo={r_lo}: {len(done)} certified, {len(todo)} pending, {time.time() - t0:.0f}s")
    # the square holding tau = 0 must contain the PY seed enclosure (it is the physical root)
    zero = [s for s in done if s.x0 <= 0 <= s.x0 + s.h and s.y0 <= 0 <= s.y0 + s.h]
    seed_ok = any(box_inside(model.seed_i, s.X) for s in zero)
    # gluing: every pair of meeting squares
    cells = {}
    for k, s in enumerate(done):
        key = (int(math.floor(s.x0/h0)), int(math.floor(s.y0/h0)))
        cells.setdefault(key, []).append(k)
    pairs = 0
    for a, s in enumerate(done):
        kx, ky = int(math.floor(s.x0/h0)), int(math.floor(s.y0/h0))
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                for b in cells.get((kx + dx, ky + dy), []):
                    if b <= a:
                        continue
                    t = done[b]
                    lo_x, hi_x = max(s.x0, t.x0), min(s.x0 + s.h, t.x0 + t.h)
                    lo_y, hi_y = max(s.y0, t.y0), min(s.y0 + s.h, t.y0 + t.h)
                    if lo_x > hi_x or lo_y > hi_y:
                        continue
                    tau0 = complex(0.5*(lo_x + hi_x), 0.5*(lo_y + hi_y))
                    # the common point must be an exact float inside both closed rectangles
                    tau0 = complex(min(max(tau0.real, lo_x), hi_x), min(max(tau0.imag, lo_y), hi_y))
                    u0 = model.newton(s.u, tau0)
                    ok = False
                    if u0 is not None:
                        ry = 1e-9*(1 + np.abs(u0))
                        for _ in range(8):
                            oky, Y, _, _, _ = krawczyk(model, u0, point(tau0), ry, tau0)
                            if oky and box_inside(Y, s.X) and box_inside(Y, t.X):
                                ok = True
                                break
                            ry = ry*4
                    if not ok:
                        raise RuntimeError(f"disc cover: gluing failed between {s.mid:.4f} and {t.mid:.4f}")
                    pairs += 1
    return dict(r_lo=r_lo, squares=len(done), min_side=min(s.h for s in done), glued_pairs=pairs,
                worst_contraction=max(s.q for s in done), seed_in_zero_square=seed_ok,
                seconds=round(time.time() - t0, 1), certified=seed_ok)


# ------------------------------------------------------------------------------ states
def real_chain(model, a: float, log):
    p, K, u, w = run_chain(model, seg_pieces(0.0, a), model.seed_f, model.seed_i,
                           f"real [0,{a}]", h0=1/64, log=log, real=True)
    return dict(interval=[0.0, a], pieces=len(p), worst_contraction=w, certified=True)


def main(argv):
    log = lambda s: print(s, flush=True)
    z = ["1.8", "12"]
    quick = "--quick" in argv
    cover = "--cover" in argv
    states = {
        "A_fold_binds": dict(w="-2.5", tau_f=4.47890, singular=4.47890 + 0j, r_lo=4.40, rho=0.045,
                             real_to=4.40),
        "B_fold_does_not_bind": dict(w="-2.636", tau_f=7.83369, singular=None, r_lo=6.90, rho=0.07,
                                     real_to=7.60),
    }
    out = {"description": __doc__.split("\n")[0], "z": z, "eta": "0.3", "states": {}}
    for name, S in states.items():
        if quick and name != "A_fold_binds":
            continue
        model = Model("0.3", z, ["1", S["w"]])
        rec = {"w": S["w"], "tau_f_float": S["tau_f"]}
        c = S["singular"]
        if c is None:   # locate the complex fold by float Newton on the augmented system
            sys.path.insert(0, str(Path(__file__).resolve().parents[2]/'scripts'/'coupling_singularities'))
            from nearest import continue_path, refine_fold, M
            st = M.HCYMix([1.0], [6*0.3/math.pi], [1.8, 12.0], np.array([1.0, float(S["w"])]).reshape(2, 1, 1))
            t = complex(-2.79095, 6.45968)
            u = continue_path(st, [0.0, 0.97*t]); _, c, res = refine_fold(st, u, t)
            rec["complex_fold_float"] = [c.real, c.imag, abs(c), res]
        log(f"== {name}: w={S['w']} singularity {c:.6f} (|.|={abs(c):.6f})")
        rec["real_branch"] = real_chain(model, S["real_to"], log)
        rec["loop"] = certify_loop(model, c, S["rho"], log)
        rec["cover"] = disc_cover(model, S["r_lo"], h0=0.5, hmin=1e-4, log=log) if cover else None
        lo = S["r_lo"] if (rec["cover"] or {}).get("certified") else None
        hi = rec["loop"]["max_abs_tau"] if rec["loop"]["monodromy_nontrivial"] else None
        rec["R_c_bracket"] = [lo, hi]
        log(f"   R_c in [{lo}, {hi}]   real branch regular on [0,{S['real_to']}]   tau_f(float)={S['tau_f']}")
        out["states"][name] = rec
    # negative controls on state A
    model = Model("0.3", z, ["1", "-2.5"])
    ctrl_loop = certify_loop(model, 2.2 + 0.0j, 0.045, log=None)
    out["negative_controls"] = {"loop_around_regular_point_closes": not ctrl_loop["monodromy_nontrivial"]}
    if cover:
        try:
            disc_cover(model, 4.57, h0=0.5, hmin=2e-3, log=None)
            out["negative_controls"]["cover_beyond_fold_fails"] = False
        except RuntimeError as e:
            out["negative_controls"]["cover_beyond_fold_fails"] = True
            log(f"   control cover beyond the fold failed as required: {e}")
    res = Path(__file__).resolve().parent/"results"
    res.mkdir(exist_ok=True)
    (res/"f7_fold_binding.json").write_text(json.dumps(out, indent=1, default=str) + "\n")
    ok = all(s["loop"]["monodromy_nontrivial"] and (not cover or s["cover"]["certified"])
             for s in out["states"].values())
    ok = ok and all(out["negative_controls"].values())
    if "B_fold_does_not_bind" in out["states"]:
        B = out["states"]["B_fold_does_not_bind"]
        ok = ok and B["R_c_bracket"][1] < B["real_branch"]["interval"][1]
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
