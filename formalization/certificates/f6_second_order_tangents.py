#!/usr/bin/env python3
"""F6 certificate: two supporting coexistence pairs at second coupling order.

Model (SI, "Finite coupling orders", one attractive Yukawa tail, compressibility route):
the strict second-order jet

    a(eta) = d(beta p)/d rho = c0 + c1 tau + c2 tau^2,   eta = pi rho / 6,  tau = 1/T*,

with the closed coefficients of `release/fmsa_mixture/paper/finite_order_two_tangents.py`
(`coeffs`). Then beta p = int_0^rho a, beta mu = log rho + int_0^eta q with
q = (a - 1)/eta (regular at 0), and f = beta f/V = rho mu - p (up to a linear term).

Claims, for z = 5, T* = 0.02 (tau = 50), with rigorous outward-rounded interval
arithmetic (Taylor-model integrands, Simpson's rule with an enclosed fourth-derivative
remainder):

1. There are two pairs (rho_a, rho_b), each with p(rho_a) = p(rho_b) and
   mu(rho_a) = mu(rho_b) (2x2 Krawczyk, unique in the stated boxes).
2. For each pair the common tangent l(rho) = mu* rho - p* satisfies f >= l on the whole
   domain 0 < rho < 6/pi (eta < 1), with equality only at the two tangency points:
   * near each tangency point a > 0 on a window containing its box, so g = f - l is convex
     there with g = g' = 0 at the point;
   * elsewhere on a grid of cells, g > 0 by a second-order Taylor lower bound;
   * on (0, rho_0] g' = mu - mu* < 0, and on [rho_1, 6/pi) a > 0 and g'(rho_1) > 0.
Hence both are supporting (convex-hull) tangents: two coexistence pairs at order two.

    python3 f6_second_order_tangents.py      # writes results/f6_second_order_tangents.json
"""
from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import mpmath

sys.path.insert(0, str(Path(__file__).resolve().parent))
from f5_competing_tails import I, dn, up, iv_from_mp  # noqa: E402

mpmath.mp.prec = 200
Z = 5
TAU = 50                         # T* = 0.02 exactly


def mp_iv(x):
    e = abs(x) * mpmath.mpf(2) ** -180 + mpmath.mpf(2) ** -1000
    return iv_from_mp(x - e, x + e)


EXPZ = mp_iv(mpmath.exp(-Z))
PI = mp_iv(mpmath.pi)
SIX_OVER_PI = mp_iv(6 / mpmath.pi)


def ilog(x: I) -> I:
    """Enclosure of log over a positive interval (log is increasing)."""
    assert x.lo > 0
    lo, hi = mpmath.log(mpmath.mpf(x.lo)), mpmath.log(mpmath.mpf(x.hi))
    e = mpmath.mpf(2) ** -180
    return iv_from_mp(lo - abs(lo) * e - e, hi + abs(hi) * e + e)


# ------------------------------------------------------------- truncated Taylor series
ORDER = 4


class TS:
    """Truncated Taylor series sum_k c_k t^k (c_k intervals) about an interval point."""
    __slots__ = ("c",)

    def __init__(self, c):
        self.c = c

    @staticmethod
    def var(x: I):
        return TS([x, I(1.0)] + [I(0.0)] * (ORDER - 1))

    @staticmethod
    def lift(o):
        if isinstance(o, TS):
            return o
        return TS([I.of(o)] + [I(0.0)] * ORDER)

    def __add__(self, o):
        o = TS.lift(o)
        return TS([a + b for a, b in zip(self.c, o.c)])

    __radd__ = __add__

    def __neg__(self):
        return TS([-a for a in self.c])

    def __sub__(self, o):
        return self + (-TS.lift(o))

    def __rsub__(self, o):
        return TS.lift(o) + (-self)

    def __mul__(self, o):
        if not isinstance(o, TS):
            o = I.of(o)
            return TS([a * o for a in self.c])
        out = []
        for k in range(ORDER + 1):
            s = I(0.0)
            for j in range(k + 1):
                s = s + self.c[j] * o.c[k - j]
            out.append(s)
        return TS(out)

    __rmul__ = __mul__

    def recip(self):
        r0 = self.c[0].inv()
        r = [r0]
        for k in range(1, ORDER + 1):
            s = I(0.0)
            for j in range(1, k + 1):
                s = s + self.c[j] * r[k - j]
            r.append(-(r0 * s))
        return TS(r)

    def __truediv__(self, o):
        if isinstance(o, TS):
            return self * o.recip()
        return self * I.of(o).inv()

    def __rtruediv__(self, o):
        return self.recip() * o


def pw(x, n):
    out = x
    for _ in range(n - 1):
        out = out * x
    return out


# ----------------------------------------------------------------------- the model
def parts(eta):
    """(a, q) as functions of eta; works for I, TS and float arguments."""
    E = EXPZ if not isinstance(eta, float) else math.exp(-Z)
    z = Z
    w = 1 - eta
    J = E * (z + 2) + (z - 2)
    H0 = E * (2 * z + 2) + (z * z - 2)
    P = eta * eta * (J * 18) + eta * w * (H0 * 6) + w * w * z ** 3
    L = eta * 2 + w * z + 1
    H = eta * (J * 6) + w * H0
    one2 = 1 + eta * 2
    w4 = pw(w, 4)
    P2 = P * P
    P5 = P2 * P2 * P
    q0 = (8 - eta * 2 + eta * eta * 4 - pw(eta, 3)) / w4
    q1 = -(one2 * L * (24 * z ** 4)) / P2
    q2 = eta * pw(w, 7) * H * (144 * z ** 11) / P5
    q = q0 + q1 * TAU + q2 * (TAU * TAU)
    a = 1 + eta * q
    return a, q


def a_times_w4(eta: I) -> I:
    """a * (1-eta)^4, finite up to eta = 1 (used to show a > 0 near packing)."""
    E, z = EXPZ, Z
    w = 1 - eta
    J = E * (z + 2) + (z - 2)
    H0 = E * (2 * z + 2) + (z * z - 2)
    P = eta * eta * (J * 18) + eta * w * (H0 * 6) + w * w * z ** 3
    L = eta * 2 + w * z + 1
    H = eta * (J * 6) + w * H0
    one2 = 1 + eta * 2
    P2 = P * P
    P5 = P2 * P2 * P
    return one2 * one2 - eta * one2 * L * pw(w, 4) * (24 * z ** 4 * TAU) / P2 \
        + eta * eta * pw(w, 11) * H * (144 * z ** 11 * TAU * TAU) / P5


def simpson(fidx, a: float, b: float, tol: float):
    """Enclosure of int_a^b f, f = parts(.)[fidx], with Simpson remainder enclosed."""
    m = 0.5 * (a + b)
    h = b - a
    fa, fm, fb = (parts(I(x))[fidx] for x in (a, m, b))
    hh = I(b) - I(a)                                # encloses the exact width b - a
    S = (fa + 4.0 * fm + fb) * hh / 6.0
    c4 = parts(TS.var(I(a, b)))[fidx].c[4]          # f''''/4! over the cell
    err = c4 * (hh * hh * hh * hh * hh / 120.0)     # Simpson: E = -(h^5/2880) f''''
    if err.mag() > max(tol, 1e-14 * S.mag()) and h > 1e-9:
        return simpson(fidx, a, m, tol / 2) + simpson(fidx, m, b, tol / 2)
    return S - err


def integrals(a: float, b: float, tol=1e-15):
    return simpson(0, a, b, tol), simpson(1, a, b, tol)


# ------------------------------------------------------------------- pair Krawczyk
def float_pair(xa, xb):
    """Float refinement of a pair (in eta) by Newton on the validated midpoint values."""
    from scipy.integrate import quad
    fa = lambda e: parts(float(e))[0]
    fq = lambda e: parts(float(e))[1]
    A = lambda e: quad(fa, 0, e, limit=500, epsabs=1e-16, epsrel=1e-15)[0]
    B = lambda e: quad(fq, 0, e, limit=500, epsabs=1e-16, epsrel=1e-15)[0]
    x, y = xa, xb
    for _ in range(40):
        H1 = A(x) - A(y)
        H2 = math.log(x) + B(x) - math.log(y) - B(y)
        a_x, a_y = fa(x), fa(y)
        det = a_x * (-a_y / y) - (-a_y) * (a_x / x)
        dx = (-H1 * (-a_y / y) + a_y * (-H2)) / det
        dy = (a_x * (-H2) - (a_x / x) * (-H1)) / det
        x, y = x + dx, y + dy
        if abs(dx) + abs(dy) < 1e-16:
            break
    return x, y


class Cumulative:
    """Validated A(eta) = int_0^eta a and B(eta) = int_0^eta q at chosen nodes."""

    def __init__(self, nodes):
        self.nodes = sorted(set(nodes))
        self.A = {0.0: I(0.0)}
        self.B = {0.0: I(0.0)}
        prev = 0.0
        for x in self.nodes:
            if x == 0.0:
                continue
            dA, dB = integrals(prev, x)
            self.A[x] = self.A[prev] + dA
            self.B[x] = self.B[prev] + dB
            prev = x

    def at(self, x: float):
        if x in self.A:
            return self.A[x], self.B[x]
        # nearest node to the left, then integrate
        left = max(n for n in self.A if n < x)
        dA, dB = integrals(left, x)
        self.A[x], self.B[x] = self.A[left] + dA, self.B[left] + dB
        return self.A[x], self.B[x]


def rho_of(eta) -> I:
    return I.of(eta) * SIX_OVER_PI


def mu_p(cum: Cumulative, x: float):
    A, B = cum.at(x)
    rho = rho_of(x)
    return ilog(rho) + B, A * SIX_OVER_PI


def krawczyk_pair(cum: Cumulative, xt: float, yt: float, rad: float):
    """Krawczyk test for H(x, y) = (A(x) - A(y), log x + B(x) - log y - B(y)) = 0."""
    Ax, Bx = cum.at(xt)
    Ay, By = cum.at(yt)
    H1 = Ax - Ay
    H2 = ilog(I(xt)) + Bx - ilog(I(yt)) - By
    X = I(dn(xt - rad * xt), up(xt + rad * xt))
    Y = I(dn(yt - rad * yt), up(yt + rad * yt))
    ax, ay = parts(X)[0], parts(Y)[0]
    J = [[ax, -ay], [ax / X, -(ay / Y)]]
    fx, fy = parts(xt)[0], parts(yt)[0]
    Jm = [[fx, -fy], [fx / xt, -fy / yt]]
    det = Jm[0][0] * Jm[1][1] - Jm[0][1] * Jm[1][0]
    Cm = [[Jm[1][1] / det, -Jm[0][1] / det], [-Jm[1][0] / det, Jm[0][0] / det]]
    CH = [H1 * Cm[0][0] + H2 * Cm[0][1], H1 * Cm[1][0] + H2 * Cm[1][1]]
    E = [[(1.0 if i == j else 0.0) - (J[0][j] * Cm[i][0] + J[1][j] * Cm[i][1]) for j in range(2)]
         for i in range(2)]
    dX = [X - xt, Y - yt]
    ctr = [xt, yt]
    K = [I(ctr[i]) - CH[i] + E[i][0] * dX[0] + E[i][1] * dX[1] for i in range(2)]
    q = max(E[i][0].mag() + E[i][1].mag() for i in range(2))
    ok = q < 1 and K[0].inside(X) and K[1].inside(Y)
    return ok, (X, Y), K, q


# --------------------------------------------------------------- tangent checks
def a_positive_on(lo: float, hi: float, n=64):
    step = (hi - lo) / n
    for k in range(n):
        cell = I(lo + k * step, lo + (k + 1) * step if k < n - 1 else hi)
        if not parts(cell)[0].lo > 0:
            if (hi - lo) < 1e-9:
                return False
            mid = 0.5 * (cell.lo + cell.hi)
            if not (a_positive_on(cell.lo, mid, 8) and a_positive_on(mid, cell.hi, 8)):
                return False
    return True


def g_cell_positive(cum, mus, ps, ea, eb, depth=0):
    """Lower bound of g = rho mu - p - mu* rho + p* on [ea, eb] (eta) is > 0."""
    mua, pa = mu_p(cum, ea)
    ra = rho_of(ea)
    rcell = rho_of(I(ea, eb))
    g = ra * mua - pa - mus * ra + ps
    gp = mua - mus
    gpp = parts(I(ea, eb))[0] / rcell
    d = rcell - ra                                     # rho - rho_a over the cell
    d = I(0.0, d.hi)
    lb = (g + gp * d + gpp * (d * d) * 0.5).lo
    if lb > 0:
        return True, 1
    if depth > 30:
        return False, 1
    m = 0.5 * (ea + eb)
    ok1, n1 = g_cell_positive(cum, mus, ps, ea, m, depth + 1)
    if not ok1:
        return False, n1
    ok2, n2 = g_cell_positive(cum, mus, ps, m, eb, depth + 1)
    return ok2, n1 + n2


def main():
    t0 = time.time()
    # float self-check against the release script's closed form
    fa_check = []
    sys.path.insert(0, str(Path(__file__).resolve().parents[4] / "release/fmsa_mixture/paper"))
    try:
        import finite_order_two_tangents as T  # optional cross-check
        for rho in (0.003, 0.05, 0.4, 1.5):
            fa_check.append(abs(parts(math.pi * rho / 6)[0] - float(T.a2(rho, 5.0, 0.02))))
    except ImportError:
        pass
    guesses = [(0.002883496543394158, 0.051563026364078605), (0.4612024750315656, 1.5370943346250914)]
    eta0, eta1 = 1e-5, 0.97
    pairs_f = [float_pair(math.pi * a / 6, math.pi * b / 6) for a, b in guesses]
    nodes = [0.0, eta0] + [eta0 * (1e-2 / eta0) ** (k / 300) for k in range(301)] + \
            [1e-2 + (eta1 - 1e-2) * k / 2000 for k in range(2000)] + [eta1] + [x for pr in pairs_f for x in pr]
    cum = Cumulative(nodes)
    out = {"model": {"z": Z, "T_star": "0.02", "tau": TAU, "a_closed_form": "finite_order_two_tangents.coeffs"},
           "float_crosscheck_max_abs_diff": max(fa_check) if fa_check else None, "pairs": []}
    all_ok = True
    for (xt, yt) in pairs_f:
        rad = 1e-12
        for _ in range(20):
            ok, (X, Y), K, q = krawczyk_pair(cum, xt, yt, rad)
            if ok:
                break
            rad *= 4
        assert ok, ("pair Krawczyk failed", xt, yt)
        # mu*, p* enclosures from the boxes: value at the float point + derivative * offset
        mux, px = mu_p(cum, xt)
        ax = parts(X)[0]
        mus = mux + (ax / X) * (X - xt)                # d mu / d eta = a / eta
        ps = px + ax * SIX_OVER_PI * (X - xt)          # d p / d eta = (6/pi) a
        # convexity windows around the four tangency points
        win = []
        for c, Bx in ((xt, X), (yt, Y)):
            for frac in (0.15, 0.08, 0.04, 0.02, 0.01):
                lo, hi = c * (1 - frac), c * (1 + frac)
                if a_positive_on(lo, hi):
                    break
            else:
                raise AssertionError(("a not positive on any window", c))
            assert lo < Bx.lo and Bx.hi < hi
            win.append((lo, hi))
        # g > 0 on the grid outside the windows, eta in [eta0, eta1]
        grid = sorted(set([n for n in cum.nodes if eta0 <= n <= eta1] + [w for pr in win for w in pr]))
        cells = 0
        for ea, eb in zip(grid[:-1], grid[1:]):
            if any(lo <= ea and eb <= hi for lo, hi in win):
                continue
            okc, nc = g_cell_positive(cum, mus, ps, ea, eb)
            cells += nc
            assert okc, ("g lower bound failed", ea, eb)
        # (0, eta0]: g' = mu - mu* < 0 (mu <= log rho0 + eta0 sup|q|)
        qsup = parts(I(0.0, eta0))[1].mag()
        mu_up = (ilog(rho_of(eta0)) + I(-qsup, qsup) * eta0).hi
        low_ok = mu_up < mus.lo
        # [eta1, 1): a > 0 (via a w^4) and g'(eta1) > 0
        n_hi = 400
        hi_ok = all(a_times_w4(I(eta1 + (1 - eta1) * k / n_hi, eta1 + (1 - eta1) * (k + 1) / n_hi if k < n_hi - 1 else 1.0)).lo > 0
                    for k in range(n_hi))
        mu1, _ = mu_p(cum, eta1)
        hi_ok = hi_ok and (mu1 - mus).lo > 0
        ok_pair = low_ok and hi_ok
        all_ok &= ok_pair
        out["pairs"].append({
            "eta_box": [[X.lo, X.hi], [Y.lo, Y.hi]],
            "rho_box": [[rho_of(X).lo, rho_of(X).hi], [rho_of(Y).lo, rho_of(Y).hi]],
            "beta_mu": [mus.lo, mus.hi], "beta_p": [ps.lo, ps.hi],
            "krawczyk_contraction": q, "convex_windows_eta": win,
            "grid_cells_checked": cells, "low_density_monotone": low_ok,
            "high_density_monotone": hi_ok, "supporting_tangent_certified": ok_pair,
        })
        print(out["pairs"][-1], flush=True)
    distinct = out["pairs"][0]["beta_mu"][1] < out["pairs"][1]["beta_mu"][0]
    # negative control on the low-density pair: raising the tangent by 1e-6 must make the
    # cell test fail (g < 0 at the tangency point); lowering it must pass everywhere,
    # windows included
    xt, _ = pairs_f[0]
    mus0, ps0 = mu_p(cum, xt)
    grid = sorted(n for n in cum.nodes if eta0 <= n <= eta1)
    ctrl = {}
    for delta, key in ((-1e-6, "raised_line_fails"), (1e-6, "lowered_line_passes")):
        passed = all(g_cell_positive(cum, mus0, ps0 + delta, ea, eb)[0]
                     for ea, eb in zip(grid[:-1], grid[1:]))
        ctrl[key] = (not passed) if delta < 0 else passed
    out["negative_control"] = ctrl
    print("negative control:", ctrl, flush=True)
    out["two_distinct_supporting_pairs"] = bool(all_ok and distinct and all(ctrl.values()))
    out["seconds"] = round(time.time() - t0, 1)
    res = Path(__file__).resolve().parent / "results"
    res.mkdir(exist_ok=True)
    (res / "f6_second_order_tangents.json").write_text(json.dumps(out, indent=1) + "\n")
    print("PASS" if out["two_distinct_supporting_pairs"] else "FAIL")
    return 0 if out["two_distinct_supporting_pairs"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
