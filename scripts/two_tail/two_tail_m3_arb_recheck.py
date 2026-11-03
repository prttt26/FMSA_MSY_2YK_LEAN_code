"""Independent EXTERNAL Arb re-check of the M3 interval certificates (user request, after Codex 143).
NOT a Lean proof.

Codex 143 re-checked only the rational part of the M3 certificate; its analytic enclosures (f, J, A)
came from the mpmath-iv forward-mode AD of two_tail_m2_jacobian_interval.residual.  This script
recomputes them by a second, independent route, and imports nothing from the other two_tail scripts:
  * the residual is re-transcribed with SymPy from the literal Lean polynomials
    (MSAConvergence/BHResidualPolynomials.lean: gammaPoly, wPoly, cPoly, mPoly, nPoly, aPoly, qpPoly,
    qhatPoly, firstPoly, secondPoly) with N = 1, sigma = 1, and the constants Q0phys, Qppphys, xi2,
    vacMix of the frozen foundation (LeanCode/HSMixture/MatrixQ0.lean);
  * J and the Taylor coefficients are exact symbolic derivatives (no AD), and every polynomial is
    evaluated over a box as its exact Taylor expansion about the box center, with the coefficients
    enclosed by Arb (python-flint) at a point; only pi and exp need transcendental enclosures;
  * every Krawczyk expression, I - C J, and the norm are then formed in exact Fraction interval
    arithmetic from the outward dyadic Arb endpoints.

Re-checked:
  (a) every stored M3 Krawczyk witness (tau_hat, tau_lo, tau_hi, the rigorous-bracket ends, and the
      parametric box over the whole bracket), with the stored center, C and X, recomputing f and J;
      the stored enclosures are also required to intersect the Arb ones (a consistency check);
  (b) the endpoint signs, independently of the stored shrunk boxes: at each bracket end tau_e a
      tiny Krawczyk box S_e around an Arb Newton point, with K(S_e) strictly inside S_e, S_e strictly
      inside the parametric X, and A over S_e of one sign.  With (a) for the parametric box this
      gives the same-branch sign change: X has a unique root u(tau) for every tau in the bracket, the
      root at tau_e is the one in S_e, so tau -> A(u(tau)) is continuous with opposite end signs.
Not certified: first loss, canonicity, connection to the PY prefix, Taylor radii.

Requires python-flint 0.6.0 and SymPy 1.13.2, e.g.
  PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 two_tail_m3_arb_recheck.py OUT.json
"""
import sys, json, hashlib
from decimal import Decimal, localcontext, ROUND_CEILING
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb
from pathlib import Path
import numpy as np
import flint
from flint import arb, arb_mat, ctx, fmpq
import sympy as sp

PREC = 256
HERE = Path(__file__).resolve().parent
RES = HERE.parents[1]
SRC = RES/'results'/'two_tail'/'two_tail_endpoint_interval_exact.json'
LEAN = [RES/'MSAConvergence'/'BHResidualPolynomials.lean',
        RES.parent/'MSA_and_1st_Truncation'/'LeanCode'/'HSMixture'/'MatrixQ0.lean']
TINY = Q(1, 10**40)          # relative radius of the endpoint boxes S_e


# ---------- exact <-> Arb ----------
def ball(q):
    return arb(fmpq(q.numerator, q.denominator))


def exact(x):
    assert x.is_exact() and x.is_finite(), str(x)
    m, e = map(int, x.man_exp())
    return Q(m)*Q(2)**e


def bounds(x):
    assert x.is_finite(), str(x)
    return (exact(x.lower()), exact(x.upper()))


def iball(lo, hi):
    """An Arb ball covering the exact rational interval [lo, hi]."""
    rad = (hi - lo)/2
    for _ in range(4):
        b = arb(ball((lo + hi)/2), ball(rad))
        blo, bhi = bounds(b)
        if blo <= lo <= hi <= bhi:
            return b
        rad = rad*2 + Q(1, 2**(PREC + 64))
    raise AssertionError('ball does not cover the interval')


# ---------- exact Fraction intervals ----------
def add(a, b): return (a[0] + b[0], a[1] + b[1])
def sub(a, b): return (a[0] - b[1], a[1] - b[0])
def mul(a, b):
    p = (a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1]); return (min(p), max(p))
def pt(x): return (x, x)
def meets(a, b): return a[0] <= b[1] and b[0] <= a[1]
def strict_in(i, o): return o[0] < i[0] and i[1] < o[1]
def S(i): return [str(i[0]), str(i[1])]


def up(q, digits=8):
    """Decimal display rounded UP (non-authoritative; the Fraction is authoritative; Codex 148)."""
    with localcontext() as cx:
        cx.prec = digits
        cx.rounding = ROUND_CEILING
        return str(Decimal(q.numerator)/Decimal(q.denominator))
def I(s): return (Q(s[0]), Q(s[1]))


# ---------- symbolic residual from the Lean polynomials ----------
def symbolic(eta, z, w):
    D1, D2, G1, G2, tau = V = sp.symbols('D1 D2 G1 G2 tau')
    Dv, Gv = (D1, D2), (G1, G2)
    pi = sp.pi
    rho = 6*eta/pi                                   # etaMix = pi/6 rho sigma^3, sigma = 1
    vac = 1 - eta                                    # vacMix
    xi2 = rho                                        # xi2 = rho sigma^2
    Q0 = 2*pi/vac*(1 + pi*xi2/(4*vac))               # Q0phys, (sigma_i + sigma_j)/2 = 1
    Qpp = 2*pi/vac*(1 + pi*xi2/(2*vac))              # Qppphys
    gam = [1 - 2*pi*rho*sp.exp(-z[t])/z[t]*Gv[t] for t in range(2)]      # gammaPoly, sigMix = 1
    wt = [2*pi/z[t]*rho*Gv[t]*Dv[t] for t in range(2)]                     # wPoly
    ct = [gam[t]*Dv[t] for t in range(2)]                                  # cPoly, exp(0) = 1
    mt = [-(1/z[t])*rho*(wt[t] + (1 + z[t])*ct[t]) for t in range(2)]      # mPoly
    nt = [rho*(1/z[t]**2*wt[t] + (1 + z[t] + z[t]**2/2)/z[t]**2*ct[t]) for t in range(2)]   # nPoly
    a = Qpp + sum(Qpp*mt[t] + 2*pi**2*xi2/vac**2*nt[t] for t in range(2))                 # aPoly
    qp = Q0 + sum(Q0*mt[t] + Qpp*nt[t] for t in range(2))                                  # qpPoly

    def qhat(s):                                     # qhatPoly, edgeLo = 0, edgeHi = 1
        e = sp.exp(-s)
        return ((1 - s - e)/s**2*qp + (1 - s + s**2/2 - e)/s**3*a
                + sum(wt[t]/(s + z[t]) + ct[t]*(1 - e)/s for t in range(2))
                + sum(ct[t]*e/(s + z[t]) for t in range(2)))
    K = (1, w)
    first = [Dv[t]*(1 - rho*qhat(z[t])) - 2*pi*tau*K[t]/z[t] for t in range(2)]          # firstPoly
    second = [2*pi*Gv[t]*(1 - rho*qhat(z[t]))
              - (a + z[t]*qp + sum(z[t]**2*z[v]/(z[t] + z[v])*ct[v] for v in range(2)))/z[t]**2
              for t in range(2)]                                                         # secondPoly
    R = [sp.expand(r) for r in first + second]
    J = [[sp.expand(sp.diff(r, v)) for v in V[:4]] for r in R]
    A = sp.expand(a)
    assert all(sp.Poly(r, *V).total_degree() <= 3 for r in R)
    assert all(not (x.free_symbols & {tau}) for row in J for x in row)
    return V, R, J, A


def ipow(x, n):
    """Integer power by repeated multiplication (arb ** int is NaN on balls containing 0)."""
    if n < 0:
        return 1/ipow(x, -n)
    out = arb(1)
    for _ in range(n):
        out = out*x
    return out


@lru_cache(None)
def ev(expr):
    if expr.is_Rational:
        return ball(Q(int(expr.p), int(expr.q)))
    if expr == sp.pi:
        return arb.pi()
    if expr.func == sp.Add:
        return sum((ev(x) for x in expr.args), arb(0))
    if expr.func == sp.Mul:
        out = arb(1)
        for x in expr.args:
            out *= ev(x)
        return out
    if expr.func == sp.Pow and expr.exp.is_Integer:
        return ipow(ev(expr.base), int(expr.exp))
    if expr.func == sp.exp:
        return ev(expr.args[0]).exp()
    raise TypeError(f'unenclosed node {expr!r}')


class TaylorPoly:
    """A polynomial in V with Arb-enclosed coefficients, evaluated over a box as its exact Taylor
    expansion about the box center (degree <= 3, so there is no remainder term)."""
    def __init__(self, expr, V):
        self.terms = [(m, ev(c)) for m, c in sp.Poly(expr, *V, domain='EX').as_dict().items()]
        self.n = len(V)

    def over(self, center, h):
        """center: exact Fractions; h: Arb balls for (box - center).  Returns an Arb ball."""
        c = [ball(x) for x in center]
        tay = {}
        for m, a in self.terms:
            for beta in product(*[range(k + 1) for k in m]):
                t = a
                for k in range(self.n):
                    if m[k] - beta[k]:
                        t = t*comb(m[k], beta[k])*ipow(c[k], m[k] - beta[k])
                tay[beta] = tay.get(beta, arb(0)) + t
        out = arb(0)
        for beta, t in tay.items():
            for k in range(self.n):
                if beta[k]:
                    t = t*ipow(h[k], beta[k])
            out += t
        return out


# ---------- Krawczyk in exact Fractions from Arb enclosures ----------
def krawczyk(Rp, Jp, center, C, X, T, tau_c):
    """center, C exact; X list of exact intervals; T exact tau interval, tau_c its center point."""
    h = [iball(X[i][0] - center[i], X[i][1] - center[i]) for i in range(4)]
    zero = [arb(0)]*4
    ht = iball(T[0] - tau_c, T[1] - tau_c)
    f = [bounds(r.over(center + [tau_c], zero + [ht])) for r in Rp]          # f(center; T)
    J = [[bounds(x.over(center + [tau_c], h + [arb(0)])) for x in row] for row in Jp]
    E = [[None]*4 for _ in range(4)]
    for i in range(4):
        for j in range(4):
            acc = pt(Q(int(i == j)))
            for m in range(4):
                acc = sub(acc, mul(pt(C[i][m]), J[m][j]))
            E[i][j] = acc
    K = []
    for i in range(4):
        acc = pt(center[i])
        for m in range(4):
            acc = sub(acc, mul(pt(C[i][m]), f[m]))
        for j in range(4):
            acc = add(acc, mul(E[i][j], sub(X[j], pt(center[j]))))
        K.append(acc)
    norm = max(sum((max(abs(e[0]), abs(e[1])) for e in row), Q(0)) for row in E)
    ok = all(strict_in(K[i], X[i]) for i in range(4)) and norm < 1
    return dict(center=[str(x) for x in center], C_rational=[[str(x) for x in r] for r in C],
                X=[S(x) for x in X], T=S(T), tau_center=str(tau_c),
                f_center_arb=[S(x) for x in f], J_over_X_arb=[[S(x) for x in r] for r in J],
                I_minus_CJ=[[S(x) for x in r] for r in E], K=[S(x) for x in K],
                inf_norm_upper=str(norm), inf_norm_display=up(norm),
                K_strictly_inside_X=all(strict_in(K[i], X[i]) for i in range(4)), norm_lt_1=norm < 1), ok, f, J


def newton(Rp, Jp, x, tau):
    """Non-rigorous Newton on Arb midpoints (only produces a center)."""
    for _ in range(30):
        zero = [arb(0)]*5
        f = arb_mat([[Rp[i].over(x + [tau], zero).mid()] for i in range(4)])
        Jm = arb_mat([[Jp[i][j].over(x + [tau], zero).mid() for j in range(4)] for i in range(4)])
        dx = Jm.solve(f)
        x = [x[i] - exact(dx[i, 0].mid()) for i in range(4)]
    return x, Jm


def main():
    assert __debug__, 'run without -O'
    out = Path(sys.argv[1]).resolve()
    assert 'MSA_and_1st_Truncation' not in str(out)
    ctx.prec = PREC
    cmd = ' '.join([sys.executable] + sys.orig_argv[1:]); print('# ' + cmd, flush=True)
    print(f'# EXTERNAL Arb interval re-check (python-flint {flint.__version__}, SymPy {sp.__version__}, '
          f'{PREC} bits); not a Lean proof', flush=True)
    raw = SRC.read_bytes(); d = json.loads(raw)
    c = next(c for c in d['controls'] if c['name'].startswith('M3'))
    eta, z, w = sp.Rational(c['eta']), [sp.Rational(x) for x in c['z']], sp.Rational(c['w'])
    assert (eta, z, w) == (sp.Rational(49, 100), [7, 14], sp.Rational(-419, 384))
    V, R, J, A = symbolic(eta, z, w)
    Rp = [TaylorPoly(r, V) for r in R]; Jp = [[TaylorPoly(x, V) for x in row] for row in J]
    Ap = TaylorPoly(A, V)
    rec = dict(command=cmd, label='EXTERNAL Arb interval re-check; NOT a Lean proof',
               serialization='All endpoints are exact rationals; *_display fields are non-authoritative.',
               source=str(SRC), source_sha256=hashlib.sha256(raw).hexdigest(),
               lean_sha256={str(p.relative_to(RES.parent)): hashlib.sha256(p.read_bytes()).hexdigest() for p in LEAN},
               script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               versions=dict(python=sys.version.split()[0], python_flint=flint.__version__, sympy=sp.__version__),
               precision_bits=PREC, data=dict(eta=c['eta'], z=c['z'], w=c['w'], sigma='1', rho='6*eta/pi'),
               symbolic_sha256=hashlib.sha256('\n'.join(sp.srepr(x) for x in R + sum(J, []) + [A]).encode()).hexdigest(),
               coordinate_order=['D1', 'D2', 'G1', 'G2', 'tau'], witnesses={})
    allok = True
    # (a) stored witnesses
    stored = {f'runs.{k}': (c['runs'][k]['krawczyk'], Q(c['runs'][k]['tau'])) for k in ('tau_hat', 'tau_lo', 'tau_hi')}
    stored.update({f'rigorous_bracket.{k}': (c['rigorous_bracket'][k]['krawczyk'], Q(c['rigorous_bracket'][k]['tau']))
                   for k in ('lo', 'hi')})
    par = c['parametric']; tl, th = map(Q, par['tau_interval_exact'])
    assert (tl, th) == (Q(c['rigorous_bracket']['lo']['tau']), Q(c['rigorous_bracket']['hi']['tau']))
    stored['parametric'] = (par['krawczyk'], (tl, th))
    for name, (kw, tau) in stored.items():
        T = tau if isinstance(tau, tuple) else (tau, tau)
        tc = (T[0] + T[1])/2
        center = [Q(x) for x in kw['center']]; C = [[Q(x) for x in r] for r in kw['C_rational']]
        X = [I(x) for x in kw['X']]
        wit, ok, f, Jb = krawczyk(Rp, Jp, center, C, X, T, tc)
        cons = all(meets(f[i], I(kw['f_center'][i])) for i in range(4)) and \
            all(meets(Jb[i][j], I(kw['J_over_X'][i][j])) for i in range(4) for j in range(4))
        wit['stored_enclosures_intersect_arb'] = cons
        rec['witnesses'][name] = wit; allok &= ok and cons
        print(f'(a) {name}: K strictly inside X {wit["K_strictly_inside_X"]}, ||I-CJ|| <= {wit["inf_norm_display"]}; '
              f'stored f, J intersect Arb enclosures: {cons}', flush=True)
    # (b) tiny endpoint boxes inside the parametric X, and the signs of A
    PX = [I(x) for x in par['krawczyk']['X']]
    x0 = [Q(x) for x in par['krawczyk']['center']]
    ends = {}
    for e, tau in (('lo', tl), ('hi', th)):
        x, Jm = newton(Rp, Jp, x0, tau)
        Cf = np.linalg.inv(np.array([[float(Jm[i, j].mid()) for j in range(4)] for i in range(4)]))
        C = [[Q(float(Cf[i, j])) for j in range(4)] for i in range(4)]
        Sx = [(x[i] - TINY*max(1, abs(x[i])), x[i] + TINY*max(1, abs(x[i]))) for i in range(4)]
        wit, ok, _, _ = krawczyk(Rp, Jp, x, C, Sx, (tau, tau), tau)
        h = [iball(Sx[i][0] - x[i], Sx[i][1] - x[i]) for i in range(4)]
        Ab = bounds(Ap.over(x + [tau], h + [arb(0)]))
        sign = '+' if Ab[0] > 0 else '-' if Ab[1] < 0 else '0?'
        inside = all(strict_in(Sx[i], PX[i]) for i in range(4))
        A_old = I(c['rigorous_bracket'][e]['A_over_root'])          # mpmath-AD value, consistency only
        ends[e] = dict(tau=str(tau), witness=wit, A_over_S=S(Ab), A_display=f'{float(Ab[0]):.6e}', detF0_sign=sign,
                       S_strictly_inside_parametric_X=inside, stored_A_intersects_arb=meets(Ab, A_old),
                       stored_sign_agrees=sign == c['rigorous_bracket'][e]['detF0_sign'])
        allok &= ok and inside and sign in '+-' and ends[e]['stored_A_intersects_arb'] and ends[e]['stored_sign_agrees']
        print(f'(b) {e}: tau = {float(tau)!r}: S (rel radius {float(TINY):.0e}) K strictly inside {wit["K_strictly_inside_X"]}, '
              f'||I-CJ|| <= {wit["inf_norm_display"]}; S strictly inside parametric X: {inside}; '
              f'A over S = {float(Ab[0]):.6e} .. {float(Ab[1]):.6e}, sign {sign}; stored A intersects / stored sign agrees: '
              f"{ends[e]['stored_A_intersects_arb']} / {ends[e]['stored_sign_agrees']}", flush=True)
    opposite = {ends['lo']['detF0_sign'], ends['hi']['detF0_sign']} == {'+', '-'}
    allok &= opposite
    rec.update(endpoints=ends, opposite_signs=opposite, passed=allok)
    print(f"\nRESULT: {'PASS' if allok else 'FAIL'} -- the stored M3 Krawczyk witnesses hold with f and J recomputed "
          f"by symbolic differentiation and Arb; det F(0) = A/(2 pi) has signs {ends['lo']['detF0_sign']} / "
          f"{ends['hi']['detF0_sign']} at the bracket ends on the unique root of the parametric box.", flush=True)
    out.write_text(json.dumps(rec, indent=1) + '\n')
    return 0 if allok else 1


if __name__ == '__main__':
    sys.exit(main())
