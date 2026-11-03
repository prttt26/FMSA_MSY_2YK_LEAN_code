"""r in terms of H alone: r(x) = E m0 - x E ln H(x), E = sum_t theta_t d/d theta_t, m0 = sum_t theta_t H_t (exact rational algebra, NOT a Lean proof).

From the integrals, by hand: r(x) = (1/pi) int k^2/(x^2 + k^2) [1/(1 - th(k)) - 1] dk and ln H(x) = (x/pi) int 1/(x^2 + k^2) ln(1/(1 - th(k))) dk. E takes ln(1/(1 - th)) to 1/(1 - th) - 1, and k^2/(x^2 + k^2) = 1 - x^2/(x^2 + k^2), so r(x) + x E ln H(x) does not depend on x; x -> infinity gives E m0. If so, with ln H(x) + ln H(-x) = -ln(1 - v(x)), the odd part of r follows at once.
Check: exact Taylor polynomials in theta at rational rates, by Picard on H_s = 1/(1 - sum_t theta_t H_t/(z_s + z_t)) and on r_s = H_s sum_t theta_t H_t (z_t - r_t)/(z_s + z_t), then compare at x = z_s and at off-node x, with H(x), r(x) from the same equations. Repeated rates included. Also the Lean quadratic formulas of handoff 300 as a control.

Usage: r_euler_identity.py [--order N]
"""
import sys
import sympy as sp


def trunc(e, X, N):
    P = sp.Poly(sp.expand(e), *X); return sum(c*sp.prod(a**k for a, k in zip(X, m)) for m, c in P.terms() if sum(m) <= N)


def inv1(e, X, N):
    """1/(1 - e), e without constant term."""
    t = sp.Integer(1); s = sp.Integer(1)
    for _ in range(N):
        t = trunc(t*e, X, N); s += t
    return s


def logH(H, X, N):
    d = H - 1; t = sp.Integer(1); s = sp.Integer(0)
    for n in range(1, N + 1):
        t = trunc(t*d, X, N); s += sp.Rational((-1)**(n + 1), n)*t
    return s


def euler(e, X):
    return sp.expand(sum(a*sp.diff(e, a) for a in X))


def run(z, N):
    T = len(z); X = sp.symbols(f't0:{T}'); H = [sp.Integer(1)]*T; R = [sp.Integer(0)]*T
    for _ in range(N + 1):
        H = [inv1(sum(X[t]*H[t]/(z[s] + z[t]) for t in range(T)), X, N) for s in range(T)]
    for _ in range(N + 1):
        R = [trunc(H[s]*sum(X[t]*H[t]*(z[t] - R[t])/(z[s] + z[t]) for t in range(T)), X, N) for s in range(T)]
    m0 = trunc(sum(X[t]*H[t] for t in range(T)), X, N); Em = euler(m0, X); out = []
    for s in range(T):
        out.append(sp.expand(R[s] - trunc(Em - z[s]*euler(logH(H[s], X, N), X), X, N)) == 0)
    for x in (sp.Rational(7, 3), sp.Rational(1, 5)):
        Hx = inv1(sum(X[t]*H[t]/(x + z[t]) for t in range(T)), X, N); Rx = trunc(Hx*sum(X[t]*H[t]*(z[t] - R[t])/(x + z[t]) for t in range(T)), X, N)
        out.append(sp.expand(Rx - trunc(Em - x*euler(logH(Hx, X, N), X), X, N)) == 0)
    return out, R, X


if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(exact rational algebra, NOT a Lean proof)', flush=True)
    N = int(sys.argv[sys.argv.index('--order') + 1]) if '--order' in sys.argv else 6
    for z in ([sp.Rational(3, 2)], [sp.Rational(1, 2), sp.Rational(7, 4)], [sp.Rational(5, 4), sp.Rational(5, 4)], [sp.Integer(1), sp.Rational(2, 3), sp.Rational(9, 5)]):
        o = N if len(z) < 3 else min(N, 5); res, R, X = run(z, o); print(f'z = {z}, order {o}: identity at each node and at two off-node x: {res}', flush=True)
    res, R, X = run([sp.Rational(1, 2), sp.Rational(7, 4)], 2); a, b = sp.Rational(1, 2), sp.Rational(7, 4); P = sp.Poly(R[0], *X)
    print('control, handoff 300, s = 0: [t0 t1] =', P.coeff_monomial(X[0]*X[1]), 'formula', 4*a*b/((a + a)*(a + b)*(a + b)), '; [t1^2] =', P.coeff_monomial(X[1]**2), 'formula', b/(a + b)**2, flush=True)
