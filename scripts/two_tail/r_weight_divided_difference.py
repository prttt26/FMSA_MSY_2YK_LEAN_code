"""The multilinear weight of r is a divided difference of the square root, and a Schur ratio (exact rational algebra and 50-digit quadrature, NOT a Lean proof).

W_S(x) = sum_t (z_t/(x + z_t)) prod_{u != t} 2 z_u/(z_u^2 - z_t^2). With y = (x, z_1, .., z_n), w = y^2, by hand:
 (1) W_S = 2^(n-1) (prod z) A, A = (-1)^(n-1) sum_j y_j/prod_{a != j}(y_j^2 - y_a^2) = (-1)^(n-1) [w_0, .., w_n] sqrt.
 (2) A = (2/pi) int_0^inf k^2 prod_a 1/(k^2 + w_a) dk, positive, by real partial fractions, each term being a convergent arctan integral for n >= 1.
 (3) A = s_{delta_(n-2)}(y)/prod_{a<b}(y_a + y_b), delta_m = (m, m-1, .., 1), from the bialternant with exponents (2n-2, .., 4, 2, 1, 0), so its numerator has nonnegative coefficients.
Checks: (1) and (3) as exact rational identities at random rational points, (3) against the bialternant, up to n = 8; (2) by mpmath quad at 50 digits, up to n = 6; and the repeated-rate limit against the integral.

Usage: r_weight_divided_difference.py [--seed S]
"""
import sys, random
from fractions import Fraction as Fr
import sympy as sp
import mpmath as mp


def W(zs, x):
    tot = Fr(0)
    for t in zs:
        term = t/(x + t)
        for u in zs:
            if u != t: term *= 2*u/(u*u - t*t)
        tot += term
    return tot


def dd_sqrt_form(y):
    tot = Fr(0)
    for j, yj in enumerate(y):
        p = Fr(1)
        for a, ya in enumerate(y):
            if a != j: p *= yj*yj - ya*ya
        tot += yj/p
    return tot


def det(M):
    return Fr(str(sp.Matrix(M).det(method='bareiss')))


if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(exact rational algebra and 50-digit quadrature, NOT a Lean proof)', flush=True)
    seed = int(sys.argv[sys.argv.index('--seed') + 1]) if '--seed' in sys.argv else 1; random.seed(seed); rnd = lambda: Fr(random.randint(1, 400), random.randint(1, 60))
    for n in range(1, 9):
        ok1 = ok3 = True
        for _ in range(6):
            zs = []
            while len(zs) < n:
                z = rnd()
                if z not in zs: zs.append(z)
            x = rnd()
            while x in zs: x = rnd()
            y = [x] + zs; A = (-1)**(n - 1)*dd_sqrt_form(y); pz = Fr(1)
            for z in zs: pz *= z
            ok1 &= W(zs, x) == 2**(n - 1)*pz*A; ok1 &= A > 0
            if n >= 2:
                exps = [2*(n - i) for i in range(1, n)] + [1, 0]; M = [[sp.Rational(v.numerator, v.denominator)**e for v in y] for e in exps]; V = [[sp.Rational(v.numerator, v.denominator)**(n - i) for v in y] for i in range(n + 1)]
                s = det(M)/det(V); d = Fr(1)
                for a in range(n + 1):
                    for b in range(a + 1, n + 1): d *= y[a] + y[b]
                ok3 &= A == s/d
        print(f'n = {n}: W = 2^(n-1) prod z A and A > 0 exact: {ok1}; A = s_delta/prod (y_a + y_b) exact: {ok3 if n >= 2 else "n/a"}', flush=True)
    mp.mp.dps = 50; worst = mp.mpf(0)
    for n in range(1, 7):
        for _ in range(3):
            zs = []
            while len(zs) < n:
                z = rnd()
                if z not in zs: zs.append(z)
            x = rnd()
            while x in zs: x = rnd()
            y = [x] + zs; A = (-1)**(n - 1)*dd_sqrt_form(y); Am = mp.mpf(A.numerator)/A.denominator; w = [mp.mpf(v.numerator)**2/mp.mpf(v.denominator)**2 for v in y]
            def f(k):
                p = k*k
                for a in w: p /= (k*k + a)
                return p
            pts = sorted(set([0] + [mp.sqrt(a) for a in w])) + [mp.inf]; I = 2/mp.pi*mp.quad(f, pts); worst = max(worst, abs(I/Am - 1))
    print(f'A against (2/pi) int_0^inf k^2 prod 1/(k^2 + w_a) dk, n <= 6: largest relative difference {mp.nstr(worst, 3)}', flush=True)
    x, z = Fr(3, 2), Fr(5, 2); h = Fr(1, 10**8)
    lim = W([z, z + h, z + 2*h], x); val = (2**2*(mp.mpf(z.numerator)/z.denominator)**3)*(2/mp.pi)*mp.quad(lambda k: k*k/(k*k + mp.mpf(9)/4)/(k*k + mp.mpf(25)/4)**3, [0, 2, mp.inf])
    print(f'repeated rate, n = 3, z = 5/2, x = 3/2: split limit {float(lim):.12f}, integral with the repeated factor {mp.nstr(val, 13)}', flush=True)
