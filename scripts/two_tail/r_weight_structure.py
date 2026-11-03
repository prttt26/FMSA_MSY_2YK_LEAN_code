"""Structure of the multilinear weight of r: is its numerator a polynomial with nonnegative coefficients? (exact rational algebra, NOT a Lean proof)

E_S(x) = n! W_S(x), W_S(x) = sum_{t in S} (z_t/(x + z_t)) prod_{u != t} 2 z_u/(z_u^2 - z_t^2), handoff 260. Its terms alternate. Put over the denominator prod_t (x + z_t) prod_{i<j} (z_i + z_j) and print the numerator; if it has nonnegative coefficients there may be a positive recursion needing no integral, which is what a Lean proof wants.

Usage: r_weight_structure.py [--max N]
"""
import sys
import sympy as sp


def weight(zs, x):
    tot = 0
    for t in zs:
        term = t/(x + t)
        for u in zs:
            if u != t: term *= 2*u/(u**2 - t**2)
        tot += term
    return tot


if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(exact rational algebra, NOT a Lean proof)', flush=True)
    M = int(sys.argv[sys.argv.index('--max') + 1]) if '--max' in sys.argv else 5
    x = sp.symbols('x')
    for n in range(1, M + 1):
        zs = sp.symbols(f'z1:{n + 1}'); den = sp.prod(x + z for z in zs)*sp.prod(zs[i] + zs[j] for i in range(n) for j in range(i + 1, n))
        num = sp.cancel(sp.together(weight(zs, x)*den)); P = sp.Poly(sp.numer(sp.together(num)), x, *zs); d = sp.denom(sp.together(num))
        cs = P.coeffs(); print(f'n = {n}: denominator leftover {d}; numerator degree {P.total_degree()}, {len(cs)} monomials, coefficients min {min(cs)} max {max(cs)}', flush=True)
        if n <= 3: print('  numerator:', sp.factor(P.as_expr()), flush=True)
