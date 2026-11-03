#!/usr/bin/env python3
"""Exact symbolic check of the prospective inverse-dressing origin principal part.

This is diagnostic algebra, not a Lean proof or analytic Laurent extraction.
The actual W,C finite sums determine p0,v0,p1,v1 in the companion Lean file.
"""

import sympy as sp


def main() -> None:
    s = sp.symbols("s")
    a, q, m, n, c, v0, v1 = sp.symbols("a q m n c v0 v1")
    p0 = 1 + m + c - v0
    p1 = n + v0 - c / 2 - v1
    p2, p3, v2, v3 = sp.symbols("p2 p3 v2 v3")
    A = a * (1 + m) + 4 * (a - q) * n
    Q = q * (1 + m) + a * n
    P = -A / s**3 + (A - Q) / s**2 + (Q - A / 2 - c) / s
    P += p0 + p1 * s + p2 * s**2 + p3 * s**3
    Shat = A / s**3 + Q / s**2 + c / s
    Shat += v0 + v1 * s + v2 * s**2 + v3 * s**3
    hard_p = 1 - a / s**3 + (a - q) / s**2 + (q - a / 2) / s
    hard_shat = a / s**3 + q / s**2
    d = sp.expand(hard_p * Shat - hard_shat * P)
    g = sp.expand(s * d)
    u = sp.expand(
        hard_p.subs(s, -s) * P - hard_shat.subs(s, -s) * Shat + d
    )
    det = a**2 - 4 * a * q - 8 * a + 4 * q**2 + 8 * q
    for power in range(-5, -2):
        assert sp.expand(g.coeff(s, power)) == 0, ("g", power)
        assert sp.expand(u.coeff(s, power)) == 0, ("u", power)
    assert sp.expand(g.coeff(s, -2) + n * det / 2) == 0
    assert sp.expand(u.coeff(s, -2) + (m + 2 * n + 1) * det / 4) == 0
    assert sp.expand(g.coeff(s, -1)) == 0
    assert sp.expand(u.coeff(s, -1)) == 0
    print("PASS: inverse dressing principal coefficients cancel modulo PY determinant")


if __name__ == "__main__":
    main()
