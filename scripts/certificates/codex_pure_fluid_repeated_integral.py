#!/usr/bin/env python3
"""Exact-rational cross-check of a candidate all-multiindex r kernel formula.

This is a finite symbolic diagnostic, not a proof of the general identity.
It compares two independently computed rational quantities: coefficients
from the formal H/R/r recursions and a half-line kernel integral evaluated
by rational partial fractions in y = k^2.
"""

from __future__ import annotations

from collections import defaultdict
from functools import lru_cache
from fractions import Fraction as Q
from itertools import product
from math import comb, factorial
import json
from pathlib import Path


def poly_mul(a: list[Q], b: list[Q]) -> list[Q]:
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return out


def poly_pow(a: list[Q], n: int) -> list[Q]:
    out = [Q(1)]
    for _ in range(n):
        out = poly_mul(out, a)
    return out


def solve_exact(columns: list[list[Q]], target: list[Q]) -> list[Q]:
    n = len(columns)
    matrix = [[columns[j][i] if i < len(columns[j]) else Q(0)
               for j in range(n)] + [target[i]] for i in range(n)]
    for k in range(n):
        pivot = next((i for i in range(k, n) if matrix[i][k]), None)
        if pivot is None:
            raise ArithmeticError("partial-fraction basis is singular")
        matrix[k], matrix[pivot] = matrix[pivot], matrix[k]
        scale = matrix[k][k]
        matrix[k] = [v / scale for v in matrix[k]]
        for i in range(n):
            if i != k:
                factor = matrix[i][k]
                matrix[i] = [a - factor * b
                             for a, b in zip(matrix[i], matrix[k])]
    return [row[-1] for row in matrix]


def kernel_integral_over_pi(rates: tuple[Q, ...], x: Q,
                            m: tuple[int, ...]) -> Q:
    """Return (1/pi) integral_0^infinity k²/((k²+x²) prod_i(...))."""
    assert x > 0 and all(z > 0 for z in rates)
    assert any(m) and len(rates) == len(m)
    counts: dict[Q, int] = defaultdict(int)
    counts[x] += 1
    for z, power in zip(rates, m):
        counts[z] += power
    nodes = sorted((a, e) for a, e in counts.items() if e)
    degree = sum(e for _, e in nodes)
    labels: list[tuple[Q, int]] = []
    basis: list[list[Q]] = []
    for a, e in nodes:
        for j in range(1, e + 1):
            p = [Q(1)]
            for b, eb in nodes:
                p = poly_mul(p, poly_pow([b * b, Q(1)], eb - (j if b == a else 0)))
            labels.append((a, j))
            basis.append(p)
    target = [Q(0)] * degree
    target[1] = Q(1)
    coeffs = solve_exact(basis, target)
    # Independent polynomial-identity check after the solve.
    assert all(sum(coeffs[j] * (basis[j][i] if i < len(basis[j]) else 0)
                   for j in range(degree)) == target[i] for i in range(degree))
    return sum((A * Q(comb(2 * j - 2, j - 1), 2 ** (2 * j - 1))
                / a ** (2 * j - 1)
                for A, (a, j) in zip(coeffs, labels)), Q(0))


def recursive_coefficient(rates: tuple[Q, ...], x: Q,
                          monomial: tuple[int, ...]) -> Q:
    tails = range(len(rates))
    zero = (0,) * len(rates)

    def splits(m: tuple[int, ...]):
        for p in product(*(range(v + 1) for v in m)):
            yield p, tuple(m[i] - p[i] for i in tails)

    def remove(m: tuple[int, ...], t: int) -> tuple[int, ...]:
        return tuple(m[i] - (i == t) for i in tails)

    @lru_cache(None)
    def H(s: int, m: tuple[int, ...]) -> Q:
        if m == zero:
            return Q(1)
        return sum((sum((H(s, p) * H(t, q) for p, q in splits(remove(m, t))), Q(0))
                    / (rates[s] + rates[t]) for t in tails if m[t]), Q(0))

    @lru_cache(None)
    def R(s: int, m: tuple[int, ...]) -> Q:
        if m == zero:
            return Q(0)
        total = Q(0)
        for t in tails:
            if not m[t]:
                continue
            d = remove(m, t)
            for p, rest in splits(d):
                for q, r in splits(rest):
                    total += H(s, p) * H(t, q) * (rates[t] * (r == zero) - R(t, r)) \
                        / (rates[s] + rates[t])
        return total

    @lru_cache(None)
    def off(m: tuple[int, ...]) -> Q:
        if m == zero:
            return Q(0)
        total = Q(0)
        for t in tails:
            if not m[t]:
                continue
            d = remove(m, t)
            for p, q in splits(d):
                total += H(t, p) * (rates[t] * (q == zero) - R(t, q) + off(q)) \
                    / (x + rates[t])
        return total

    return off(monomial)


def candidate_coefficient(rates: tuple[Q, ...], x: Q,
                          m: tuple[int, ...]) -> Q:
    degree = sum(m)
    multinomial = factorial(degree) // prod_fraction(factorial(v) for v in m)
    scale = Q(multinomial * 2 ** degree) * prod_fraction(z ** power for z, power in zip(rates, m))
    return scale * kernel_integral_over_pi(rates, x, m)


def prod_fraction(values):
    out = Q(1)
    for value in values:
        out *= value
    return out


def rational_string(value: Q) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def main() -> None:
    cases = [
        ((Q(1), Q(2)), Q(1), (2, 1)),
        ((Q(1), Q(2)), Q(3), (3, 2)),
        ((Q(1), Q(2)), Q(1), (4, 4)),
        ((Q(1), Q(1)), Q(1), (1, 1)),
        ((Q(1), Q(1)), Q(2), (2, 1)),
        ((Q(2, 3), Q(5, 2), Q(7, 3)), Q(2, 3), (1, 2, 1)),
        ((Q(2, 3), Q(5, 2), Q(7, 3)), Q(3, 2), (2, 1, 2)),
    ]
    rows = []
    for rates, x, m in cases:
        recursive = recursive_coefficient(rates, x, m)
        integral = candidate_coefficient(rates, x, m)
        if recursive != integral:
            raise ArithmeticError(f"exact mismatch at {rates}, {x}, {m}: {recursive} != {integral}")
        rows.append({"rates": [rational_string(z) for z in rates],
                     "x": rational_string(x), "multiindex": list(m),
                     "coefficient": rational_string(recursive),
                     "equal_exactly": True})
    report = {"status": "MATCHES_SAMPLED_EXACT_RATIONAL_CASES",
              "scope": "Independent rational recursion and partial-fraction integral checks; not a general proof or Lean certificate.",
              "formula": "coeff_m r(x) = multinomial(m) * 2^degree(m) * prod_i z_i^m_i / pi * integral_0^infinity k^2 / ((k^2+x^2) prod_i (k^2+z_i^2)^m_i) dk",
              "cases": rows}
    path = Path(__file__).resolve().parents[2] / "results/certificates/codex_pure_fluid_repeated_integral.json"
    path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"PASS: {len(rows)} exact-rational repeated-index kernel cross-checks")


if __name__ == "__main__":
    main()
