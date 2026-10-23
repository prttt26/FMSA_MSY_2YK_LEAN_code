#!/usr/bin/env python3
"""Exact rational probes of finite-pole completion of the mixture Ward identities.

These are finite symbolic examples, not an arbitrary-N/rate theorem or a Lean
closure certificate. The inputs r_i represent pi*rho_i; C,W,A,qp are divided
by pi. Contact exponentials are absent from this residue-completion problem.
Every reported coefficient identity is checked by exact polynomial arithmetic.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import sympy as sp
from sympy.polys.matrices import DomainMatrix


def probe(label, densities, diameters, rates):
    r, sigma, z = [[sp.Rational(t) for t in seq]
                   for seq in (densities, diameters, rates)]
    n, tails = len(r), len(z)
    if len(sigma) != n or len(set(z)) != tails:
        raise ValueError('This completion probe requires distinct positive rates.')
    if any(t <= 0 for t in sigma + z):
        raise ValueError('Diameters and rates must be positive.')
    s = sp.Symbol('s')
    C = [sp.Matrix(n, n, lambda i, j: sp.Symbol(f'c_{u}_{i}_{j}')) for u in range(tails)]
    W = [sp.Matrix(n, n, lambda i, j: sp.Symbol(f'w_{u}_{i}_{j}')) for u in range(tails)]
    variables = [v for matrix in C + W for v in matrix]
    density = sp.diag(*r)
    vac = 1 - sum(r[i]*sigma[i]**3 for i in range(n))/6
    xi = sum(r[i]*sigma[i]**2 for i in range(n))
    if vac <= 0:
        raise ValueError('Positive free volume required.')
    a0 = [2/vac*(1+xi*sigma[j]/(2*vac)) for j in range(n)]
    q0 = sp.Matrix(n, n, lambda i, j:
                   2/vac*((sigma[i]+sigma[j])/2+xi*sigma[i]*sigma[j]/(4*vac)))
    M = [-sum(r[i]*(W[u][i,j]+(1+z[u]*sigma[i])*C[u][i,j])/z[u]
              for u in range(tails) for i in range(n)) for j in range(n)]
    T = [sum(r[i]*((1+z[u]*(sigma[j]-sigma[i])/2)*W[u][i,j]/z[u]**2
                   + ((1+z[u]*sigma[i]+(z[u]*sigma[i])**2/2)/z[u]**2
                      +(sigma[j]-sigma[i])*(1+z[u]*sigma[i])/(2*z[u]))*C[u][i,j])
             for u in range(tails) for i in range(n)) for j in range(n)]
    A = [sp.expand(a0[j]*(1+M[j])+2*xi*T[j]/vac**2) for j in range(n)]
    qp = sp.Matrix(n, n, lambda i,j: sp.expand(q0[i,j]*(1+M[j])+a0[i]*T[j]))
    b = sp.Matrix(n, n, lambda i,j: sp.expand(-sigma[i]*qp[i,j]+A[j]*sigma[i]**2/2
                                             +sum(W[u][i,j]+C[u][i,j] for u in range(tails))))
    P = sp.prod(s+t for t in z)
    D = s**2*P
    J = sp.Matrix(n, n, lambda i,j: sp.expand((A[j]+qp[i,j]*s)*P
         +sum(z[u]*C[u][i,j]*s**2*sp.prod(s+z[v] for v in range(tails) if v != u)
              for u in range(tails))))
    L = sp.Matrix(n, n, lambda i,j: sp.expand((A[j]+(qp[i,j]-sigma[i]*A[j])*s+b[i,j]*s**2)*P
         -sum(z[u]*W[u][i,j]*s**2*sp.prod(s+z[v] for v in range(tails) if v != u)
              for u in range(tails))))
    Jm, Lm = J.subs(s, -s), L.subs(s, -s)
    U = (-L*s*D.subs(s, -s)+Lm.T*s*D+Jm*density*J.T-L*density*Lm.T).applyfunc(sp.expand)
    V = ((J-J.T)*s*D.subs(s, -s)+J*density*Lm.T-Lm*density*J.T).applyfunc(sp.expand)
    basis, basis_names = [], []
    for name, matrix in [('U', U), ('V', V)]:
        for i in range(n):
            for j in range(n):
                for point in z + [-t for t in z]:
                    expression = sp.expand(matrix[i,j].subs(s, point))
                    if expression != 0:
                        basis.append(sp.Poly(expression, *variables))
                        basis_names.append(f'{name}[{i},{j}]({point})')
    targets, target_names = [], []
    for name, matrix in [('U', U), ('V', V)]:
        for i in range(n):
            for j in range(n):
                for (degree,), coefficient in sp.Poly(matrix[i,j], s).terms():
                    if coefficient != 0:
                        targets.append(sp.Poly(coefficient, *variables))
                        target_names.append(f'{name}[{i},{j}].coeff({degree})')
    monomials = sorted(set().union(*(set(p.monoms()) for p in basis + targets)))
    matrix = sp.Matrix([[p.coeff_monomial(m) for p in basis] for m in monomials])
    rhs = sp.Matrix([[p.coeff_monomial(m) for p in targets] for m in monomials])
    _, columns = DomainMatrix.from_Matrix(matrix).to_field().rref()
    independent = matrix[:, list(columns)]
    _, rows = DomainMatrix.from_Matrix(independent.T).to_field().rref()
    coefficients = independent[list(rows), :].inv()*rhs[list(rows), :]
    mismatch = independent*coefficients-rhs
    identities, failures = [], []
    for k, name in enumerate(target_names):
        if any(mismatch[row,k] != 0 for row in range(len(monomials))):
            failures.append(name)
            continue
        expression = sum(coefficients[j,k]*basis[col].as_expr() for j,col in enumerate(columns))
        assert sp.expand(expression-targets[k].as_expr()) == 0
        identities.append(dict(target=name, terms=[
            dict(pole_value=basis_names[col], multiplier=str(coefficients[j,k]))
            for j,col in enumerate(columns) if coefficients[j,k] != 0]))
    return dict(label=label, pi_scaled_densities=list(map(str,r)), diameters=list(map(str,sigma)),
                rates=list(map(str,z)), free_volume=str(vac),
                independent_pole_values=len(columns), coefficient_identities=len(identities),
                failures=failures, completion_verified=not failures, identities=identities)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    cases = [('binary_single', ['1/50','1/100'], [1,3], [1]),
             ('binary_two_rates', ['1/50','1/100'], [1,3], [1,5]),
             ('ternary_single', ['1/100','1/200','1/300'], [1,2,3], [2])]
    results = []
    for label, r, sigma, z in cases:
        result = probe(label, r, sigma, z)
        results.append(result)
        print(label, 'completion', result['completion_verified'], 'exact identities',
              result['coefficient_identities'], 'failures', len(result['failures']), flush=True)
    args.output.write_text(json.dumps(dict(
        scope='Exact finite-instance polynomial identities over independent normalized C,W; not a universal completion proof, not a Lean theorem, and not a physical root/stability or phase calculation.',
        implication='In each successful finite instance, zero U,V numerator values at every reflected rate imply all U,V numerator coefficients vanish.',
        limitations='Fixed rational density/diameter/rate examples; distinct rates only. Uniform arbitrary-species/arbitrary-tail completion and repeated-rate multiplicity remain unproved.',
        cases=results), indent=2)+'\n')


if __name__ == '__main__':
    main()
