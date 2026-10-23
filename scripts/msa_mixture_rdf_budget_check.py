#!/usr/bin/env python3
"""Evaluate the Lean-certified sufficient causal RDF kernel budget.

This is floating-point quadrature, not a kernel-checked interval certificate.
A budget >= 1 means only that this sufficient condition does not apply.
The pair-contact HS reference is constructed internally for arbitrary positive
additive diameters if the actual weighted-budget criterion is certified.
"""

from __future__ import annotations

import argparse
import json
from math import exp, isfinite, pi
from pathlib import Path

from scipy.integrate import quad


def weighted_kernel_budget(rho, sigma, delta, rates):
    """Finite-window expression proved in rdfWeightedKernelBudget_eq_finite_windows."""
    if len(rho) != len(sigma) or not rho:
        raise ValueError("rho and sigma must have the same positive length")
    values = [*rho, *sigma, delta, *rates]
    if not all(isfinite(x) for x in values):
        raise ValueError("all parameters must be finite")
    if any(x <= 0 for x in rho + sigma) or delta <= 0:
        raise ValueError("the physical RDF certificate requires rho, sigma, delta > 0")
    if any(z < delta for z in rates):
        raise ValueError("delta must not exceed any tail rate")
    vacancy = 1 - pi / 6 * sum(r * s**3 for r, s in zip(rho, sigma))
    if vacancy <= 0:
        raise ValueError("positive mixture free volume is required")
    xi2 = sum(r * s**2 for r, s in zip(rho, sigma))
    entries, errors = [], []
    for i, si in enumerate(sigma):
        row, erow = [], []
        for sj in sigma:
            q0 = 2 * pi / vacancy * (
                (si + sj) / 2 + pi * xi2 * si * sj / (4 * vacancy)
            )
            qpp = 2 * pi / vacancy * (1 + pi * xi2 * sj / (2 * vacancy))
            # LEFT density rho_i; row support [0, sigma_i].
            value, error = quad(
                lambda t: exp(delta * t)
                * abs(rho[i] * (q0 * (t - si) + qpp / 2 * (t - si) ** 2)),
                0,
                si,
                epsabs=1e-12,
                epsrel=1e-12,
            )
            row.append(value)
            erow.append(error)
        entries.append(row)
        errors.append(erow)
    budget = sum(map(sum, entries))
    return {
        "rho": rho,
        "sigma": sigma,
        "delta": delta,
        "rates": rates,
        "vacancy": vacancy,
        "entry_budgets": entries,
        "quadrature_error_estimate": sum(map(sum, errors)),
        "weighted_kernel_budget": budget,
        "numerical_sufficient_budget_passes": budget < 1,
        "equal_diameters": all(s == sigma[0] for s in sigma),
        "Y_bound_multiplier": 1 / (1 - budget) if budget < 1 else None,
        "U_bound_multiplier": 1 / (1 - budget) ** 2 if budget < 1 else None,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rho", type=json.loads, help="JSON array of number densities")
    parser.add_argument("--sigma", type=json.loads, help="JSON array of additive diameters")
    parser.add_argument("--rates", type=json.loads, help="JSON array of positive tail rates")
    parser.add_argument("--delta", type=float, help="positive exponential weight")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    supplied = [args.rho, args.sigma, args.rates, args.delta]
    if any(x is not None for x in supplied):
        if any(x is None for x in supplied):
            parser.error("supply rho, sigma, rates and delta together")
        cases = [supplied]
    else:
        cases = [
            [[0.02], [1.0], [0.5, 1.8], 0.2],
            [[0.01, 0.015], [1.0, 1.6], [0.6, 1.8, 1.8], 0.2],
            [[0.0003, 0.0005, 0.0008], [1.0, 1.4, 2.3], [0.5, 3.0], 0.35],
            [[0.4], [1.0], [0.5, 1.8], 0.2],
            [[0.01, 0.015], [1.0, 1.0], [0.6, 1.8, 1.8], 0.2],
            [[0.0003, 0.0005, 0.0008], [1.4, 1.4, 1.4], [0.5, 3.0], 0.35],
        ]
    result = {
        "scope": "floating-point evaluation of the explicit sufficient kernel budget only",
        "not_a_formal_interval_certificate": True,
        "reference_condition": "arbitrary positive additive diameters: actual pair-contact HS reference constructed internally under the certified weighted budget; strictly positive densities and vacMix>0 required by the actual HS factorization; floating-point values here do not certify the exact budget inequality",
        "failure_meaning": "budget >= 1 does not imply nonintegrability or physical instability",
        "cases": [weighted_kernel_budget(r, s, d, z) for r, s, z, d in cases],
    }
    data = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(data)
    print(data, end="")


if __name__ == "__main__":
    main()
