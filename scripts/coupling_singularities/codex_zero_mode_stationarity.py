"""Exact symbolic identities for the single-species MSA zero-mode factor.

Run from the package root. This writes only the Codex-owned result JSON.
The checks prove algebraic identities, not branch selection, absence of
finite-k instabilities, a global minimum, or a parameter-domain certificate.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys
import time

import sympy as s


def verify() -> dict:
    started = time.monotonic()
    eta, z = s.symbols("eta z", nonzero=True)
    e, D, G = s.symbols("E D G")
    rho = 6 * eta / s.pi
    vac = 1 - eta
    A0 = 2 * s.pi * (1 + 2 * eta) / vac**2
    B0 = -3 * s.pi * eta / vac**2
    qp0 = 2 * s.pi * (1 + eta / 2) / vac**2
    c = 2 * s.pi * rho / z
    W = c * G * D
    Ct = (1 - c * e * G) * D
    M = -rho * (W + (1 + z) * Ct) / z
    Nc = rho * (W + (1 + z + z**2 / 2) * Ct) / z**2
    A = A0 * (1 + M) - 4 * B0 * Nc
    qp = qp0 * (1 + M) + A0 * Nc

    # Independent evaluation of 1-rho*Qhat(0), using phi1(0)=-1/2,
    # phi2(0)=1/6 and the full tail transform at zero.
    Qhat0 = -qp / 2 + A / 6 + W / z + Ct * (1 + 1 / z)
    F0 = 1 - rho * Qhat0
    Fhs = (1 + 2 * eta) / vac**2
    alpha = rho * (6 * eta + (4 * eta - 1) * z + (eta - 1) * z**2) / (vac**2 * z**2)
    beta = rho * 12 * eta / (vac**2 * z**3) * (
        -(1 + 2 * eta) * z * (1 - (1 + z) * e)
        + 6 * eta * (1 - (1 + z + z**2 / 2) * e)
    )
    assert s.cancel(F0 - A / (2 * s.pi)) == 0
    assert s.cancel(F0 - (Fhs + D * (alpha + beta * G))) == 0
    assert s.cancel(s.diff(F0, D) - (alpha + beta * G)) == 0
    assert s.cancel(s.diff(F0, G) - beta * D) == 0
    assert s.cancel(s.diff(F0, D, G) - beta) == 0
    assert s.cancel(s.diff(F0, D, 2)) == 0
    assert s.cancel(s.diff(F0, G, 2)) == 0

    # The physical two-tail forcing is supported on the first two rows.
    # J, its directional derivative K, g and its derivative gd are otherwise
    # independent symbols, so these identities hold for any regular 4D model.
    n = 4
    js = s.symbols("j0:16")
    ks = s.symbols("k0:16")
    gs = s.symbols("g0:4")
    gds = s.symbols("gd0:4")
    b0, b1 = s.symbols("b0 b1")
    J, K = s.Matrix(n, n, js), s.Matrix(n, n, ks)
    g, gd = s.Matrix([gs]), s.Matrix([gds])
    b = s.Matrix([b0, b1, 0, 0])
    adj = J.adjugate()
    det = s.expand(J.det(method="berkowitz"))
    N = s.expand((g * adj * b)[0])
    bordered = J.row_join(-b).col_join(s.Matrix([list(gs) + [0]]))
    assert s.expand(bordered.det(method="berkowitz") - N) == 0
    ddet = sum(s.diff(det, x) * dx for x, dx in zip(js, ks))
    trace = s.trace(adj * K)
    assert s.expand(ddet - trace) == 0
    dN = sum(s.diff(N, x) * dx for x, dx in zip(js, ks))
    dN += sum(s.diff(N, x) * dx for x, dx in zip(gs, gds))
    adj_rule = det * (gd * adj * b)[0] + N * trace - (g * adj * K * adj * b)[0]
    assert s.expand(det * dN - adj_rule) == 0

    return {
        "status": "PASS",
        "scope": "Exact algebraic identities; no state/parameter or canonicity certificate.",
        "sympy_version": s.__version__,
        "normalization": "sigma=1, rho=6*eta/pi; E=exp(-z) is an independent symbol in the checks",
        "physical_domain": "z>0 and 0<eta<1",
        "unknown_order": ["D1", "D2", "G1", "G2"],
        "zero_mode": "F0=Fhs+sum_i D_i*(alpha_i+beta_i*G_i)=A/(2*pi)",
        "Fhs": str(Fhs),
        "alpha": str(alpha),
        "beta": str(beta),
        "verified_identities": [
            "1-rho*Qhat(0)=A/(2*pi)",
            "one-tail contribution D*(alpha+beta*G); additive for any finite tail family",
            "grad(F0)=(alpha_i+beta_i*G_i, beta_i*D_i)",
            "only nonzero Hessian entries are H[D_i,G_i]=H[G_i,D_i]=beta_i",
            "det([[J,-b],[g,0]])=g*adj(J)*b",
            "directional_derivative(det J)=trace(adj(J)*K)",
            "det(J)*dN=det(J)*gd*adj(J)*b+N*trace(adj(J)*K)-g*adj(J)*K*adj(J)*b",
        ],
        "derived_stationary_criterion": {
            "assumptions": "P(u(tau))=tau*b, det J != 0, J=DP, g=grad F0",
            "N": "g*adj(J)*b",
            "F0_derivative": "N/det J",
            "M": "grad(N)*adj(J)*b",
            "F0_second_derivative_at_N_zero": "M/(det J)^2",
            "strict_local_minimum": "N=0 and M>0",
            "transition_candidates": "P(u)=tau*b(w), F0(u)=0, N(u,w)=0; retain det J != 0 and M>0",
            "limitations": "Candidate roots must be connected to the PY branch; global and finite-k checks remain necessary.",
        },
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "seconds": round(time.monotonic() - started, 3),
    }


def main() -> None:
    result = verify()
    if "--model-crosscheck" in sys.argv[1:]:
        result["actual_model_float_crosscheck"] = crosscheck_actual_model()
    target = Path(__file__).resolve().parents[2] / "results/coupling_singularities/codex_zero_mode_stationarity.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(f"PASS: zero-mode and generic 4D stationarity identities ({result['seconds']} s)")
    print(target)


def crosscheck_actual_model() -> dict:
    """Independent numeric transcription check, not part of the exact proof."""
    import numpy as np

    package = Path(__file__).resolve().parents[2]
    workspace = package.parent.parent
    sys.path.insert(0, str(workspace))
    import msa_exact_mix as model

    checked, worst = 0, 0.0
    for eta in (0.1, 0.3, 0.49):
        rho = 6 * eta / np.pi
        for zs in ((1.8, 12.0), (2.9637, 14.0167), (0.6, 0.84)):
            z = np.asarray(zs)
            E = np.exp(-z)
            alpha = rho * (6*eta + (4*eta-1)*z + (eta-1)*z*z) / ((1-eta)**2*z*z)
            beta = rho*12*eta / ((1-eta)**2*z**3) * (
                -(1+2*eta)*z*(1-(1+z)*E) + 6*eta*(1-(1+z+z*z/2)*E)
            )
            st = model.HCYMix([1.0], [rho], zs, np.array([1.0, -1.0]).reshape(2,1,1))
            for ds, gs in (((0.0,0.0),(0.2,0.4)), ((0.02,-0.03),(0.7,0.8)), ((0.3,-0.6),(-0.1,0.6))):
                D, G = np.asarray(ds), np.asarray(gs)
                pieces = model._pieces(st, D.reshape(2,1,1), G.reshape(2,1,1))
                observed = float(np.real(1-rho*model.qhat(st,pieces,0)[0,0]))
                predicted = (1+2*eta)/(1-eta)**2 + float(np.sum(D*(alpha+beta*G)))
                relative = abs(observed-predicted)/max(1.0,abs(observed))
                worst = max(worst,relative)
                assert relative < 5e-12, (eta,zs,ds,gs,observed,predicted)
                checked += 1
    return {
        "status": "PASS", "cases": checked, "max_scaled_abs_error": worst,
        "scope": "Float64 transcription comparison at off-root amplitudes, not an interval certificate",
        "model_source_sha256": hashlib.sha256(Path(model.__file__).read_bytes()).hexdigest(),
    }


if __name__ == "__main__":
    main()
