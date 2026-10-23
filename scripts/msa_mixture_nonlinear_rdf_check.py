#!/usr/bin/env python3
"""Floating-point checks of the actual RIGHT nonlinear pair-contact renewal.

Checks are numerical evidence only: finite grids, truncated excess Laplace and
radial integrals, and floating-point weighted budgets are not Lean certificates.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

import numpy as np
from scipy.integrate import cumulative_trapezoid, quad

from msa_multitail_closure_check import RealBaxter

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from msa_exact_mix import HCYMix, solve_bh_mix, qhat


def probe(label, st, step=0.004, ceiling=14.0):
    sol = solve_bh_mix(st)
    if sol is None:
        raise RuntimeError(f"{label}: BH continuation did not produce a root")
    real = RealBaxter(sol, 72)
    p, n = sol.p, st.N
    t = np.arange(0, ceiling + step / 2, step)
    q = np.empty((len(t), n, n))
    for i in range(n):
        for j in range(n):
            q[:, i, j] = real.value(i, j, t + real.lo[i, j])
    kernel = st.rho[None, :, None] * q
    source = (t[:, None, None] * p['A'][None, None, :] + p['qp'][None, :, :]) / (2 * np.pi)
    source += np.einsum('ut,uij,u->tij', np.exp(-st.z[:, None] * t), p['Ct'], st.z) / (2 * np.pi)
    y = np.empty_like(source)
    y[0] = source[0]
    right_block = np.eye(n) - step / 2 * kernel[0]
    for k in range(1, len(t)):
        rhs = source[k] + step * (np.einsum('tim,tmj->ij', y[1:k], kernel[k-1:0:-1])
                                  + y[0] @ kernel[k] / 2)
        y[k] = np.linalg.solve(right_block.T, rhs.T).T
    excess = y - t[:, None, None] - st.SIG[None, :, :]
    excess_primitive = cumulative_trapezoid(excess, t, axis=0, initial=0)
    delta = min(0.2, float(np.min(st.z)) / 2)
    budget = 0.0
    for i in range(n):
        for j in range(n):
            fun = lambda v: np.exp(delta*v)*abs(st.rho[i]*float(real.value(i, j, [v+real.lo[i,j]])[0]))
            budget += quad(fun, 0, st.sigma[i], epsabs=2e-10, limit=200)[0]
            budget += quad(fun, st.sigma[i], max(st.sigma)+45/(min(st.z)-delta),
                           epsabs=2e-10, limit=200)[0]
    moment_errors = []
    for u, z in enumerate(st.z):
        got = 1/z**2 + st.SIG/z + np.trapz(np.exp(-z*t)[:, None, None]*excess, t, axis=0)
        moment_errors.append(float(np.max(abs(got-sol.Gt[u]))))
    residuals = []
    lower = -st.sigma[:, None]*p['qp']+p['A'][None,:]*st.sigma[:,None]**2/2
    lower += np.sum(p['Wt']+p['Ct'], axis=0)
    def jl(s):
        J = p['A'][None,:]/s**2+p['qp']/s+np.sum(st.z[:,None,None]*p['Ct']/(s+st.z[:,None,None]),axis=0)
        L = p['A'][None,:]/s**2+(p['qp']-st.sigma[:,None]*p['A'][None,:])/s+lower
        L -= np.sum(st.z[:,None,None]*p['Wt']/(s+st.z[:,None,None]),axis=0)
        return J, L

    for s in (0.37, 1.3, 9.0):
        J, L = jl(s)
        H = J-J.T+(J.T@np.diag(st.rho)@L-L.T@np.diag(st.rho)@J)/s
        residuals.append(float(np.max(abs(H))))
    wronskian_u, wronskian_v, factor_samples = [], [], []
    # Samples of actual rational residuals; not exact polynomial certificates.
    for k in (0.1, 0.37, 1.3, 9.0, 60.0):
        s = 1j*k
        J, L = jl(s)
        Jm, Lm = jl(-s)
        U = -L+Lm.T+(Jm@np.diag(st.rho)@J.T-L@np.diag(st.rho)@Lm.T)/s
        V = J-J.T+(J@np.diag(st.rho)@Lm.T-Lm@np.diag(st.rho)@J.T)/s
        wronskian_u.append(float(np.max(abs(U))))
        wronskian_v.append(float(np.max(abs(V))))
    sqrt_density = np.sqrt(st.rho)
    for k in (0.0, 0.1, 0.37, 1.3, 9.0, 60.0):
        F = np.eye(n)-sqrt_density[:,None]*qhat(st,p,1j*k)*sqrt_density[None,:]
        gram = F@F.conj().T
        factor_samples.append(dict(k=k, minimum_gram_eigenvalue=float(np.min(np.linalg.eigvalsh(gram)))))

    def psi(i, j, r):
        return -r if r < st.SIG[i,j] else float(np.interp(r-st.SIG[i,j],t,excess[:,i,j]))

    def primitive(i, j, r):
        R = st.SIG[i,j]
        return -r*r/2 if r <= R else -R*R/2+float(np.interp(r-R,t,excess_primitive[:,i,j]))

    oz_errors = []
    for i in range(n):
        for j in range(n):
            for r in (0.31, st.SIG[i,j]+0.23, 2.9):
                conv = 0.0
                for m in range(n):
                    top = max(st.sigma)+min(10, 18/min(st.z))
                    cuts = sorted({0., top, st.SIG[i,m], abs(real.lo[i,m]),
                                   abs(r-st.SIG[m,j]), r+st.SIG[m,j]})
                    cuts = [v for v in cuts if 0 <= v <= top]
                    conv += st.rho[m]*2*np.pi/r*sum(real.bounded(
                        lambda vs: np.array([real.numerator(i,m,v)/(2*np.pi)*
                            (primitive(m,j,r+v)-primitive(m,j,abs(r-v))) for v in vs]), a,b)
                        for a,b in zip(cuts[:-1],cuts[1:]))
                c = real.numerator(i,j,r)/(2*np.pi*r)
                oz_errors.append(abs(psi(i,j,r)/r-c-conv))
    return dict(label=label, sigma=st.sigma.tolist(), rho=st.rho.tolist(), z=st.z.tolist(),
                strengths=st.K.tolist(), step=step, excess_ceiling=ceiling,
                root_residual=sol.residual, weighted_budget_delta=delta,
                numerical_weighted_budget=budget, numerical_budget_passes=budget<1,
                contact_minimum=float(np.min(sol.contact)),
                maximum_RDF_reciprocity_error=float(np.max(abs(y-y.transpose(0,2,1)))),
                maximum_labelled_G_moment_error=max(moment_errors),
                maximum_rational_reciprocity_residual=max(residuals),
                maximum_sampled_imaginary_axis_Wronskian_U_residual=max(wronskian_u),
                maximum_sampled_imaginary_axis_Wronskian_V_residual=max(wronskian_v),
                actual_Fourier_factor_gram_samples=factor_samples,
                maximum_sampled_radial_OZ_residual=max(oz_errors),
                maximum_absolute_excess_at_truncation=float(np.max(abs(excess[-1]))))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    pair = np.array([[1., .8], [.8, 1.2]])
    cases = [
        ('binary_single', HCYMix([1.,1.6],[.008,.012],[1.8],[.3*pair]),.004),
        ('binary_single_refined', HCYMix([1.,1.6],[.008,.012],[1.8],[.3*pair]),.002),
        ('binary_high_z_signed', HCYMix([1.,1.6],[.004,.006],[1.,60.],[.2*pair,-.1*pair]),.004),
        ('binary_repeated_rates', HCYMix([1.,1.6],[.004,.006],[5.,5.],[.2*pair,-.1*pair]),.004),
        ('ternary_multitail', HCYMix([1.,1.4,2.3],[.0003,.0005,.0008],[1.,5.,20.],
             np.array([.15,-.06,.03])[:,None,None]*np.ones((3,3))),.004),
        ('dilute_long_attraction_short_repulsion_negative_g', HCYMix([1.,1.6],[0.,0.],[1.,20.],
             np.array([1.,-3.])[:,None,None]*np.array([[1.,1.3],[1.3,1.6]])),.004),
    ]
    results = []
    for label, st, step in cases:
        result = probe(label, st, step)
        results.append(result)
        print(label, 'budget', result['numerical_weighted_budget'], 'OZ',
              result['maximum_sampled_radial_OZ_residual'], flush=True)
    args.output.write_text(json.dumps(dict(
        scope='floating-point actual nonlinear renewal/DCF diagnostic only; no interval or all-state certificate',
        orientation='Yg=GSource+Yg causal-convolved with K; K_ij=rho_i*Q_ij(t+lambda_ij)',
        limitations='finite grid and quadrature; excess Laplace/radial tails truncated; sampled OZ and Wronskian tests are not formal or exact coefficient certificates; Gram samples use actual Q but are not an all-k proof or zero-k radial thermodynamic identity',
        cases=results),indent=2)+'\n')


if __name__ == '__main__':
    main()
