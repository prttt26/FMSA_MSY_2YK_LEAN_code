"""Refined finite-k audit of previously computed Maxwell endpoints.

Uses strict D_N=[|1-rho*qhat|^2]_{<=N}, never |F_N|^2. The compact
k interval is checked numerically; a conservative analytic tail bound is
evaluated for the computed coefficients. Neither is an interval-arithmetic
certificate for the underlying exact coefficients or a global phase comparison.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize_scalar

from msa_finite_order_thermo_check import ScalarSeries, at_tau
from msa_range_multitail_thermo_check import spectral_coefficients

RESULTS = Path(__file__).resolve().parents[1] / 'results'


class Spectrum:
    def __init__(self, rho, z, K, T, order):
        self.model = ScalarSeries(rho, z, K)
        self.jet = self.model.construct(order)
        self.p = self.model.pieces(self.jet['x'])
        self.weights = (1/np.longdouble(T))**np.arange(order+1)
        self.order = order
        A, qp, C, W = self.p
        # For k>=1: |qhat_n|<=b_n/k and |Re qhat_n|<=d_n/k^2.
        # C*(exp(-s)/(s+z)+(1-exp(-s))/s)
        #   = C*(1/s-z*exp(-s)/(s*(s+z))). Its leading term is imaginary.
        b = self.weights*(3*abs(qp)+np.longdouble('3.5')*abs(A)
                         +np.sum(abs(W)+2*abs(C), axis=0))
        d = self.weights*(2*abs(qp)+2*abs(A)
                         +np.sum(self.model.z[:, None]*(abs(W)+abs(C)), axis=0))
        pair_bound = np.convolve(b, b)[:order+1].sum()
        self.tail_constant = float(2*self.model.rho*d.sum()+self.model.rho**2*pair_bound)
        # D_N(k)>=1-C_N/k^2. At this cutoff the computed bound is >=1/2.
        self.cutoff = max(32., float(np.sqrt(2*self.tail_constant)))*(1+1e-10)

    def values(self, waves):
        k = np.atleast_1d(waves).astype(np.longdouble)
        out = np.empty(len(k), dtype=np.longdouble)
        zero = k == 0
        out[zero] = at_tau(self.jet['a'], self.weights[1])
        if (~zero).any():
            s = np.clongdouble(1j)*k[~zero, None]
            em = np.exp(-s)
            A, qp, C, W = self.p
            q = ((1-s-em)/s**2*qp + (1-s+s**2/2-em)/s**3*A)
            # Grouping cancels two oscillatory O(1/k) contact contributions.
            for z, c, w in zip(self.model.z, C, W):
                q += w/(s+z)+c*(1/s-z*em/(s*(s+z)))
            q *= self.weights
            prefix = np.cumsum(q, axis=1)
            pair = np.sum(q*np.conjugate(prefix[:, ::-1]), axis=1).real
            out[~zero] = 1-2*self.model.rho*q.sum(axis=1).real+self.model.rho**2*pair
        return np.asarray(out, float)


def audit_endpoint(rho, z, K, T, order, step=.02):
    spectrum = Spectrum(rho, z, K, T, order)
    low = np.arange(0, 32, step)
    tail = np.linspace(32, spectrum.cutoff, max(2, int(np.ceil((spectrum.cutoff-32)/.1))+1))
    waves = np.unique(np.r_[low, tail])
    # Bounded batches keep the longest conservative tail scans inexpensive in memory.
    values = np.concatenate([spectrum.values(waves[i:i+2048]) for i in range(0, len(waves), 2048)])
    if not np.isfinite(values).all():
        raise RuntimeError('Nonfinite spectrum')
    idx = int(np.argmin(values))
    best_k, best = float(waves[idx]), float(values[idx])
    competitive = np.flatnonzero((values[1:-1] <= values[:-2]) &
                                (values[1:-1] <= values[2:]) &
                                (values[1:-1] <= min(1., best+.02)))+1
    for i in competitive:
        fit = minimize_scalar(lambda k: spectrum.values([k])[0],
                              bounds=(waves[i-1], waves[i+1]), method='bounded',
                              options={'xatol': 2e-10})
        if fit.fun < best:
            best_k, best = float(fit.x), float(fit.fun)
    # Infinity has limiting D=1, so this can be an infimum instead of an attained minimum.
    if best > 1:
        best_k, best = None, 1.
    probe = np.array([0., .01, 1., 10., 30.])
    reference, imaginary_defect = spectral_coefficients(spectrum.model, spectrum.jet, probe)
    expected = np.asarray([at_tau(c, spectrum.weights[1]) for c in reference], float)
    defect = float(np.max(abs(spectrum.values(probe)-expected)/np.maximum(1, abs(expected))))
    if defect > 2e-8:
        raise RuntimeError(f'Independent spectral evaluation discrepancy {defect}')
    status = ('finite_k_unstable' if best < -1e-8 else
              'numerically_unresolved' if best <= 1e-8 else 'numerical_screen_pass')
    return dict(rho=rho, k0=float(values[0]), minimum_D=best, k_min=best_k,
                status=status, scanned_k_max=spectrum.cutoff, scan_points=len(waves),
                optimized_local_minima=len(competitive), tail_constant=spectrum.tail_constant,
                tail_lower_bound_at_cutoff=1-spectrum.tail_constant/spectrum.cutoff**2,
                coefficient_defect=spectrum.jet['coefficient_defect'],
                spectral_evaluation_defect=defect, spectral_imaginary_defect=imaginary_defect)


def candidates():
    omitted = []
    for source in ['finite_order_thermo', 'range_multitail_thermo']:
        report = json.loads((RESULTS/source/'results.json').read_text())
        for model in report['models']:
            name = model.get('name', model.get('model'))
            states = [(f'T={s["T"]:.12g}', s['T'], int(n), summary)
                      for s in model['isotherms'] for n, summary in s['orders'].items()]
            states += [('0.8 own Tc', s['T'], s['order'], s['summary'])
                       for s in model.get('own_critical_comparison', [])]
            for scope, T, n, summary in states:
                if name == 'HSY_z20' and scope == '0.8 own Tc' and n == 40:
                    omitted.append(dict(source=source, model=name, scope=scope, order=n,
                                        reason='Previously flagged grid-sensitive critical temperature'))
                    continue
                for i, c in enumerate(summary['coexistence_candidates']):
                    if c['supporting_tangent']:
                        yield dict(source=source, model=name, z=model['z'], K=model['K'],
                                   scope=scope, T=T, order=n, candidate=i,
                                   rho_g=c['rho_g'], rho_l=c['rho_l'])
    return omitted


def independent_precision(rows):
    """Independent 70-digit BH transcription at negative and positive controls."""
    import mpmath as mp
    import fmsa_first_order_exact as high
    mp.mp.dps = 70
    selected = []
    requests = [('2YK_long_repulsion', 1, '0.8 own Tc'),
                ('2YK_long_repulsion', 2, '0.8 own Tc'),
                ('2YK_long_repulsion', 3, '0.8 own Tc'),
                ('HSY_z20', 2, '0.8 own Tc'), ('HSY_z1.8', 3, '0.8 own Tc'),
                ('HSY_z5', 40, '0.8 own Tc'),
                ('2YK_long_repulsion', 20, 'T=0.133194309369')]
    for name, n, scope in requests:
        row = next(r for r in rows if r['model']==name and r['order']==n and r['scope']==scope)
        for end in row['endpoints']:
            if n >= 20 and end['endpoint']=='liquid':
                continue
            st = high.State(['1'], [str(end['rho'])], list(map(str, row['z'])),
                            [[[str(k)]] for k in row['K']])
            seed = high.u0_of(st)
            J, _ = high.jacobian_and_dlam(st, seed)
            jets = [mp.matrix(seed)]
            for degree in range(1, n+1):
                def residual(t):
                    state = sum((v*t**j for j, v in enumerate(jets)), mp.zeros(len(seed), 1))
                    return mp.matrix(high.residuals(list(state), st.scaled(t)))
                jets.append(mp.lu_solve(mp.matrix(J), -mp.diff(residual, 0, degree)/mp.factorial(degree)))
            k = mp.mpf(str(end['k_min'] if end['k_min'] is not None else 1))
            def inverse_structure(t):
                state = sum((v*t**j for j, v in enumerate(jets)), mp.zeros(len(seed), 1))
                nt = len(row['z'])
                D = [[[state[i]]] for i in range(nt)]
                G = [[[state[nt+i]]] for i in range(nt)]
                p = high.pieces(st, D, G)
                return ((1-st.rho[0]*high.qhat(st, p, mp.j*k)[0][0])*
                        (1-st.rho[0]*high.qhat(st, p, -mp.j*k)[0][0])).real
            tau = 1/mp.mpf(str(row['T']))
            value = sum(mp.diff(inverse_structure, 0, j)/mp.factorial(j)*tau**j for j in range(n+1))
            computed = Spectrum(end['rho'], row['z'], row['K'], row['T'], n).values([float(k)])[0]
            selected.append(dict(model=row['model'], order=n, endpoint=end['endpoint'],
                                 rho=end['rho'], T=row['T'], k=float(k), reference_D=float(value),
                                 absolute_error=abs(computed-float(value))))
    return selected


def render(rows, out):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    fig, axes = plt.subplots(1, 2, figsize=(11, 4))
    for n in [1, 2, 3]:
        row = next(r for r in rows if r['model']=='2YK_long_repulsion' and r['order']==n and r['scope']=='0.8 own Tc')
        for end in row['endpoints']:
            k = np.linspace(0, 8, 801)
            values = Spectrum(end['rho'], row['z'], row['K'], row['T'], n).values(k)
            axes[0].plot(k, values, label=f'N={n}, {end["endpoint"]}',
                         linestyle='-' if end['endpoint']=='gas' else '--')
    axes[0].set(title='Competing tails: Maxwell endpoints', xlabel=r'$k\sigma$', ylabel=r'$D_N(k)$', ylim=(-10, 12))
    axes[0].legend(fontsize=8)
    for name, n in [('HSY_z1.8', 1), ('HSY_z20', 2), ('HSY_z12', 6)]:
        row = next(r for r in rows if r['model']==name and r['order']==n and r['scope']=='0.8 own Tc')
        for end in row['endpoints']:
            k = np.linspace(0, 25, 1251)
            values = Spectrum(end['rho'], row['z'], row['K'], row['T'], n).values(k)
            axes[1].plot(k, values, label=f'{name}, N={n}, {end["endpoint"]}',
                         linestyle='-' if end['endpoint']=='gas' else '--')
    axes[1].set(title='Attractive-tail controls', xlabel=r'$k\sigma$', ylabel=r'$D_N(k)$', ylim=(-.1, 6))
    axes[1].legend(fontsize=7)
    for ax in axes:
        ax.axhline(0, color='black', linewidth=.7)
        ax.axhline(1, color='gray', linewidth=.7, linestyle=':')
    fig.tight_layout()
    for suffix in ['png', 'svg']:
        fig.savefig(out/f'maxwell_endpoint_spectra.{suffix}', dpi=180)
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=RESULTS/'maxwell_finite_k')
    parser.add_argument('--step', type=float, default=.02)
    args = parser.parse_args()
    if not 0 < args.step <= .02:
        parser.error('Use 0 < step <= .02')
    args.out.mkdir(parents=True, exist_ok=True)
    rows = []
    for row in candidates():
        row['endpoints'] = [dict(endpoint=label, **audit_endpoint(row[key], row['z'], row['K'],
                                                               row['T'], row['order'], args.step))
                            for label, key in [('gas', 'rho_g'), ('liquid', 'rho_l')]]
        row['status'] = ('finite_k_unstable' if any(e['status']=='finite_k_unstable' for e in row['endpoints'])
                         else 'numerically_unresolved' if any(e['status']=='numerically_unresolved' for e in row['endpoints'])
                         else 'numerical_screen_pass')
        rows.append(row)
        if len(rows)%20 == 0:
            print(f'Checked {len(rows)} pairs', flush=True)
    endpoints = [e for r in rows for e in r['endpoints']]
    precision = independent_precision(rows)
    if max(p['absolute_error'] for p in precision) > 1e-8:
        raise RuntimeError('High precision comparison failed')
    report = dict(definition='D_N(k) = strict order-N truncation of |1-rho*qhat(ik,tau)|^2',
                  finite_interval='Numerical grid plus bounded optimization of competitive local minima',
                  small_k_step=args.step, tail_step_max=.1,
                  tail_bound='For computed coefficients: D_N(k)>=1-C_N/k^2, k>=1; cutoff gives >=1/2',
                  limitations='Scalar PY models; no interval certificate or global modulated-phase free-energy comparison',
                  omitted=[dict(model='HSY_z20', order=40, scope='0.8 own Tc',
                                reason='Previously flagged grid-sensitive critical temperature')],
                  pair_counts={s:sum(r['status']==s for r in rows) for s in
                               ['numerical_screen_pass', 'finite_k_unstable', 'numerically_unresolved']},
                  endpoint_counts={s:sum(e['status']==s for e in endpoints) for s in
                                   ['numerical_screen_pass', 'finite_k_unstable', 'numerically_unresolved']},
                  maximum_spectral_evaluation_defect=max(e['spectral_evaluation_defect'] for e in endpoints),
                  precision_checks=precision, pairs=rows)
    (args.out/'results.json').write_text(json.dumps(report, indent=2)+'\n')
    # A line-oriented, human-readable ledger avoids a spreadsheet dependency.
    lines = ['model | scope | N | T | endpoint | rho | D(0) | min D | k_min | status | k_cutoff']
    for r in rows:
        for e in r['endpoints']:
            lines.append(f'{r["model"]} | {r["scope"]} | {r["order"]} | {r["T"]:.12g} | '
                         f'{e["endpoint"]} | {e["rho"]:.12g} | {e["k0"]:.12g} | '
                         f'{e["minimum_D"]:.12g} | {e["k_min"]} | {e["status"]} | {e["scanned_k_max"]:.6g}')
    (args.out/'endpoint_ledger.txt').write_text('\n'.join(lines)+'\n')
    render(rows, args.out)
    print(json.dumps({k:v for k,v in report.items() if k not in ['pairs', 'precision_checks']}, indent=2), flush=True)


if __name__ == '__main__':
    main()
