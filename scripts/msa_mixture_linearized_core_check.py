"""Independent numerical check of the certified linearized BH convolution.

No nonlinear solve constructs the first variation: HS blocks supply D1/G0.
Compare the core pointwise with the existing double-propagator FMSA formula,
and separately with central differences of actual nonlinear BH roots.
These finite checks support, and do not replace, the open Lean DP identity.
"""
import argparse
import json
import sys
from pathlib import Path
from types import SimpleNamespace

import numpy as np

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from fmsa_double_prop import FMSA_double_prop
from msa_exact_mix import HCYMix, _pieces, from_fmsa, qhat, solve_bh_mix
from msa_multitail_closure_check import RealBaxter


def linearized(st, order=96):
    zero = np.zeros_like(st.K)
    p0 = _pieces(st, zero, zero)
    G0, D1 = np.empty_like(zero), np.empty_like(zero)
    eye = np.eye(st.N)
    for u, z in enumerate(st.z):
        Q = qhat(st, p0, z).real
        Y = np.exp(-z * st.LAM.T) * (eye - st.rho[:, None] * Q.T)
        Z = np.exp(z * st.LAM.T) * (eye - st.rho[:, None] * Q)
        D1[u] = (2*np.pi*st.K[u]/z) @ np.linalg.inv(Y)
        G0[u] = ((st.A0[None, :] + z*st.QP0)/z**2) @ np.linalg.inv(Z)/(2*np.pi)
    plus = RealBaxter(SimpleNamespace(st=st, p=_pieces(st, D1, G0)), order)
    minus = RealBaxter(SimpleNamespace(st=st, p=_pieces(st, -D1, G0)), order)
    # With fixed G0, Q is affine in Dt and c is quadratic. Odd polarization
    # extracts the exact linear term, with no small-step cancellation.
    return lambda i, j, r: (plus.raw_numerator(i, j, r)-minus.raw_numerator(i, j, r))/(4*np.pi*r)


def run():
    rows = []
    designs = [
        ('binary_single', [1., 1.5], [1.8], [1.]),
        ('binary_signed', [1., 1.5], [1.8, 6.], [1., -.35]),
        ('binary_repeated', [1., 1.5], [3., 3.], [1., -.35]),
        ('binary_high_z', [1., 1.5], [1.8, 60.], [1., -.15]),
        ('ternary_unequal', [1., 1.8, 3.4], [1.8, 6.], [1., -.35]),
    ]
    for label, sig, zs, ks in designs:
        n = len(sig)
        x = np.arange(1, n+1, dtype=float)
        x /= x.sum()
        rho_tot = 6*.15/(np.pi*np.dot(x, np.array(sig)**3))
        dp = FMSA_double_prop(sig, np.ones(n), x, rho_tot, 1., n_tails=len(zs),
                              z=zs, k=ks, input_type='bh', n_k=128, verbose=False)
        st = from_fmsa(dp)
        if label == 'binary_repeated':
            # Undo from_fmsa's duplicate-pole grouping: this checks genuine
            # repeated labelled rates with signed strengths in the BH system.
            st = HCYMix(st.sigma, st.rho, np.repeat(st.z, 2),
                        (st.K[:, None, :, :] * np.array([1., -.35])[None, :, None, None]/.65)
                        .reshape(2*st.T, n, n))
        c1 = linearized(st)
        points, max_dp, max_exterior = [], 0., 0.
        for i in range(n):
            for j in range(i+1):  # larger diameter is the row
                R = st.SIG[i, j]
                knot = abs(st.LAM[i, j])
                rs = set([.07*R, .29*R, .63*R, .93*R, 1.1*R])
                if knot > 0:
                    rs.update([knot*.99, knot, knot*1.01])
                # Includes mediated overlap knots in the ternary core.
                for ell in range(n):
                    mediated = abs(st.sigma[ell]-R)
                    if 0 < mediated < R:
                        rs.update([mediated*.99, mediated*1.01])
                for r in sorted(rs):
                    got = c1(i, j, r)
                    target = dp.get_c1_inner(r, i, j)
                    defect = abs(got-target)/(1+abs(target))
                    max_dp = max(max_dp, defect)
                    if r > R:
                        tail = np.sum(st.K[:, i, j]*np.exp(-st.z*(r-R)))/r
                        max_exterior = max(max_exterior, abs(got-tail)/(1+abs(tail)))
                    points.append((i, j, r, got))
        roots = []
        # Core comparisons against the nonlinear branch on two decreasing steps.
        for step in [1e-3, 5e-4]:
            pm = []
            for sign in [1., -1.]:
                scaled = HCYMix(st.sigma, st.rho, st.z, sign*step*st.K)
                sol = solve_bh_mix(scaled, tol=2e-12)
                if sol is None:
                    raise AssertionError((label, step, 'root missing'))
                pm.append(RealBaxter(sol, 96))
            defect = max(abs((pm[0].raw_numerator(i,j,r)-pm[1].raw_numerator(i,j,r))/
                             (4*np.pi*r*step)-got)/(1+abs(got)) for i,j,r,got in points)
            roots.append(dict(step=step, normalized_defect=defect))
        rows.append(dict(label=label, species=n, tails=st.T, rates=st.z.tolist(),
                         point_count=len(points), normalized_DP_defect=max_dp,
                         normalized_exterior_defect=max_exterior, actual_root_differences=roots))
        print(json.dumps(rows[-1]), flush=True)
        assert max_dp < 2e-7, rows[-1]
        assert max_exterior < 2e-8, rows[-1]
        assert roots[-1]['normalized_defect'] < 2e-6, rows[-1]
    return dict(scope='finite numerical evidence; independent DP Lean identity remains open', states=rows)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = run()
    args.output.write_text(json.dumps(report, indent=2)+'\n')
