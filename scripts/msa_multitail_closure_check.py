#!/usr/bin/env python3
"""Independent real-space closure checks for pure and mixture multi-Yukawa MSA.

The c-side is the piecewise real-space Baxter convolution, integrated directly.
It is never constructed from |F|² or from an inverse FFT of the spectral side.
Finite quadrature checks are evidence, not a substitute for a Lean closure theorem.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.integrate import quad

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from msa_exact_mix import HCYMix, solve_bh_mix, qhat, chat_k


class RealBaxter:
    def __init__(self, sol, order=96):
        self.sol, self.st, self.p = sol, sol.st, sol.p
        self.nodes, self.weights = leggauss(order)
        self.lo = (self.st.sigma[None, :] - self.st.sigma[:, None]) / 2
        self.hi = self.st.SIG

    def value(self, i, j, x, derivative=False):
        x = np.asarray(x)
        lo, hi = self.lo[i, j], self.hi[i, j]
        y = x - hi
        zz = self.st.z[:, None]
        # Clamp unused branches so large negative support coordinates never overflow.
        ec = np.exp(-zz * np.maximum(x - lo, 0))
        et = np.exp(-zz * np.maximum(x - hi, 0))
        w, c = self.p['Wt'][:, i, j, None], self.p['Ct'][:, i, j, None]
        if derivative:
            core = self.p['qp'][i, j] + self.p['A'][j] * y - np.sum(zz * w * ec, axis=0)
            tail = -np.sum(zz * (w * ec + c * et), axis=0)
        else:
            core = self.p['qp'][i, j] * y + self.p['A'][j] * y**2 / 2 + np.sum(w * ec + c, axis=0)
            tail = np.sum(w * ec + c * et, axis=0)
        return np.where(x < lo, 0, np.where(x <= hi, core, tail))

    def bounded(self, f, a, b):
        if b <= a:
            return 0.0
        x = (a + b) / 2 + (b - a) / 2 * self.nodes
        return float((b - a) / 2 * np.dot(self.weights, f(x)))

    def conv_pair(self, i, j, ell, r):
        start = max(self.lo[j, ell], self.lo[i, ell] - r)
        cuts = sorted({start, max(start, self.hi[j, ell]), max(start, self.hi[i, ell] - r)})
        ans = sum(self.bounded(lambda x: self.value(i, ell, x + r, True) *
                              self.value(j, ell, x), a, b)
                  for a, b in zip(cuts[:-1], cuts[1:]))
        c = cuts[-1]
        z = self.st.z
        # At c both factors are in their tails; the exact improper integral uses
        # z_nu + z_mu, so coincident rates require no limiting prescription.
        vi = (self.p['Wt'][:, i, ell] * np.exp(-z * (c + r - self.lo[i, ell])) +
              self.p['Ct'][:, i, ell] * np.exp(-z * (c + r - self.hi[i, ell])))
        vj = (self.p['Wt'][:, j, ell] * np.exp(-z * (c - self.lo[j, ell])) +
              self.p['Ct'][:, j, ell] * np.exp(-z * (c - self.hi[j, ell])))
        return ans - float(np.sum(z[:, None] * vi[:, None] * vj[None, :] /
                                  (z[:, None] + z[None, :])))

    def raw_numerator(self, i, j, r):
        """2π r c_ij(r), evaluated from Q' and the actual convolution."""
        return -float(self.value(i, j, r, True)[0]) + sum(
            self.st.rho[ell] * self.conv_pair(i, j, ell, r) for ell in range(self.st.N))

    def numerator(self, i, j, r):
        # Baxter's ordered-pair relation covers the whole positive core when
        # the larger-diameter species is the row. Below a positive support edge,
        # obtain the other entry by reciprocity, as in the existing unequal-core
        # derivation. The raw formula is tested for symmetry on its common domain.
        if self.st.sigma[i] < self.st.sigma[j]:
            i, j = j, i
        return self.raw_numerator(i, j, r)

    def chat(self, i, j, k):
        sig = self.hi[i, j]
        bp = abs(self.lo[i, j])
        cuts = sorted({0.0, min(bp, sig), sig})
        core = sum(self.bounded(lambda xs: np.array([
            self.numerator(i, j, r) * np.sin(k * r) for r in xs]), a, b)
            for a, b in zip(cuts[:-1], cuts[1:])) * 2 / k
        tail = 4 * np.pi / k * np.sum(self.st.K[:, i, j] *
            (self.st.z * np.sin(k * sig) + k * np.cos(k * sig)) /
            (self.st.z**2 + k**2))
        return core + tail

    def laplace_quad(self, i, j, s):
        lo, hi = self.lo[i, j], self.hi[i, j]
        core = self.bounded(lambda xs: self.value(i, j, xs) * np.exp(-s * xs), lo, hi)
        z = self.st.z
        tail_at_hi = self.p['Wt'][:, i, j] * np.exp(-z * (hi - lo)) + self.p['Ct'][:, i, j]
        return core + np.exp(-s * hi) * np.sum(tail_at_hi / (s + z))


def states():
    for eta in (0.05, 0.25, 0.45):
        for zs, ks, label in (
            ([1.0], [.015], 'single'),
            ([1.0, 5.0], [.015, .008], 'two_attractive'),
            ([1.0, 20.0], [.015, -.008], 'long_attraction_short_repulsion'),
            ([1.0, 5.0, 60.0], [.01, .007, -.004], 'three_high_z'),
            ([5.0, 5.0], [.012, -.004], 'coincident_rates'),
            ([1.0, 5.0], [.012, 0.0], 'zero_strength_tail'),
        ):
            yield f'pure_eta{eta}_{label}', HCYMix([1.0], [6 * eta / np.pi], zs,
                np.asarray(ks)[:, None, None])
    for sig in ([1.0, 1.0], [1.0, 1.5]):
        fractions = np.array([.4, .6])
        rho = fractions * (.15 * 6 / np.pi / np.dot(fractions, np.array(sig)**3))
        for zs, scales, label in (
            ([1.0], [.02], 'single'),
            ([1.0, 5.0], [.02, -.008], 'two'),
            ([1.0, 5.0, 20.0], [.02, -.008, .004], 'three'),
            ([5.0, 5.0], [.012, -.004], 'coincident_rates'),
        ):
            K = np.array(scales)[:, None, None] * np.array([[1., .8], [.8, 1.2]])
            yield f'binary_sig{sig[1]}_{label}', HCYMix(sig, rho, zs, K)


def check_state(label, st, order):
    sol = solve_bh_mix(st)
    if sol is None:
        raise AssertionError(f'{label}: numerical root not found; no existence claim justified')
    real = RealBaxter(sol, order)
    errors = dict(laplace=0., exterior=0., fourier=0., symmetry=0.)
    for s in (0.7, 2.0, 9.0):
        ref = qhat(st, sol.p, s).real
        for i in range(st.N):
            for j in range(st.N):
                got = real.laplace_quad(i, j, s)
                errors['laplace'] = max(errors['laplace'], abs(got - ref[i, j]) / (1 + abs(ref[i, j])))
    for i in range(st.N):
        for j in range(st.N):
            for offset in (.03, .3, 1.0):
                r = st.SIG[i, j] + offset
                target = 2 * np.pi * np.sum(st.K[:, i, j] * np.exp(-st.z * offset))
                errors['exterior'] = max(errors['exterior'], abs(real.numerator(i, j, r) - target))
            bp = abs(real.lo[i, j])
            for r in (bp + .03, (bp + st.SIG[i, j]) / 2, .9 * st.SIG[i, j]):
                errors['symmetry'] = max(errors['symmetry'], abs(real.raw_numerator(i, j, r) -
                                                                real.raw_numerator(j, i, r)))
    ks = np.array([.3, 1.7, 5.1, 12.0])
    spectral = chat_k(sol, ks)
    for m, k in enumerate(ks):
        for i in range(st.N):
            for j in range(st.N):
                got = real.chat(i, j, k)
                errors['fourier'] = max(errors['fourier'], abs(got - spectral[m, i, j]) /
                                        (1 + abs(spectral[m, i, j])))
    # A selected convolution is also checked against adaptive quadrature,
    # independently of the fixed-order Gauss rule and analytic tail-pair formula.
    i, j, ell, r = 0, st.N - 1, 0, .37
    start = max(real.lo[j, ell], real.lo[i, ell] - r)
    cuts = sorted({start, max(start, real.hi[j, ell]), max(start, real.hi[i, ell] - r)})
    integrand = lambda x: float(real.value(i, ell, x + r, True)[0] * real.value(j, ell, x)[0])
    independent = sum(quad(integrand, a, b, epsabs=1e-10, epsrel=1e-10)[0]
                      for a, b in zip(cuts[:-1], cuts[1:]))
    independent += quad(integrand, cuts[-1], np.inf, epsabs=1e-10, epsrel=1e-10)[0]
    errors['adaptive_conv'] = abs(independent - real.conv_pair(i, j, ell, r)) / (1 + abs(independent))
    if max(errors.values()) > 2e-8:
        raise AssertionError((label, errors))
    return dict(label=label, species=st.N, tails=st.T, z=st.z.tolist(), eta=st.eta,
                diameters=st.sigma.tolist(), amplitudes=st.K.tolist(),
                residual=sol.residual, errors=errors)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1] /
                    'results/multitail_extension/independent_closure_checks.json')
    ap.add_argument('--order', type=int, default=96)
    args = ap.parse_args()
    rows = []
    for label, st in states():
        row = check_state(label, st, args.order)
        rows.append(row)
        print(label, row['errors'], flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(dict(quadrature_order=args.order,
        sampled_k=[.3, 1.7, 5.1, 12.0],
        unequal_core_orientation='Larger-diameter row on the full positive core; '
            'raw reciprocal entries compared only on their common valid domain.', states=rows,
        scope='Numerical checks at selected real roots; no universal root/phase-existence certificate.'),
        indent=2) + '\n')
    print(f'PASS {len(rows)} states; {args.output}', flush=True)


if __name__ == '__main__':
    main()
