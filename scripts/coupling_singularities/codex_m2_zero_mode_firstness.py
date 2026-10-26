"""Certify first zero-mode contact for the PY-linked M2 control.

The zero-mode statement does not exclude a finite-wave-number instability.
All existence, uniqueness, sign and linkage inequalities use real Arb balls.
The earlier certificate's JSON supplies a predictor, never a proof verdict.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
from importlib.metadata import version
import json
import math
from pathlib import Path
import time

import numpy as np
from flint import arb, arb_mat, ctx

from codex_m2_tangency import (
    PACKAGE, D, TwoTail, branch_krawczyk, branch_link, enclosing_endpoints,
    interval_record, krawczyk, local_geometry, matvec, newton,
)


def balls(records):
    return [enclosing_endpoints(*r) for r in records]


def velocity(model, U, W):
    _, J = model.PJ(U)
    return [v[0] for v in arb_mat(J).solve(
        arb_mat([[b] for b in model.forcing(W)])).tolist()]


def stationary_box(model, root, center):
    W = root[5]
    y = np.r_[center[:5], center[6:]]
    nested = [D(D(float(a), [float(b)]), [D(float(b), [0.])])
              for a, b in zip(center[:4], center[6:])]
    Hvv = np.array([q.g[0].g[0] for q in model.P(nested, True)])
    _, J = model.PJ(list(center[:4]), True)
    accel = np.linalg.solve(np.asarray(J, float), -Hvv)

    def equations(q):
        U, T, V = q[:4], q[4], q[5:]
        P, J = model.PJ(U)
        b = model.forcing(W)
        return ([a-T*bi for a, bi in zip(P, b)] +
                [a-bi for a, bi in zip(matvec(J, V), b)] +
                [sum((a*b for a, b in zip(model.grad_zero(U), V)), 0)])

    radii = .004*np.r_[abs(center[6:])+.05, .5, abs(accel)+.1]
    ok, Z, _, _, q = krawczyk(equations, y, radii)
    assert ok, "No unique stationary-point box"
    root9 = root[:5] + root[6:]
    assert all(z.contains(a) for z, a in zip(Z, root9)), "Tangency outside stationary box"
    return Z, q


def refine_terminal_segment(model, root, Z, prefix):
    W, wm = root[5], float(root[5].mid())
    t = prefix[-1]['tau'][1]
    initial = t
    B = float(root[4].mid())-.001
    target = math.nextafter(float(root[4].upper()), math.inf)+1e-6
    assert initial < B < float(root[4].lower()) < target
    Yprev = balls(prefix[-1]['endpoint_box'])
    u = np.array([float(y.mid()) for y in Yprev])
    h, chain, root_covered = .001, [], False
    while t < target:
        tn = min(target, t+h, B if t < B else target)
        tm = (t+tn)/2
        T = enclosing_endpoints(t, tn)
        um = newton(lambda y: model.residual(y, tm, wm, True), u)
        ub = newton(lambda y: model.residual(y, tn, wm, True), um)
        _, Jf = model.PJ(list(um), True)
        vf = np.linalg.solve(np.asarray(Jf, float), model.forcing(wm, True))
        radii = 2.5*abs(vf)*(tn-t)+.2*(1+abs(um))*(tn-t)+1e-12*(1+abs(um))
        radii = np.maximum(radii, np.array([
            max(abs(float(y.lower())-a), abs(float(y.upper())-a))
            for y, a in zip(Yprev, um)])*1.5)
        ok, U, _, _, q = branch_krawczyk(model, T, W, um, radii)
        if ok and all(x.contains(y) for x, y in zip(U, Yprev)):
            try:
                V = velocity(model, U, W)
                df = sum((a*b for a, b in zip(model.grad_zero(U), V)), arb(0))
                if t < B:
                    classification = 'strictly_decreasing'
                    usable = df < 0
                else:
                    classification = 'unique_stationary_neighborhood'
                    usable = all(z.contains(a) for z, a in zip(Z, U+[T]+V))
            except (ValueError, ZeroDivisionError):
                usable = False
        else:
            usable = False
        if not usable:
            h /= 2
            assert h > 1e-11, f"Terminal sign/containment refinement stalled at {t}"
            continue

        _, Jb = model.PJ(list(ub), True)
        uw = np.linalg.solve(np.asarray(Jb, float), tn*np.array([0., model.kf['kt'][1], 0., 0.]))
        end_rad = 4*abs(uw)*float(W.rad())+1e-12*(1+abs(ub))
        endpoint_ok = False
        for _ in range(12):
            oke, Y, Ke, _, qe = branch_krawczyk(model, arb(tn), W, ub, end_rad)
            if oke and all(x.contains(y) for x, y in zip(U, Y)):
                endpoint_ok = True
                break
            need = np.array([max(abs(float(a.lower())-b), abs(float(a.upper())-b))
                             for a, b in zip(Ke, ub)])
            end_rad = np.maximum(end_rad, 1.5*need)
        if not endpoint_ok:
            h /= 2
            assert h > 1e-11, f"Terminal endpoint refinement stalled at {t}"
            continue
        root_covered = root_covered or (
            T.contains(root[4]) and all(a.contains(b) for a, b in zip(U, root[:4])))
        chain.append({'tau': [t, tn], 'u_box': [interval_record(x) for x in U],
                      'velocity_box': [interval_record(x) for x in V],
                      'F0_tau_derivative': interval_record(df),
                      'classification': classification, 'weighted_contraction': q,
                      'endpoint_box': [interval_record(x) for x in Y], 'endpoint_contraction': qe})
        Yprev, u, t = Y, ub, tn
        assert len(chain) <= 100000, "Terminal piece limit"
        if len(chain) % 1000 == 0:
            print(f'  terminal: {len(chain)} pieces, tau={t:.10g}/{target:.10g}', flush=True)
        h = min(h*1.25, .002)
    assert root_covered, "Entire root u/tau box not covered by any terminal slab"
    return {'tau_start': initial, 'stationary_neighborhood_start': B, 'tau_end': target,
            'pieces': len(chain), 'root_box_covered': True, 'chain': chain}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--predictor', default=str(PACKAGE/'results/coupling_singularities/codex_m2_tangency.json'))
    ap.add_argument('--out', default=str(PACKAGE/'results/coupling_singularities/codex_m2_zero_mode_firstness.json'))
    args = ap.parse_args()
    ctx.prec = 192
    start = time.monotonic()
    predictor = json.loads(Path(args.predictor).read_text())
    label = predictor['model']
    model = TwoTail(label['eta'], *label['z'])
    x = np.array([sum(v)/2 for v in predictor['root_box']])
    x = newton(lambda y: model.augmented(y, True), x)
    radii = 1e-11*(1+abs(x))
    ok, root, _, C, q = krawczyk(model.augmented, x, radii)
    assert ok, "Tight augmented root certificate failed"
    geometry = local_geometry(model, root)
    def displaced(y):
        v = model.augmented(y)
        v[8] += arb('0.001')
        return v
    bad, *_ = krawczyk(displaced, x, radii, X=root, C=C)
    assert not bad, "Displaced zero constraint passed"
    linkage = branch_link(model, root)
    prefix = []
    for slab in linkage['chain']:
        f0 = model.zero_mode(balls(slab['u_box']))
        if not f0 > 0:
            break
        prefix.append({**slab, 'F0_box': interval_record(f0)})
    assert prefix and len(prefix) < len(linkage['chain'])
    print('Positive prefix:', len(prefix), 'slabs through', prefix[-1]['tau'][1], flush=True)
    Z, stationary_q = stationary_box(model, root, x)
    terminal = refine_terminal_segment(model, root, Z, prefix)
    cover_path = Path(args.out).with_suffix('.cover.json.gz')
    cover = {'positive_prefix': prefix, 'terminal': terminal.pop('chain')}
    cover_bytes = gzip.compress(json.dumps(cover, separators=(',', ':')).encode(), mtime=0)
    cover_path.write_bytes(cover_bytes)
    result = {
        'status': 'PASS_FIRST_ZERO_MODE_CONTACT', 'model': model.label,
        'root_box': [interval_record(v) for v in root], 'f_box': interval_record(root[5]/model.w0),
        'strict_augmented_Krawczyk': True, 'augmented_contraction': q, 'geometry': geometry,
        'negative_control_displaced_F0_rejected': True,
        'positive_prefix': {'pieces': len(prefix), 'tau_start': 0,
                            'tau_end': prefix[-1]['tau'][1]},
        'cover': {'file': cover_path.name, 'format': 'gzip-compressed JSON',
                  'sha256': hashlib.sha256(cover_bytes).hexdigest()},
        'stationary_unique_box_order': ['D1', 'D2', 'G1', 'G2', 'tau', 'vD1', 'vD2', 'vG1', 'vG2'],
        'stationary_unique_box': [interval_record(z) for z in Z],
        'stationary_box_contraction': stationary_q,
        'terminal': terminal, 'precision_bits': ctx.prec,
        'claim': 'At the certified touching w, F0>0 at every 0<=tau<tau_touch, and F0(tau_touch)=0 on the PY-seeded regular real BH branch.',
        'argument': 'Positive prefix; strict decrease to the terminal stationary neighborhood; all late stationary roots lie in one unique nine-equation box, containing the certified nondegenerate minimum with value zero. No other late critical point exists, so the function is strictly decreasing before that minimum and positive there. Endpoint boxes glue all slabs to PY.',
        'scope': 'First zero-mode zero only. Does not exclude an earlier finite-k instability, establish full canonicity, compare a Taylor radius or prove any all-density condition. Not Lean.',
        'dependencies': {'python_flint': version('python-flint'), 'numpy': np.__version__},
        'source_sha256': {str(p.relative_to(PACKAGE)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in [Path(__file__).resolve(), PACKAGE/'scripts/coupling_singularities/codex_m2_tangency.py',
                                    PACKAGE/'formalization/certificates/f5_competing_tails.py']},
        'seconds': round(time.monotonic()-start, 3),
    }
    Path(args.out).write_text(json.dumps(result, indent=2)+'\n')
    print('PASS: first zero-mode contact on the PY-seeded regular BH branch', flush=True)
    print(args.out)


if __name__ == '__main__':
    main()
