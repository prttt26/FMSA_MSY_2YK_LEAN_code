"""Convergence margin of the coupling series for a mixed-sign two-Yukawa tail, single component.

State: hard spheres sigma = 1, packing eta, tail K = (1, w) at decay rates z = (z1, z2).
The requirement "the series converges at the physical coupling for every stable state at
every temperature" reduces (scale-free) to R_c(eta) >= tau_inst(eta) for every eta, with

  tau_inst  first loss of canonicity along the traced real branch: the det F(0) sign change
            (k = 0 spinodal) or a winding flip of det F(ik) (k != 0 instability);
  R_c       modulus of the nearest physical-sheet singularity (nearest.nearest_singularity).

margin = R_c/tau_inst - 1; a state with no instability up to lam_max has margin -inf
(the stable range is unbounded while R_c is finite).  Float64; evidence, not proof.

Usage: two_tail_margin.py z1 z2 w eta [eta ...]
"""
from __future__ import annotations

import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from nearest import M, nearest_singularity  # noqa: E402
from family_crossing import series_radius  # noqa: E402
from msa_instability_before_fold_check import diag  # noqa: E402


def state(z1, z2, w, eta):
    return M.HCYMix([1.0], [6*eta/np.pi], [z1, z2], np.array([1.0, w]).reshape(2, 1, 1))


def tau_inst(st, lam_max=40.0):
    """(tau_inst, kind, tau_f): first canonicity loss on the traced branch, and its end if a fold."""
    tr = M.trace_coupling_mix(st, lam_max=lam_max)
    lam = np.array([l for l, _ in tr]); D = [diag(s) for _, s in tr]
    W = np.array([round(d['W']) for d in D]); d0 = np.array([d['detF0'] for d in D])
    tf = lam[-1] if lam[-1] < lam_max - 1e-9 else None
    i = next((j for j in range(1, len(W)) if W[j] != W[0] or np.sign(d0[j]) != np.sign(d0[0])), None)
    if i is None:
        return None, None, tf
    if np.sign(d0[i]) != np.sign(d0[i - 1]):
        return lam[i - 1] + (lam[i] - lam[i - 1])*d0[i - 1]/(d0[i - 1] - d0[i]), 'k=0', tf
    return 0.5*(lam[i - 1] + lam[i]), 'k!=0', tf


def series_scale(st, sc, it=4):
    """Shrink the series scale to 0.9 R_est while the root-test radius sits well inside it.

    A scale far beyond R makes the scaled coefficients grow like (scale/R)^n and the Pade
    systems singular (seen: tau_f = 24 with R ~ 7 gave NaN poles)."""
    for _ in range(it):
        R = float(np.median(series_radius(st, sc)))
        if not np.isfinite(R) or R <= 0:
            sc *= 0.5
        elif R < 0.8*sc:
            sc = 0.9*R
        else:
            break
    return sc


def margin(z1, z2, w, eta, lam_max=40.0):
    st = state(z1, z2, w, eta)
    ti, kind, tf = tau_inst(st, lam_max)
    sc = series_scale(st, 0.9*(tf if tf else (ti if ti else 5.0)))
    ts, info = None, None
    for f in (1.0, 0.8, 1.15):                   # Pade candidates are scale-sensitive; retry nearby
        try:
            ts, info = nearest_singularity(st, f*sc, verbose=False, res_rel=True)
        except (np.linalg.LinAlgError, RuntimeError):
            continue
        if ts is not None:
            break
    R = None if ts is None else abs(ts)
    m = (-np.inf if ti is None else (None if R is None else R/ti - 1.0))
    return dict(z1=z1, z2=z2, w=w, eta=eta, tau_inst=ti, kind=kind, tau_f=tf,
                tau_star=None if ts is None else [ts.real, ts.imag], R_c=R,
                binding=None if info is None else info['kind'], margin=m)


def main(argv):
    z1, z2, w = map(float, argv[:3])
    for eta in map(float, argv[3:]):
        t0 = time.time(); r = margin(z1, z2, w, eta)
        print(f"z=({z1},{z2}) w={w} eta={eta}: tau_inst={r['tau_inst']} ({r['kind']}) tau_f={r['tau_f']} "
              f"tau*={r['tau_star']} R_c={r['R_c']} [{r['binding']}] margin={r['margin']}  ({time.time() - t0:.1f}s)",
              flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
