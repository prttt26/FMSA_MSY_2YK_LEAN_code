"""Convergence margin of the coupling series for a mixed-sign two-Yukawa tail, single component.

State: hard spheres sigma = 1, packing eta, tail K = (1, w) at decay rates z = (z1, z2).
The requirement "the series converges at the physical coupling for every state of the initial
stable interval 0 <= tau < tau_inst(eta)" (user decision 2026-10-26: re-entrant stable states
after a closed instability interval are not included) is R_c(eta) >= tau_inst(eta), with

  tau_inst  first canonicity loss detected along the traced real branch: a det F(0) sign change
            (k = 0) or a change of the rounded winding of det F(ik) on diag's finite k grid
            (k != 0).  A crossing detector: a touch-and-retreat or two crossings between
            samples go undetected;
  R_c       modulus of the nearest physical-sheet singularity (nearest.nearest_singularity).

status (handoff/claude_codex/002 §4, 003):
  crossing_bracket       crossing found; margin = R_c/tau_inst - 1 (a value)
  no_crossing_up_to_cap  traced to the cap min(lam_max, 1.02 R_c) with no crossing, so
                         tau_inst > tau_max.  If R_c < tau_max the state fails (R < tau_max <
                         tau_inst) and margin = R_c/tau_max - 1 is an upper bound; otherwise
                         margin is None
  trace_stalled          trace ended below lam_max without a crossing; same rule with tau_max
                         = the trace end
  R_unresolved           no sheet-tested singularity found; margin None
None means unknown, never failure.  Float64; evidence, not proof.

Usage: two_tail_margin.py z1 z2 w eta [eta ...]
"""
from __future__ import annotations

import sys
import time
from pathlib import Path

import numpy as np

_HERE = Path(__file__).resolve().parent
_FOUNDATION = _HERE.parents[2]/'MSA_and_1st_Truncation'/'scripts'   # frozen 1.0.17, imported read-only
sys.path[:0] = [str(_HERE), str(_FOUNDATION/'coupling_singularities'), str(_FOUNDATION)]
from nearest import M, nearest_singularity  # noqa: E402
from family_crossing import series_radius  # noqa: E402
from msa_instability_before_fold_check import diag  # noqa: E402


def state(z1, z2, w, eta):
    return M.HCYMix([1.0], [6*eta/np.pi], [z1, z2], np.array([1.0, w]).reshape(2, 1, 1))


def tau_inst(st, lam_max=40.0):
    """(tau_inst, kind, tau_f, tau_max): first detected crossing on the traced branch, the trace
    end if it stopped below lam_max (a fold or a stall, not certified), and the traced maximum."""
    tr = M.trace_coupling_mix(st, lam_max=lam_max)
    lam = np.array([l for l, _ in tr]); D = [diag(s) for _, s in tr]
    W = np.array([round(d['W']) for d in D]); d0 = np.array([d['detF0'] for d in D])
    tf = lam[-1] if lam[-1] < lam_max - 1e-9 else None
    i = next((j for j in range(1, len(W)) if W[j] != W[0] or np.sign(d0[j]) != np.sign(d0[0])), None)
    if i is None:
        return None, None, tf, float(lam[-1])
    if np.sign(d0[i]) != np.sign(d0[i - 1]):
        return lam[i - 1] + (lam[i] - lam[i - 1])*d0[i - 1]/(d0[i - 1] - d0[i]), 'k=0', tf, float(lam[-1])
    return 0.5*(lam[i - 1] + lam[i]), 'k!=0', tf, float(lam[-1])


def series_scale(st, sc, it=16):
    """Move the series scale to 0.9 R_est while the root-test radius is far from it.

    A scale far beyond R makes the scaled coefficients grow like (scale/R)^n and the Pade
    systems singular (seen: tau_f = 24 with R ~ 7 gave NaN poles).  A scale far below R hides
    the singularity: candidates are kept only within 3 scales (seen: no crossing, default
    scale 4.5, R ~ 84 never a candidate).  Far below R the root test is roundoff-limited and
    reads about 1.5 scales whatever R is, so growth is geometric until the estimate settles."""
    for _ in range(it):
        R = float(np.median(series_radius(st, sc)))
        if not np.isfinite(R) or R <= 0:
            sc *= 0.5
        elif R < 0.8*sc:
            sc = 0.9*R
        elif R > 1.25*sc:
            sc = max(1.5*sc, 0.9*R)
        else:
            break
    return sc


MIN_FACTORS = (0.6, 0.7, 0.8, 0.9, 1.0, 1.1, 1.15, 1.3)
MIN_MARGIN = 1e-3


def margin(z1, z2, w, eta, lam_max=40.0):
    """R_c first, then the trace only to min(lam_max, 1.02 R_c): no crossing up to there means
    tau_inst > R_c, a failure, so the branch beyond R_c is never needed.

    nearest_singularity follows one Pade candidate.  When a real fold binds at tau_inst (margin
    in [0, MIN_MARGIN)), a complex pair of nearly the same modulus may be the nearer singularity
    and be found or missed depending on the scale (two_tail_recheck_real: 31 of 313 such passes
    were false, all with margin < 1.4e-4).  Then R_c is the smallest |tau*| over MIN_FACTORS."""
    st = state(z1, z2, w, eta)
    sc = series_scale(st, 5.0)
    ts, info = None, None
    for f in (1.0, 0.8, 1.15):                   # Pade candidates are scale-sensitive; retry nearby
        try:
            ts, info = nearest_singularity(st, f*sc, verbose=False, res_rel='hadamard', sheet_retry=True)
        except (np.linalg.LinAlgError, RuntimeError):
            continue
        if ts is not None:
            break
    R = None if ts is None else abs(ts)
    cap = lam_max if R is None else min(lam_max, 1.02*R)
    ti, kind, tf, tmax = tau_inst(st, cap)
    n_scales = 1
    if R is not None and ti is not None and info['kind'] == 'real' and 0 <= R/ti - 1.0 < MIN_MARGIN:
        n_scales = len(MIN_FACTORS)
        for f in MIN_FACTORS:
            try:
                t2, i2 = nearest_singularity(st, f*sc, verbose=False, res_rel='hadamard', sheet_retry=True)
            except Exception:
                continue
            if t2 is not None and abs(t2) < R:
                ts, info, R = t2, i2, abs(t2)
    if R is None:
        status, m, mk = 'R_unresolved', None, None
    elif ti is not None:
        status, m, mk = 'crossing_bracket', R/ti - 1.0, 'value'
    else:
        status = 'no_crossing_up_to_cap' if tf is None else 'trace_stalled'
        m, mk = (R/tmax - 1.0, 'upper_bound') if R < tmax else (None, None)
    return dict(z1=z1, z2=z2, w=w, eta=eta, lam_max=lam_max, trace_cap=cap, tau_inst=ti, kind=kind,
                tau_f=tf, tau_max=tmax, tau_star=None if ts is None else [ts.real, ts.imag], R_c=R,
                binding=None if info is None else info['kind'], status=status, margin=m, margin_kind=mk,
                n_scales=n_scales)


def main(argv):
    z1, z2, w = map(float, argv[:3])
    for eta in map(float, argv[3:]):
        t0 = time.time(); r = margin(z1, z2, w, eta)
        print(f"z=({z1},{z2}) w={w} eta={eta}: tau_inst={r['tau_inst']} ({r['kind']}) tau_f={r['tau_f']} "
              f"tau_max={r['tau_max']} tau*={r['tau_star']} R_c={r['R_c']} [{r['binding']}] {r['status']} "
              f"margin={r['margin']} ({r['margin_kind']})  ({time.time() - t0:.1f}s)",
              flush=True)


if __name__ == '__main__':
    main(sys.argv[1:])
