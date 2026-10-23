"""Fold-binding transition in z = (1.8, 12), K = (1, w), eta = 0.3.

For each w: the real fold tau_f (end of the traced real branch), the nearest complex
physical-sheet fold tau*_c (tracked in w by Newton on the augmented system, sheet
membership tested by ray continuation with sqrt-d approach), the prediction
R_pred = min(tau_f, |tau*_c|), and an independent series estimate of R (root test with
the square-root correction).  The crossing w_c (|tau*_c| = tau_f) is bisected.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import brentq

sys.path.insert(0, str(Path(__file__).resolve().parent))
from nearest import M, candidates, continue_path, nearest_singularity, on_sheet, refine_fold, series  # noqa: E402

ETA = 0.3
OUT = Path(__file__).resolve().parents[2]/'results'/'coupling_singularities'


def state(w):
    return M.HCYMix([1.0], [6*ETA/np.pi], [1.8, 12.0], np.array([1.0, w]).reshape(2, 1, 1))


def real_fold(w, lam_max=80.0):
    tr = M.trace_coupling_mix(state(w), lam_max=lam_max)
    return tr[-1][0] if tr[-1][0] < lam_max - 1e-9 else None


def series_radius(st, scale, nmax=80):
    U, _ = series(st, nmax, scale)
    cm = np.abs(U[1:]).max(axis=1)
    return [scale*cm[k - 1]**(-1/k)/np.exp(1.5*np.log(k)/k) for k in (60, 70, 80)]


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    w0 = -2.65
    st = state(w0)
    t0, info = nearest_singularity(st, 5.0)
    u, t = info['u'], t0
    rows = []
    ws = np.r_[np.arange(-2.65, -2.399, 0.01), np.arange(-2.38, -1.99, 0.04)]
    for w in ws:
        st = state(w)
        u, t, res = refine_fold(st, u, t)
        dist, slopes = on_sheet(st, t, u)
        tf = real_fold(w)
        pred = min(abs(t), tf) if tf else abs(t)
        sc = 0.9*pred
        Rs = series_radius(st, sc)
        row = dict(w=float(w), tau_f=tf, tau_c=[t.real, t.imag], abs_tau_c=abs(t), fold_residual=res,
                   sheet_slopes=slopes, R_pred=pred, binding='fold' if (tf and tf < abs(t)) else 'complex',
                   R_series=Rs)
        rows.append(row)
        print(f"w={w:+.3f}: tau_f={tf if tf is None else round(tf, 5)}  tau*_c={t:.5f} |.|={abs(t):.5f} slopes={np.round(slopes, 3)}"
              f"  R_pred={pred:.5f} ({row['binding']})  R_series(60,70,80)={np.round(Rs, 4)}", flush=True)
    # crossing
    def gap(w):
        st = state(w); nonlocal_u = gap.u
        uu, tt, _ = refine_fold(st, nonlocal_u, gap.t); gap.u, gap.t = uu, tt
        return abs(tt) - real_fold(w)
    i = next(k for k in range(len(rows) - 1) if rows[k]['binding'] != rows[k + 1]['binding'])
    gap.u = None
    lo, hi = rows[i]['w'], rows[i + 1]['w']
    st = state(lo); gap.t = complex(*rows[i]['tau_c'])
    gap.u, _ = continue_path(st, [0.0, 0.97*gap.t]), None
    gap.u, gap.t, _ = refine_fold(st, gap.u, gap.t)
    wc = brentq(gap, lo, hi, xtol=1e-6) if rows[i]['tau_f'] and rows[i + 1]['tau_f'] else None
    print(f"crossing |tau*_c| = tau_f at w_c = {wc}", flush=True)
    (OUT/'family_crossing.json').write_text(json.dumps(dict(command=' '.join(sys.argv), eta=ETA, z=[1.8, 12.0],
                                                            rows=rows, w_c=wc), indent=1, default=str))


if __name__ == '__main__':
    main()
