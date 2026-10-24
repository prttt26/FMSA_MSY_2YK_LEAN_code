"""Boundary w*(z2, eta) of the convergence set for K = (1, w), z = (z1, z2), single component.

w is parametrised by the cancelled fraction f = w/w0 of the attractive tail integral,
w0 = -(1/z1 + 1/z1^2)/(1/z2 + 1/z2^2) (net-neutral tail).  For each (z2, eta): margin on a
coarse f grid (the number of sign changes is reported, so monotonicity is checked, not
assumed), then bisection of the first sign change to |df| < FTOL.

Usage: two_tail_scan.py [--z1 Z1] [--z2 a,b,..] [--eta a,b,..] [--procs P] [--out FILE]
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time
from multiprocessing import Pool
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from two_tail_margin import margin  # noqa: E402

F_GRID = (0.01, 0.02, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.4, 0.5, 0.7, 0.9)
FTOL = 2e-3


def w0(z1, z2):
    return -(1/z1 + 1/z1**2)/(1/z2 + 1/z2**2)


def task(args):
    z1, z2, eta = args
    t0 = time.time(); W0 = w0(z1, z2); evals = []

    def ev(f):
        try:
            r = margin(z1, z2, f*W0, eta)
        except Exception as e:                                   # noqa: BLE001
            r = dict(z1=z1, z2=z2, w=f*W0, eta=eta, margin=None, error=repr(e))
        r['f'] = f; evals.append(r)
        print(f"  z2={z2} eta={eta} f={f:.4f} w={f*W0:+.4f}: tau_inst={r.get('tau_inst')} R_c={r.get('R_c')} "
              f"[{r.get('binding')}] margin={r['margin']}", flush=True)
        return r['margin']

    ms = [ev(f) for f in F_GRID]
    sgn = [None if m is None else (m >= 0) for m in ms]
    changes = [i for i in range(len(sgn) - 1) if None not in (sgn[i], sgn[i + 1]) and sgn[i] != sgn[i + 1]]
    fstar = None
    if changes and sgn[changes[0]]:
        lo, hi = F_GRID[changes[0]], F_GRID[changes[0] + 1]
        while hi - lo > FTOL:
            mid = 0.5*(lo + hi); m = ev(mid)
            if m is None:
                lo = hi = None
                break
            lo, hi = (mid, hi) if m >= 0 else (lo, mid)
        if lo is not None:
            fstar = [lo, hi]
    return dict(z1=z1, z2=z2, eta=eta, w0=W0, grid_signs=sgn, sign_changes=len(changes),
                f_star=fstar, w_star=None if fstar is None else [fstar[0]*W0, fstar[1]*W0],
                seconds=time.time() - t0, evals=evals)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--z1', type=float, default=1.8)
    ap.add_argument('--z2', default='2.5,3,4,6,8,12,16,24')
    ap.add_argument('--eta', default='0.02,0.05,0.1,0.2,0.3,0.4,0.45,0.47,0.49')
    ap.add_argument('--procs', type=int, default=12)
    ap.add_argument('--out', default=None)
    a = ap.parse_args()
    z2s = [float(x) for x in a.z2.split(',')]; etas = [float(x) for x in a.eta.split(',')]
    out = Path(a.out or Path(__file__).resolve().parents[2]/'results'/'coupling_singularities'/f'two_tail_scan_z1_{a.z1}.json')
    out.parent.mkdir(parents=True, exist_ok=True)
    cmd = ' '.join([sys.executable] + sys.orig_argv[1:])
    print(f"# {cmd}\n# F_GRID={F_GRID} FTOL={FTOL} OMP_NUM_THREADS={os.environ.get('OMP_NUM_THREADS')}", flush=True)
    jobs = [(a.z1, z2, e) for z2 in z2s for e in etas]
    rows = []
    with Pool(a.procs) as p:
        for r in p.imap_unordered(task, jobs):
            rows.append(r)
            print(f"DONE z2={r['z2']} eta={r['eta']}: signs={r['grid_signs']} changes={r['sign_changes']} "
                  f"f*={r['f_star']} w*={r['w_star']} ({r['seconds']:.0f}s)", flush=True)
            out.write_text(json.dumps(dict(command=cmd, F_GRID=F_GRID, FTOL=FTOL, rows=rows), indent=1, default=str))


if __name__ == '__main__':
    main()
