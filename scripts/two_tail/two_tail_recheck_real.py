"""Re-check every real-fold pass of a classify JSON for a missed nearer singularity.

nearest_singularity follows one Pade candidate and can return a real fold when a complex pair of
nearly the same modulus is nearer: z = (0.6, 0.84), eta = 0.49, where tau* = -9.69 +- 0.57i
(|tau*| = 9.71) and tau_f = 9.79 are found or missed depending on the scale.  Here every type-R
evaluation is redone at several scale factors and the smallest accepted |tau*| is kept.  A flag
means that point is really a fail.  Float64 evidence.

--types R,C+ also rechecks the complex-binding passes (default R).

Usage: two_tail_recheck_real.py CLASSIFY.json OUT.json [--types T,...] [--procs N]
"""
import os, sys, json, argparse
os.environ.setdefault('OMP_NUM_THREADS', '1')
from multiprocessing import Pool
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parent))
from two_tail_margin import state, series_scale
from two_tail_scan import w0
from nearest import nearest_singularity

FACTORS = (0.6, 0.7, 0.8, 0.9, 1.0, 1.1, 1.15, 1.3)


def recheck(e):
    st = state(e['z1'], e['z2'], e['f']*w0(e['z1'], e['z2']), e['eta'])
    sc = series_scale(st, 5.0); found = []
    for k in FACTORS:
        try:
            ts, info = nearest_singularity(st, k*sc, verbose=False, res_rel='hadamard', sheet_retry=True)
        except Exception:
            continue
        if ts is not None:
            found.append((abs(ts), [ts.real, ts.imag], info['kind'], k))
    best = min(found) if found else None
    return dict(type=e['type'], z1=e['z1'], z2=e['z2'], eta=e['eta'], f=e['f'], tau_inst=e['tau_inst'], R_c_old=e['R_c'],
                R_c_min=None if best is None else best[0], tau_star=None if best is None else best[1],
                kind=None if best is None else best[2], n_found=len(found),
                flag=bool(best is not None and best[0] < e['tau_inst']))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('classify'); ap.add_argument('out'); ap.add_argument('--procs', type=int, default=12)
    ap.add_argument('--types', default='R')
    a = ap.parse_args()
    cmd = ' '.join([sys.executable] + sys.orig_argv[1:]); print('# ' + cmd, flush=True)
    evs = [e for c in json.load(open(a.classify))['cells'] for e in c['evals'] if e['type'] in a.types.split(',')]
    with Pool(a.procs) as p:
        res = p.map(recheck, evs, chunksize=1)
    for r in sorted(res, key=lambda r: (-r['eta'], r['z1'], r['z2'], r['f'])):
        print(f"{r['type']} eta={r['eta']} z=({r['z1']},{r['z2']}) f={r['f']:.7f} tau_inst={r['tau_inst']:.6f} "
              f"R_old={r['R_c_old']:.6f} R_min={r['R_c_min']} {r['kind']} n={r['n_found']}"
              + ('  <-- FLAG' if r['flag'] else ''), flush=True)
    json.dump(dict(command=cmd, factors=FACTORS, rows=res), open(a.out, 'w'), indent=1)
    print(f"# {sum(r['flag'] for r in res)} of {len(res)} passes of type {a.types} flagged", flush=True)


if __name__ == '__main__':
    main()
