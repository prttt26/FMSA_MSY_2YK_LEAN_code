"""Re-check the lower (pass) end of every scan bracket at 8 Pade scales.

The single-candidate defect (build history item 5 of the note) only creates false PASSES:
taking the smallest |tau*| over scales can only lower R_c.  So a scan bracket [lo, hi] stays valid
iff its pass end lo is a true pass; the fail end hi stays a fail.  For every row this redoes the
nearest-singularity search at lo with two_tail_recheck_real.recheck (smallest |tau*| over
FACTORS) and flags lo if that is inside tau_inst.  A flagged row has f* < lo and needs a search
below.  Float64 evidence.

Usage: two_tail_recheck_lo.py SCAN.json[,SCAN.json] OUT.json [--procs N]
"""
import os, sys, json, argparse
os.environ.setdefault('OMP_NUM_THREADS', '1')
from multiprocessing import Pool
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from two_tail_recheck_real import recheck, FACTORS


def lo_eval(r):
    lo = r['f_star'][0]
    e = min(r['evals'], key=lambda e: abs(e['f'] - lo))
    assert abs(e['f'] - lo) < 1e-12 and e['margin'] is not None and e['margin'] >= 0, (r['z1'], r['z2'], r['eta'])
    return dict(type='R' if e['binding'] == 'real' else 'C+', z1=r['z1'], z2=r['z2'], eta=r['eta'], f=e['f'],
                tau_inst=e['tau_inst'], R_c=e['R_c'])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('scans'); ap.add_argument('out'); ap.add_argument('--procs', type=int, default=10)
    a = ap.parse_args()
    cmd = ' '.join([sys.executable] + sys.orig_argv[1:]); print('# ' + cmd, flush=True)
    rows = [(Path(s).name, r) for s in a.scans.split(',') for r in json.load(open(s))['rows']]
    evs = [lo_eval(r) for _, r in rows]
    with Pool(a.procs) as p:
        res = p.map(recheck, evs, chunksize=1)
    out = []
    for (src, r), x in zip(rows, res):
        x.update(source=src, f_star=r['f_star'])
        out.append(x)
    for x in sorted(out, key=lambda x: (x['source'], x['z2'], x['eta'])):
        print(f"{x['source']} z=({x['z1']},{x['z2']}) eta={x['eta']} lo={x['f']:.7f} [{x['type']}] "
              f"tau_inst={x['tau_inst']:.6f} R_old={x['R_c_old']:.6f} R_min={x['R_c_min']} {x['kind']} "
              f"n={x['n_found']}" + ('  <-- FLAG' if x['flag'] else ''), flush=True)
    json.dump(dict(command=cmd, factors=FACTORS, rows=out), open(a.out, 'w'), indent=1)
    print(f"# {sum(x['flag'] for x in out)} of {len(out)} bracket pass ends flagged", flush=True)


if __name__ == '__main__':
    main()
