"""For each scan cell at one eta: locate the zero-mode tangency (f_M2, tau_touch) seeded just
outside the bracket, and compare it with the bracket.  Float64 evidence."""
import os, sys, json
os.environ.setdefault('OMP_NUM_THREADS', '1')
from multiprocessing import Pool
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from two_tail_m2_locate import locate

def run(c):
    z1, z2, eta, lo, hi, Rout = c
    try:
        r = locate(z1, z2, eta, hi, lam_max=2.0*Rout)
    except Exception as e:
        r = dict(error=repr(e)[:120])
    r.update(cell=[z1, z2, eta], bracket=[lo, hi], R_out=Rout)
    return r

if __name__ == '__main__':
    scan, eta, out = sys.argv[1], float(sys.argv[2]), sys.argv[3]
    d = json.load(open(scan)); cells = []
    for r in d['rows']:
        if r['eta'] != eta or not r['f_star']:
            continue
        lo, hi = r['f_star']; o = [e for e in r['evals'] if abs(e['f'] - hi) < 1e-12][0]
        cells.append((r['z1'], r['z2'], eta, lo, hi, o['R_c']))
    cmd = ' '.join([sys.executable] + sys.orig_argv[1:])
    res = []
    with Pool(12) as p:
        for r in p.imap_unordered(run, cells):
            res.append(r)
            f = r.get('f'); lo, hi = r['bracket']
            tag = 'ERR' if 'error' in r else ('M2 in bracket' if lo <= f <= hi + 2e-3 else ('f_M2 > bracket (M1 first)' if f > hi else 'f_M2 < bracket ?'))
            print(f"{r['cell']} bracket={r['bracket']} f_M2={f} tau_touch={r.get('tau')} F0dd={r.get('F0_dd')} res={r.get('residual')} detJ={r.get('detJ')} -> {tag}", flush=True)
            json.dump(dict(command=cmd, rows=res), open(out, 'w'), indent=1)
