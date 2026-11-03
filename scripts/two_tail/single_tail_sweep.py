"""Numeric cross-check of Codex 017: one attractive tail, one species -> det F(0) changes sign
strictly before the end (fold) of the traced PY branch.  Float64 evidence."""
import os, sys
os.environ.setdefault('OMP_NUM_THREADS', '1')
from multiprocessing import Pool
import numpy as np
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[4]))   # msa_exact_mix (read-only)
import msa_exact_mix as M

def run(args):
    z, eta = args
    st = M.HCYMix([1.0], [6*eta/np.pi], [z], np.array([1.0]).reshape(1, 1, 1))
    try:
        tr = M.trace_coupling_mix(st, lam_max=4000.0)
    except Exception as e:
        return (z, eta, None, None, repr(e)[:60])
    lam = np.array([l for l, _ in tr]); d0 = np.array([float(np.real(s.detF(0.0))) for _, s in tr])
    i = next((j for j in range(1, len(d0)) if d0[j] <= 0 < d0[j-1]), None)
    ts = None if i is None else lam[i-1] + (lam[i]-lam[i-1])*d0[i-1]/(d0[i-1]-d0[i])
    return (z, eta, ts, lam[-1], 'ok')

if __name__ == '__main__':
    print('# ' + ' '.join([sys.executable] + sys.orig_argv[1:]), flush=True)
    jobs = [(z, e) for z in (0.2, 0.6, 1.8, 4.0, 10.0, 25.0) for e in (0.005, 0.05, 0.15, 0.3, 0.45, 0.55, 0.62)]
    bad = 0
    with Pool(6) as p:
        for z, e, ts, lend, msg in p.imap_unordered(run, jobs):
            ok = ts is not None and ts < lend
            bad += not ok
            print(f"z={z} eta={e}: tau_s={ts} trace_end={lend} {'tau_s<end' if ok else 'CHECK'} {msg}", flush=True)
    print(f"# states={len(jobs)} not-confirmed={bad}")
