"""Fine f-resolution inside a scan bracket: margin, tau_inst, R_c, binding, the end of the traced
branch (tau_f), and the minimum of det F(0) along the branch up to 1.3 R_c (a zero-mode crossing
is present iff that minimum is < 0).  Float64 evidence.

Usage: two_tail_m2_fine.py eta z1:z2:f_lo:f_hi[:n] [...]      (n = number of f values, default 14)
       two_tail_m2_fine.py                                       (the first run: 7/56 and 4.5/22.5)
"""
import os, sys
os.environ.setdefault('OMP_NUM_THREADS', '1')
from multiprocessing import Pool
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parent))
from two_tail_margin import margin, state, M
from two_tail_scan import w0


def run(a):
    z1, z2, eta, f = a
    r = margin(z1, z2, f*w0(z1, z2), eta, lam_max=4000.0)
    st = state(z1, z2, f*w0(z1, z2), eta)
    tr = M.trace_coupling_mix(st, lam_max=1.3*r['R_c'] if r['R_c'] else 200.0)
    d0 = np.array([float(np.real(s.detF(0.0))) for _, s in tr]); lam = np.array([l for l, _ in tr])
    i = int(np.argmin(d0))
    return (z1, z2, f, r['status'], r['tau_inst'], r['R_c'], r['binding'], r['margin'], r['tau_f'],
            float(d0[i]), float(lam[i]), float(lam[-1]))


if __name__ == '__main__':
    print('# ' + ' '.join([sys.executable] + sys.orig_argv[1:]), flush=True)
    if len(sys.argv) > 2:
        eta = float(sys.argv[1]); jobs = []
        for c in sys.argv[2:]:
            p = c.split(':'); z1, z2, lo, hi = map(float, p[:4]); n = int(p[4]) if len(p) > 4 else 14
            jobs += [(z1, z2, eta, float(f)) for f in np.round(np.linspace(lo, hi, n), 6)]
    else:
        jobs = [(7.0, 56.0, 0.49, f) for f in np.round(np.arange(0.2620, 0.2646, 0.0002), 5)] + \
               [(4.5, 22.5, 0.49, f) for f in np.round(np.arange(0.2260, 0.2286, 0.0002), 5)]
    with Pool(int(os.environ.get('FINE_PROCS', 14))) as p:
        for z1, z2, f, s, ti, R, b, m, tf, dmin, lmin, lend in sorted(p.map(run, jobs)):
            print(f"z=({z1},{z2}) f={f:.5f}: {s:21} ti={ti} R={R} [{b}] m={m} tau_f={tf}  "
                  f"minF0={dmin:+.4g}@tau={lmin:.3f} trace_end={lend:.3f}", flush=True)
