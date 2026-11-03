"""Counterexample search: all-attractive multi-tail coefficient sign constancy in extreme regimes
(read-only use of the frozen probe)."""
import os, sys, io, contextlib, time
import numpy as np
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_and_1st_Truncation/scripts')
import msa_coupling_series_sign_probe as P
import msa_exact_mix as Mx
from concurrent.futures import ProcessPoolExecutor
eta = lambda e: 6*e/np.pi
cases = []
ZS = [(0.05, 1.0), (0.1, 100.0), (1.0, 1.001), (0.2, 2.0, 20.0, 200.0), (0.5, 0.6, 0.7), (5.0, 50.0)]
for z in ZS:
    T = len(z)
    for w in [1e-3, 1.0, 1e3]:
        K = [1.0] + [w**((i+1)/(T-1)) if i % 2 == 0 else w**(-(i+1)/(T-1)) for i in range(T-1)]
        for e in [0.01, 0.2, 0.45, 0.49]:
            cases.append(('pure', z, K, e))
for z in [(0.5, 3.0), (1.8, 12.0)]:
    for sig in [(1.0, 3.0), (1.0, 1.0)]:
        for x2 in [0.5, 1e-3]:
            for e in [0.3]:
                cases.append(('binary', z, sig, x2, e))
def run(c):
    buf = io.StringIO(); t0 = time.time()
    try:
        if c[0] == 'pure':
            _, z, K, e = c; name = f'pure z={z} K={[float(f"{k:.4g}") for k in K]} eta={e}'
            st = Mx.HCYMix([1.0], [eta(e)], list(z), np.array(K).reshape(len(z), 1, 1))
        else:
            _, z, sig, x2, e = c; name = f'binary z={z} sigma={sig} x2={x2} eta={e}'
            s = np.array(sig); x = np.array([1-x2, x2]); rho = x*e/((np.pi/6)*np.sum(x*s**3))
            SIG = .5*(s[:, None]+s[None, :]); eps = np.array([[1.0, .7], [.7, .5]])
            K = np.array([(eps*SIG), 0.4*(eps*SIG)])
            st = Mx.HCYMix(list(s), list(rho), list(z), K)
        with contextlib.redirect_stdout(buf):
            P.report(name, st, nmax=40)
    except Exception as ex:
        return f'{c}: ERROR {ex!r}'
    return buf.getvalue().strip() + f'  [{time.time()-t0:.0f}s]'
if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), 'OMP_NUM_THREADS=', os.environ.get('OMP_NUM_THREADS'), 'cases=', len(cases), flush=True)
    with ProcessPoolExecutor(16) as ex:
        for out in ex.map(run, cases):
            print(out, flush=True)
