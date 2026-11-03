"""Falsification test of the Stieltjes picture, pure fluids (float64 evidence, NOT a Lean proof).

If a component u_k(tau) = c_0 + c_1 tau + Int tau^2 dmu(x)/(x^2 (x - tau)) has a positive measure on
[R, inf), its coefficients c_n (n >= 2) are moments, so they are log-convex:
c_n^2 <= c_{n-1} c_{n+1} for n >= 3, and the 3x3 Hankel determinants of (c_n)_{n>=2} are >= 0.
Reported per family: the largest c_n^2/(c_{n-1} c_{n+1}) over components and orders 3..29, and the
smallest normalised 3x3 Hankel determinant separately for D, G and the energy E = sum K_t G_t, using coefficients of (tau/tau_end)^n, skipping
coefficients below 1e-10 of a component's largest. Control: mixed-sign tails must violate it.
"""
import sys, io, contextlib, warnings, signal
import numpy as np
from concurrent.futures import ProcessPoolExecutor
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_and_1st_Truncation/scripts')
import msa_coupling_series_sign_probe as P
import msa_exact_mix as Mx
NMAX = 30
class Slow(Exception): pass
def _alarm(*_): raise Slow()

def stats(c):
    z, K, eta = c
    signal.signal(signal.SIGALRM, _alarm); signal.alarm(300)
    try:
        with warnings.catch_warnings(), contextlib.redirect_stdout(io.StringIO()):
            warnings.simplefilter('ignore')
            # a strength with no fold below lam_max scales the series away from tau_f, into noise
            K = np.array(K, float)
            for _ in range(8):
                st = Mx.HCYMix([1.0], [6*eta/np.pi], list(z), K.reshape(len(z), 1, 1))
                tf = Mx.trace_coupling_mix(st, lam_max=8.0)[-1][0]
                if tf < 8.0 - 1e-9: break
                K = K*10.0
            else:
                return None
            U, _ = P.series(st, NMAX, tf)
        c = U[1:]                                           # c[0] is order 1
        if not np.all(np.isfinite(c)): return None
        T = len(z); worst = 0.0; hank = dict(D=np.inf, G=np.inf, E=np.inf)
        ene = c[:, T:] @ K
        cols = [('D', c[:, k]) for k in range(T)] + [('G', c[:, T+k]) for k in range(T)] + [('E', ene)]
        for fam, full in cols:
            col = full[1:]*np.sign(full[1])                 # orders 2.. with the sign of order 2
            mx = np.max(np.abs(col)); good = np.abs(col) > 1e-10*mx
            for n in range(1, len(col)-1):
                if good[n-1] and good[n] and good[n+1] and col[n-1]*col[n+1] > 0:
                    worst = max(worst, col[n]**2/(col[n-1]*col[n+1]))
            for n in range(0, 14):
                H3 = np.array([[col[n+i+j] for j in range(3)] for i in range(3)])
                nrm = np.prod([col[n+2*i] for i in range(3)])
                # the determinant of a moment matrix is tiny; below 1e-10 of its terms float64 has no sign
                if nrm != 0 and abs(np.linalg.det(H3)) > 1e-10*abs(nrm): hank[fam] = min(hank[fam], np.linalg.det(H3)/abs(nrm))
        return worst, hank, tuple(np.round(z, 3)), tuple(np.round(K, 3)), round(eta, 3)
    except Exception:
        return None
    finally:
        signal.alarm(0)

if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(float64 evidence, NOT a Lean proof)', flush=True)
    rng = np.random.default_rng(7)
    fams = {}
    def rand(T, mixed):
        z = np.sort(np.exp(rng.uniform(np.log(0.3), np.log(30), T)))
        K = np.exp(rng.uniform(np.log(0.01), np.log(100), T))
        if mixed: K = K*rng.choice([-1.0, 1.0], T); K[0] = abs(K[0])
        return (z, K, float(rng.uniform(0.05, 0.5)))
    fams['attractive T=1'] = [rand(1, False) for _ in range(48)]
    fams['attractive T=2'] = [rand(2, False) for _ in range(192)]
    fams['attractive T=3'] = [rand(3, False) for _ in range(192)]
    fams['CONTROL mixed T=2'] = [rand(2, True) for _ in range(64)]
    for name, cs in fams.items():
        with ProcessPoolExecutor(12) as ex:
            res = [r for r in ex.map(stats, cs) if r is not None]
        w = max(res, key=lambda r: r[0]); viol = sum(r[0] > 1+1e-6 for r in res)
        line = f'{name}: {len(res)}/{len(cs)} evaluated; states violating log-convexity: {viol}; max ratio {w[0]:.6f}'
        for f in 'DGE':
            h = min(res, key=lambda r: r[1][f]); neg = sum(r[1][f] < 0 for r in res)
            line += f'; {f}: {neg} states with a negative Hankel3, min {h[1][f]:+.2e} at z={h[2]} K={h[3]} eta={h[4]}'
        print(line, flush=True)
