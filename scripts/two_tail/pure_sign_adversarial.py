"""Adversarial counterexample search for strict coefficient sign constancy, pure all-attractive
multi-tail fluids (float64 evidence, NOT a Lean proof).

margin(state) = min over components k and orders 2..29 of s_k c_{n,k} / sqrt(|c_{n-1,k} c_{n+1,k}|),
with s_k = sign c_{1,k} and coefficients of (tau / tau_end)^n. It is ~1 for a smooth geometric
sequence, tends to 0 near a sign change, and is negative at a change (a strict-form
counterexample). Random sampling, then Nelder-Mead from the best points, in log-parameters:
z1 in [0.1, 20], z_{t+1}/z_t in [1.01, 300] with z capped at 200, strength ratios in [1e-3, 1e3],
eta in [0.01, 0.6]. An evaluation is abandoned after 60 s and counted as not evaluated.
"""
import sys, io, contextlib, warnings, signal
import numpy as np
from scipy.optimize import minimize
from concurrent.futures import ProcessPoolExecutor
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_and_1st_Truncation/scripts')
import msa_coupling_series_sign_probe as P
import msa_exact_mix as Mx
SEED = int(sys.argv[sys.argv.index('--seed') + 1]) if '--seed' in sys.argv else 1
NS = int(sys.argv[sys.argv.index('--n') + 1]) if '--n' in sys.argv else 480
NMAX = 30

def decode(x, T):
    z1 = np.exp(np.clip(x[0], np.log(0.1), np.log(20)))
    rat = np.exp(np.clip(x[1:T], np.log(1.01), np.log(300)))
    z = np.minimum(z1 * np.cumprod(np.r_[1.0, rat]), 200.0*(1+1e-3*np.arange(T)))
    w = np.exp(np.clip(x[T:2*T-1], np.log(1e-3), np.log(1e3)))
    K = np.r_[1.0, w]
    eta = 1/(1+np.exp(-x[2*T-1]))*0.59 + 0.01
    return z, K, eta

class Slow(Exception): pass
def _alarm(*_): raise Slow()

def margin(args):
    x, T = args
    signal.signal(signal.SIGALRM, _alarm); signal.alarm(60)
    z, K, eta = decode(np.asarray(x), T)
    try:
        with warnings.catch_warnings(), contextlib.redirect_stdout(io.StringIO()):
            warnings.simplefilter('ignore')
            st = Mx.HCYMix([1.0], [6*eta/np.pi], list(z), K.reshape(T, 1, 1))
            tf = Mx.trace_coupling_mix(st, lam_max=8.0)[-1][0]
            U, _ = P.series(st, NMAX, tf)
        c = U[1:]
        if not np.all(np.isfinite(c)): return 9.0
        s = np.sign(c[0])
        m = (s[None, :]*c[1:-1]) / np.sqrt(np.abs(c[:-2]*c[2:]) + 1e-300)
        # below 1e-11 of a component's largest coefficient float64 carries no sign (no-fold scaling)
        a = np.abs(c) > 1e-11*np.max(np.abs(c), axis=0, keepdims=True)
        use = a[:-2] & a[1:-1] & a[2:]
        return float(m[use].min())
    except Exception:
        return 9.0
    finally:
        signal.alarm(0)

def local(args):
    x0, T = args
    res = minimize(lambda x: margin((x, T)), x0, method='Nelder-Mead', options=dict(maxiter=150, xatol=1e-4, fatol=1e-6))
    return res.fun, res.x

if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(float64 evidence, NOT a Lean proof)', flush=True)
    rng = np.random.default_rng(SEED)
    for T in (2, 3):
        lo = np.r_[np.log(0.1), [np.log(1.01)]*(T-1), [np.log(1e-3)]*(T-1), -3.0]
        hi = np.r_[np.log(20), [np.log(300)]*(T-1), [np.log(1e3)]*(T-1), 3.0]
        X = lo + (hi-lo)*rng.random((NS, 2*T))
        with ProcessPoolExecutor(16) as ex:
            m = []
            for k, v in enumerate(ex.map(margin, [(x, T) for x in X])):
                m.append(v)
                if (k+1) % 60 == 0: print(f'  T={T}: {k+1}/{NS} done, min so far {min(m):.4f}', flush=True)
            m = np.array(m)
        ok = m < 9
        order = np.argsort(m)
        print(f'T={T}: {ok.sum()}/{NS} evaluated; margin quantiles (min, 1%, 10%, 50%) = '
              f'{np.min(m[ok]):.4f} {np.quantile(m[ok], .01):.4f} {np.quantile(m[ok], .1):.4f} {np.median(m[ok]):.4f}', flush=True)
        with ProcessPoolExecutor(16) as ex:
            loc = list(ex.map(local, [(X[i], T) for i in order[:16]]))
        for f, x in sorted(loc, key=lambda r: r[0])[:5]:
            z, K, eta = decode(x, T)
            print(f'   local min margin {f:+.5f} at z={np.round(z, 4).tolist()} K={np.round(K, 5).tolist()} eta={eta:.4f}', flush=True)
