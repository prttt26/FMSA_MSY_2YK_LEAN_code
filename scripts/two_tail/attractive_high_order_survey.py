"""Coefficients to high order against the arclength fold, all-attractive states
(float64 evidence, NOT a Lean proof).

Each state: first fold tau_f by pseudo-arclength (attractive_real_branch, which does not jump folds),
then Taylor coefficients of u(tau_f s) through order NMAX with the frozen probe's exact recursion.
Per state: the last order with a sign change in any component (a component below 1e-10 of its
largest is not read), and the root-test radius in units of tau_f, |c_NMAX|^(-1/NMAX) * NMAX^(-3/(2 NMAX))
with the sqrt-singularity factor removed. All-order sign: no change at all. Eventual sign: the last
change is well below NMAX. R = tau_f: slope near 1. FLAG marks a change in the last quarter of the orders
or a slope off by more than 1 %, either of which would mean a singularity other than the fold.
The radius is the slope of the envelope max_k |c_n,k| n^{3/2} over the last 30 orders, which does not
carry the amplitude (an earlier root test read 1.03 - 1.10 from the amplitude alone).
With --ternary or --quaternary: only N = 3 or 4, T = 1, 2, diameter ratio to 4, K_t a sum of two rank-one terms.
Families: pure T = 2, 3 (rates 0.1-200, K ratio to 1e5, eta to 0.6); binaries T = 1, 2 (diameter ratio to 5,
rates 0.3-40, composition 0.01-0.99, eta to 0.5) with K_t positive semidefinite and all entries positive
("PSD+"), positive semidefinite with entries of either sign ("PSD+-"), or all entries positive but
indefinite ("INDEF", which indefinite_binary_check shows can fail outright).
"""
import sys, io, contextlib, warnings, signal
import numpy as np
from concurrent.futures import ProcessPoolExecutor
sys.path[:0] = ['/home/rpan/YK_tail_FMSA/Lean_code/MSA_Convergence/scripts/two_tail',
                '/home/rpan/YK_tail_FMSA/Lean_code/MSA_and_1st_Truncation/scripts']
import msa_coupling_series_sign_probe as P
import msa_exact_mix as Mx
import attractive_real_branch as RB
NMAX = 150
SEED = int(sys.argv[sys.argv.index('--seed') + 1]) if '--seed' in sys.argv else 1
COUNT = int(sys.argv[sys.argv.index('--count') + 1]) if '--count' in sys.argv else 48
TIMEOUT = 900
class Slow(Exception): pass
def _alarm(*_): raise Slow()


def cases():
    rng = np.random.default_rng(SEED); out = []
    def pure(T):
        z = np.sort(np.exp(rng.uniform(np.log(0.1), np.log(200), T)))
        K = np.exp(rng.uniform(0, np.log(1e5), T))
        return dict(sig=[1.0], x=[1.0], eta=float(rng.uniform(0.02, 0.6)), z=z.tolist(), K=K.reshape(T, 1, 1).tolist())
    def binary(T, kind):
        s2 = float(np.exp(rng.uniform(0, np.log(5)))); x2 = float(np.exp(rng.uniform(np.log(.01), np.log(.99))))
        Ks = []
        for _ in range(T):
            a, b = np.exp(rng.uniform(np.log(.03), np.log(3), (2, 2)))
            if kind == 'PSD+-':
                a = a*rng.choice([-1.0, 1.0], 2); b = b*rng.choice([-1.0, 1.0], 2)
            A = np.outer(a, a) + np.outer(b, b)
            if kind == 'INDEF':
                A = np.exp(rng.uniform(np.log(.01), np.log(10), (2, 2))); A = (A + A.T)/2
                if A[0, 1]**2 <= A[0, 0]*A[1, 1]: A[0, 1] = A[1, 0] = 1.5*np.sqrt(A[0, 0]*A[1, 1])
            Ks.append(A.tolist())
        return dict(sig=[1.0, s2], x=[1 - x2, x2], eta=float(rng.uniform(0.02, 0.5)),
                    z=np.sort(np.exp(rng.uniform(np.log(.3), np.log(40), T))).tolist(), K=Ks)
    def ternary(T, kind):
        s = np.r_[1.0, np.exp(rng.uniform(0, np.log(4), 2))]; x = rng.dirichlet(np.ones(3))
        Ks = []
        for _ in range(T):
            v = np.exp(rng.uniform(np.log(.03), np.log(3), (2, 3)))
            if kind == 'PSD+-': v = v*rng.choice([-1.0, 1.0], (2, 3))
            Ks.append((v.T @ v).tolist())
        return dict(sig=s.tolist(), x=x.tolist(), eta=float(rng.uniform(0.02, 0.5)),
                    z=np.sort(np.exp(rng.uniform(np.log(.3), np.log(40), T))).tolist(), K=Ks)
    def quaternary(T, kind):
        s = np.r_[1.0, np.exp(rng.uniform(0, np.log(4), 3))]; x = rng.dirichlet(np.ones(4))
        Ks = []
        for _ in range(T):
            v = np.exp(rng.uniform(np.log(.03), np.log(3), (2, 4)))
            if kind == 'PSD+-': v = v*rng.choice([-1.0, 1.0], (2, 4))
            Ks.append((v.T @ v).tolist())
        return dict(sig=s.tolist(), x=x.tolist(), eta=float(rng.uniform(0.02, 0.5)),
                    z=np.sort(np.exp(rng.uniform(np.log(.3), np.log(40), T))).tolist(), K=Ks)
    if '--quaternary' in sys.argv:
        for kind in ('PSD+', 'PSD+-'):
            for T in (1, 2):
                out += [(f'quaternary {kind} T={T}', quaternary(T, kind)) for _ in range(COUNT)]
        return out
    if '--ternary' in sys.argv:
        for kind in ('PSD+', 'PSD+-'):
            for T in (1, 2):
                out += [(f'ternary {kind} T={T}', ternary(T, kind)) for _ in range(COUNT)]
        return out
    out += [('pure T=2', pure(2)) for _ in range(COUNT)] + [('pure T=3', pure(3)) for _ in range(COUNT)]
    for kind in ('PSD+', 'PSD+-', 'INDEF'):
        for T in (1, 2):
            out += [(f'binary {kind} T={T}', binary(T, kind)) for _ in range(COUNT)]
    return out


def run(c):
    fam, d = c
    desc = f"eta={d['eta']:.4g} sig={np.round(d['sig'], 3).tolist()} x={np.round(d['x'], 4).tolist()} z={np.round(d['z'], 4).tolist()} K={np.array(d['K']).ravel().round(4).tolist()}"
    signal.signal(signal.SIGALRM, _alarm); signal.alarm(TIMEOUT)
    try:
        with warnings.catch_warnings(), contextlib.redirect_stdout(io.StringIO()):
            warnings.simplefilter('ignore')
            sig = np.array(d['sig']); x = np.array(d['x']); rho = x*d['eta']/((np.pi/6)*np.sum(x*sig**3))
            st = Mx.HCYMix(sig, rho, d['z'], np.array(d['K']))
            B = RB.H.Branch(st); u1 = np.linalg.solve(B.J(B.u0).real, B.b.real)
            tm = 1.0/np.max(np.abs(u1)/(1 + np.abs(B.u0.real)))
            tf = None
            for _ in range(12):
                tf = RB.first_fold(st, tm)
                if tf is not None: break
                tm *= 4.0
            if tf is None: return fam, 'nofold', f'{desc}: no fold found'
            sc = tf
            for _ in range(12):
                U, _ = P.series(st, NMAX, sc)
                c = np.real(U[1:])
                if np.all(np.isfinite(c)) and np.max(np.abs(c[-1])) < 1e100: break
                sc /= 2.0                       # a singularity well inside tau_f: scaled coefficients overflow
            else:
                return fam, 'nan', f'{desc}: non-finite coefficients, tf={tf:.5g}'
        last = 0; flips = 0
        for k in range(c.shape[1]):
            col = c[:, k]; mx = np.max(np.abs(col))
            if mx == 0: continue
            live = np.abs(col) > 1e-10*mx
            idx = np.where(live)[0]
            if len(idx) < 2: continue
            s = np.sign(col[idx]); ch = idx[1:][s[1:] != s[:-1]]
            if len(ch):
                last = max(last, int(ch[-1]) + 1); flips += len(ch)
        env = np.max(np.abs(c), axis=1)*np.arange(1, NMAX + 1)**1.5
        rt = float((sc/tf)*(np.max(env[-40:-30])/np.max(env[-10:]))**(1.0/30))
        flag = last > 3*NMAX//4 or not (0.99 < rt < 1.01)
        return fam, ('FLAG' if flag else 'ok'), f'{desc}: tf={tf:.6g} sign changes {flips}, last at order {last}, R/tf {rt:.4f}', last, rt
    except Slow:
        return fam, 'timeout', f'{desc}: TIMEOUT'
    except Exception as e:
        return fam, 'error', f'{desc}: ERROR {e!r}'[:300]
    finally:
        signal.alarm(0)


if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), f'NMAX={NMAX} (float64 evidence, NOT a Lean proof)', flush=True)
    todo = cases(); res = {}
    with ProcessPoolExecutor(int(sys.argv[sys.argv.index('--workers') + 1]) if '--workers' in sys.argv else 24) as ex:
        for r in ex.map(run, todo):
            res.setdefault(r[0], []).append(r)
            if r[1] != 'ok' or (len(r) > 3 and r[3] > 0): print(r[0], r[1], r[2], flush=True)
    for fam, rs in res.items():
        good = [r for r in rs if len(r) > 3]
        cnt = {k: sum(r[1] == k for r in rs) for k in ('ok', 'FLAG', 'nofold', 'nan', 'timeout', 'error')}
        if good:
            print(f'== {fam}: {cnt}; states with any sign change {sum(r[3] > 0 for r in good)}/{len(good)}, largest last-change order {max(r[3] for r in good)}; R/tf range [{min(r[4] for r in good):.4f}, {max(r[4] for r in good):.4f}]', flush=True)
        else:
            print(f'== {fam}: {cnt}', flush=True)
