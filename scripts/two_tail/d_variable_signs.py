"""Signs of F and G - G0 as series in D_1, ..., D_T alone (EXTERNAL multiprecision evidence, NOT a Lean proof).

Eliminate G: with D as independent variables, Gt_s = sum_t D_t (SD_st + SP_st Gt_t)/(2 pi F_s), F_s = F0_s + sum_t D_t (FD_st + FP_st Gt_t). If F0_s - F_s has nonnegative Taylor coefficients in D, then
D_t = tau_t/F_t(D) gives nonnegative coefficients of D(tau) by Lagrange, with no need for SP >= 0. If G - G0 is also nonnegative in D, the mixed-coefficient statement follows in full.

Usage: d_variable_signs.py --states S --order N [--T T] [--seed S] [--workers W]
"""
import sys, itertools
import numpy as np
import mpmath as mp
from multiprocessing import Pool
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_Convergence/scripts/two_tail')
import shifted_affine_closed_form as CF
from multivariate_sign_mp import mul


def series(z, e, N, T):
    z = [mp.mpf(v) for v in z]; e = mp.mpf(e); zero = [mp.mpf(0)]*(2*T)
    F0, S0 = CF.fs(z, e, zero); G0 = [S0[t]/(2*mp.pi*F0[t]) for t in range(T)]
    FD = [[None]*T for _ in range(T)]; FP = [[None]*T for _ in range(T)]; SD = [[None]*T for _ in range(T)]; SP = [[None]*T for _ in range(T)]
    for t in range(T):
        eD = list(zero); eD[t] = mp.mpf(1); eP = list(zero); eP[T + t] = mp.mpf(1)
        A, B = CF.fs(z, e, eD); C, E = CF.fs(z, e, eP)
        for s in range(T):
            fp = C[s] - F0[s]; sp = E[s] - S0[s]; fd = A[s] - F0[s] + fp*G0[t]; sd = B[s] - S0[s] + sp*G0[t]
            FD[s][t], FP[s][t], SD[s][t], SP[s][t] = fd, fp, sd - 2*mp.pi*G0[s]*fd, sp - 2*mp.pi*G0[s]*fp
    O = tuple([0]*T); Ds = [{tuple(1 if i == t else 0 for i in range(T)): mp.mpf(1)} for t in range(T)]
    G = [{} for _ in range(T)]; invF = [{O: 1/F0[s]} for s in range(T)]; dF = [{} for _ in range(T)]; St = [{} for _ in range(T)]
    for d in range(1, N + 1):
        ks = [a for a in itertools.product(range(d + 1), repeat=T) if sum(a) == d]
        P = [mul(Ds[t], G[t], d) for t in range(T)]
        for s in range(T):
            for a in ks:
                St[s][a] = sum(SD[s][t]*Ds[t].get(a, 0) + SP[s][t]*P[t].get(a, 0) for t in range(T))
                dF[s][a] = sum(FD[s][t]*Ds[t].get(a, 0) + FP[s][t]*P[t].get(a, 0) for t in range(T))
        for s in range(T):
            pr = mul(dF[s], invF[s], d)
            for a in ks: invF[s][a] = -pr.get(a, mp.mpf(0))/F0[s]
            pr = mul(St[s], invF[s], d)
            for a in ks: G[s][a] = pr.get(a, mp.mpf(0))/(2*mp.pi)
    return dF, G


def run(job):
    i, seed, N, T = job; rng = np.random.default_rng([seed, i]); mp.mp.dps = 70
    if i % 3 == 0:
        zw = float(np.exp(rng.uniform(np.log(.3), np.log(5)))); z = [zw] + [zw*float(np.exp(rng.uniform(np.log(10), np.log(300)))) for _ in range(T - 1)]
    elif i % 3 == 1:
        z0 = float(np.exp(rng.uniform(np.log(.2), np.log(30)))); z = [z0*float(np.exp(rng.uniform(0, .2))) for _ in range(T)]
    else:
        z = np.exp(rng.uniform(np.log(.1), np.log(300), T)).tolist()
    e = float(rng.uniform(.005, .79)); dF, G = series(z, e, N, T); r = {}
    for name, ps, sg in (('F0-F', dF, -1), ('G-G0', G, 1)):
        neg = tot = 0; low = None
        for p in ps:
            for k, v in p.items():
                if v == 0: continue
                tot += 1
                if sg*v < 0:
                    neg += 1
                    if low is None or sum(k) < sum(low): low = k
        r[name] = (neg, tot, low)
    return z, e, r


if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(EXTERNAL multiprecision evidence, NOT a Lean proof)', flush=True)
    val = lambda f, d: type(d)(sys.argv[sys.argv.index(f) + 1]) if f in sys.argv else d
    S, N, T, seed, W = val('--states', 30), val('--order', 12), val('--T', 1), val('--seed', 1), val('--workers', 8)
    with Pool(W) as ex: res = ex.map(run, [(i, seed, N, T) for i in range(S)], chunksize=1)
    tot = {}
    for z, e, r in res:
        for k, v in r.items():
            a = tot.setdefault(k, [0, 0, 0, None]); a[0] += v[0]; a[1] += v[1]; a[2] += v[0] > 0
            if v[2] is not None and (a[3] is None or sum(v[2]) < sum(a[3])): a[3] = v[2]
    print(f'== {S} states, T={T}, order {N}: (negative monomials, total, states with any, lowest monomial) {tot}', flush=True)
    for z, e, r in res[:8]: print(f'   z={np.round(z, 4).tolist()} eta={e:.4f}: {r}', flush=True)
