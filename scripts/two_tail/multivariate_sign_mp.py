"""Every mixed coefficient at multiprecision, by a second route (EXTERNAL multiprecision evidence, NOT a Lean proof).

multivariate_sign_test uses the cubic residual in float and reads entries above 1e-9 of the largest at that order. Here nothing is cut, and the recursion is the Picard form of
shifted_affine_signs, truncated power series in (tau_1, ..., tau_T), tau_t with right side tau_t:
    D_t = tau_t/F_t,  Gt_s = St_s/(2 pi F_s),  F_s = F0_s + sum (FD D + FP Pt),  St_s = sum (SD D + SP Pt),  Pt_t = D_t Gt_t.
Reports the sign of every monomial of D, Gt, and of St and -(F - F0), which would have to be positive for a proof that treats 1/F and St separately. Includes near-tie shapes, z_w << z_s.
Two precision levels; the sign must agree.

Usage: multivariate_sign_mp.py --states S --order N [--T T] [--seed S] [--workers W]
"""
import sys, itertools
import numpy as np
import mpmath as mp
from multiprocessing import Pool
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_Convergence/scripts/two_tail')
import shifted_affine_closed_form as CF


def mul(a, b, N):
    out = {}
    for x, u in a.items():
        for y, v in b.items():
            k = tuple(i + j for i, j in zip(x, y))
            if sum(k) <= N: out[k] = out.get(k, mp.mpf(0)) + u*v
    return out


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
    O = tuple([0]*T); D = [{} for _ in range(T)]; G = [{} for _ in range(T)]; P = [{} for _ in range(T)]; St = [{} for _ in range(T)]
    invF = [{O: 1/F0[s]} for s in range(T)]; dF = [{} for _ in range(T)]
    for d in range(1, N + 1):
        ks = [a for a in itertools.product(range(d + 1), repeat=T) if sum(a) == d]
        for t in range(T):                         # D at order d needs 1/F at order d - 1
            for a in ks:
                if a[t] >= 1:
                    b = tuple(x - (1 if i == t else 0) for i, x in enumerate(a))
                    D[t][a] = invF[t].get(b, mp.mpf(0))
        for t in range(T):                         # Pt at order d needs Gt at order < d
            pr = mul(D[t], G[t], d)
            for a in ks: P[t][a] = pr.get(a, mp.mpf(0))
        for s in range(T):
            for a in ks:
                St[s][a] = sum(SD[s][t]*D[t].get(a, 0) + SP[s][t]*P[t].get(a, 0) for t in range(T))
                dF[s][a] = sum(FD[s][t]*D[t].get(a, 0) + FP[s][t]*P[t].get(a, 0) for t in range(T))
        for s in range(T):                         # 1/F and Gt at order d
            pr = mul(dF[s], invF[s], d)
            for a in ks: invF[s][a] = -pr.get(a, mp.mpf(0))/F0[s]
            pr = mul(St[s], invF[s], d)
            for a in ks: G[s][a] = pr.get(a, mp.mpf(0))/(2*mp.pi)
    return D, G, St, dF, invF


def count(D, G, St, dF, invF, T):
    out = {}
    def tally(name, polys, sg):
        neg = 0; tot = 0; worst = None
        for p in polys:
            for k, v in p.items():
                if sum(k) == 0: continue
                if v == 0: continue
                tot += 1
                if sg*v < 0:
                    neg += 1
                    if worst is None or sum(k) < sum(worst): worst = k
        out[name] = (neg, tot, worst)
    tally('D', D, 1); tally('Gt', G, 1); tally('St', St, 1); tally('-dF', dF, -1); tally('1/F', invF, 1)
    return out


def run(job):
    i, seed, N, T = job; rng = np.random.default_rng([seed, i])
    if i % 3 == 0:
        zw = float(np.exp(rng.uniform(np.log(.3), np.log(5)))); z = [zw] + [zw*float(np.exp(rng.uniform(np.log(10), np.log(300)))) for _ in range(T - 1)]
    elif i % 3 == 1:
        z0 = float(np.exp(rng.uniform(np.log(.2), np.log(30)))); z = [z0*float(np.exp(rng.uniform(0, .2))) for _ in range(T)]
    else:
        z = np.exp(rng.uniform(np.log(.2), np.log(300), T)).tolist()
    e = float(rng.uniform(.01, .79)); res = []
    for dps in (50, 90):
        mp.mp.dps = dps; res.append(count(*series(z, e, N, T), T))
    return z, e, res[1], res[0] == res[1]


if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(EXTERNAL multiprecision evidence, NOT a Lean proof)', flush=True)
    val = lambda f, d: type(d)(sys.argv[sys.argv.index(f) + 1]) if f in sys.argv else d
    S, N, T, seed, W = val('--states', 30), val('--order', 14), val('--T', 2), val('--seed', 1), val('--workers', 8)
    with Pool(W) as ex: res = ex.map(run, [(i, seed, N, T) for i in range(S)], chunksize=1)
    tot = {}
    for z, e, r, agree in res:
        for k, v in r.items():
            a = tot.setdefault(k, [0, 0, 0]); a[0] += v[0]; a[1] += v[1]; a[2] += v[0] > 0
        if r['D'][0] or r['Gt'][0] or not agree: print(f'z={z} eta={e}: {r} digits agree {agree}', flush=True)
    print(f'== {S} states, T={T}, order {N}: digits agree in {sum(x[3] for x in res)}; by series (negative monomials, total, states with any): {tot}', flush=True)
    bad = [x for x in res if x[2]['St'][0]]
    for z, e, r, _ in bad[:6]: print(f'St has negative monomials: z={np.round(z, 4).tolist()} eta={e:.4f}: {r["St"]}', flush=True)
