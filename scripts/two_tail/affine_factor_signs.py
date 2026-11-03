"""Affine structure of the one-species BH factor and source in per-tail variables (D_m, P_m = G_m D_m)
(float64 evidence, NOT a Lean proof).

For one species, F_t = 1 - rho Qhat(z_t) and S_t = secondRHS_t depend on the amplitudes only through
W_m ∝ G_m D_m and C_m = D_m - (2 pi rho e^{-z_m sigma}/z_m) G_m D_m. Hence they are AFFINE in
(D_m, P_m):
    F_t = F0_t - sum_m (alpha_tm D_m + beta_tm P_m),   S_t = S0_t + sum_m (gamma_tm D_m + delta_tm P_m).
The BH equations read D_t F_t = tau k_t and 2 pi G_t F_t = S_t. If alpha, beta, gamma, delta >= 0
and F0, S0, k > 0, then x_t = D_t / tau = k_t / F_t and G_t = S_t x_t / (2 pi k_t) have positive
Taylor coefficients at every order (positive-system induction). This script checks the affinity
and reports the coefficient signs.
"""
import sys
import numpy as np
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_and_1st_Truncation/scripts')
import msa_coupling_series_sign_probe as P
import msa_exact_mix as Mx

def FS(st, D, G):
    """F_t and S_t for one species from the frozen residual: r1 = D F, r2 = 2 pi G F - S."""
    T = st.T
    u = np.concatenate([np.asarray(D, float), np.asarray(G, float)]).astype(complex)
    r, _ = P.residual_c(u, st); r = r.real
    # F from r1 needs D != 0; evaluate F separately with a tiny probe D on each tail if needed
    return r[:T], r[T:]

def factor_source(st, D, G):
    T = st.T; eps = 1e-7
    F = np.empty(T); S = np.empty(T)
    for t in range(T):
        Dp = np.array(D, float).copy()
        if abs(Dp[t]) < eps:   # F_t is D_t-independent only through P; add a probe and remove its affine effect
            raise ValueError('use D_t != 0')
        r1, r2 = FS(st, Dp, G)
        F[t] = r1[t]/Dp[t]
        S[t] = 2*np.pi*G[t]*F[t] - r2[t]
    return F, S

def coefficients(st):
    T = st.T
    base_D = np.full(T, 1e-3); base_G = np.zeros(T)
    F0, S0 = factor_source(st, base_D, base_G)
    alpha = np.empty((T, T)); beta = np.empty((T, T)); gamma = np.empty((T, T)); delta = np.empty((T, T))
    h = 0.5; g = 0.7
    for m in range(T):
        D1 = base_D.copy(); D1[m] += h
        F1, S1 = factor_source(st, D1, base_G)
        alpha[:, m] = -(F1 - F0)/h; gamma[:, m] = (S1 - S0)/h
        G2 = base_G.copy(); G2[m] = g
        F2, S2 = factor_source(st, D1, G2)   # P_m changes from 0 to g (base_D[m] + h)
        Pm = g*(base_D[m] + h)
        Pm0 = 0.0
        # remove the P contribution of the base point's other tails (base_G = 0, so none)
        beta[:, m] = -(F2 - F1)/(Pm - Pm0); delta[:, m] = (S2 - S1)/(Pm - Pm0)
    # constant parts at D = P = 0
    F00 = F0 + alpha @ base_D; S00 = S0 - gamma @ base_D
    # affinity check at a random point
    rng = np.random.default_rng(0); Dr = rng.uniform(0.2, 1.0, T); Gr = rng.uniform(0.0, 1.0, T)
    Fr, Sr = factor_source(st, Dr, Gr)
    Pr = Gr*Dr
    aff = max(np.max(np.abs(Fr - (F00 - alpha @ Dr - beta @ Pr))), np.max(np.abs(Sr - (S00 + gamma @ Dr + delta @ Pr))))
    return F00, S00, alpha, beta, gamma, delta, aff

if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(float64 evidence, NOT a Lean proof)')
    np.set_printoptions(precision=4, linewidth=150)
    eta = lambda e: 6*e/np.pi
    for z in [(1.8,), (0.3, 3.0), (1.0, 10.0), (3.0, 30.0), (1.0, 1.05), (0.5, 2.0, 8.0)]:
        for e in [0.05, 0.3, 0.49]:
            st = Mx.HCYMix([1.0], [eta(e)], list(z), np.ones(len(z)).reshape(len(z), 1, 1))
            F00, S00, a, b, c, d, aff = coefficients(st)
            mins = {k: float(np.min(v)) for k, v in dict(alpha=a, beta=b, gamma=c, delta=d).items()}
            print(f'z={z} eta={e}: affinity defect {aff:.1e}; F0={F00} S0={S00}; mins ' +
                  ' '.join(f'{k}={v:+.3e}' for k, v in mins.items()), flush=True)
            if min(mins.values()) < 0:
                for k, v in dict(alpha=a, beta=b, gamma=c, delta=d).items():
                    if v.min() < 0: print(f'    {k} =\n    ' + np.array2string(v).replace('\n', '\n    '))
