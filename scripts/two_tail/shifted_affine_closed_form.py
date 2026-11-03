"""Closed form of the D block of the shifted affine system, at multiprecision (EXTERNAL multiprecision evidence, NOT a Lean proof).

shifted_affine_signs finds SD_st = z_t/((z_s + z_t) F0_s F0_t), which is the known order-one closed form M_st = 1/((z_s + z_t) F0_s^2 F0_t^2). Its float scan reports 263 wrong signs at
rates near 0.01; the same entries are evaluated here with 60 digits. Rates 0.005-1000, eta to 0.85. Also the signs of FD, FP at these digits.

Usage: shifted_affine_closed_form.py --states S [--seed S]
"""
import sys
import numpy as np
import mpmath as mp
mp.mp.dps = 60


def fs(z, eta, v):
    T = len(z); rho = 6*eta/mp.pi; D, P = v[:T], v[T:]; d = 2*mp.pi/(1 - eta)**2
    A0, B0, QP0 = d*((1 - eta) + 3*eta), d*(-mp.mpf(3)/2*eta), d*(mp.mpf(3)/2*eta + (1 - eta))
    C = [D[t] - 2*mp.pi*rho*P[t]*mp.exp(-z[t])/z[t] for t in range(T)]; W = [(2*mp.pi/z[t])*rho*P[t] for t in range(T)]
    Mv = -sum(rho*(W[t] + (1 + z[t])*C[t])/z[t] for t in range(T)); Nc = sum(rho*(W[t]/z[t]**2 + (1 + z[t] + z[t]**2/2)/z[t]**2*C[t]) for t in range(T))
    A = A0*(1 + Mv) - 4*B0*Nc; qp = QP0*(1 + Mv) + A0*Nc; F = []; S = []
    for x in z:
        phi1 = (1 - x - mp.exp(-x))/x**2; phi2 = (1 - x + x*x/2 - mp.exp(-x))/x**3; ex = (1 - mp.exp(-x))/x
        Q = phi1*qp + phi2*A + sum(W[t]/(x + z[t]) + C[t]*(mp.exp(-x)/(x + z[t]) + ex) for t in range(T))
        F.append(1 - rho*Q); S.append((A + x*qp + sum(x**2*z[t]/(x + z[t])*C[t] for t in range(T)))/x**2)
    return F, S


if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(EXTERNAL multiprecision evidence, NOT a Lean proof)', flush=True)
    val = lambda f, d: type(d)(sys.argv[sys.argv.index(f) + 1]) if f in sys.argv else d
    S_, seed = val('--states', 2000), val('--seed', 1); rng = np.random.default_rng(seed); T = 2
    worst = mp.mpf(0); wrong = dict(FD=0, FP=0, SD=0, SP_pos=0); F0min = mp.inf
    for i in range(S_):
        small = i % 2 == 0
        z = [mp.mpf(float(v)) for v in (np.exp(rng.uniform(np.log(.005), np.log(.1), T)) if small else np.exp(rng.uniform(np.log(.005), np.log(1000), T)))]
        e = mp.mpf(float(rng.uniform(.001, .85))); zero = [mp.mpf(0)]*(2*T)
        F0, S0 = fs(z, e, zero); G0 = [S0[t]/(2*mp.pi*F0[t]) for t in range(T)]; F0min = min(F0min, min(F0))
        for t in range(T):
            eD = list(zero); eD[t] = mp.mpf(1); eP = list(zero); eP[T + t] = mp.mpf(1)
            FDr, SDr = fs(z, e, eD); FPr, SPr = fs(z, e, eP)
            for s in range(T):
                fp = FPr[s] - F0[s]; sp = SPr[s] - S0[s]; fd = FDr[s] - F0[s] + fp*G0[t]; sd = SDr[s] - S0[s] + sp*G0[t]
                SD = sd - 2*mp.pi*G0[s]*fd; SP = sp - 2*mp.pi*G0[s]*fp
                cf = z[t]/((z[s] + z[t])*F0[s]*F0[t]); worst = max(worst, abs(SD/cf - 1))
                wrong['FD'] += fd > 0; wrong['FP'] += fp > 0; wrong['SD'] += SD < 0; wrong['SP_pos'] += SP > 0
    print(f'{S_} states, T = {T}: largest |SD/closed form - 1| = {mp.nstr(worst, 5)}; smallest F0 {mp.nstr(F0min, 6)}; entries of the wrong sign, by block: {wrong}', flush=True)
