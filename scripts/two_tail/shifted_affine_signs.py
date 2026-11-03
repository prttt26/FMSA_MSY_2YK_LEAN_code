"""Signs of the affine factors after removing the hard-sphere value of G (float64 evidence, NOT a Lean proof).

With Gt = G - G0, Pt = D Gt, G0_s = S0_s/(2 pi F0_s), the system is D_t = tau_t/F_t, Gt_t = St_t/(2 pi F_t), Pt_t = D_t Gt_t, where
    F_s = F0_s + sum_t (FD_st D_t + FP_st Pt_t),    St_s = S_s - 2 pi G0_s F_s = sum_t (SD_st D_t + SP_st Pt_t), St has no constant term.
If FD, FP <= 0 and SD, SP >= 0 elementwise, with F0 > 0, then the Picard iteration has nonnegative Taylor coefficients in (tau_1, ..., tau_T), and all-order
positivity of D, Gt follows. affine_factor_signs tested the unshifted P = G D, which has mixed signs. Reports the worst entry of each block, normalised.

Usage: shifted_affine_signs.py --states S [--T T] [--seed S]
"""
import sys
import numpy as np
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_Convergence/scripts/two_tail')
import attractive_tie_limit as L


def blocks(z, eta):
    f = L.Affine(z, eta); T = f.T
    G0 = f.S0/(2*np.pi*f.F0)
    FD = f.FV[:, :T] + f.FV[:, T:]*G0; FP = f.FV[:, T:]
    SD_raw = f.SV[:, :T] + f.SV[:, T:]*G0; SP_raw = f.SV[:, T:]
    SD = SD_raw - 2*np.pi*G0[:, None]*FD; SP = SP_raw - 2*np.pi*G0[:, None]*FP
    return f.F0, G0, FD, FP, SD, SP


if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(float64 evidence, NOT a Lean proof)', flush=True)
    val = lambda f, d: type(d)(sys.argv[sys.argv.index(f) + 1]) if f in sys.argv else d
    S, T, seed = val('--states', 20000), val('--T', 2), val('--seed', 1); rng = np.random.default_rng(seed)
    bad = dict(FD=0, FP=0, SD=0, SP=0, F0=0, G0=0); worst = {k: (0.0, None) for k in bad}
    for _ in range(S):
        z = np.exp(rng.uniform(np.log(.01), np.log(1000), T)); e = rng.uniform(.001, .85)
        F0, G0, FD, FP, SD, SP = blocks(z, e)
        for name, M, sg in (('FD', FD, -1), ('FP', FP, -1), ('SD', SD, 1), ('SP', SP, 1)):
            v = sg*M
            if np.min(v) < 0:
                bad[name] += 1; r = np.min(v)/np.max(np.abs(M))
                if r < worst[name][0]: worst[name] = (float(r), (z.tolist(), float(e), np.round(M, 5).tolist()))
        if np.min(F0) <= 0: bad['F0'] += 1
        if np.min(G0) <= 0: bad['G0'] += 1
    print(f'{S} states, T={T}: states with a wrong-signed entry {bad}', flush=True)
    for k, v in worst.items(): print(k, v, flush=True)
    for z, e in ([1.8, 5.0], .3), ([.5, 20.], .5), ([3., 3.5], .1):
        F0, G0, FD, FP, SD, SP = blocks(np.array(z), e)
        print(f'z={z} eta={e}: F0 {np.round(F0, 4).tolist()} G0 {np.round(G0, 4).tolist()}\n  FD {np.round(FD, 4).tolist()}\n  FP {np.round(FP, 4).tolist()}\n  SD {np.round(SD, 4).tolist()}\n  SP {np.round(SP, 4).tolist()}', flush=True)
