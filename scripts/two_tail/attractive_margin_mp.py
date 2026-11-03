"""Sign changes reported by attractive_sign_margin, decided in multiprecision
(EXTERNAL multiprecision arithmetic, NOT a Lean proof).

The float tensors lose accuracy at small rates: at z near 0.05 the float c_40 can differ from the mp one in
sign. So a negative f from the float search is only a candidate. Uses attractive_pair_series_mp.coefficients,
any number of tails, and reads every component at every order at two precisions.

Usage: attractive_margin_mp.py N dps,dps 'z-json' 'K-json' eta
"""
import sys, json
import mpmath as mp
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_Convergence/scripts/two_tail')
import attractive_pair_series_mp as PS

if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(EXTERNAL multiprecision arithmetic, NOT a Lean proof)', flush=True)
    N, dps = int(sys.argv[1]), [int(d) for d in sys.argv[2].split(',')]
    z, K, eta = json.loads(sys.argv[3]), json.loads(sys.argv[4]), sys.argv[5]
    res = {}
    for d in dps:
        mp.mp.dps = d
        st = PS.pure_state([mp.mpf(repr(v)) for v in z], [mp.mpf(repr(v)) for v in K], mp.mpf(eta))
        u0, c, defect = PS.coefficients(st, N); res[d] = c; n = len(u0)
        print(f'== mp.dps={d}: cubic reproduction defect {mp.nstr(defect, 3)}', flush=True)
        for k in range(n):
            flips = [m for m in range(2, N + 1) if (c[m][k] > 0) != (c[m - 1][k] > 0)]
            est = abs(c[N - 1][k]/c[N][k])/(1 + mp.mpf(3)/(2*N))
            print(f'  comp {k}: c1 {mp.nstr(c[1][k], 8)}, c_N sign {"+" if c[N][k] > 0 else "-"}, sign changes {len(flips)} at {flips[:20]}, radius estimate at N {mp.nstr(est, 10)}', flush=True)
    if len(dps) > 1:
        a, b = res[dps[0]], res[dps[-1]]; mp.mp.dps = dps[0]
        print(f'largest relative difference between the two precisions: {mp.nstr(max(abs(a[m][i] - b[m][i])/abs(b[m][i]) for m in range(1, N + 1) for i in range(len(a[1]))), 3)}', flush=True)
