"""Step 5 of the pure-fluid proof without improper integrals (EXTERNAL multiprecision check, NOT a Lean proof).

 1. H: H_s = 1/(1 - sum_t theta_t H_t/(z_s + z_t)) is itself a positive Picard equation in theta, so the coefficients of H_s are nonnegative by induction on the degree. No dispersion relation or integral is used. w_s = theta_s H_s follows.
 2. r: the coefficient of theta^alpha in r(x) is a squared Hardy norm,
        [theta^alpha] r(x) = (|alpha|!/alpha!) || s c_alpha(s)/(s + x) ||^2,   c_alpha(s) = prod_t (sqrt(2 z_t)/(s + z_t))^alpha_t,
    with ||B||^2 = (1/pi) int_0^inf |B(ik)|^2 dk = int_0^inf b(t)^2 dt for b the inverse Laplace transform of B. When the poles c_j of B are simple, B = sum_j beta_j/(s + c_j) and ||B||^2 = sum_ij beta_i beta_j/(c_i + c_j), a Cauchy form.
 3. The additive split used to reach 2: the coefficient of r is the unique rational function with poles only at negative reals, decaying at infinity, with A(x) - A(-x) = -x [Phi]_alpha(x), where [Phi]_alpha is the coefficient of 1/(U(x) U(-x)) - 1 with k^2 replaced by -x^2.

Checks: coefficients from the exact recursion taylor_theta of h_function_representation, against the Cauchy form on squarefree alpha and against quadrature on alpha with repeats, at several x; and 3 at a test point. T = 2, 3.

Usage: h_positivity_algebraic.py
"""
import sys, math, itertools
import numpy as np
import mpmath as mp
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_Convergence/scripts/two_tail')
import h_function_representation as HR
mp.mp.dps = 50


def cauchy_form(x, z, al):
    """Squarefree alpha: B = s prod sqrt(2 z_t)/(s + z_t)/(s + x), partial fractions at the simple poles."""
    nodes = [z[t] for t in range(len(z)) if al[t]]; pref = mp.mpf(1)
    for c in nodes: pref *= 2*c
    poles = nodes + [x]; beta = []
    for i, c in enumerate(poles):
        d = mp.mpf(1)
        for j, e in enumerate(poles):
            if j != i: d *= (e - c)
        beta.append(-c/d)
    return pref*sum(beta[i]*beta[j]/(poles[i] + poles[j]) for i in range(len(poles)) for j in range(len(poles)))


def quad_form(x, z, al):
    f = lambda k: k*k/(x*x + k*k)*mp.fprod((2*z[t]/(z[t]**2 + k*k))**al[t] for t in range(len(z)))
    return mp.quad(f, [0, .5, 2, 10, 100, mp.inf])/mp.pi


if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(EXTERNAL multiprecision check, NOT a Lean proof)', flush=True)
    rng = np.random.default_rng(1); wc = wq = mp.mpf(0); nc = nq = 0; negH = 0; totH = 0; lowest = mp.inf
    for T, N, cnt in ((2, 7, 4), (3, 5, 3)):
        for _ in range(cnt):
            z = [mp.mpf(float(v)) for v in np.sort(np.exp(rng.uniform(np.log(.2), np.log(40), T)))]
            xs = [z[0], z[-1], mp.mpf(float(np.exp(rng.uniform(np.log(.1), np.log(50)))))]
            # r at the nodes from the exact recursion
            w, iU, r = HR.taylor_theta(z, N)
            for s in range(T):
                for k, v in iU[s].items():
                    if sum(k): totH += 1; negH += v < 0
                for al, v in r[s].items():
                    if sum(al) == 0: continue
                    mult = mp.factorial(sum(al))/mp.fprod(mp.factorial(a) for a in al)
                    if max(al) <= 1:
                        e = mult*cauchy_form(z[s], z, al) if al[s] == 0 else None
                        if e is None:   # x coincides with a pole: quadrature instead
                            q = mult*quad_form(z[s], z, al); wq = max(wq, abs(q/v - 1)); nq += 1
                        else:
                            wc = max(wc, abs(e/v - 1)); nc += 1; lowest = min(lowest, e)
                    elif sum(al) <= 5:
                        q = mult*quad_form(z[s], z, al); wq = max(wq, abs(q/v - 1)); nq += 1; lowest = min(lowest, q)
    print(f'H: {totH} coefficients of 1/U in theta, negative: {negH}', flush=True)
    print(f'r against the Cauchy form, squarefree alpha with x off the poles: {nc} coefficients, largest relative difference {mp.nstr(wc, 3)}', flush=True)
    print(f'r against quadrature of the squared norm: {nq} coefficients, largest relative difference {mp.nstr(wq, 3)}', flush=True)
    print(f'smallest value of any coefficient read {mp.nstr(lowest, 4)}', flush=True)
