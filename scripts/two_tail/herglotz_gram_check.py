"""Two checks of the Herglotz structure, one species (float64 evidence, NOT a Lean proof).

1. Convergence of the identity Im(tau) sum_t K_t Im Gt_t = (2 pi)^-3 Int_0^kmax k^2 |S|^2 (Im c^)^2 dk
   in kmax. The integrand decays like k^-2 up to oscillation, so the defect should scale like 1/kmax.
2. At real canonical couplings, with independent tail couplings tau_t = tau K_t:
   M_st = d Gt_s / d tau_t should be symmetric positive definite (Gram matrix of the tails under the
   exterior compression of |1 - rho c^|^2). Entrywise positivity of M is reported separately: it
   is not implied by the Gram form, and it is what would give component-wise signs for K >= 0.
3. The closed form at tau = 0: M_st = 1/[(z_s + z_t) F(z_s)^2 F(z_t)^2], from Wiener-Hopf on the half-line with factor
   F^2 (the Hankel reflection vanishes because c has core support). This makes order 1 explicit and positive at tau = 0.
"""
import sys
import numpy as np
from scipy.integrate import simpson
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_Convergence/scripts/two_tail')
import herglotz_test as H
import herglotz_identity as I
Mx = H.Mx

def identity_defect(st, u, tau, kmax, dk=0.005):
    k = np.arange(1e-4, kmax, dk)
    Fp, Fm = I.F_line(st, u, k), I.F_line(st, u, -k)
    prod = Fp*Fm; Imc = -prod.imag/st.rho[0]
    rhs = (2*np.pi)**-3*simpson(k**2*(Imc/np.abs(prod))**2, x=k)
    T = st.T; lhs = tau.imag*np.sum(st.K[:, 0, 0]*u[T:]).imag
    return abs(lhs-rhs)/abs(lhs)

def gram(st, tau_list):
    B = H.Branch(st); T = st.T; u = B.u0.copy(); t0 = 0.0; out = []
    for t in tau_list:
        u, ok = B.newton(u, t+0j)
        J = B.J(u)
        M = np.empty((T, T))
        for m in range(T):
            bm = np.zeros(2*T, complex); bm[m] = 2*np.pi/st.z[m]      # d residual / d tau_m
            du = np.linalg.solve(J, bm).real
            M[:, m] = du[T:]
        out.append((t, M))
    return out

def closed_form_ratio(st):
    """Entries of M / C at tau = 0 with C = 1/[(z_s+z_t) F_s^2 F_t^2]; the closed form says all equal 1."""
    B = H.Branch(st); T = st.T; M = gram(st, [0.0])[0][1]
    Fz = I.F_line(st, B.u0, -1j*np.array(st.z)).real
    C = 1.0/((st.z[:, None] + st.z[None, :])*Fz[:, None]**2*Fz[None, :]**2)
    return M/C


if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(float64 evidence, NOT a Lean proof)')
    eta = lambda e: 6*e/np.pi
    pure = lambda z, K, e: Mx.HCYMix([1.0], [eta(e)], list(z), np.array(K, float).reshape(len(z), 1, 1))
    st = pure([1, 10], [1, 1], 0.3); B = H.Branch(st); tau = 0.5642*np.exp(1j*np.deg2rad(90))
    u = B.u0.copy()
    for s in np.linspace(0.02, 1, 50): u, ok = B.newton(u, s*tau)
    print('identity defect vs kmax, z=(1,10) eta=0.3 tau=0.5642i:', ' '.join(f'{km}: {identity_defect(st, u, tau, km):.2e}' for km in (100, 200, 400, 800)), flush=True)
    for name, st in [('z=(1,10) eta=.3', pure([1, 10], [1, 1], .3)), ('z=(.3,3) eta=.49', pure([.3, 3], [1, 1], .49)),
                     ('z=(.5,2,8) eta=.3', pure([.5, 2, 8], [1, 1, 1], .3)), ('z=(7,14) eta=.49', pure([7, 14], [1, 1], .49))]:
        r = closed_form_ratio(st)
        print(f'closed form at tau=0, {name}: M/C min {r.min():.12f} max {r.max():.12f}', flush=True)
    for name, st, tfrac in [('z=(1,10) K=(1,1) eta=0.3', pure([1, 10], [1, 1], 0.3), 0.5642),
                            ('z=(.3,3) K=(1,1) eta=0.49', pure([.3, 3], [1, 1], 0.49), 0.3105),
                            ('z=(.5,2,8) K=(1,1,1) eta=0.3', pure([.5, 2, 8], [1, 1, 1], 0.3), 0.1899),
                            ('F5 z=(1.8,12) K=(1,-6) eta=0.3', pure([1.8, 12], [1, -6], 0.3), 2.0),
                            ('M3 z=(7,14) K=(1,-419/384) eta=0.49', pure([7, 14], [1, -419/384], 0.49), 80.0)]:
        for t, M in gram(st, np.linspace(0, 0.8, 5)*tfrac):
            ev = np.linalg.eigvalsh((M+M.T)/2)
            print(f'{name} tau={t:.4f}: asym {np.max(np.abs(M-M.T))/np.max(np.abs(M)):.1e}; min eig {ev.min():+.3e}; min entry {M.min():+.3e}', flush=True)
