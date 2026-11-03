"""Is the BH branch a Pick (Herglotz) function of the coupling? (float64 evidence, NOT a Lean proof)

If each component S_k u_k(tau), with S = sign u_1, extends analytically to the upper half tau-plane
with S_k Im u_k > 0 there, the branch has a Stieltjes-type representation: no complex singularity,
and one sign at every order. The script continues the root from tau = 0 along rays
tau = r e^{i theta}, theta in (0, pi), to r = RMAX * tau_end, with Newton corrections (the residual is cubic). It reports
the first failure of the continuation and the smallest normalised S_k Im u_k / Im tau on each state.
Controls: one tail (closed form); a competing-sign tail, which must fail. Both the competing-sign F5 and M3 pass
this ray test, so it has NO discrimination: a ray simply passes a complex branch point. uhp_monodromy_test is the
test with discrimination, and it refutes the Pick picture for some all-attractive states.
"""
import sys
import numpy as np
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_and_1st_Truncation/scripts')
import msa_coupling_series_sign_probe as P
import msa_exact_mix as Mx
RMAX = 12.0
THETAS = [5, 15, 30, 60, 90, 120, 150, 175]

class Branch:
    def __init__(self, st):
        self.st = st; T, N = st.T, st.N; n2 = N*N; self.n = n = 2*T*n2
        _, G0 = Mx.seed_zero_K(Mx.HCYMix(st.sigma, st.rho, st.z, 0*st.K))
        self.u0 = np.concatenate([np.zeros(T*n2), G0.ravel()]).astype(complex)
        self.b = np.concatenate([(2*np.pi*st.K/st.z[:, None, None]).ravel(), np.zeros(T*n2)]).astype(complex)
    def R(self, u): return P.residual_c(u, self.st)[0]
    def J(self, u):
        n = self.n; Jm = np.empty((n, n), complex)
        for j in range(n):
            e = np.zeros(n, complex); e[j] = 1.0
            c1 = (self.R(u+1e-3*e) - self.R(u-1e-3*e))/2e-3; c2 = (self.R(u+2e-3*e) - self.R(u-2e-3*e))/4e-3
            Jm[:, j] = (4*c1 - c2)/3                 # exact for a cubic
        return Jm
    def newton(self, u, tau):
        for _ in range(12):
            r = self.R(u) - tau*self.b
            if np.linalg.norm(r) < 1e-11*(1+np.linalg.norm(u)): return u, True
            u = u - np.linalg.solve(self.J(u), r)
            if not np.all(np.isfinite(u)): return u, False
        return u, np.linalg.norm(self.R(u) - tau*self.b) < 1e-9*(1+np.linalg.norm(u))
    def ray(self, theta, rmax, S):
        ph = np.exp(1j*np.deg2rad(theta)); u = self.u0.copy(); r = 0.0; dr = rmax/400; prev = None; mn = np.inf
        while r < rmax and dr > rmax*1e-7:
            rn = min(r+dr, rmax); pred = u if prev is None else u + (u-prev[0])*(rn-r)/(r-prev[1])
            un, ok = self.newton(pred, rn*ph)
            if ok and np.linalg.norm(un-u) > 0.2*(1+np.linalg.norm(u)): ok = False
            if not ok: dr /= 2; continue
            prev = (u, r); u, r = un, rn
            imt = rn*np.sin(np.deg2rad(theta))
            vals = S*(u.imag)/imt
            live = np.abs(S) > 0
            mn = min(mn, float(np.min(vals[live]/np.maximum(np.abs(u[live]-self.u0[live])/rn, 1e-300))))
            dr = min(dr*1.3, rmax/100)
        return r, mn

def run(name, st, tf=None):
    B = Branch(st)
    if tf is None: tf = Mx.trace_coupling_mix(st, lam_max=8.0)[-1][0]
    J0 = B.J(B.u0); u1 = np.linalg.solve(J0, B.b).real; S = np.sign(np.where(np.abs(u1) > 1e-12*np.max(np.abs(u1)), u1, 0))
    res = []
    for th in THETAS:
        r, mn = B.ray(th, RMAX*tf, S)
        res.append(f'{th}deg: r/tf={r/tf:.2f} min={mn:+.3f}')
    print(f'{name} (tf={tf:.4f}): ' + '; '.join(res), flush=True)

if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(float64 evidence, NOT a Lean proof); min = smallest S_k Im u_k/Im tau divided by |u_k-u_k0|/r')
    eta = lambda e: 6*e/np.pi
    pure = lambda z, K, e: Mx.HCYMix([1.0], [eta(e)], list(z), np.array(K, float).reshape(len(z), 1, 1))
    run('CONTROL one tail z=1.8 eta=0.3', pure([1.8], [1], 0.3))
    run('two attractive z=(1,10) K=(1,1) eta=0.3', pure([1, 10], [1, 1], 0.3))
    run('two attractive z=(0.3,3) K=(1,1) eta=0.49', pure([0.3, 3], [1, 1], 0.49))
    run('two attractive z=(1,1.05) K=(1,20) eta=0.05', pure([1, 1.05], [1, 20], 0.05))
    run('three attractive z=(.5,2,8) eta=0.3', pure([.5, 2, 8], [1, 1, 1], 0.3))
    run('CONTROL competing F5 z=(1.8,12) K=(1,-6) eta=0.3', pure([1.8, 12], [1, -6], 0.3), tf=2.0)
