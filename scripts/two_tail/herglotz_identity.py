"""Quantitative check of the one-species energy Herglotz identity, and canonicity in the upper half
tau-plane (float64 evidence, NOT a Lean proof).

For a complex coupling tau with a root whose factor has no zero on the imaginary axis,
OZ gives Im h^(k) = |S(k)|^2 Im c^(k), and Parseval with Im h = 0 in the core and
Im c = Im(tau) phi outside gives
    Im(tau) sum_t K_t Im Gt_t = (2 pi)^-3 Int_0^inf k^2 |S(k)|^2 (Im c^(k))^2 dk  >= 0,
    S(k) = 1/(F(ik) F(-ik)),  rho c^(k) = 1 - F(ik) F(-ik),
for ANY tail signs. Reported along rays tau = r e^{i theta}: the relative defect of the identity,
the smallest Im E / Im tau, the number of zeros of F in the right half-plane (winding of
F(ik) over real k; 0 = canonical), and how far the root continues. Also the negative axis.
"""
import sys
import numpy as np
from scipy.integrate import simpson
sys.path.insert(0, '/home/rpan/YK_tail_FMSA/Lean_code/MSA_Convergence/scripts/two_tail')
import herglotz_test as H
P, Mx = H.P, H.Mx

def pieces_c(st, u):
    """Same formulas as the frozen probe's residual_c, one species, complex amplitudes."""
    T = st.T; rho, sig, z = st.rho[0], st.sigma[0], st.z
    D, G = u[:T], u[T:]
    gam = 1 - 2*np.pi*rho*G*np.exp(-z*sig)/z
    Ct = gam*D; Wt = (2*np.pi/z)*G*rho*D
    Mv = -np.sum((1/z)*rho*(Wt + (1+z*sig)*Ct))
    Nc = np.sum(rho*((1/z**2)*Wt + ((1+z*sig+0.5*(z*sig)**2)/z**2)*Ct))
    A = st.A0[0]*(1+Mv) - 4*st.B0[0]*Nc/sig**2
    qp = st.QP0[0, 0]*(1+Mv) + st.A0[0]*Nc
    return dict(A=np.array([A]), qp=np.array([[qp]]), Wt=Wt.reshape(T, 1, 1), Ct=Ct.reshape(T, 1, 1))

def F_line(st, u, k):
    p = pieces_c(st, u)
    return 1 - st.rho[0]*np.array([Mx.qhat(st, p, 1j*kk)[0, 0] for kk in k])

def analyse(st, u, tau):
    kmax = 400.0
    k = np.r_[np.linspace(1e-4, 40, 12001), np.linspace(40, kmax, 12001)[1:]]
    Fp, Fm = F_line(st, u, k), F_line(st, u, -k)
    prod = Fp*Fm
    Imc = -prod.imag/st.rho[0]
    rhs = (2*np.pi)**-3*(simpson(k[:12001]**2*(Imc[:12001]/np.abs(prod[:12001]))**2, x=k[:12001])
                         + simpson(k[12000:]**2*(Imc[12000:]/np.abs(prod[12000:]))**2, x=k[12000:]))
    T = st.T
    E = np.sum(st.K[:, 0, 0]*u[T:])
    lhs = tau.imag*E.imag
    # zeros of F in Re s > 0: F -> 1 at infinity along the imaginary axis
    line = np.r_[Fm[::-1], Fp]
    wind = (np.unwrap(np.angle(line))[-1] - np.unwrap(np.angle(line))[0])/(2*np.pi)
    return lhs, rhs, E.imag/tau.imag, wind

def run(name, st, tf, rs=(0.3, 1.0, 3.0, 8.0), thetas=(1, 5, 30, 90, 150)):
    B = H.Branch(st)
    print(f'{name} (tf={tf:.4f})', flush=True)
    for th in thetas:
        ph = np.exp(1j*np.deg2rad(th)); u = B.u0.copy(); r = 0.0; prev = None; out = []
        for rt in rs:
            rmax = rt*tf; dr = rmax/200; stuck = False
            while r < rmax - 1e-12:
                if dr < tf*1e-8: stuck = True; break
                rn = min(r+dr, rmax); pred = u if prev is None else u + (u-prev[0])*(rn-r)/(r-prev[1])
                un, ok = B.newton(pred, rn*ph)
                if ok and np.linalg.norm(un-u) > 0.2*(1+np.linalg.norm(u)): ok = False
                if not ok: dr /= 2; continue
                prev = (u, r); u, r = un, rn; dr = min(dr*1.3, rmax/50)
            if stuck: out.append(f'r/tf={r/tf:.3f} STOPPED'); break
            lhs, rhs, ratio, wind = analyse(st, u, rn*ph)
            out.append(f'r/tf={rt}: ImE/Imt={ratio:+.3e} defect={abs(lhs-rhs)/abs(rhs):.1e} zeros={wind:+.2f}')
        print(f'   {th}deg: ' + '; '.join(out), flush=True)
    # negative real axis: all tails change sign
    u = B.u0.copy(); r = 0.0; prev = None; rmax = 40*tf; dr = rmax/400
    while r < rmax and dr > tf*1e-8:
        rn = min(r+dr, rmax); pred = u if prev is None else u + (u-prev[0])*(rn-r)/(r-prev[1])
        un, ok = B.newton(pred, -rn+0j)
        if ok and np.linalg.norm(un-u) > 0.2*(1+np.linalg.norm(u)): ok = False
        if not ok: dr /= 2; continue
        prev = (u, r); u, r = un, rn; dr = min(dr*1.3, rmax/100)
    print(f'   negative axis: continued to tau/tf = -{r/tf:.3f}' + (' (full range)' if r >= rmax-1e-9 else ' STOPPED'), flush=True)

if __name__ == '__main__':
    print('cmd:', ' '.join(sys.argv), '(float64 evidence, NOT a Lean proof)')
    eta = lambda e: 6*e/np.pi
    pure = lambda z, K, e: Mx.HCYMix([1.0], [eta(e)], list(z), np.array(K, float).reshape(len(z), 1, 1))
    run('one tail z=1.8 eta=0.3', pure([1.8], [1], 0.3), 1.307)
    run('two attractive z=(1,10) K=(1,1) eta=0.3', pure([1, 10], [1, 1], 0.3), 0.5642)
    run('three attractive z=(.5,2,8) eta=0.3', pure([.5, 2, 8], [1, 1, 1], 0.3), 0.1899)
    run('F5 z=(1.8,12) K=(1,-6) eta=0.3', pure([1.8, 12], [1, -6], 0.3), 2.0)
    run('M3 z=(7,14) K=(1,-419/384) eta=0.49', pure([7, 14], [1, -419/384], 0.49), 84.0, rs=(0.5, 0.95, 1.05, 2.0), thetas=(0.5, 2, 5, 30, 90))
