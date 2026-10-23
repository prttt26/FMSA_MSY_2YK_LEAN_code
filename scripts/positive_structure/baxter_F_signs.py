"""Signs of the tau-coefficients of F(s; tau) = 1 - rho Qhat(s) at real s >= 0 (N = 1),
and of g-Laplace values, from the exact (D, W) series."""
import sys, numpy as np
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent)); sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[1]))
from dw_system import series, Mx

def F_affine(st, s):
    T = st.T; z = st.z; rho = float(st.rho[0]); e = np.exp(-z)
    def F(D, W):
        Ct = D - e*W
        M = -np.sum((rho/z)*(W + (1+z)*Ct)); Nc = np.sum(rho*(W/z**2 + ((1+z+z**2/2)/z**2)*Ct))
        A = st.A0[0]*(1+M) - 4*st.B0[0]*Nc; qp = st.QP0[0, 0]*(1+M) + st.A0[0]*Nc
        p = dict(A=np.array([A]), qp=np.array([[qp]]), Wt=W.reshape(T, 1, 1), Ct=Ct.reshape(T, 1, 1))
        return 1 - rho*Mx.qhat(st, p, s)[0, 0].real
    F0 = F(np.zeros(T), np.zeros(T))
    gD = np.array([F(np.eye(T)[m], np.zeros(T)) - F0 for m in range(T)])
    gW = np.array([F(np.zeros(T), np.eye(T)[m]) - F0 for m in range(T)])
    return F0, gD, gW

def run(name, st, nmax=36):
    tr = Mx.trace_coupling_mix(st, lam_max=8.0); sc = min(tr[-1][0], 2.0)
    D, W, _ = series(st, nmax, sc)
    out = []
    for s in (1e-9, 0.5, 1.0, 1.8, 3.0, 6.0, 12.0, 30.0):
        F0, gD, gW = F_affine(st, s)
        Fc = D@gD + W@gW; Fc = Fc[1:]
        big = np.abs(Fc) > 1e-10*np.max(np.abs(Fc))
        sg = np.sign(Fc[big])
        out.append(f"s={s:g}:{'all-' if np.all(sg < 0) else ('all+' if np.all(sg > 0) else 'mixed('+''.join('+' if x > 0 else '-' for x in np.sign(Fc[:10]))+')')}")
    print(f"{name} (scale {sc:.3f}): " + "  ".join(out), flush=True)

if __name__ == "__main__":
    eta = lambda e: 6*e/np.pi
    for name, st in (("1 tail z=1.8 eta=0.2", Mx.HCYMix([1.0], [eta(0.2)], [1.8], [[[1.0]]])),
                     ("1 tail z=1.8 eta=0.4", Mx.HCYMix([1.0], [eta(0.4)], [1.8], [[[1.0]]])),
                     ("2 attr z=(1.8,4) eta=0.3", Mx.HCYMix([1.0], [eta(0.3)], [1.8, 4.0], np.array([1.0, .5]).reshape(2, 1, 1))),
                     ("2 attr z=(1.8,.8) eta=0.3", Mx.HCYMix([1.0], [eta(0.3)], [1.8, 0.8], np.array([1.0, .3]).reshape(2, 1, 1))),
                     ("2YK eta=0.25", Mx.HCYMix([1.0], [eta(0.25)], [2.9637, 14.0167], np.array([2.1714, -2.1714]).reshape(2, 1, 1))),
                     ("F5 eta=0.3", Mx.HCYMix([1.0], [eta(0.3)], [1.8, 12.0], np.array([1.0, -6.0]).reshape(2, 1, 1)))):
        run(name, st)
