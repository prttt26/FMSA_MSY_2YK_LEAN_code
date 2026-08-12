"""
MIXCHS.4 regularity probe — is `cMixMomentDCF` a polynomial (regular at r->0)?

`cMixMomentDCF Q sigma i j r = (moment_expr)/r` on (0,sigma), where the WINDOWED-seed moment
expression (`matBaxterUQm_coreSeed_moment`, MixtureBaxterSeed.lean) is

    moment_expr = (r*(S0_i - 1) - S1_i)
                  - sum_k  int_0^{sigma-r} Q_ik(t) * ((r+t)(S0_k - 1) - S1_k) dt

with S0_i = sum_k int_0^sigma Q_ik, S1_i = sum_k int_0^sigma t*Q_ik.

For c_ij = cMixMomentDCF to be a polynomial, moment_expr must factor as r*(polynomial), i.e.
lim_{r->0} moment_expr = 0.  In the "all-full" region (all sigma-r >= R_ik, non-empty for the
smaller-species row) the coupling range is r-independent, so moment_expr = r*P_i + Q_i with

    Q_i = -S1_i + sum_k S1_k*M0_ik - sum_k (S0_k - 1)*M1_ik,      M0/M1 = full row moments.

RESULT (this script): Q_i = 0 EXACTLY at equal diameters, but Q_i != 0 at UNEQUAL diameters, for
BOTH the q0MixPolyMat (clamped) kernel and the q0MixEntry ([lam,R]-restricted) kernel.  So the
WINDOWED-seed `cMixMomentDCF` has a genuine 1/r pole at unequal diameters -> it is NOT a polynomial.
The polynomial Lebowitz c_ij must come from the loss-free EXTENDED seed `matBaxterUQmSymFullExt`
(= cHSmixRenewal); `matBaxterUQm` (windowed) carries a windowing loss and does not vanish at r=0.

Physical PY coefficients replicated from HSMixture/MatrixQ0.lean (Q0phys/Qppphys, Lebowitz mixture).
"""
import numpy as np
from scipy.integrate import quad
pi = np.pi


def coeffs(rho, sigma):
    xi2 = sum(rho[i] * sigma[i] ** 2 for i in range(len(rho)))
    eta = pi / 6 * sum(rho[i] * sigma[i] ** 3 for i in range(len(rho)))
    vac = 1 - eta
    N = len(rho)
    R = [[(sigma[i] + sigma[k]) / 2 for k in range(N)] for i in range(N)]
    lam = [[(sigma[k] - sigma[i]) / 2 for k in range(N)] for i in range(N)]
    Q0 = [[(2 * pi / vac) * (R[i][k] + pi * xi2 * sigma[i] * sigma[k] / (4 * vac))
           for k in range(N)] for i in range(N)]
    Qpp = [(2 * pi / vac) * (1 + pi * xi2 * sigma[k] / (2 * vac)) for k in range(N)]
    return R, lam, Q0, Qpp


def poly(t, Q0ik, Qppk, Rik):
    return Q0ik * (t - Rik) + Qppk * (t - Rik) ** 2 / 2


def kernel(name, t, Q0ik, Qppk, Rik, lamik):
    if name == "poly":                       # q0MixPolyMat: clamp at R, no lower cutoff
        m = min(t, Rik)
        return Q0ik * (m - Rik) + Qppk * (m - Rik) ** 2 / 2
    return poly(t, Q0ik, Qppk, Rik) if (lamik <= t <= Rik) else 0.0  # q0MixEntry: [lam,R]


def moment_expr(rho, sigma, i, r, name):
    """Direct numerical evaluation of the windowed-seed moment_expr = matBaxterUQm."""
    R, lam, Q0, Qpp = coeffs(rho, sigma)
    N = len(rho)
    sig = max(sigma)
    K = lambda t, a, b: kernel(name, t, Q0[a][b], Qpp[b], R[a][b], lam[a][b])
    S0 = [sum(quad(lambda t: K(t, a, b), 0, sig)[0] for b in range(N)) for a in range(N)]
    S1 = [sum(quad(lambda t: t * K(t, a, b), 0, sig)[0] for b in range(N)) for a in range(N)]
    lead = r * (S0[i] - 1) - S1[i]
    coup = sum(quad(lambda t: K(t, i, k) * ((r + t) * (S0[k] - 1) - S1[k]), 0, sig - r)[0]
               for k in range(N))
    return lead - coup


if __name__ == "__main__":
    cases = [([0.3, 0.2], [1.0, 1.6]), ([0.4, 0.1], [1.0, 1.3]),
             ([0.2, 0.2], [1.0, 2.0]), ([0.25, 0.25], [1.0, 1.0]),
             ([0.1, 0.35], [1.2, 0.7])]
    print("=== lim_{r->0} matBaxterUQm  (= Q_i;  0 <=> cMixMomentDCF regular/polynomial) ===")
    for rho, sigma in cases:
        tag = "EQUAL" if sigma[0] == sigma[1] else "unequal"
        for name in ("poly", "entry"):
            q = [moment_expr(rho, sigma, i, 1e-6, name) for i in (0, 1)]
            print(f"rho={rho} sigma={sigma} [{name:5s},{tag:7s}]: "
                  f"Q_0={q[0]:+.5e}  Q_1={q[1]:+.5e}")
