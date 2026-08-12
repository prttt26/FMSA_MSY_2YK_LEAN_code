#!/usr/bin/env python3
"""Test whether the mixture DCF matrix is negative-semidefinite (NSD) pointwise in the core.

*** CORRECTION (2026-08-09) ***  An earlier version of this script scanned only r in (0, 0.95*R_min)
with R_min = min_ij R_ij = sigma_min, and concluded (wrongly) that the UNEQUAL-diameter DCF is NSD
a.e.  That conclusion was an artifact of the truncated scan range.  Scanning the FULL support range
(0, sigma_max) reveals a band  sigma_min < r < R_01 = (sigma_0+sigma_1)/2  on which the DCF matrix is
INDEFINITE (a robust positive eigenvalue ~ +0.1..+0.26, NOT a finite-difference artifact): there the
like-pair DCF c_00 has already vanished (PY range = sigma_0) while the unlike-pair c_01 is still
nonzero (its range is R_01 > sigma_0), so the matrix is [[0,b],[b,d]] with det = -b^2 < 0.  Hence the
three per-r inequalities (c_00<=0, c_11<=0, det>=0) are FALSE on the band, and the pointwise-DCF-NSD
near-0 sign route (matSymbol_near_bound / hNSD) does NOT extend to unequal diameters.  It is EQUAL-
diameter-specific: equal diameters have R_01 = sigma so the band is empty (matDCF_coreNSD_equalDiam).

We compute the symmetric-normalized real-space DCF matrix M_ij(r) = r*c~_ij(r) (the odd 1D Baxter
combination) via the exact Lebowitz PY Baxter factor, and report eigenvalues over the FULL range,
splitting (0,sigma_min) [NSD] from (sigma_min,R_max_offdiag) [INDEFINITE band].
"""
import numpy as np
trapz = np.trapezoid if hasattr(np, 'trapezoid') else np.trapz


def dcf_matrix_eigs(sig, rho, label):
    N = len(sig)
    sig = np.array(sig, float); rho = np.array(rho, float)
    xi = [(np.pi / 6) * np.sum(rho * sig ** n) for n in range(4)]
    D = 1 - xi[3]
    R = np.array([[(sig[i] + sig[j]) / 2 for j in range(N)] for i in range(N)])
    lam = np.array([[(sig[j] - sig[i]) / 2 for j in range(N)] for i in range(N)])
    a = np.array([(1 - xi[3] + 3 * sig[j] * xi[2]) / D ** 2 for j in range(N)])
    b = np.array([-(3 / 2) * sig[j] ** 2 * xi[2] / D ** 2 for j in range(N)])
    qpp = 2 * np.pi * a
    qp = np.array([[2 * np.pi * (a[j] * R[i, j] + b[j]) for j in range(N)] for i in range(N)])
    sq = np.sqrt(np.outer(rho, rho))

    def Qm(i, j, r):
        r = np.asarray(r, float)
        x = r - R[i, j]
        val = sq[i, j] * (qp[i, j] * x + qpp[j] * x * x / 2)
        return np.where((r >= lam[i, j]) & (r <= R[i, j]), val, 0.0)

    Rmax = R.max()
    conv_s = np.linspace(-Rmax - 0.5, Rmax + 0.5, 40000)

    def combo(i, j, r):
        base = Qm(i, j, np.array([r]))[0] + Qm(j, i, np.array([-r]))[0]
        s = 0.0
        for l in range(N):
            s += trapz(Qm(i, l, conv_s) * Qm(j, l, conv_s - r), conv_s)
        return base - s

    def Mij(i, j, r, dr):    # symmetric-normalized r*c~_ij(r) = -(1/2pi) d/dr combo
        return -(combo(i, j, r + dr) - combo(i, j, r - dr)) / (2 * dr) / (2 * np.pi)

    # DCF kinks: combo has a knot at r = |lam_ij| (where the reflected factor Qm_ji(-r) switches)
    kinks = sorted({abs(lam[i, j]) for i in range(N) for j in range(N)} - {0.0})
    print(f"\n===== {label}: sig={sig} rho={rho}  kinks at r={[f'{k:.3f}' for k in kinks]} =====")
    smin = sig.min()                       # smallest diameter = where the FIRST diagonal DCF vanishes
    Roff = max((R[i, j] for i in range(N) for j in range(N) if i != j), default=smin)  # R_01
    smax = sig.max()

    def maxeig(r):
        dr = 5e-3
        M = np.array([[Mij(i, j, r, dr) for j in range(N)] for i in range(N)])
        M = 0.5 * (M + M.T)
        return np.linalg.eigvalsh(M).max()

    def worst_over(lo, hi, npts=40):
        w = -np.inf
        for r in np.linspace(lo, hi, npts):
            if any(abs(r - k) < 0.03 for k in kinks):    # skip finite-diff kink artifacts
                continue
            w = max(w, maxeig(r))
        return w

    # Region 1: (0, sigma_min) -- all diagonals still active; DCF IS NSD here.
    w_active = worst_over(0.03 * smin, 0.95 * smin)
    print(f"  (0, sigma_min={smin:.3f}):   worst max-eig = {w_active:+.4e}  "
          f"{'==> NSD holds' if w_active <= 1e-3 else '==> NSD FAILS'}")
    # Region 2: (sigma_min, R_01) -- a diagonal DCF has vanished but off-diagonal has not: INDEFINITE.
    if N >= 2 and Roff > smin + 1e-6:
        w_band = worst_over(1.02 * smin, 0.98 * Roff)
        print(f"  (sigma_min, R_off={Roff:.3f}):  worst max-eig = {w_band:+.4e}  "
              f"{'==> NSD holds' if w_band <= 1e-3 else '==> INDEFINITE (positive eigenvalue): NSD FAILS on band'}")
    else:
        w_band = -np.inf
        print(f"  (no band: R_off = sigma_min, equal diameters)")
    return w_active, w_band


w = []
w.append(dcf_matrix_eigs([1.0], [0.4], "N=1 (scalar, c_HS<0)"))
w.append(dcf_matrix_eigs([1.0, 1.0], [0.15, 0.25], "N=2 equal diameters (rank-1, no band)"))
w.append(dcf_matrix_eigs([1.0, 0.9], [0.15, 0.25], "N=2 mild asym (1.0/0.9)"))
w.append(dcf_matrix_eigs([1.0, 0.6], [0.15, 0.25], "N=2 strong asym (1.0/0.6)"))
w.append(dcf_matrix_eigs([1.0, 0.4], [0.2, 0.3], "N=2 very strong asym (1.0/0.4)"))
w.append(dcf_matrix_eigs([1.0, 0.7, 0.4], [0.1, 0.15, 0.2], "N=3 unequal (1.0/0.7/0.4)"))
print(f"""
================================ SUMMARY ================================
 Real-space mixture DCF matrix  M_ij(r) = r*c~_ij(r)  (Lebowitz PY Baxter):
   worst max-eig on (0,sigma_min) ; on the band (sigma_min,R_off):
 {'; '.join(f'{a:+.1e}/{b:+.1e}' for a, b in w)}
 On (0, sigma_min): worst max-eig <= 0  ==>  DCF IS NSD there (all diagonals active).
 On (sigma_min, R_off): a POSITIVE eigenvalue (~+0.1..+0.26) for every UNEQUAL case
   ==>  the DCF matrix is INDEFINITE on the band -- a diagonal DCF has vanished
        (PY range = sigma_i) while the off-diagonal has not (range R_off > sigma_min),
        so the 2x2 block is [[0,b],[b,d]] with det = -b^2 < 0.
 ==> The three per-r inequalities (c00<=0, c11<=0, det>=0) are FALSE on the band, and
     hNSD of matSymbol_near_bound CANNOT hold on the full core for unequal diameters.
     The pointwise-DCF-NSD near-0 route is EQUAL-DIAMETER-SPECIFIC (equal diameters have
     R_off = sigma, empty band; matDCF_coreNSD_equalDiam). For unequal diameters the
     near-0 region must be covered by continuity of the regular 1-rho*C_hat(k) at k=0
     plus stability (det Q0_hat != 0 at the origin), NOT by pointwise DCF-NSD.
 See Lean refutation: FMSA.MixtureOzStar.matSym_2x2_pos_of_zero_diag.
========================================================================""")
