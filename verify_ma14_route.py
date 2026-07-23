"""Numerical witness for the MA.14 (`baxter_no_open_lhp_pole_core`) route triage, 2026-07-21.

MA.14 claims `G_baxter = Npoly - Dpoly*exp(-i k sigma)` has no zero on the open lower half-plane
core `{Im k < 0, k != 0, |Npoly| <= |Dpoly|}`.  This script (a) confirms the statement, (b) refutes
the two tempting elementary routes, and (c) verifies the four inputs of the surviving homotopy route.
MA.14 was RETIRED to a theorem 2026-07-21 (Lean: BaxterLowerHalfPlane.lean); this script
is the numerical witness. See `proof_notes_pole.md` -> "POLE.11-general / MA.14".
"""
import numpy as np

def coeffs(eta, sigma=1.0):
    rho = 6 * eta / (np.pi * sigma ** 3)
    qp  = np.pi * sigma * (2 + eta) / (1 - eta) ** 2      # q_prime_py
    qpp = 2 * np.pi * (1 + 2 * eta) / (1 - eta) ** 2      # q_doubleprime_py
    return (rho, sigma,
            rho * qpp * sigma ** 2 / 2 - rho * qp * sigma,  # baxterP0
            rho * qp - rho * qpp * sigma,                   # baxterP1
            rho * qpp / 2)                                  # baxterP2

Nf = lambda k, P0, P1, P2:    1j * k ** 3 - P0 * k ** 2 + 1j * P1 * k + 2 * P2
Df = lambda k, P0, P1, P2, s: 1j * (P1 + 2 * P2 * s) * k + 2 * P2
Gf = lambda k, P0, P1, P2, s: Nf(k, P0, P1, P2) - Df(k, P0, P1, P2, s) * np.exp(-1j * k * s)

def wind(f, x0, x1, y0, y1, M=400000):
    """Zero count inside a CCW rectangle, by unwrapped argument."""
    segs = [(x0+1j*y0, x1+1j*y0), (x1+1j*y0, x1+1j*y1),
            (x1+1j*y1, x0+1j*y1), (x0+1j*y1, x0+1j*y0)]
    return sum(np.sum(np.diff(np.unwrap(np.angle(f(a + (b-a)*np.linspace(0,1,M))))))
               for a, b in segs) / (2*np.pi)

ETAS = [0.05, 0.2, 0.5, 0.8, 0.95]

print("[0] contour-orientation calibration (CCW box must give +1 / 0)")
print("    root inside:", wind(lambda z: z-(0.3-0.5j), -3,3,-3,-1e-9),
      " root outside:", wind(lambda z: z-(0.3+5j), -3,3,-3,-1e-9))

print("\n[1] STATEMENT: open-LHP zero count of G/k^3  (must be 0; the raw count is garbage")
print("    because G has a TRIPLE zero at k=0 sitting on the contour)")
for eta in ETAS:
    _, s, P0, P1, P2 = coeffs(eta)
    f = lambda z: Gf(z, P0, P1, P2, s) / z**3
    r = [f"R={R:g},eps={e:g}:{wind(f,-R,R,-R,-e):+.3f}" for R in (15.,40.,100.) for e in (1e-3,1e-6)]
    print(f"    eta={eta:<5} " + "  ".join(r))

print("\n[2] REFUTES route A: Npoly has exactly ONE open-LHP root (purely imaginary)")
for eta in ETAS:
    _, s, P0, P1, P2 = coeffs(eta)
    rts = np.roots([1j, -P0, 1j*P1, 2*P2])
    lhp = [r for r in rts if r.imag < 0]
    print(f"    eta={eta:<5} #LHP={len(lhp)}  root={lhp[0]:.4f}  (Re ~ 0 => on the imaginary axis)")

print("\n[3] REFUTES route B: |N| > |D|exp(sigma Im k) FAILS (at exactly that root, where |N|=0)")
for eta in ETAS:
    _, s, P0, P1, P2 = coeffs(eta)
    worst = (1e18, None)
    for sc in (0.05, 0.5, 3.0, 20.0):
        x = np.linspace(-sc, sc, 601); y = np.linspace(-sc, -sc*1e-5, 601)
        X, Y = np.meshgrid(x, y); K = X + 1j*Y
        V = (np.abs(Nf(K,P0,P1,P2)) - np.abs(Df(K,P0,P1,P2,s))*np.exp(s*Y)) / np.abs(K)
        i = np.unravel_index(np.argmin(V), V.shape)
        if V[i] < worst[0]: worst = (V[i], K[i])
    print(f"    eta={eta:<5} min (|N|-|D|e^(s Im k))/|k| = {worst[0]:+.4f} at k={worst[1]:.4f}")

print("\n[4] route C input 3: exact triple zero at 0 with  c3 = i(1+2eta)/(1-eta)^2  (sigma-free)")
for eta in (0.01, 0.2, 0.6, 0.95):
    for s in (0.7, 1.0, 2.3):
        _, _, P0, P1, P2 = coeffs(eta, s); e = 1e-5
        got, pred = Gf(e,P0,P1,P2,s)/e**3, 1j*(1+2*eta)/(1-eta)**2
        print(f"    eta={eta:<5} sigma={s}: Im(G/e^3)={got.imag:12.6f}  pred={pred.imag:12.6f}"
              f"  relerr={abs(got.imag-pred.imag)/abs(pred.imag):.1e}")

print("\n[5] route C input 4: escape radius R with |N|>|D| for all |k|>=R, Im k<=0")
for eta in ETAS + [0.99]:
    _, s, P0, P1, P2 = coeffs(eta); th = np.linspace(np.pi, 2*np.pi, 2001); R = 0.1
    while R < 1e5:
        k = R*np.exp(1j*th)
        if np.all(np.abs(Nf(k,P0,P1,P2)) > np.abs(Df(k,P0,P1,P2,s))): break
        R *= 1.05
    print(f"    eta={eta:<5} R_escape={R:.3f}")

print("\n[6] route C: zero count constant along the eta-homotopy (base case eta* = "
      f"{(3-np.sqrt(7))/2:.6f} is PROVEN in-repo)")
for eta in np.linspace(0.02, 0.97, 8):
    _, s, P0, P1, P2 = coeffs(eta)
    print(f"    eta={eta:.3f}: count={wind(lambda z: Gf(z,P0,P1,P2,s)/z**3, -60,60,-60,-1e-6):+.3f}")
