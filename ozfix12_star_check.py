#!/usr/bin/env python3
"""OZFIX.12 — decisive test of the (star) reduction (scratch, not committed).

CLAIM (star):  Sum'_n [Hterm_n(u) - Hterm_n(sigma)] = pi*(sigma^2 - u^2)   for u in (0, sigma]
  i.e. the exterior residue series, continued into the core, reproduces h = -1.
  Absolutely convergent only for u > sigma/2 (terms ~ ||k||^{-2u/sigma}).

If (star) holds, then for sigma < r < 2 sigma:
  Sum'_n D_n(r) = -2*pi*Phi(r)   [ == the collapse defect identity ]
where D_n(r) = int_{r-sigma}^{sigma} Chat_poly(t) [Hterm_n(r-t) - Hterm_n(sigma)] dt
and  Phi(r)  = -(1/2) int_{r-sigma}^{sigma} Chat_poly(t) (sigma^2-(r-t)^2) dt
             = r*oz_forcing(r)/(2*pi*rho).

Checks:
  A. Hterm is real (mirror pairing)                          [Lean: h_explicit_term real]
  B. (star) at u in (0.55..1.0), convergence in N            [DECISIVE]
  C. (star) below sigma/2 (expect divergence / no abs conv)  [scope boundary]
  D. Sum' D_n(r) vs -2 pi Phi(r) at r=1.5,1.8,1.95           [the actual target]
  E. real-analyticity check: D_n(r) single formula on (sigma,2sigma)
  F. incomplete-moment arc decay (the unchecked item)
"""
import numpy as np
from scipy.integrate import quad

eta, sigma = 0.3, 1.0
rho = 6 * eta / (np.pi * sigma**3)

a0 = (1 + 2 * eta)**2 / (1 - eta)**4
a1 = -6 * eta * (1 + eta / 2)**2 / (1 - eta)**4
a3 = eta * (1 + 2 * eta)**2 / (2 * (1 - eta)**4)

qp = np.pi * sigma * (2 + eta) / (1 - eta)**2
qpp = 2 * np.pi * (1 + 2 * eta) / (1 - eta)**2
P0 = rho * qpp * sigma**2 / 2 - rho * qp * sigma
P1 = rho * qp - rho * qpp * sigma
P2 = rho * qpp / 2


def c_HS(r):
    return -(a0 + a1 * (r / sigma) + a3 * (r / sigma)**3) if r < sigma else 0.0


def Chat_poly(r):
    return -(a0 * r + (a1 / sigma) * r**2 + (a3 / sigma**3) * r**4)


def Chat_F(k):
    c = -1j * k
    E = np.exp(c * sigma)
    t1 = -a0 * ((sigma / c - 1 / c**2) * E + 1 / c**2)
    t2 = -(a1 / sigma) * ((sigma**2 / c - 2 * sigma / c**2 + 2 / c**3) * E - 2 / c**3)
    t3 = -(a3 / sigma**3) * ((sigma**4 / c - 4 * sigma**3 / c**2 + 12 * sigma**2 / c**3
                              - 24 * sigma / c**4 + 24 / c**5) * E - 24 / c**5)
    return t1 + t2 + t3


def Chat_complex(k):
    return (4 * np.pi / k) * ((Chat_F(-k) - Chat_F(k)) / (2j))


def Npoly(k):
    return 1j * k**3 - P0 * k**2 + 1j * P1 * k + 2 * P2


def Dpoly(k):
    return 1j * (P1 + 2 * P2 * sigma) * k + 2 * P2


def G(k):
    return Npoly(k) - Dpoly(k) * np.exp(-1j * k * sigma)


def Gp(k):
    E = np.exp(-1j * k * sigma)
    return (3j * k**2 - 2 * P0 * k + 1j * P1) - ((1j * rho * qp) * E
                                                 + Dpoly(k) * (-1j * sigma) * E)


def A_coef(k):
    return k**7 * Chat_complex(k) / (G(-k) * Gp(k))


def residue_term(x, k):
    return A_coef(k) * np.exp(1j * k * x)


def Hterm(n, x, poles):
    k = poles[n]
    km = -np.conj(k)
    return residue_term(x, k) / (1j * k) + residue_term(x, km) / (1j * km)


def h_term(n, x, poles):
    k = poles[n]
    return residue_term(x, k) + residue_term(x, -np.conj(k))


def cquad(f, lo, hi):
    re = quad(lambda t: f(t).real, lo, hi, limit=400)[0]
    im = quad(lambda t: f(t).imag, lo, hi, limit=400)[0]
    return re + 1j * im


# ---------------------------------------------------------------- poles
NPOLES = 400
poles = []
k = 6.0 + 1.4j
for n in range(NPOLES):
    for _ in range(80):
        dk = G(k) / Gp(k)
        k = k - dk
        if abs(dk) < 1e-13:
            break
    poles.append(k)
    k = k + 2 * np.pi
poles = np.array(poles)
print(f"poles: n=0 {poles[0]:.6f}, n={NPOLES-1} {poles[-1]:.4f}, "
      f"max|G|={max(abs(G(p)) for p in poles):.2e}")

# ---------------------------------------------------------------- A: reality
print("\n=== A. Hterm / h_term reality (mirror pairing) ===")
for n in [0, 5, 30]:
    for x in [0.7, 1.0, 1.5]:
        H = Hterm(n, x, poles)
        print(f"  n={n:2d} x={x}: Hterm={H.real:+.6e} {H.imag:+.3e}i  "
              f"|Im/Re|={abs(H.imag)/max(abs(H.real),1e-300):.2e}")

# ---------------------------------------------------------------- B: (star)
print("\n=== B. (star): Sum'[Hterm(u)-Hterm(sigma)] =?= pi*(sigma^2-u^2)  [DECISIVE] ===")
Hs_sigma = np.array([Hterm(n, sigma, poles) for n in range(NPOLES)])
S_sigma_partial = np.cumsum(Hs_sigma)

for u in [0.99, 0.9, 0.8, 0.7, 0.6, 0.55]:
    Hs_u = np.array([Hterm(n, u, poles) for n in range(NPOLES)])
    S_u_partial = np.cumsum(Hs_u)
    target = np.pi * (sigma**2 - u**2)
    print(f"  u={u}:  target = pi*(s^2-u^2) = {target:.6f}")
    for N in [20, 50, 100, 200, 400]:
        lhs = (S_u_partial[N - 1] - S_sigma_partial[N - 1]).real
        print(f"      N={N:3d}: LHS={lhs:+.6f}  diff={lhs - target:+.3e}  "
              f"term_N={abs(Hs_u[N-1]):.2e}")

# ---------------------------------------------------------------- C: below sigma/2
print("\n=== C. below sigma/2 (expect NO absolute convergence: ||Hterm_n(u)|| ~ n^{-2u/s}) ===")
for u in [0.45, 0.3]:
    Hs_u = np.array([Hterm(n, u, poles) for n in range(NPOLES)])
    e20, e100, e400 = abs(Hs_u[19]), abs(Hs_u[99]), abs(Hs_u[399])
    slope = np.log(e400 / e100) / np.log(400 / 100)
    lhs = (np.cumsum(Hs_u)[399] - S_sigma_partial[399]).real
    print(f"  u={u}: |term| n=20/100/400: {e20:.2e}/{e100:.2e}/{e400:.2e}  "
          f"slope={slope:+.2f} (predict {-2*u/sigma:+.2f})  "
          f"partial(N=400)={lhs:+.4f} vs target {np.pi*(sigma**2-u**2):.4f}")

# ---------------------------------------------------------------- D: the target
print("\n=== D. Sum' D_n(r) =?= -2 pi Phi(r)   [sigma < r < 2 sigma] ===")


def Phi(r):
    return -0.5 * quad(lambda t: Chat_poly(t) * (sigma**2 - (r - t)**2),
                       r - sigma, sigma, limit=400)[0]


def D_n(n, r):
    return cquad(lambda t: Chat_poly(t) * (Hterm(n, r - t, poles) - Hterm(n, sigma, poles)),
                 r - sigma, sigma)


for r in [1.95, 1.8, 1.5, 1.2]:
    tgt = -2 * np.pi * Phi(r)
    Ds = np.array([D_n(n, r) for n in range(150)])
    cs = np.cumsum(Ds)
    region = "u>=s/2 OK" if r - sigma >= sigma / 2 else "u<s/2 (abs-conv fails pointwise)"
    print(f"  r={r} [{region}]: target=-2 pi Phi = {tgt:+.6f}")
    for N in [20, 50, 100, 150]:
        print(f"      N={N:3d}: Sum D_n={cs[N-1].real:+.6f}  diff={cs[N-1].real - tgt:+.3e}"
              f"   |D_N|={abs(Ds[N-1]):.2e}")

# ---------------------------------------------------------------- E: D_n decay rate
print("\n=== E. |D_n(r)| decay (interchange majorant; predict n^{-1-2(r-s)/s}) ===")
for r in [1.95, 1.5, 1.2, 1.05]:
    Ds = np.array([abs(D_n(n, r)) for n in [20, 40, 80]])
    slope = np.log(Ds[2] / Ds[0]) / np.log(80 / 20)
    print(f"  r={r}: |D_n| n=20/40/80: {Ds[0]:.2e}/{Ds[1]:.2e}/{Ds[2]:.2e}  "
          f"slope={slope:+.2f} (predict {-1-2*(r-sigma)/sigma:+.2f})")

print("\nDone.")
