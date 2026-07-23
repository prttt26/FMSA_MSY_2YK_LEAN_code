#!/usr/bin/env python3
"""OZFIX.15 — real-space Baxter/Wertheim-Thiele route: decisive structural check. (scratch)

Conventions taken VERBATIM from the Lean code:
  q0_poly(r) = rho*qp*(r-sigma) + rho*qpp*(r-sigma)^2/2   for r <= sigma, else 0
               (BaxterRealSpace.lean:200, phi1_real/phi2_real)
  Qhat_complex(k) = int_0^sigma q0_poly(r) e^{-ikr} dr    (BaxterZeros.lean:339)
  baxter_wiener_hopf_complex:  (1-Qhat(k))(1-Qhat(-k)) = 1 - rho*Chat_complex(k)   [PROVED]

Real-space reading of that PROVED identity.  With
  psi(v) := v*h(|v|)   (= r*h(r), odd),   phi(v) := v*c_HS(|v|)   (odd, supp [-sigma,sigma])
  Q_+ := delta - q0*1_[0,sigma]   (so F[Q_+](k) = 1 - Qhat(k)),   Q_-(r) := Q_+(-r)
the identity is  F[psi]*F[Q_+]*F[Q_-] = F[phi], i.e. in real space

  (*)   psi (*) Q_+ (*) Q_- = phi

Define u := psi (*) Q_+ , i.e.  u(r) = psi(r) - int_0^sigma q0(t) psi(r-t) dt.

CLAIMS TO TEST (this is what makes the real-space route structurally different from the
Fourier route: the core value h=-1 is DEFINITIONAL in OzFixedPt, so u is EXPLICIT):
  A.  u(r) = 0                      for r > sigma          [the renewal/Volterra equation]
  B.  u(r) = r*(M0-1) - M1          for 0 < r < sigma      [explicit linear polynomial!]
      with M0 = int_0^sigma q0, M1 = int_0^sigma t*q0(t) dt
  C.  (u (*) Q_-)(r) = phi(r) = r*c_HS(r)                  [<=> OZ]
  D.  Is Qhat(k_n) = 1 at the poles?  (the real-space collapse factor -- would replace
      OZFIX.11's rho*Chat(k_n)=1 route, and needs only Qhat_pole_iff_G_baxter_zero)
"""
import numpy as np
from scipy.integrate import quad

exec(open('ozfix12_star_check.py').read().split('# ---------------------------------------------------------------- A: reality')[0])

def h_explicit(r, fam):
    return (1 / (2 * np.pi * r)) * sum(h_term(n, r, fam) for n in range(len(fam))).real

# ---- q0_poly, verbatim from BaxterRealSpace.lean ----
def q0(r):
    if r <= sigma:
        return rho * qp * (r - sigma) + rho * qpp * (r - sigma) ** 2 / 2
    return 0.0

M0 = quad(q0, 0, sigma, limit=200)[0]
M1 = quad(lambda t: t * q0(t), 0, sigma, limit=200)[0]
print(f"rho={rho:.6f}  M0=int q0 = {M0:.6f}   M1=int t*q0 = {M1:.6f}")

# ---- D first (cheapest, and it is the collapse factor) ----
print("\n=== D. Qhat(k_n) = 1 at the poles?  (real-space collapse factor) ===")
def Qhat(k):
    re = quad(lambda t: (q0(t) * np.exp(-1j * k * t)).real, 0, sigma, limit=200)[0]
    im = quad(lambda t: (q0(t) * np.exp(-1j * k * t)).imag, 0, sigma, limit=200)[0]
    return re + 1j * im
for n in [0, 3, 8, 40]:
    k = poles[n]
    print(f"  n={n:2d}: |Qhat(k_n) - 1| = {abs(Qhat(k) - 1):.3e}    "
          f"mirror: {abs(Qhat(-np.conj(k)) - 1):.3e}")

# ---- the true h: -1 inside, residue series outside ----
NP = 300
pl = poles[:NP]
def h(x):
    return -1.0 if x < sigma else h_explicit(x, pl)
def psi(v):
    return v * h(abs(v))

def conv_Qplus(f, r):
    """(f (*) Q_+)(r) = f(r) - int_0^sigma q0(t) f(r-t) dt"""
    g = lambda t: q0(t) * f(r - t)
    # split at the core boundary crossings of r-t to help the quadrature
    pts = sorted({0.0, sigma} | {r - sigma, r + sigma} & set())
    brk = [p for p in (r - sigma, r + sigma, r) if 0.0 < p < sigma]
    lo, out = 0.0, 0.0
    for p in sorted(brk) + [sigma]:
        out += quad(g, lo, p, limit=200)[0]
        lo = p
    return f(r) - out

def u(r):
    return conv_Qplus(psi, r)

print("\n=== A. u(r) = 0 for r > sigma ?  [the renewal / Volterra equation] ===")
for r in [1.05, 1.3, 1.7, 2.0, 2.5, 3.0, 4.0]:
    print(f"  r={r:4.2f}: u(r) = {u(r):+.6e}    (psi(r) = {psi(r):+.6f})")

print("\n=== B. u(r) = r*(M0-1) - M1 for 0 < r < sigma ?  [explicit linear polynomial] ===")
for r in [0.1, 0.3, 0.5, 0.7, 0.9]:
    pred = r * (M0 - 1) - M1
    got = u(r)
    print(f"  r={r:4.2f}: u={got:+.8f}   r(M0-1)-M1={pred:+.8f}   diff={got-pred:+.2e}")

print("\n=== C. (u (*) Q_-)(r) = r*c_HS(r) ?  [<=> OZ]  (u_expl = B/A closed form) ===")
def u_expl(v):
    if v <= 0:      return None          # not needed for 0<r<sigma (r+t>0)
    if v < sigma:   return v * (M0 - 1) - M1
    return 0.0
for r in [0.1, 0.3, 0.5, 0.7, 0.9]:
    # (u (*) Q_-)(r) = u(r) - int_0^sigma q0(t) u(r+t) dt ; u(r+t)=0 once r+t>sigma
    inner = quad(lambda t: q0(t) * u_expl(r + t), 0, max(0.0, sigma - r), limit=200)[0] \
            if r < sigma else 0.0
    lhs = u_expl(r) - inner
    rhs = r * c_HS(r)
    print(f"  r={r:4.2f}: (u*Q_-)(r)={lhs:+.8f}   r*c_HS(r)={rhs:+.8f}   diff={lhs-rhs:+.2e}")

print("\nDone.")
