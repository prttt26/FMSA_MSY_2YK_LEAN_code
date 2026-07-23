#!/usr/bin/env python3
"""OZFIX.10 re-examination: is the arc-vanishing really blocked?  (scratch)

The recorded blocker: "sup_arc ||k*Hhat(k)|| grows ~ 1.745*R, so Jordan's crude sup-bound
gives a growing estimate; the real O(1/R) decay is oscillatory cancellation needing
Van der Corput."

CLAIM UNDER TEST: that is a bookkeeping error, not a real obstruction.  Jordan's lemma is
applied to  F(z) = g(z)*e^{i a z}  and needs  M(R) := sup_arc||g|| -> 0, NOT sup||k Hhat||.
Splitting the phase  r = b + a  with  sigma < b < r,  a = r-b > 0:
      k*Hhat(k)*e^{ikr} = [ z*Hhat(z)*e^{izb} ] * e^{iaz}
and the bracket's sup SHOULD tend to 0, because the "1.745*R plateau" lives exactly where
e^{izb} is exponentially small.  Two regimes:
  - near the real axis (|Im z| <~ delta ln R, delta<1/sigma): |Chat| ~ e^{Im z*sigma}/|z|^2 -> 0,
    so ||Hhat|| ~ |z|^{delta*sigma-2}, hence ||z Hhat e^{izb}|| ~ C/R.
  - interior: ||Hhat|| <= 1/rho but |e^{izb}| = e^{-R sin(theta) b} kills it: <= (1/rho) R^{1-b/sigma}.
So predict  M(R) ~ max(C/R, (1/rho) R^{1-b/sigma}) -> 0  iff  b > sigma  (needs r > sigma).

Checks:
  A. sup_arc ||z*Hhat(z)||          -> reproduce the recorded ~1.745*R growth (sanity)
  B. sup_arc ||z*Hhat(z)*e^{izb}||  -> should DECAY for b > sigma  [DECISIVE]
  C. Jordan bound pi*M(R)/a vs the true |arc| at r=1.5
  D. b < sigma  -> should NOT decay (boundary of the method, matches r>sigma requirement)
  E. sup_arc ||Hhat(z)*e^{izb}||  (no k factor) -> should decay for ANY b>0
"""
import numpy as np

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


def G(k):
    return (1j * k**3 - P0 * k**2 + 1j * P1 * k + 2 * P2) - \
           (1j * (P1 + 2 * P2 * sigma) * k + 2 * P2) * np.exp(-1j * k * sigma)


def Gp(k):
    E = np.exp(-1j * k * sigma)
    return (3j * k**2 - 2 * P0 * k + 1j * P1) - \
           ((1j * rho * qp) * E + (1j * (P1 + 2 * P2 * sigma) * k + 2 * P2) * (-1j * sigma) * E)


def Hhat_stable(k):
    """Hhat = Chat/(1-rho Chat), overflow-safe for Im k >= 0 (factor out e^{-ik sigma})."""
    c = -1j * k
    W = (-a0 * (sigma / c - 1 / c**2)
         - (a1 / sigma) * (sigma**2 / c - 2 * sigma / c**2 + 2 / c**3)
         - (a3 / sigma**3) * (sigma**4 / c - 4 * sigma**3 / c**2 + 12 * sigma**2 / c**3
                              - 24 * sigma / c**4 + 24 / c**5))
    V = (-a0 / c**2 + (a1 / sigma) * 2 / c**3 + (a3 / sigma**3) * 24 / c**5)
    cm = -c
    Wm = (-a0 * (sigma / cm - 1 / cm**2)
          - (a1 / sigma) * (sigma**2 / cm - 2 * sigma / cm**2 + 2 / cm**3)
          - (a3 / sigma**3) * (sigma**4 / cm - 4 * sigma**3 / cm**2 + 12 * sigma**2 / cm**3
                               - 24 * sigma / cm**4 + 24 / cm**5))
    Vm = (-a0 / cm**2 + (a1 / sigma) * 2 / cm**3 + (a3 / sigma**3) * 24 / cm**5)
    ep = np.exp(1j * k * sigma)
    T = -W + ((Vm - V) + Wm * ep) * ep
    return 2 * np.pi * T / (1j * k * ep - 2 * np.pi * rho * T)


# pole-avoiding radii
poles = []
k = 6.0 + 1.4j
for n in range(200):
    for _ in range(80):
        dk = G(k) / Gp(k)
        k = k - dk
        if abs(dk) < 1e-13:
            break
    poles.append(k)
    k = k + 2 * np.pi
poles = np.array(poles)


def Rmid(N):
    return 0.5 * (abs(poles[N]) + abs(poles[N + 1]))


TH = np.linspace(0.0, np.pi, 3001)


def sup_arc(f, R):
    z = R * np.exp(1j * TH)
    return np.max(np.abs(np.array([f(zz) for zz in z])))


Ns = [5, 15, 40, 80, 150]

print("=== A. sup_arc ||z*Hhat(z)||  (reproduce the recorded ~1.745*R growth) ===")
for N in Ns:
    R = Rmid(N)
    s = sup_arc(lambda z: z * Hhat_stable(z), R)
    print(f"  R={R:8.2f}: sup={s:10.2f}   sup/R={s/R:.4f}  (1/rho={1/rho:.4f})")

print("\n=== B. sup_arc ||z*Hhat(z)*e^{izb}||  for b>sigma  [DECISIVE] ===")
for b in [1.05, 1.2, 1.4]:
    print(f"  b={b} (sigma={sigma}); predict decay ~ max(C/R, (1/rho) R^{{{1-b/sigma:+.2f}}})")
    prev = None
    for N in Ns:
        R = Rmid(N)
        s = sup_arc(lambda z: z * Hhat_stable(z) * np.exp(1j * z * b), R)
        rate = "" if prev is None else f" slope={np.log(s/prev[1])/np.log(R/prev[0]):+.2f}"
        print(f"      R={R:8.2f}: sup={s:.4e}{rate}")
        prev = (R, s)

print("\n=== C. Jordan bound  pi*M(R)/a  vs true |arc|,  r=1.5, b=1.2, a=0.3 ===")
r, b = 1.5, 1.2
a = r - b
for N in Ns:
    R = Rmid(N)
    M = sup_arc(lambda z: z * Hhat_stable(z) * np.exp(1j * z * b), R)
    # true arc integral of z*Hhat(z)*e^{izr} dz
    z = R * np.exp(1j * TH)
    integ = np.array([zz * Hhat_stable(zz) * np.exp(1j * zz * r) * 1j * zz for zz in z])
    arc = np.trapezoid(integ, TH)
    print(f"  R={R:8.2f}: Jordan bound pi*M/a={np.pi*M/a:.4e}   true |arc|={abs(arc):.4e}"
          f"   (|arc|*R={abs(arc)*R:.2f})")

print("\n=== D. b < sigma -> method must FAIL (boundary: needs r > sigma) ===")
for b in [0.9, 0.5]:
    print(f"  b={b}; predict ~ (1/rho) R^{{{1-b/sigma:+.2f}}} -> GROWS")
    for N in [5, 40, 150]:
        R = Rmid(N)
        s = sup_arc(lambda z: z * Hhat_stable(z) * np.exp(1j * z * b), R)
        print(f"      R={R:8.2f}: sup={s:.4e}")

print("\n=== E. sup_arc ||Hhat(z)*e^{izb}||  (no k factor) -> decay for ANY b>0 ===")
for b in [0.9, 0.4, 0.1]:
    row = []
    for N in [5, 40, 150]:
        R = Rmid(N)
        row.append(f"R={R:7.1f}: {sup_arc(lambda z: Hhat_stable(z)*np.exp(1j*z*b), R):.3e}")
    print(f"  b={b}: " + "   ".join(row))

print("\nDone.")
