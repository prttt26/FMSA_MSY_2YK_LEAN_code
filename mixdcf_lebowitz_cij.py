#!/usr/bin/env python3
"""The explicit two-piece Lebowitz mixture PY-HS DCF c_ij (derived 2026-08-14).

Derived from the PROVEN `matDCFreCore` derivative (Lean `matDCFreCore_hasDerivAt_lower` for the lower
piece; the analogous upper-piece derivative via the moving-limit `qpConv_upper_intervalForm`), via
the shell-inverse `c_ij(v) = −matDCFreCore_ij'(v) / (2π·rg_ij·v)` (rg_ij = √(ρ_iρ_j)).  Verified three
independent ways: (i) symbolic coefficients == numerical fit of the candidate to 1e-10; (ii) the
candidate passes the hard-core OZ test g_ij(r<σ)=0 (`mixdcf_unequal_value_check.py`); (iii) at equal σ
both pieces reduce EXACTLY to the scalar PY c_HS = −(a0 + a1(v/σ) + a3(v/σ)³).

Conventions (matching the Lean `MatrixQ0`): ξ₂ = Σₖ ρₖσₖ², η = (π/6)Σₖ ρₖσₖ³, D = vac = 1−η,
R_ij=(σ_i+σ_j)/2, λ_ij=(σ_j−σ_i)/2.  Pair (i,j)=(0,1) with σ_0 < σ_1 so λ_01 > 0.

STRUCTURE (the key finding):
* LOWER piece  0 < v < λ_ij :  c_ij(v) = CONSTANT  (the numerator of −matDCFreCore'/(2πv) is linear in
  v with vanishing constant term — the ξ₂ identity kills the v⁰ term, so no 1/v pole).
* UPPER piece  λ_ij < v < R_ij :  c_ij(v) = a + b/v + c2·v + e·v³  (NO v² term).  The `b/v` term is
  ∝ (σ_i−σ_j)², so it VANISHES at equal diameters, recovering the scalar cubic.  The natural
  POLYNOMIAL object is r·c_ij (degree 1 lower, degree 4 upper).
"""
import numpy as np


def _D(s, r):
    return 1.0 - (np.pi / 6) * np.sum(r * s ** 3)


def c_lower(s0, s1, r0, r1):
    """Constant value of c_ij on the lower piece (0, (s1-s0)/2), σ_0 < σ_1."""
    pi = np.pi
    D = _D(np.array([s0, s1]), np.array([r0, r1]))
    num = (24 * D ** 3
           + 28 * D ** 2 * pi * r0 * s0 ** 3 + 4 * D ** 2 * pi * r1 * s0 ** 3
           + 12 * D ** 2 * pi * r1 * s0 ** 2 * s1 + 12 * D ** 2 * pi * r1 * s0 * s1 ** 2
           + 10 * D * pi ** 2 * r0 ** 2 * s0 ** 6 + 4 * D * pi ** 2 * r0 * r1 * s0 ** 5 * s1
           + 16 * D * pi ** 2 * r0 * r1 * s0 ** 4 * s1 ** 2 + 4 * D * pi ** 2 * r1 ** 2 * s0 ** 3 * s1 ** 3
           + 6 * D * pi ** 2 * r1 ** 2 * s0 ** 2 * s1 ** 4
           + pi ** 3 * r0 ** 3 * s0 ** 9 + 3 * pi ** 3 * r0 ** 2 * r1 * s0 ** 7 * s1 ** 2
           + 3 * pi ** 3 * r0 * r1 ** 2 * s0 ** 5 * s1 ** 4 + pi ** 3 * r1 ** 3 * s0 ** 3 * s1 ** 6)
    return -num / (24 * D ** 4)


def c_upper_coeffs(s0, s1, r0, r1):
    """Upper-piece c_ij = a + b/v + c2*v + e*v^3 on (λ, R); returns (a, b, c2, e)."""
    pi = np.pi
    D = _D(np.array([s0, s1]), np.array([r0, r1]))
    G0 = (36 * D ** 2 * r0 * s0 ** 2 + 24 * D ** 2 * r0 * s0 * s1 + 4 * D ** 2 * r0 * s1 ** 2
          + 4 * D ** 2 * r1 * s0 ** 2 + 24 * D ** 2 * r1 * s0 * s1 + 36 * D ** 2 * r1 * s1 ** 2
          + 12 * D * pi * r0 ** 2 * s0 ** 5 + 16 * D * pi * r0 ** 2 * s0 ** 4 * s1
          + 4 * D * pi * r0 ** 2 * s0 ** 3 * s1 ** 2 + 4 * D * pi * r0 * r1 * s0 ** 4 * s1
          + 28 * D * pi * r0 * r1 * s0 ** 3 * s1 ** 2 + 28 * D * pi * r0 * r1 * s0 ** 2 * s1 ** 3
          + 4 * D * pi * r0 * r1 * s0 * s1 ** 4 + 4 * D * pi * r1 ** 2 * s0 ** 2 * s1 ** 3
          + 16 * D * pi * r1 ** 2 * s0 * s1 ** 4 + 12 * D * pi * r1 ** 2 * s1 ** 5
          + pi ** 2 * r0 ** 3 * s0 ** 8 + 2 * pi ** 2 * r0 ** 3 * s0 ** 7 * s1 + pi ** 2 * r0 ** 3 * s0 ** 6 * s1 ** 2
          + 3 * pi ** 2 * r0 ** 2 * r1 * s0 ** 6 * s1 ** 2 + 6 * pi ** 2 * r0 ** 2 * r1 * s0 ** 5 * s1 ** 3
          + 3 * pi ** 2 * r0 ** 2 * r1 * s0 ** 4 * s1 ** 4 + 3 * pi ** 2 * r0 * r1 ** 2 * s0 ** 4 * s1 ** 4
          + 6 * pi ** 2 * r0 * r1 ** 2 * s0 ** 3 * s1 ** 5 + 3 * pi ** 2 * r0 * r1 ** 2 * s0 ** 2 * s1 ** 6
          + pi ** 2 * r1 ** 3 * s0 ** 2 * s1 ** 6 + 2 * pi ** 2 * r1 ** 3 * s0 * s1 ** 7 + pi ** 2 * r1 ** 3 * s1 ** 8)
    num0 = 3 * pi * (s0 - s1) ** 2 * G0
    G1 = (48 * D ** 3 + 28 * D ** 2 * pi * r0 * s0 ** 3 + 12 * D ** 2 * pi * r0 * s0 ** 2 * s1
          + 12 * D ** 2 * pi * r0 * s0 * s1 ** 2 + 4 * D ** 2 * pi * r0 * s1 ** 3 + 4 * D ** 2 * pi * r1 * s0 ** 3
          + 12 * D ** 2 * pi * r1 * s0 ** 2 * s1 + 12 * D ** 2 * pi * r1 * s0 * s1 ** 2 + 28 * D ** 2 * pi * r1 * s1 ** 3
          + 10 * D * pi ** 2 * r0 ** 2 * s0 ** 6 + 6 * D * pi ** 2 * r0 ** 2 * s0 ** 4 * s1 ** 2
          + 4 * D * pi ** 2 * r0 ** 2 * s0 ** 3 * s1 ** 3 + 4 * D * pi ** 2 * r0 * r1 * s0 ** 5 * s1
          + 16 * D * pi ** 2 * r0 * r1 * s0 ** 4 * s1 ** 2 + 16 * D * pi ** 2 * r0 * r1 * s0 ** 2 * s1 ** 4
          + 4 * D * pi ** 2 * r0 * r1 * s0 * s1 ** 5 + 4 * D * pi ** 2 * r1 ** 2 * s0 ** 3 * s1 ** 3
          + 6 * D * pi ** 2 * r1 ** 2 * s0 ** 2 * s1 ** 4 + 10 * D * pi ** 2 * r1 ** 2 * s1 ** 6
          + pi ** 3 * r0 ** 3 * s0 ** 9 + pi ** 3 * r0 ** 3 * s0 ** 6 * s1 ** 3 + 3 * pi ** 3 * r0 ** 2 * r1 * s0 ** 7 * s1 ** 2
          + 3 * pi ** 3 * r0 ** 2 * r1 * s0 ** 4 * s1 ** 5 + 3 * pi ** 3 * r0 * r1 ** 2 * s0 ** 5 * s1 ** 4
          + 3 * pi ** 3 * r0 * r1 ** 2 * s0 ** 2 * s1 ** 7 + pi ** 3 * r1 ** 3 * s0 ** 3 * s1 ** 6 + pi ** 3 * r1 ** 3 * s1 ** 9)
    num1 = -16 * G1
    G2 = (20 * D ** 2 * r0 * s0 ** 2 + 8 * D ** 2 * r0 * s0 * s1 + 4 * D ** 2 * r0 * s1 ** 2 + 4 * D ** 2 * r1 * s0 ** 2
          + 8 * D ** 2 * r1 * s0 * s1 + 20 * D ** 2 * r1 * s1 ** 2 + 8 * D * pi * r0 ** 2 * s0 ** 5
          + 4 * D * pi * r0 ** 2 * s0 ** 4 * s1 + 4 * D * pi * r0 ** 2 * s0 ** 3 * s1 ** 2 + 4 * D * pi * r0 * r1 * s0 ** 4 * s1
          + 12 * D * pi * r0 * r1 * s0 ** 3 * s1 ** 2 + 12 * D * pi * r0 * r1 * s0 ** 2 * s1 ** 3
          + 4 * D * pi * r0 * r1 * s0 * s1 ** 4 + 4 * D * pi * r1 ** 2 * s0 ** 2 * s1 ** 3 + 4 * D * pi * r1 ** 2 * s0 * s1 ** 4
          + 8 * D * pi * r1 ** 2 * s1 ** 5 + pi ** 2 * r0 ** 3 * s0 ** 8 + pi ** 2 * r0 ** 3 * s0 ** 6 * s1 ** 2
          + 3 * pi ** 2 * r0 ** 2 * r1 * s0 ** 6 * s1 ** 2 + 3 * pi ** 2 * r0 ** 2 * r1 * s0 ** 4 * s1 ** 4
          + 3 * pi ** 2 * r0 * r1 ** 2 * s0 ** 4 * s1 ** 4 + 3 * pi ** 2 * r0 * r1 ** 2 * s0 ** 2 * s1 ** 6
          + pi ** 2 * r1 ** 3 * s0 ** 2 * s1 ** 6 + pi ** 2 * r1 ** 3 * s1 ** 8)
    num2 = 24 * pi * G2
    G4 = (4 * D ** 2 * r0 + 4 * D ** 2 * r1 + 4 * D * pi * r0 ** 2 * s0 ** 3 + 4 * D * pi * r0 * r1 * s0 ** 2 * s1
          + 4 * D * pi * r0 * r1 * s0 * s1 ** 2 + 4 * D * pi * r1 ** 2 * s1 ** 3 + pi ** 2 * r0 ** 3 * s0 ** 6
          + 3 * pi ** 2 * r0 ** 2 * r1 * s0 ** 4 * s1 ** 2 + 3 * pi ** 2 * r0 * r1 ** 2 * s0 ** 2 * s1 ** 4
          + pi ** 2 * r1 ** 3 * s1 ** 6)
    num4 = -16 * pi * G4
    den = 768 * D ** 4
    return num1 / den, num0 / den, num2 / den, num4 / den   # a, b(1/v), c2, e(v^3)


def c_ij(s0, s1, r0, r1, v):
    """Full two-piece c_ij(v) for the pair with σ_0 < σ_1 (v > 0)."""
    lam = (s1 - s0) / 2
    if v <= lam:
        return c_lower(s0, s1, r0, r1)
    a, b, c2, e = c_upper_coeffs(s0, s1, r0, r1)
    return a + b / v + c2 * v + e * v ** 3


if __name__ == "__main__":
    # (i) lower-piece constant, (ii) upper coeffs, (iii) equal-σ → scalar c_HS
    print("pair σ=(0.7,1.0) ρ=(0.25,0.30):")
    print("  lower-piece constant c =", round(c_lower(0.7, 1.0, 0.25, 0.30), 5), "(num check: -3.44165)")
    a, b, c2, e = c_upper_coeffs(0.7, 1.0, 0.25, 0.30)
    print(f"  upper a={a:+.5f} b(1/v)={b:+.5f} c2={c2:+.5f} e={e:+.5f}  (fit: -4.55858,+0.08343,+3.75330,-0.67101)")
    s, r0, r1 = 1.0, 0.15, 0.20
    eta = np.pi / 6 * (r0 + r1) * s ** 3
    a0 = (1 + 2 * eta) ** 2 / (1 - eta) ** 4
    a1 = -6 * eta * (1 + eta / 2) ** 2 / (1 - eta) ** 4
    a3 = eta * (1 + 2 * eta) ** 2 / (2 * (1 - eta) ** 4)
    ae, be, c2e, ee = c_upper_coeffs(s, s, r0, r1)
    print(f"\nequal σ=1 ρ=(.15,.20): upper a={ae:+.5f} b={be:+.5f} c2={c2e:+.5f} e={ee:+.5f}")
    print(f"  scalar c_HS      : -a0={-a0:+.5f}  -a1/s={-a1 / s:+.5f}  -a3/s³={-a3 / s ** 3:+.5f} (b must be 0)")
