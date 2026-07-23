#!/usr/bin/env python3
"""OZFIX.11 Stage-0 numerical scoping (scratch, not committed).

Confirms/refutes, at machine precision, the Lean lemmas planned for
OzCollapseTwoSigma.lean (hcollapse on r >= 2*sigma), plus Stage-2/3 de-risks.

All definitions mirror the Lean code exactly:
  - Chat_poly / Chat_F (closed form = Chat_F_formula) / Chat_J / Chat_complex
    (RadialFourierCHSComplex.lean)
  - baxterP0/P1/P2, Npoly, Dpoly, G_baxter, G_baxter_deriv (BaxterPoles.lean)
  - residue_term, h_explicit_term, Hterm, h_explicit (BaxterResidue.lean)
  - oz_forcing, oz_linear_op (PYOZ_GHS.lean)

Checks:
  A. self-check: closed-form Chat_F vs direct quadrature
  B. poles via Newton on G_baxter; gate: rho*Chat_complex(k_n) = 1   [Lemma 5]
  C. gate: per-pole t-integral identity
     int_0^sigma Chat_poly(t)*(Hterm_n(r+t)-Hterm_n(r-t)) dt
       = h_explicit_term(n)(r)/(2*pi*rho)                            [Lemmas 6-9]
  D. end-to-end: oz_forcing + oz_linear_op[h_explicit] vs h_explicit
     at r in {2.0, 2.5} (r>=2sigma) and r=1.5 (context)              [Lemma 12]
  E. circle-mean of Hhat on pole-avoiding radii -> -1/rho  (finding 2 sanity)
  F. sum_n ||h_explicit_term(sigma)||: converge or diverge?          [Stage 3]
  G. Stage-2 de-risk: sup on upper arc of the doubly-integrated kernel
     pieces (Jordan-readiness) + abs-convergence of sum ||Hterm(sigma)||
"""
import numpy as np
from scipy.integrate import quad

eta, sigma = 0.3, 1.0
rho = 6 * eta / (np.pi * sigma**3)          # heta_def inverted

a0 = (1 + 2 * eta)**2 / (1 - eta)**4
a1 = -6 * eta * (1 + eta / 2)**2 / (1 - eta)**4
a3 = eta * (1 + 2 * eta)**2 / (2 * (1 - eta)**4)

qp = np.pi * sigma * (2 + eta) / (1 - eta)**2        # q_prime_py
qpp = 2 * np.pi * (1 + 2 * eta) / (1 - eta)**2       # q_doubleprime_py
P0 = rho * qpp * sigma**2 / 2 - rho * qp * sigma     # baxterP0
P1 = rho * qp - rho * qpp * sigma                    # baxterP1
P2 = rho * qpp / 2                                   # baxterP2


def c_HS(r):
    return -(a0 + a1 * (r / sigma) + a3 * (r / sigma)**3) if r < sigma else 0.0


def Chat_poly(r):
    return -(a0 * r + (a1 / sigma) * r**2 + (a3 / sigma**3) * r**4)


# ---- Chat_F closed form (Chat_F_formula), c := -i*k, E := exp(-i*k*sigma) ----
def Chat_F(k):
    c = -1j * k
    E = np.exp(c * sigma)
    t1 = -a0 * ((sigma / c - 1 / c**2) * E + 1 / c**2)
    t2 = -(a1 / sigma) * ((sigma**2 / c - 2 * sigma / c**2 + 2 / c**3) * E - 2 / c**3)
    t3 = -(a3 / sigma**3) * ((sigma**4 / c - 4 * sigma**3 / c**2 + 12 * sigma**2 / c**3
                              - 24 * sigma / c**4 + 24 / c**5) * E - 24 / c**5)
    return t1 + t2 + t3


def Chat_J(k):
    return (Chat_F(-k) - Chat_F(k)) / (2j)


def Chat_complex(k):
    return (4 * np.pi / k) * Chat_J(k)


def Npoly(k):
    return 1j * k**3 - P0 * k**2 + 1j * P1 * k + 2 * P2


def Dpoly(k):
    return 1j * (P1 + 2 * P2 * sigma) * k + 2 * P2


def G(k):
    return Npoly(k) - Dpoly(k) * np.exp(-1j * k * sigma)


def Gp(k):  # G_baxter_deriv
    E = np.exp(-1j * k * sigma)
    return (3j * k**2 - 2 * P0 * k + 1j * P1) - ((1j * rho * qp) * E
                                                 + Dpoly(k) * (-1j * sigma) * E)


def residue_term(r, k):
    return k**7 * Chat_complex(k) * np.exp(1j * k * r) / (G(-k) * Gp(k))


def h_term(n_pole, r, poles):
    k = poles[n_pole]
    return residue_term(r, k) + residue_term(r, -np.conj(k))


def Hterm(n_pole, x, poles):
    k = poles[n_pole]
    km = -np.conj(k)
    return residue_term(x, k) / (1j * k) + residue_term(x, km) / (1j * km)


def h_explicit(r, poles):
    s = sum(h_term(n, r, poles) for n in range(len(poles)))
    return (1 / (2 * np.pi * r)) * s.real


def cquad(f, lo, hi, **kw):
    re = quad(lambda t: f(t).real, lo, hi, limit=400, **kw)[0]
    im = quad(lambda t: f(t).imag, lo, hi, limit=400, **kw)[0]
    return re + 1j * im


# ---------------------------------------------------------------- A: self-check
print("=== A. Chat_F closed form vs quadrature ===")
for k in [2.0 + 0.5j, 7.3 - 1.1j, 31.0 + 5.0j]:
    direct = cquad(lambda t: Chat_poly(t) * np.exp(-1j * k * t), 0, sigma)
    cf = Chat_F(k)
    print(f"  k={k}: |closed-quad|={abs(cf - direct):.3e}")

# ---------------------------------------------------------------- B: poles + gate rho*Chat=1
print("\n=== B. Newton poles of G_baxter; gate rho*Chat_complex(k_n)=1 ===")
NPOLES = 160
poles = []
k = 6.0 + 1.4j
for n in range(NPOLES):
    for _ in range(60):
        dk = G(k) / Gp(k)
        k = k - dk
        if abs(dk) < 1e-13:
            break
    poles.append(k)
    k = k + 2 * np.pi  # continuation guess for the next pole

poles = np.array(poles)
print(f"  n=0 pole: {poles[0]:.6f}   (ground truth 6.0580+1.4368i)")
print(f"  max |G(k_n)| over family: {max(abs(G(p)) for p in poles):.3e}")
sp = np.diff(poles.real)
print(f"  Re spacing min/max: {sp.min():.4f}/{sp.max():.4f} (~2pi={2*np.pi:.4f})")
gate_B = 0.0
for n in [0, 3, 8, 40, 159]:
    err = abs(rho * Chat_complex(poles[n]) - 1)
    errm = abs(rho * Chat_complex(-np.conj(poles[n])) - 1)
    gate_B = max(gate_B, err, errm)
    print(f"  n={n:3d}: |rho*Chat(k_n)-1|={err:.3e}   mirror: {errm:.3e}")
print(f"  GATE B: {'PASS' if gate_B < 1e-8 else 'FAIL'} (max {gate_B:.3e})")

# ---------------------------------------------------------------- C: per-pole identity
print("\n=== C. per-pole: int Chat_poly*(Hterm(r+t)-Hterm(r-t)) = h_term/(2*pi*rho) ===")
gate_C = 0.0
for r in [2.0, 2.5, 3.0]:
    for n in [0, 3, 8]:
        lhs = cquad(lambda t: Chat_poly(t) * (Hterm(n, r + t, poles) - Hterm(n, r - t, poles)),
                    0, sigma)
        rhs = h_term(n, r, poles) / (2 * np.pi * rho)
        rel = abs(lhs - rhs) / max(abs(rhs), 1e-300)
        gate_C = max(gate_C, rel)
        print(f"  r={r} n={n}: lhs={lhs:.6e} rhs={rhs:.6e} rel={rel:.3e}")
print(f"  GATE C: {'PASS' if gate_C < 1e-8 else 'FAIL'} (max rel {gate_C:.3e})")

# ---------------------------------------------------------------- D: end-to-end
print("\n=== D. oz_forcing + oz_linear_op[h_explicit] vs h_explicit ===")
NUSE = 40
pl = poles[:NUSE]


def oz_forcing(r):
    if r <= 0:
        return 0.0
    val = quad(lambda t: t * c_HS(t) * (sigma**2 - (r - t)**2) * (1.0 if r < sigma + t else 0.0),
               0, sigma, limit=400)[0]
    return -(np.pi * rho / r) * val


def oz_linear_op(r):
    if r <= 0:
        return 0.0

    def outer(t):
        lo = max(r - t, sigma)
        hi = r + t
        inner = quad(lambda s: s * h_explicit(s, pl), lo, hi, limit=200)[0]
        return t * c_HS(t) * inner

    return (2 * np.pi * rho / r) * quad(outer, 0, sigma, limit=200)[0]


print(f"  h_explicit(2.0) with N={len(poles)}: {h_explicit(2.0, poles):.6f} "
      f"(ground truth 0.005663)")
for r in [2.0, 2.5, 1.5]:
    lhs = oz_forcing(r) + oz_linear_op(r)
    rhs = h_explicit(r, pl)
    tag = "r>=2s" if r >= 2 * sigma else "sigma<r<2s (slow-converging region, context only)"
    print(f"  r={r} [{tag}]: LHS={lhs:.8f} RHS={rhs:.8f} diff={lhs - rhs:.2e}")

# ---------------------------------------------------------------- E: circle mean of Hhat
print("\n=== E. circle-mean of Hhat on pole-avoiding radii (finding 2: -> -1/rho) ===")


def Hhat_stable(k):
    """Hhat = Chat/(1-rho*Chat), overflow-safe for Im k >= 0 via e^{+iks} factoring."""
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
    # Chat = (2pi/(ik)) * S,  S = dV + Wm*e^{ik s} - W*e^{-ik s}
    ep = np.exp(1j * k * sigma)     # tiny for Im k > 0
    dV = Vm - V
    # factor out e^{-ik s}:  S = e^{-iks} * T,  T = -W + (dV + Wm*ep)*ep
    T = -W + (dV + Wm * ep) * ep
    return 2 * np.pi * T / (1j * k * ep - 2 * np.pi * rho * T)


# sanity: stable Hhat vs direct at moderate k
for kk in [7.0 + 1.0j, 40.0 + 3.0j]:
    d = Chat_complex(kk) / (1 - rho * Chat_complex(kk))
    print(f"  sanity k={kk}: |Hhat_stable - direct| = {abs(Hhat_stable(kk) - d):.3e}")

for N in [10, 40, 120]:
    R = 0.5 * (abs(poles[N]) + abs(poles[N + 1]))
    th = np.linspace(0, np.pi, 4001)
    vals = np.array([Hhat_stable(R * np.exp(1j * t)) for t in th])
    mean_full = np.trapezoid(vals.real, th) / np.pi   # full-circle mean via conj symmetry
    supH = np.max(np.abs(vals))
    print(f"  N={N:3d} R={R:8.2f}: mean={mean_full:+.6f} (-1/rho={-1/rho:+.6f}) "
          f"sup||Hhat||={supH:.6f} (1/rho={1/rho:.6f})")

# ---------------------------------------------------------------- F: r = sigma summability
print("\n=== F. sum_n ||h_explicit_term(sigma)|| — Summable at r=sigma? ===")
norms = np.array([abs(h_term(n, sigma, poles)) for n in range(len(poles))])
part = np.cumsum(norms)
for N in [10, 20, 40, 80, 159]:
    print(f"  N={N:3d}: term={norms[N]:.4e}  n*term={ (N+1)*norms[N]:.4e}  partial={part[N]:.4f}")
print("  (n*term ~ const  =>  terms ~ C/n  =>  NOT absolutely summable — junk-tsum risk real)")

# ---------------------------------------------------------------- G: Stage-2 de-risks
print("\n=== G. Stage-2 de-risks ===")
Hs = np.array([abs(Hterm(n, sigma, poles)) for n in range(len(poles))])
print(f"  sum ||Hterm(sigma)|| partials: N=40: {np.cumsum(Hs)[40]:.5f}  "
      f"N=159: {np.cumsum(Hs)[159]:.5f}  (should converge: terms ~ 1/n^2)")
print(f"  n^2*||Hterm_n(sigma)|| at n=40,159: {40**2*Hs[40]:.3e}, {159**2*Hs[159]:.3e}")

r2 = 1.5  # sigma < r < 2 sigma


def ChatF_inc(k, up):  # incomplete Chat_F over [0, up], quadrature (moderate k only)
    return cquad(lambda t: Chat_poly(t) * np.exp(-1j * k * t), 0, up)


for N in [10, 40, 120]:
    R = 0.5 * (abs(poles[N]) + abs(poles[N + 1]))
    th = np.linspace(0.0, np.pi, 721)
    z = R * np.exp(1j * th)
    # piece 1: Hhat(z) e^{izr} ChatF(-z) over full [0,sigma]  (r>=... uses phase r)
    amp1 = np.array([abs(Hhat_stable(zz) * np.exp(1j * zz * r2) * Chat_F(-zz)) for zz in z])
    # piece 2: Hhat(z) e^{iz sigma} (flat piece amplitude, phase sigma)
    amp2 = np.array([abs(Hhat_stable(zz) * np.exp(1j * zz * sigma)) for zz in z])
    print(f"  N={N:3d} R={R:8.2f}: sup|Hhat*e^{{izr}}*ChatF(-z)|={amp1.max():.3e} "
          f"(R*sup={R*amp1.max():.3f})   sup|Hhat*e^{{iz s}}|={amp2.max():.3f} (flat piece, O(1))")

print("\nDone.")
