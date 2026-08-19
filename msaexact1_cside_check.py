"""MSAEXACT.1's `c`-side, pinned numerically before it is formalised.

`MSAFactorizationSplit.lean` reduces MSAEXACT.1 to matching the `O(D)`/`O(D²)`
increments of `|1 − ρQ̂|²` against `−ρ(ĉ_MSA − ĉ_HS)(k)`.  Doing that in Lean
requires knowing `ĉ_MSA(k)` — Waisman's inner Eq. (2) plus the exterior Yukawa —
and Eq. (2) is **printed with a defect** (the `v²` term's missing `1/x`,
`waisman_msa_closed_form.md` §7f).  Formalising the printed form would be
formalising a false statement, so the target is pinned here first.

The gate is the factorisation itself, at finite `k`:

    F(ik)·F(−ik) = 1 − ρ ĉ_MSA(k),      ĉ(k) = (4π/k)∫₀^∞ r c(r) sin(kr) dr

with the left side from `baxter_F` (the Blum & Høye route: `Q̂` from `A`, `q′`,
`D̃`, `ĝ`) and the right side built term by term from Eq. (2) inside the core and
`c = −βu = K e^{−z(r−1)}/r` outside.  ⭐ The two sides share **no** code path:
one is a Laplace transform of the Baxter factor, the other a Fourier transform of
the DCF, so agreement is a genuine test of Eq. (2) rather than a tautology.

⭐ Run with `--printed` to use Waisman's Eq. (2) as printed.  It fails — which is
an independent confirmation of the `1/x` repair, obtained from the factorisation
rather than from `y₀`, and at every `k` rather than at contact.
"""

import sys

import numpy as np
from scipy.integrate import quad

sys.path.insert(0, "..")
import msa_exact as M                                            # noqa: E402


def minus_C_printed(st: M.HCY, x, a, b, w):
    """Eq. (2) **as printed** — the `v²` term without its `1/x`."""
    xi, K, z = st.xi, st.K, st.z
    v = K * w
    yuk = v * (1.0 - np.exp(-z * x)) / (z * x)
    quad_t = v * v / (2.0 * K * z * z) * M._cosh_ratio(z, x)
    return a + b * x + xi * a * x ** 3 / 2.0 + yuk + quad_t


def chat(st: M.HCY, sol: M.Solution, k: float, printed: bool = False) -> float:
    """`ĉ_MSA(k) = (4π/k)[∫₀^1 r c(r) sin kr dr + K(k cos k + z sin k)/(z²+k²)]`.

    Inner: `c = −(Eq. 2)`.  Outer: the MSA closure `c = K e^{−z(r−1)}/r`, whose
    `1/r` cancels the radial transform's `r`, leaving an elementary integral —
    the one `yukawa_tail_laplace`'s sine partner will state in Lean.
    """
    a, b, w, K, z = sol.a, sol.b, sol.w, st.K, st.z
    mc = (lambda x: minus_C_printed(st, x, a, b, w)) if printed else \
         (lambda x: float(st.minus_C(x, a, b, w)))
    inner = quad(lambda r: -r * mc(r) * np.sin(k * r), 0.0, 1.0,
                 limit=400, epsabs=1e-13, epsrel=1e-13)[0]
    outer = K * (k * np.cos(k) + z * np.sin(k)) / (z ** 2 + k ** 2)
    return 4.0 * np.pi / k * (inner + outer)


def check(xi: float, K: float, z: float, ks, printed: bool = False):
    st = M.HCY(xi, K, z)
    sol, soln = M.solve_bh(st), M.solve_bh_n(xi, [z], [K])
    if sol is None or soln is None:
        return None
    rho = 6.0 * xi / np.pi
    out = []
    for k in ks:
        lhs = complex(M.baxter_F(soln, 1j * k) * M.baxter_F(soln, -1j * k))
        rhs = 1.0 - rho * chat(st, sol, k, printed)
        out.append((k, lhs.real, rhs, abs(lhs.imag)))
    return sol, out


def main() -> int:
    printed = "--printed" in sys.argv
    print(__doc__)
    print("=" * 78)
    print("F(ik)F(-ik)  vs  1 - rho*chat(k)     Eq. (2) "
          + ("AS PRINTED  (expected to FAIL)" if printed else "CORRECTED (with 1/x)"))
    print("=" * 78)
    ks = [0.35, 1.0, 2.0, np.pi, 5.0, 8.0, 13.0, 21.0]
    states = [(0.05, 0.9, 1.8), (0.10, 0.5, 1.8), (0.20, 1.0, 1.8),
              (0.30, 0.6, 1.8), (0.20, 2.0, 4.0), (0.15, 1.5, 2.5),
              (0.35, 0.8, 1.0), (0.40, 0.3, 1.8)]
    worst, neg = 0.0, 0
    for xi, K, z in states:
        r = check(xi, K, z, ks, printed)
        if r is None:
            print(f"  eta={xi:.2f} K={K:.1f} z={z:.1f}   no solution")
            continue
        sol, rows = r
        rel = max(abs(l - rr) / max(1.0, abs(l)) for _, l, rr, _ in rows)
        worst = max(worst, rel)
        neg += sum(1 for _, _, rr, _ in rows if rr < 0.0)
        print(f"\n  eta={xi:.2f}  K={K:.1f}  z={z:.1f}   "
              f"(a={sol.a:.5f}, b={sol.b:.5f}, v={sol.v:.5f}, res={sol.residual:.1e})")
        print(f"     {'k':>7}{'F(ik)F(-ik)':>16}{'1-rho*chat':>16}"
              f"{'rel diff':>12}{'|Im|':>10}")
        for k, l, rr, im in rows:
            print(f"     {k:7.3f}{l:16.9f}{rr:16.9f}"
                  f"{abs(l - rr) / max(1.0, abs(l)):12.2e}{im:10.1e}")
    print("\n" + "=" * 78)
    print(f"  worst relative disagreement over all states and k: {worst:.3e}")
    if printed:
        print(f"  ⭐ and {neg} of the sampled points give 1 - rho*chat(k) < 0 — impossible")
        print("     for a squared modulus, so the printed Eq. (2) is refuted by the")
        print("     factorisation alone, with no reference to the corrected form.")
    print("=" * 78)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
