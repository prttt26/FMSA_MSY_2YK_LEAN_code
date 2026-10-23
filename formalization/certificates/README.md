# Interval certificates for FORMALIZATION_TODO items F5, F6 and F7

These are computer-assisted proofs in rigorous interval arithmetic, not Lean proofs.
Every floating-point operation is rounded outward (one ulp, `math.nextafter`) and every
transcendental constant is computed at 200 bits with `mpmath` and then widened. Complex
numbers are rectangles. Only `numpy` (for floating-point Newton predictors and
preconditioners, which need not be exact) and `mpmath` are used; the optional
cross-checks import the release scripts when they are present. The exception is
`f7_cover_arb.py` and `f7_fold_turning.py`, which use Arb ball arithmetic through
`python-flint` (tested with 0.6.0, `pip install python-flint`).

| Script | Claim | Runtime |
|---|---|---|
| `f5_competing_tails.py` | z = (1.8, 12), weights (1, -6), eta = 0.2, 0.3, 0.4: the PY-seeded exact-MSA branch is real and regular on 0 <= tau <= 3, and the Taylor radius of that branch satisfies R_c <= 2.75 < 3, so the coupling series diverges at tau = 3. | ~12 min |
| `f6_second_order_tangents.py` | One attractive Yukawa tail, z = 5, T* = 0.02, strict second-order jet a = c0 + c1 tau + c2 tau^2: two distinct pairs with equal pressure and chemical potential, each with a common tangent lying below beta f/V on the whole domain 0 < rho* < 6/pi. | ~2 min |
| `f7_fold_binding.py`, `f7_fold_turning.py`, `f7_cover_arb.py` | z = (1.8, 12), weights (1, w), eta = 0.3: the Taylor radius of the PY-seeded branch is the nearest singularity, which need not be the real fold. A (w = -2.5): R_c in [4.47, 4.524], tau_f in [4.4761, 4.5070]. B (w = -2.636): R_c in [7.00, 7.107] < 7.8336 <= tau_f, a real fold that does not bind. | binding: not timed (about 10^5 pure-Python pieces); turning: 7-65 s; cover: 1.5-30 min per run |

Results are written to `results/`.

## F5 method

The unknowns are u = (Dt_1, Dt_2, G_1, G_2); the residual is the unnormalised
Blum-Hoye system of `release/fmsa_mixture/paper/msa_series_radius.py`, re-implemented
independently. The residual is polynomial in u and affine in tau, so it is entire.

* A chain of Krawczyk tests: for each path piece with enclosure T, a box X with
  K(X, T) inside int X and an explicit bound ||I - C J(X, T)||_inf < 1. This gives exactly
  one root in X for every tau in T, with invertible Jacobian.
* Consecutive pieces are joined at their shared end point by a small box Y, certified by
  a point Krawczyk test and contained in both neighbouring boxes.
* The real chain [0, 3] uses boxes symmetric about the real axis. Conjugation symmetry then
  makes the unique root real. Its first box contains an enclosure of the PY seed.
* The monodromy loop is [0, 2.75] followed by the circle |tau| = 2.75. The end-point boxes
  at tau = 2.75 before and after the loop are disjoint. If R_c > 2.75, the Taylor sum would
  be a single-valued analytic root on a disc containing the loop. A clopen argument over
  the chain would identify it with the certified roots, which is a contradiction.

## F6 method

* With eta = pi rho / 6 and q = (a - 1)/eta (regular at 0), define
  beta p = (6/pi) int_0^eta a and beta mu = log rho + int_0^eta q.
* Both integrals are enclosed by adaptive Simpson rules. The fourth-derivative remainder is
  bounded with interval Taylor arithmetic of order 4.
* Each pair is a 2x2 Krawczyk solution of equal p and mu. The Jacobian is
  [[a(x), -a(y)], [a(x)/x, -a(y)/y]].
* The proof that g = f - (mu* rho - p*) >= 0 has four parts:
  * Near each tangency point, a > 0 on a window containing its box, so g is convex there
    with g = g' = 0 at the point.
  * On every other grid cell, a second-order Taylor lower bound of g is positive.
  * On (0, rho_0], g' < 0.
  * On [rho_1, 6/pi), a > 0, shown through a (1 - eta)^4 which stays finite at eta = 1,
    and g'(rho_1) > 0.

Run from this directory: `python3 f5_competing_tails.py` and
`python3 f6_second_order_tangents.py`. Each prints PASS and exits with code 0 on success.

Both scripts include a negative control that must behave as expected for PASS: F5
re-runs the loop at eta = 0.1 (Taylor radius about 3.97 > 2.75), where the loop closes
and the test must not certify; F6 raises the low-density tangent by 1e-6, which must
fail the cell test, and lowers it by 1e-6, which must pass everywhere.

## F7 method

Same unknowns and residual as F5; family z = (1.8, 12), K = (1, w), eta = 0.3.

* **Upper bound** (`f7_fold_binding.py`, pure-Python intervals). A Krawczyk chain along a ray
  to a point near the singularity, then around a circle of radius rho about it. Disjoint
  enclosures at the start and end of the loop give `R_c <= |c| + rho`, by the F5 argument.
  Acceptance is by inclusion alone, K(X, T) in int X (Rump's theorem gives uniqueness and an
  invertible Jacobian for any preconditioner); the F5 unweighted contraction test fails here
  because the components differ by two orders of magnitude. Negative control: the same loop
  around the regular point 2.2 must close.
* **Real fold** (`f7_fold_turning.py`, Arb). A tau-chain on the real branch, then an arclength
  chain on the curve P(u) = tau b, re-anchored when the tangent turns. tau attains an interior
  maximum on the continuation of the physical branch, enclosed in [tau_lo, tau_hi]. Run as
  `python3 f7_fold_turning.py <w> <a> <tau_hi> <tau_lo>` (A: `-2.5 4.40 4.47 4.43`;
  B: `-2.636 7.6 7.82 7.7`).
* **Lower bound** (`f7_cover_arb.py`, Arb). A quadtree of dyadic rectangles covers the closed
  upper half disc |tau| <= r_lo; each leaf carries a Krawczyk box. Leaves that share an edge
  segment are glued: the Krawczyk image on the common segment lies in the other box, or a box
  certified at one exact common point lies in both. Leaves on the real axis are symmetric, so
  the glued root is real there and extends by Schwarz reflection; the leaf at 0 contains the
  PY seed. This gives `R_c >= r_lo`. The Jacobian over a box is enclosed in centred form (the
  residual is a cubic polynomial in u, so this is an exact Taylor identity); the natural
  interval extension is 7-15x wider and cost about 250x more rectangles. Run as
  `python3 f7_cover_arb.py <w> <r_lo> [h0] [hmin]`.

| run | result | leaves | time |
|---|---|---|---|
| A, r_lo = 4.40 | certified | 23 803 | 93 s |
| A, r_lo = 4.47 | certified | 44 554 | 179 s |
| A, r_lo = 4.57, hmin = 2^-14 (control, past the real fold) | fails at tau = 4.47702 + 0.00041i, at the fold | - | - |
| B, r_lo = 6.90 | certified | 260 262 | 1067 s |
| B, r_lo = 7.00 | certified | 330 024 | 1341 s |
| B, r_lo = 7.10, hmin = 2^-14 (control, past the complex fold) | fails at tau = -2.78903 + 6.46078i, 0.002 from tau*_c | - | - |

Logs and JSON records are in `results/f7_*`.
