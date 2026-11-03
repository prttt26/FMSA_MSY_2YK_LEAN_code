# M2 actual root existence inside the kernel-certified box

The original four-dimensional BH system has exactly one root inside the
existing literal amplitude box, at the exact rational state parameters below.
No root witness, analytic interval enclosure, preconditioner inverse or
external success flag is supplied as a mathematical hypothesis. This closes
the box-nonvacuity gap left by the regularity certificate, for this state.
It does not identify the root as the PY branch or the joint tangency witness.

## Exact state and domain

Use the existing N=1, sigma=1, eta=1/10, rho=3/(5*pi) and z=(9/5,12).
The strengths are K=(1,w) and the coupling b is fixed by

```
b = 11227143292458953 / 2000000000000000
w = -9657507677060143 / 2000000000000000
```

These rationals are state parameters, chosen as midpoints of the earlier
numerical joint-witness parameter intervals. They are NOT asserted to solve
the zero-mode/tangency conditions. In particular, existence at these exact
midpoints does not certify a solution of the ten-dimensional augmented joint system.

`M2KernelCertificate.lower` and `upper` are unchanged. The center is their
exact midpoint, in the original order (Dt1,Dt2,G1,G2):

```
(31826038630952869/2000000000000000,
 -12966401805408291/1000000000000000,
 5529385108141801/10000000000000000,
 -96599446204049623/200000000000000000)
```

All signed original amplitudes are retained. No reduced X=Dt*G variable or
rescaling of the residual is used. The physical pi and exponential constants
keep their genuine real values.

## Proof structure

1. `NewtonBoxExistence` constructs the continuous linear map of an arbitrary
   finite matrix and proves the exact Pi-space operator-norm bound from its
   absolute row sums. It proves the preconditioner itself injective from the
   defect bound: C*J is invertible, so det(C) is nonzero. Neither an inverse
   of C nor a norm-convention identification is assumed.

   Its `exists_unique_root_in_box` applies the convex mean-value inequality
   to G(x)=x-C*f(x). A derivative bound q<1 makes G a contraction. The exact
   center residual and box geometry prove G maps the nonempty closed box
   into itself. Completeness and Banach's fixed-point theorem construct a
   fixed point; injectivity of C turns it into a true root. Contraction
   proves uniqueness INSIDE the box, including its boundary.

2. `M2ResidualFormula` proves four candidate formulas against evaluation of
   the literal ORIGINAL BH residual polynomials, for arbitrary amplitudes,
   strengths and coupling. Both directions of `actual_root_iff_formula_zero`
   cover every original amplitude coordinate. SymPy chooses expressions;
   the ordinary Lean kernel proves the identities independently.

3. `M2ResidualDerivative` constructs the continuous linear equivalence from
   all original amplitudes to Fin4. The actual analytic residual, chain rule
   and existing exact ordered-partial identity prove
   `hasFDerivAt_formula`: the matrix `M2JacobianFormula.formula x` is exactly
   the derivative of the original four-coordinate residual at EVERY point.
   No root or regularity premise is used for differentiation.

4. `M2RootCertificate` proves all four components of C*f(center) bounded in
   absolute value by 10^-12. Rational simplification chooses a constant
   expression in pi and the five previously bounded exponentials; Lean proves
   its identity to the original residual. The existing signed four-corner
   rules prove every analytic leaf, product, sum and outward rounding. This
   is not an Arb enclosure premise.

   Exact arithmetic also proves center-to-face distance at least m=10^-10
   and uniform box radius R=2*10^-9. Together with the unchanged proved
   row bound q=10^-6, the required self-map inequality is

       q*R + epsilon = 10^-6 * (2*10^-9) + 10^-12 <= 10^-10.

5. `M2RootExistence.exists_unique_coordinate_root` discharges ALL hypotheses
   of the generic existence theorem from these proved bounds.
   `exists_unique_actual_root` transports existence and local uniqueness to
   the original Dt/G root interface. `exists_actual_regular_root` combines
   the constructed root with the unchanged actual regularity certificate.

## Reproduction

From the research package root, with the existing read-only SymPy/Flint
helper dependencies (the Flint import supplies no proof premise):

```sh
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/generate_m2_residual_formula.py > /tmp/M2ResidualFormula.body
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/generate_m2_root_certificate.py > /tmp/M2RootCertificate.body
python3 scripts/check_project.py
```

The generated bodies match the source prefix before the first `/-- info:`
axiom-report guard. The center generator reuses the unchanged interval
operation generator, but none of its old analytic output is trusted.
The old JSON chooses only rational box/preconditioner values.

## Scope still open

PY-prefix and endpoint identification, exact zero-mode/tangency conditions,
first loss, all-real-wave stability, complex-domain exclusion and Taylor
radii remain separate obligations. This theorem is local root uniqueness
inside one fixed box at one exact rational parameter pair; it excludes no
roots outside the box and proves no global component statement. The earlier
joint numerical root-existence report retains its external status.
M1/M3 analytic numerical reports and generic positive-density finite fibers,
matrix escape, nonisolated singular endpoints and multitailed Taylor lower
bounds remain open. No universal real-root/Taylor equivalence follows.

Foundation 1.0.17 is frozen and untouched; TeX is untouched. No new
mathematical axiom is introduced. The complete guarded validation passed.

## Complete guarded validation (2026-10-30)

PASS: **1016** exact standard-three-axiom guards across **75** research modules
plus the root, **76** pinned direct compiler commands. All 16 new public
axiom reports were actually queried before their exact guards were installed.
Every input/source/artifact/raw-log hash was independently checked afterward.
ALL 70 earlier module source/artifact/footprint records are unchanged from the
1000-guard baseline. All 530 frozen hashes and nine paper/eight Mathlib/two
raw LeanCode import pins remain unchanged. No new direct external import or
shared/Lake build was required. Raw compiler warnings are retained verbatim.

Both generators reproduce their guarded source prefixes exactly. A temporary
copy of the actual first center certificate with the first product lower
bound raised by one is rejected by Lean with an explicit false-corner proof
failure and nonzero exit. No repository proof was corrupted. Existing M2
Jacobian, M2 second-root and M3 witness rational checkers also pass their old
source/model pins, retaining their explicitly external analytic status.

Complete evidence: `results/lean/validation.json`, `results/lean/build.log`.
Research remains active and unmerged; the remaining mathematical obligations
above have not been reclassified as complete.
