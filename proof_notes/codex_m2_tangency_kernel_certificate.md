# Kernel proof of an M2 stationary zero-mode contact

All ten new proof bodies have compiled. All 34 public axiom reports have
actually been queried and contain only propext, Classical.choice and Quot.sound.
All 1050 exact guards passed across 85 research modules plus the root module
(86 pinned compiler commands). The independent post-run hash audit also passed.
This result constructs an actual stationary zero of the honest zero-frequency factor; it does not
supply PY membership, first contact, positive curvature or a Taylor radius.

## Exact statement and physical data

`M2TangencyExistence.exists_unique_system_zero` constructs a zero of ALL TEN
contact equations, uniquely inside the explicit rational box. No root witness,
preconditioner inverse, analytic enclosure or external success flag is a premise.

The data are N=1, sigma=1, eta=1/10, rho=3/(5*pi), z=(9/5,12), strengths
K=(1,w) and positive coupling b. The real b and w are CONSTRUCTED in the literal
intervals `M2TangencyData.lower/upper` at coordinates4/5. Unlike the earlier
fixed-midpoint theorem, the new b and w are not asserted to be rational.

`exists_actual_regular_noncanonical_root` constructs an original signed Dt/G
BH root at these parameters. Its true amplitude partial is invertible, yet it
is not fully canonical: the honest renewal determinant and physical Fourier
factor have a genuine zero at frequency0. Thus actual amplitude regularity
does NOT imply full canonicity, even at an actual positive-density BH root.
This is no conclusion about the HS Taylor germ or its radius.

`exists_actual_stationary_branch` constructs an actual two-sided local analytic
root curve at fixed w. Its coupling derivative equals the four velocity
variables in the ten-dimensional certificate. The honest zero-frequency factor
on that curve has value and first derivative zero. This is stationarity; no
minimum-curvature or first-contact conclusion is inferred.

## Correct dimension and box scope

The frozen external `TwoTail.augmented` implementation has TEN unknowns:

    (Dt1,Dt2,G1,G2,coupling,weight,vDt1,vDt2,vG1,vG2).

The ten equations are four original residuals, four J*v-forcing equations,
F0=0 and grad(F0)*v=0. Earlier six-dimensional wording counted only amplitudes
and parameters, omitting velocities. This has been corrected in current own
records; immutable154 is superseded by155. The earlier four-dimensional
fixed-state root theorem is unaffected.

The first four new intervals equal the earlier kernel-certified amplitude
regularity box. The remaining six use exact decimal-source fractions from the
old root JSON, widened by 10^-10*max(1,abs(lower),abs(upper)). The center is
the exact midpoint. C is a fixed exact dyadic-rational matrix selected from a
floating midpoint inverse. The input JSON supplies ONLY candidate rational
choices; all their mathematical proof obligations are independently checked.

The new box is WIDER than the old serialized joint root box. This proves
existence and uniqueness in the new box, not membership in the old narrower
box or correctness of all old external firstness/geometry/linkage claims.

## Actual interfaces and derivative proof

1. `M2ZeroMode` proves the candidate F0 exactly equals original A/(2*pi),
   1-rho*nonlinearQMoment0, the honest Laplace factor at s=0, the actual
   renewal determinant at s=0 and the physical Fourier factor at k=0.
   These identities hold at every amplitude, without a root hypothesis.
   Its explicit polynomial gradient is the true Frechet derivative; along
   any differentiable coordinate curve it gives the honest factor derivative.
   A separate positive-density, zero-amplitude counterexample proves that
   substituting s=0 into the quotient transform misses the true moment.
   That zero-amplitude point is not asserted to be a BH root.

2. `M2TangencySystem` retains all ten equations and proves their exact
   decomposition. The velocity equation is equivalent to the ORIGINAL
   actualPartial equation. Exact affine coupling dependence proves that
   the derivative of any actual differentiable root curve satisfies
   J*v=forcing. On the old regular amplitude box the analytic IFT constructs
   the local curve, and injectivity identifies its true derivative with v.
   Root, curve, velocity and stationarity are conclusions at a system zero.

3. `PolynomialNewtonMap` proves formal polynomial pderiv is a genuine
   Frechet derivative in the same finite Pi-space norm as the Newton-box
   criterion. `M2TangencyPolynomials` proves all ten candidate polynomials
   equal the actual system. `M2TangencyJacobian` proves all100 candidate
   derivative entries from formal pderiv. SymPy chooses expressions only;
   its algebra and differentiation are not trusted as mathematical premises.

## Numerical inequalities proved in Lean

`M2TangencyData` proves compatibility with the old amplitude box, positive
coupling, negative second-tail strength, center-to-face margin m>=10^-10
and a uniform radius R<=2*10^-9.

`M2TangencyJacobianBounds` proves all100 entry enclosures from the existing
real pi/reciprocal-pi and five rigorous exponential bounds. Signed four-corner
interval rules check every product, sum and outward rounding to denominator
10^24. `M2TangencyDefect` proves all100 defect bounds, then EVERY row sum

    sum_j abs((1-C*J(x))_ij) < 10^-6

on the complete ten-dimensional box. No external analytic interval is assumed.

`M2TangencyCenter` proves every RAW residual at the exact center has absolute
value <=10^-13. It separately proves the true Pi-space operator norm of C
at most50 by exact rational row sums. Thus

    ||C*F(center)|| <= 50*10^-13 = 5*10^-12.

This sufficient bound avoids unnecessary large cancellation/common-denominator
expansions of C*F. The earlier 10^-12 candidate target for the JOINT system was
never a verified claim and is not needed. All generated identities still
refer to the exact original system. The self-map arithmetic is

    10^-6*(2*10^-9) + 5*10^-12 = 5.002*10^-12 < 10^-10.

The already proved `NewtonBoxExistence` criterion discharges all remaining
obligations and constructs the unique joint zero. Original amplitude regularity
comes from the unchanged earlier four-dimensional certificate, uniform in b/K.

## Reproduction and completed verification

From this research package root, with the existing read-only SymPy/Flint
helpers on PYTHONPATH (their output is never a proof premise):

```sh
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/generate_m2_zero_mode.py > /tmp/M2ZeroMode.body
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/generate_m2_tangency_polynomials.py > /tmp/M2TangencyPolynomials.body
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/generate_m2_tangency_jacobian.py > /tmp/M2TangencyJacobian.body
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/generate_m2_tangency_certificate.py data > /tmp/M2TangencyData.body
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/generate_m2_tangency_certificate.py jacobian_bounds > /tmp/M2TangencyJacobianBounds.body
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/generate_m2_tangency_certificate.py defect > /tmp/M2TangencyDefect.body
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/generate_m2_tangency_certificate.py center > /tmp/M2TangencyCenter.body
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/check_m2_tangency_generation.py
python3 scripts/check_project.py
```

Generated bodies are compared to the source prefix before compiler-derived
axiom guards. The seven prefixes and all21 source/input fingerprints passed the explicit
replay. The full checker uses only the standard library to verify that receipt
before and after Lean compilation, and pins it in the validation metadata.
Controlled changes to an input hash and a prefix hash were rejected. Running
the checker with Python assertions disabled is rejected before metadata writes.
Full guarded validation and the independent post-run audit passed. Evidence is
`results/lean/validation.json` with its unedited raw `results/lean/build.log`.
Every recorded input, source, artifact and raw-log hash was checked. All 75
previous module sources, compiled artifacts and axiom footprints are unchanged,
as are all 530 frozen source/configuration hashes and the nine paper, eight
Mathlib and two separately locked raw LeanCode import pins. No new direct
external import or shared dependency build was introduced. Compiler style
warnings remain in the raw log; they are not proof failures.

The generated-prefix receipt has seven exact canonical prefixes and all 21
input hashes, checked before and after compilation. Canonicalization removes
only extra trailing LF bytes before restoring one LF. The receipt remains a
provenance record, not a mathematical premise. The existing independent
rational checks for M2 Jacobian, M2 second-root separation and M3 Arb witnesses
also passed read-only, without upgrading their external analytic premises.

## Mathematical obligations still open

Update2026-10-30: the separate `M2Curvature` extension now discharges positive
coupling curvature and the strict local minimum at this constructed boxed
contact. Its1065-guard/89-module checkpoint and independent audit passed;
see `codex_m2_curvature.md`. The list below records obligations beyond the
original stationary-contact result; weight transversality, firstness, PY
linkage and Taylor-radius questions remain separate.

Positive second derivative/minimum curvature, parameter transversality,
first-zero-mode-contact, PY-prefix/endpoint identification, all-wave stability,
complex-radius exclusion and Taylor radii are separate obligations. In
particular, a local analytic curve at this nonzero coupling is not identified
with the HS germ at coupling0. The old firstness/linkage/curvature reports and
M1/M3 analytic certificates retain their separate external status.

Generic mixture escape, nonisolated singular endpoint limits, positive-density
fiber certificates and generic multitailed Taylor lower bounds remain open.
No universal real-root/Taylor equivalence is asserted. Foundation1.0.17 and its
.lake outputs are read-only; TeX is untouched. No mathematical axiom is added.
Research remains active and unmerged.

## Verified negative controls

Two temporary copies of ACTUAL generated proof fragments were corrupted:
the last formal Jacobian entry was raised by1, and the first raw center
product lower endpoint was raised by1. Both are rejected by Lean proof
diagnostics with exit1. No repository proof was corrupted. Positive versions
and all ten complete module bodies compiled.
