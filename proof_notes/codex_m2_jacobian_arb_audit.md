# Independent external M2 Jacobian audit (2026-10-28)

Handoff 138 supplies Claude's mpmath interval-AD regularity certificate.
Codex independently rechecked its conclusion with exact symbolic derivatives
and Arb, retaining the original `(D1,D2,G1,G2)` coordinates and residual scaling.
This is **external interval evidence, not a Lean proof**. Neither session's
certificate proves root existence, first instability or canonicity by itself.

## Inputs and independent calculation

Read-only root-box source:
`../MSA_and_1st_Truncation/results/coupling_singularities/codex_m2_zero_mode_firstness.json`,
SHA256 `d75a89d83c0c5fb80c3bdcf243e04c9de906384f1a1da4e573a3c518dff0cbb9`.
Only Claude's exact rational preconditioner is reused from
`results/two_tail/two_tail_m2_jacobian_interval.json`. Its stored Jacobian,
AD implementation, residual bounds and PASS flag are not reused. The source
hashes, exact rational C and all interval endpoints are in the new report.

Exact physical data are eta=1/10, rho=3/(5*pi), sigma=1, z=(9/5,12), K=(1,w).
The script independently specializes the literal `gam`, `Ct`, `Wt`, `mixM`,
`mixN`, `amplitudeA`, `amplitudeQp`, `Qhat` and both BH residual lines.
The dictionary and coefficient source hashes are recorded, including
`MSAConvergence/BHResidualPolynomials.lean`, whose evaluation theorems identify
its residual polynomials with the actual residual. The script transcription
and its derivatives themselves have not been checked by Lean.

SymPy differentiates the expanded exact symbolic residual. It checks residual
amplitude degree <=3, Jacobian degree <=2 and exact independence of tau and w.
Arb at 192 bits evaluates each derivative expression over the full amplitude
box. Pi and exp have genuine Arb enclosures; no physical coefficient is
rationalized, and no finite differences or float Jacobian is used.

JSON decimal endpoint tokens are parsed as exact decimal rationals. Each of
the first six intervals [l,h] is widened by the EXACT rational amount

    delta = 10^(-10) * max(1, abs(l), abs(h)),
    new interval = [l-delta, h+delta].

The script verifies by exact endpoint comparisons that its input Arb ball
contains that entire rational interval. This deliberately avoids the 53-bit
`mpmath.mpf` conversion and nearest-rounded decimal serialization issue in
138's input path. It does not manufacture a root-existence certificate.

Arb Jacobian enclosure endpoints are serialized as exact dyadic fractions.
The product `I-C*J(box)`, its interval bounds, row sums and final comparison
are then computed entirely with Python `Fraction`, starting from those stored
Jacobian endpoints. `check_m2_jacobian_rational.py` checks this rational part
independently using only the Python standard library. The analytic enclosure
of J remains dependent on the external SymPy/Arb calculation.

## Result and precise consequences

The default widened-box computation gives the upward-rounded bound

    ||I-C*J(u)||_infinity <= 9.99755712775e-8 < 1e-7 < 1,
    ||J(u)^(-1)||_infinity <= 58.4404856812.

The exact fractions in `results/certificates/codex_m2_jacobian_arb.json` are
authoritative; the displayed decimal upper bounds are rounded UP. This proves
externally that every actual BH amplitude Jacobian in the stated box is
invertible, for arbitrary fixed tau and w since J is independent of both.

There is also at most one root in this convex box at any FIXED tau,w.
Indeed, writing q for the certified bound, integration on the segment gives

    ||C*(R(u)-R(v))||_infinity >= (1-q)*||u-v||_infinity.

This uses the same fixed C throughout the box; pointwise invertibility alone
would not justify injectivity. Existence is still a separate obligation.
The interval residual contains zero in every coordinate, which checks
consistency but does not prove existence.

At a genuine root, regularity supplies local isolation. If that root is
identified as an approaching cluster of a given continuous actual root prefix,
then the existing formal theorem
`IsolatedEndpointLimits.actual_regular_cluster_has_limit` supplies the whole
left limit from its actual `EndpointRegular` premise; no global finite-fiber
enumeration is needed. With a canonical old prefix,
`RegularEndpointContinuation.regular_cluster_gives_extension` also supplies
an analytic root continuation retaining the whole old left germ.

**Formal gap retained:** the external interval conclusion has not been
instantiated as Lean's `EndpointRegular` for this numerical box. That would
require a proved coordinate-Jacobian identification and kernel-checked bounds
for the real constants/interval calculation. No hypothesis or new axiom is
introduced to conceal that gap. Nor has this note identified this control
point with the constructed maximal canonical endpoint. The original source
certifies a zero-mode contact; all-wave first-loss and branch-identification
claims must retain their own obligations. No generic finite-fiber claim,
nondegenerate fold, singular endpoint classification or Taylor-radius lower
bound follows.

## Reproduction and verification

The new scripts need python-flint and SymPy for the analytic enclosure;
the validated versions were python-flint 0.6.0 and SymPy 1.13.2. For this
session the dependencies are already available in `/tmp/codex_fmsa_arb_deps`:

```sh
PYTHONPATH=/tmp/codex_fmsa_arb_deps python3 scripts/certificates/codex_m2_jacobian_arb.py
python3 scripts/certificates/check_m2_jacobian_rational.py
```

The default replay is byte-identical. Independent reruns at 384 bits and at
relative widening 1e-12 also pass; their bounds are respectively
`9.99755712271e-8` and `1.10561798139e-8`. Corrupting the recorded norm,
a Jacobian entry, or a rational input-box endpoint is rejected by the
standard-library checker. A relative-widening=1 negative control fails the
strict contraction check and writes no PASS report.

No Lean source, configuration, existing validation record or compiler artifact
was changed. The existing 919 exact standard-three guards /63 research modules
plus root /64 compiler commands were not rerun; their entire input, source,
artifact and raw-log hash audit was rechecked successfully. All 530 frozen
source/config hashes and nine paper/seven Mathlib/two raw LeanCode pins remain
unchanged. No foundation script, shared build, TeX write or merge-back.
