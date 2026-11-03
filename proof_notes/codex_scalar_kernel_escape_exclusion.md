# Actual scalar kernel normalization and finite amplitude escape

2026-10-28. All 64 new theorems have compiled and their ACTUAL axiom reports
were queried: each uses exactly propext, Classical.choice and Quot.sound.
Exact guards, full-package validation and independent auditing have PASSED.
Foundation 1.0.17, TeX, Claude-owned notes/numerics and frozen caches are untouched.

## Proved exact statement

`canonical_roots_uniformly_bounded` proves that, for fixed finite positive
rates, positive one-species diameter and nonnegative density, actual canonical
BH roots with bounded finite strength matrices have uniformly bounded amplitudes
in their ORIGINAL norm. Vacuum uses the explicit affine root formula. Strength
signs are arbitrary; repeated and empty finite tail sets remain allowed. No
root curve, amplitude bound, source estimate or new mathematical axiom is supplied.
The bound is an existence theorem, not an executable numerical value.

`no_finite_canonical_amplitude_escape` excludes escape on every finite canonical
root prefix, even without a continuity premise. The finite constructed maximal
endpoint therefore has a genuine actual physical Fourier-zero CLUSTER root.
This does NOT give a full noncanonical endpoint limit or a complex Taylor-radius
lower bound. Boundedness does not assert a topological ProperMap:
the canonical root set need not be closed, and its limits can lose canonicity.

## Actual finite kernel and its source

`ScalarKernelSource` uses the existing CONTINUOUS recenteredBasis dictionary.
The compact observation map takes arbitrary finite coefficient data to their
honest kernel field in C([0,2*sigma],R), in a sup norm. This is a separate
codomain; no amplitude-space norm is changed. A linear section of its finite
image removes redundant coefficient directions, including repeated rates.

If compact data vanish, the core exponential polynomial vanishes on (0,sigma)
and the tail on (sigma,2*sigma). The analytic identity principle makes both
continuations zero globally. Their difference at sigma+t is

    Qp*t + (A/2)*t^2 + sum C_u*(1-exp(-z_u*t)).

Its genuine derivative is the source numerator. Hence every kernel-null
direction is source-null. Honest positively damped integrals factor through
the compact kernel image and acquire a pure linear norm bound. The actual BH
coefficient map and the actual source transform identify this functional with
secondRHS at z_u. Actual weighted compact data are proved equal to the actual
row-density causal kernel, at every point of the interval, without a root
premise. This source estimate also covers each positive-density row of general
mixtures; scalar escape exclusion does not automatically extend to matrices.

## Honest half-plane symbols and normalized limits

`FiniteKernelLaplace` proves integrability on the entire CLOSED right half-plane,
including zero, before exchanging a finite sum and the integral. Equal compact
observations determine the entire nonnegative kernel and every honest Laplace
symbol. The compact sup norm controls these symbols uniformly at ALL closed-
right frequencies. Laplace injectivity proves that a nonzero compact field
cannot give the identically zero symbol on the open half-plane.

The finite field is identified with the genuine free finite q dictionary and
its causal extension before applying QhatComplex. This proves holomorphy and
joint coefficient/frequency continuity in the open right half-plane. Dominated
convergence proves the honest symbol tends to zero along the positive real
axis. Thus a nonzero constant minus a symbol is nontrivial too.

The proved reciprocal maximum-modulus closure theorem can now be applied to
families a-L(q): a nonzero constant OR nonzero actual compact field rules out
an identically zero limit. Nonzero scalar factors remain nonzero in the OPEN
right half-plane. This does not assert nonvanishing on its boundary.

## Proved root-sequence normalization argument

For positive fixed rho, write q for the actual weighted compact kernel and
v=(1,q) in R times the finite actual-kernel image. Normalize by r=1/norm(v)>0.
The frames r*v have norm ONE. Reduced coefficients supplied by the continuous
linear section reproduce the whole scaled actual field, not merely samples.
The normalized factor is exactly r*(1-L(q)), hence zero-free by actual
canonicity. Both normalized BH identities are derived from the actual equations:

    Dt_u * F_normal(z_u) = r * (2*pi*K_u/z_u),
    G_u * rho * 2*pi * F_normal(z_u) = sourceMap_u(reduced normalized kernel).

For bounded K, take a convergent subsequence of (K,normalized frame) in a compact
finite-dimensional ball. The frame limit has norm one. Its constant and field
parts cannot BOTH vanish; the normalized-symbol closure theorem therefore
makes the limiting factor nonzero at EVERY positive z_u. Continuity of the
linear source and the two displayed equations then give convergent Dt/G
coordinates by division by those nonzero limiting factors. A sequence of
canonical roots with amplitudes tending to infinity is consequently impossible,
by the compiled `canonical_root_sequence_has_convergent_subsequence`.
The limiting root need NOT remain canonical.

`vacuum_root_sequence_has_convergent_subsequence` uses the actual fixed-density formula
Dt_u=2*pi*K_u/z_u and
G_u=(1+z_u*edgeHi)/(z_u)^2+sum_t K_t/(z_u+z_t), with no division by rho.
Its continuous affine strength dependence proves the corresponding compactness.
`nonnegative_canonical_root_sequence_has_convergent_subsequence` combines the
two cases. A sequence with norm above n would have a convergent subsequence,
which proves the uniform bound on ALL canonical roots at bounded strengths.
`canonical_prefix_uniformly_bounded` applies it with strength norm b*norm(K).

`maximal_finite_prefix_bounded` supplies the bound for the constructed maximal
branch, and `maximal_finite_endpoint_has_physical_cluster` combines it with
actual maximal nonextendability / cluster continuation. The resulting sequence
approaches the excluded finite endpoint; its amplitude limit is an ACTUAL root
in canonical closure and has det(fourierFactor(a,k))=0 at some real k, possibly
zero. No value of the arbitrary representative AT the excluded endpoint is used.
The physical factor is I-S*Qhat*S, the density-weighted BAXTER factor.

`exists_hs_maximal_branch_with_finite_axis_cluster` constructs the maximal branch
from physical scalar HS DATA alone at EVERY eta<1, then gives that finite-endpoint
cluster alternative WITHOUT the old escape disjunct. It supplies no root curve,
inverse, initial canonicity, maximality, amplitude bound or endpoint-limit premise.
The branch's intrinsic Taylor criterion is still beta<=R, not automatic equality.

The scalar zero-free-limit step does NOT transfer to matrix factors: a
normalized matrix limit can be identically singular. General mixture escape,
general unequal-diameter initial canonicity beyond low density, full noncanonical
limit control and complex Taylor LOWER bounds / tail-all-density classification
remain open. No universal real-root/Taylor iff is inferred.

## Verification status

PASS: 786 exact standard-three guards across 52 research modules plus root,
53 direct pinned compiler commands. All 64 new actual reports were queried
before generating guards; each is exactly propext, Classical.choice, Quot.sound.

Independent audit checks EVERY input/source/artifact/raw-log hash; ALL 49 prior
module sources/artifacts/axiom records unchanged; all 530 frozen source/config
hashes, all nine validated-paper / seven Mathlib / two separately locked
LeanCode source-cache import pins unchanged. No new direct import, shared/Lake
build, foundation/TeX/numerical edit or merge-back. Evidence:
`results/lean/validation.json` and `results/lean/build.log`.

The main Markdown TODO records exact theorem names, scope and proposed SI
correspondence. The constructed INITIAL domain is unchanged; later stable
islands are not appended. No paper/TeX build is run.
