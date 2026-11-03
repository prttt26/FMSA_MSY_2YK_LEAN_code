# Actual finite endpoint continuation, cluster loss and amplitude-escape radius

Date: 2026-10-28. Research over frozen foundation 1.0.17 / 06e3268.
New modules: `CanonicalEndpointContinuation.lean` (12 theorems),
`AmplitudeEscapeRadius.lean` (3 theorems). No new axiom or direct import,
foundation/TeX/numerical edit or merge-back. No endpoint value or continuity
of a given half-open branch at its excluded endpoint is assumed.

## Correct target and physical assumptions

Fix finite positive rates and diameters, nonnegative densities (arbitrary
tracers allowed), symmetric finite strengths K and nonzero actual vacancy.
Let p be a continuous ACTUAL BH root branch on [0,b), b>0, fully canonical
there. Its values at b and outside this domain may be arbitrary.

Prove the actual finite-boundary alternatives: a longer continuous canonical
initial root branch retaining every old value; arbitrarily large amplitudes
arbitrarily near b; or a genuine finite approaching CLUSTER root at coupling b
whose physical Fourier factor has determinant zero at some real frequency.
These alternatives do not claim a unique full limit for a noncanonical cluster,
and the last two need not be mutually exclusive.

Global existence of a maximal branch, automatic boundedness and a complex
Taylor-radius LOWER bound remain separate obligations. This result does not
rename a conditional supplied branch as a globally constructed one.

## Actual finite cluster root, no endpoint continuity

`bounded_prefix_has_cluster` uses the original finite-dimensional amplitude
norm. Take a sequence in [0,b) converging to b, obtained from real closure.
If norm(p(t))<=B on this prefix, its images lie in the compact closed ball;
a subsequence converges to some a with norm(a)<=B. No root, continuity or
canonical hypothesis is needed for this compactness step.

`actual_endpoint_cluster_isRoot` uses continuity of the actual POLYNOMIAL
residual along the joint sequence (t_n,p(t_n)) to prove a is an ACTUAL root
at coupling b. `actual_endpoint_cluster_mem_closure` proves a lies in the
closure of the genuine canonical amplitude set. A value p(b) is never used.

## A canonical cluster forces the whole left germ and a true limit

`canonical_cluster_gives_extension` is the substantive sheet step. Assume one
finite approaching cluster a is canonical. Its actual Jacobian inverse is
internally discharged by the existing full tracer theorem. The true analytic
IFT branch q through (b,a) is constructed, with q(b)=a, actual nearby roots
and proved nearby canonicity.

The IFT GRAPH uniqueness neighbourhood applies to the actual approaching
sequence, producing q(t_n)=p(t_n) at some point in a left interval where q is
analytic/canonical. The given continuous p and q are actual roots on that
connected interval. Connected root uniqueness, using q as the canonical first
branch, gives equality on the ENTIRE interval. Thus p=q on a left neighbourhood
of b, and p has the actual one-sided limit a. It is not merely a convergent
subsequence. Neither p's endpoint continuity nor its limit was assumed.
Only continuity and actual roots of p are needed for this canonical-cluster
step; canonicity of the original entire prefix is not an extra hidden premise.

`HasCanonicalLeftExtension` records the genuine analytic canonical extension
of the left germ. `left_extension_gives_longer_prefix` glues p below b and q
at/above b. Eventual left equality makes the glued function analytic near b;
relative continuity below b and nearby root/canonical data construct a curve
on [0,c), c>b, matching ALL old values on [0,b). This is the ordinary longer
continuous canonical-root notion `HasLongerCanonicalPrefix`, not merely an
unmatched analytic root elsewhere.

## Bounded prefixes: continuation or true Fourier-zero cluster

If the constructed finite cluster a is canonical, the preceding step gives
a longer prefix. Otherwise, our already-proved canonical-closure maximum-
modulus theorem excludes strictly-right zeros and locates a renewal zero on
the imaginary axis. The actual kernel-unit / physical-factor-unit equivalence
converts it to a physical Fourier determinant zero, including k=0 and every
zero-density species. No inverse density is used.

`bounded_prefix_continuation_or_axis_cluster` and
`bounded_prefix_continuation_or_physical_cluster` retain the full sequence
witness: t_n in [0,b), t_n->b, p(t_n)->a, norm(a)<=B, actual root at b,
canonical-closure membership and the true determinant zero. These are actual
boundary cluster states of THIS branch, not unrelated roots at that coupling.

`bounded_nonextendable_prefix_has_physical_cluster` applies when there is no
longer continuous canonical prefix preserving all old values. It does not
assume a finite continuous endpoint, an endpoint root or an endpoint zero.
The maximality premise here is explicit; existence of a globally maximal
branch is not claimed by this theorem.

`bounded_prefix_continues_of_endpoint_axis_units` gives the converse useful
criterion: a bounded prefix MUST continue if every possible norm-bounded
canonical-closure endpoint ROOT has physical factors invertible at EVERY real
frequency. The all-frequency premise is not replaced by a finite sample.

## Unbounded prefixes and the full boundary alternative

`unbounded_prefix_escapes_near_endpoint`: continuity bounds p on every compact
initial subinterval. Thus an unbounded [0,b) prefix has arbitrarily large
amplitudes arbitrarily close to b:

    for every B and every c<b, exists t in [0,b), c<t and B<norm(p(t)).

This is a subsequential escape / limsup statement, NOT norm(p(t))->infinity.
`finite_prefix_boundary_alternatives` proves continuation OR this near-endpoint
escape OR an actual physical Fourier-zero cluster root. For an explicitly
nonextendable prefix, `finite_nonextendable_prefix_boundary_obstruction`
retains the last two alternatives. Boundedness is never silently assumed.

## True amplitude escape excludes Taylor sums beyond b

`nonconvergence_beyond_amplitude_escape` takes a genuine smooth root germ g
with the same seed VALUE as p, plus the above actual canonical prefix and
unboundedness. Suppose all component Taylor series of g converge at r>b.
The frozen, proved `analytic_root_of_convergence_at` constructs an analytic
ACTUAL root q on (-r,r), through that seed. Connected actual root uniqueness
matches q to p on ALL of [0,b). But q is continuous on the COMPACT [0,b], so
it has one finite norm bound, contradicting the actual amplitude escape.
No finite p(b), fold or supplied Jacobian inverse is used.

A Fourier-zero cluster alone is NOT such an escape hypothesis and does not
automatically obstruct Taylor continuation: a noncanonical root may still be
a regular algebraic BH root. No radius upper bound by the physical first-loss
coupling is inferred from the bounded spectral-cluster alternative.

`amplitude_radius_le_escape_endpoint` applies the true common component
radius theorem to obtain R(g)<=ofReal(b). This is an UPPER bound. It does
not prove R=b or convergence/nonconvergence exactly at b.

`exists_intrinsic_germ_radius_le_escape` handles a branch specified only on
its initial nonnegative interval. The previously proved analytic-extension
theorem CONSTRUCTS the genuine germ g, EqOn p throughout [0,b), analytic there,
with an actual two-sided local root identity and positive radius. It then
proves 0<R(g)<=ofReal(b). No arbitrary negative-time values of p are treated
as analytic or differentiated to define the series. This connects the correct
boundary escape alternative to actual amplitude Taylor data, without a
universal real-root/Taylor iff or an all-stable-interval radius lower bound.

## Terminology correction from checking the actual factor

Earlier handoff 105 called `fourierFactor` a density-weighted Gram product;
that wording was wrong. Its ACTUAL definition is the density-weighted Baxter
factor I-S*Qhat*S. A Gram product requires the additional conjugate-transpose
multiplication. At the one-species HS seed it agrees with 1-Qhat_complex under
the proved density/phase dictionary. The Lean proofs always used these genuine
definitions; only the prose is corrected. Immutable 105/109 are corrected by
111, and the earlier own low-density note / main TODO are corrected. No proof
or numerical definition changed.

## Validation and remaining scope

All 15 new actual footprints were queried before guards and contain exactly
propext, Classical.choice and Quot.sound. Use `python3 scripts/check_project.py`.
Required complete coverage: 695 exact guards, 47 research modules + root / 48
pinned compiler commands; all 530 frozen source/configuration hashes; unchanged
nine validated paper pins / seven Mathlib pins and both separately locked
LeanCode source/cache pairs. All 45 previous module sources/artifacts/footprints
and EVERY input/source/artifact/raw-log hash are independently compared.
No new direct import, Lake/shared dependency build or merge-back.


Full validation and independent audit: PASS, 695 exact standard-three guards,
47 research modules plus root / 48 fixed compiler commands. EVERY research
input/source/artifact/raw-log hash matches. ALL 45 prior module sources,
artifacts and footprints are unchanged, as are all 530 frozen hashes, all
nine paper-validation-covered pins, seven Mathlib pins and both separately
locked LeanCode source/cache pairs. Results: `results/lean/validation.json`
and `results/lean/build.log`. No compiler remains live.

Still open: construction of a global maximal PY-connected canonical branch;
exclusion of finite amplitude escape for the physical parameter regions;
uniqueness/control of a full noncanonical endpoint limit; arbitrary unequal-
diameter mixture initial canonicity beyond low density; all-wave-number
parameter certificates; complex Taylor-radius LOWER bounds and complete tail /
all-density classification. No strict fold inequality, RDF positivity,
unexamined observable-series convergence or global-L2 amplitude-family
smoothness is inferred. The next global construction can use coherent unique
initial prefixes and their supremum; the proved boundary alternatives will
then apply to its finite endpoints.
