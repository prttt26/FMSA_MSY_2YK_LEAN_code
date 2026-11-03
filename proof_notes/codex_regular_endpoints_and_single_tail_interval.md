# Regular endpoint limits and one-attractive-tail interval convergence

2026-10-28 local. Two modules, 28 new theorems. All have compiled and their
ACTUAL axiom reports were queried before exact guards: each contains exactly
propext, Classical.choice and Quot.sound. Full-package validation and the
independent hash audit have PASSED. Foundation 1.0.17 is frozen;
no TeX, shared cache build, numerical file or Claude-owned note is modified.

## Actual regular clusters, without a supplied endpoint limit

`RegularEndpointContinuation.EndpointRegular` is the EXACT actual residual
amplitude partial at (b,a): fderiv of the existing polynomial BH residual,
composed with the amplitude inclusion. It is not an alternative residual,
assumed inverse formula or assertion of endpoint canonicity.

`regular_cluster_gives_extension` takes physical data, a continuous canonical
actual root prefix on [0,b), b>0, and ONE approaching sequence t_n<b with
p(t_n)->a and t_n->b. The actual partial at (b,a) is assumed invertible as an
explicit local regularity condition. No full limit, endpoint value p(b),
boundedness, canonicity of a, or canonical neighbourhood of a is supplied.

The actual residual is analytic and a is a root by continuity. The analytic
IFT at (b,a) constructs q with q(b)=a. Eventually the approaching sequence
lies in the IFT graph neighbourhood, hence p(t_n)=q(t_n). On a connected left
interval J the original p is canonical, so its own actual amplitude partial
is invertible there by the proved canonical-to-Jacobian bridge. The coincidence
set of p and q is relatively closed by continuity, relatively open by local
root uniqueness at p, and nonempty by the sequence. Thus p=q on ALL of J.
Importantly q is never assumed canonical on J or beyond b.

This proves a two-sided analytic actual ROOT extension of the whole left germ,
and the genuine finite limit p(t)->a as t approaches b from below. Every other
approaching cluster equals a (`endpoint_cluster_unique_of_left_limit`).
`analytic_left_extension_gives_longer_root_prefix` glues q to ALL original
prefix values, obtains a strictly longer continuous root prefix and is analytic
through b, with endpoint value a. It does not enlarge the canonical interval.
The arbitrary original representative p(b) is never used as the endpoint state.

`left_limit_bounds_entire_prefix` combines a bounded neighbourhood from the
true finite left limit with a compact earlier subinterval. It gives an honest
ORIGINAL-norm bound on the entire prefix. Consequently:

- ONE regular finite cluster bounds the whole canonical prefix, without a
  supplied bound (`regular_cluster_bounds_entire_prefix`);
- if no full finite left limit exists, ALL finite approaching clusters have
  singular actual amplitude partials (`no_full_limit_forces_singular_clusters`);
- an unbounded canonical prefix can have no REGULAR finite cluster
  (`unbounded_prefix_forces_singular_clusters`). This does not supply a finite
  cluster in the escape case or exclude matrix escape.

A true physical Fourier-factor zero is noncanonical, including k=0/tracers,
by the actual phase/Sylvester factor-unit dictionary, without a BH-root-only
OZ implication (`physical_zero_not_canonical`). `ResolvedPhysicalEndpoint`
retains the full actual sequence/root/canonical-closure/physical-zero certificate
and separates a singular actual cluster from the regular case above.

The general constructed maximal branch has escape OR this refined physical
endpoint resolution (`maximal_finite_boundary_resolution`). In the scalar case
the existing proof excludes escape, so this resolution is unconditional at
every finite endpoint. The two HS data-only branch constructors are connected
by `exists_mixture_hs_branch_with_endpoint_resolution` and
`exists_scalar_hs_branch_with_endpoint_resolution`. General singular-cluster
full-limit control is NOT proved merely by splitting these cases.

## Singularity is not automatically an identified fold

Here singular means exactly noninvertibility of the genuine amplitude partial.
A certified nondegenerate fold needs its own rank/kernel, transversality and
quadratic nondegeneracy hypotheses. A cluster also does not give a unique full
endpoint or identify the specified first fold on the same sheet. Therefore the
remaining general singular-limit issue is related to possible strictness failure,
but an unconditional equivalence with tau_inst=tau_f is not asserted.

The frozen `SingleTailSpinodal` theorem gives a zero-mode point before the
explicit fold in its positive one-species, one-attractive-tail class. The next
module connects that result to the actual constructed initial canonical branch;
it does not use a conjectured multi-tail analogue.

## One attractive tail: strict canonical-endpoint/radius separation

`SingleTailCanonicalRadius` assumes one species, a unique tail index, strictly
positive rate, density, diameter and attractive strength, and positive vacancy
(eta<1). These are physical DATA. No root curve, seed canonicity, Jacobian inverse,
coefficient sign, fold identification or radius lower bound is supplied.
Vacuum is NOT silently included in the positive-density quartic assumptions.

Let M be the actual data-constructed maximal initial canonical HS branch,
beta=M.bound (extended nonnegative real), R its intrinsic common Taylor radius,
and f=SingleTailRadius.foldCoupling. The module proves

    0 < beta < R = ofReal(f) < infinity.

`maximal_radius_eq_fold` applies the frozen actual one-tail radius theorem to
the TRUE analytic germ of M, with its actual seed and local root equations.
That frozen theorem proves the required all-order signs and fold/radius equality
internally; no Pringsheim/sign hypothesis is added here.

`maximal_path_eq_explicit_before` matches M to the explicit actual quartic
branch on the overlap before both beta and f. Connected root uniqueness uses
regularity ONLY along M's canonical prefix; the explicit branch is not assumed
canonical until the fold. This distinction is necessary because it loses
canonicity strictly earlier.

`maximal_bound_le_zero_before_radius` takes the frozen genuine Fourier-zero-mode
witness at a positive t<R. Since R=f, the explicit root is analytic up to t.
If t lay inside M's canonical interval, overlap matching would identify M(t)
with this noncanonical Fourier-zero root, a contradiction. Thus

    beta <= ofReal(t) < R,

and `maximal_bound_lt_radius` gives the STRICT inequality. The witness is an
upper bound on beta; it is NOT proved to be the FIRST instability, and no
first-wave-number k=0 assertion is made.

`maximal_whole_initial_interval_hasSum` now discharges the complex-radius
condition in the exact intrinsic criterion: ALL actual amplitude Taylor series
sum to the ORIGINAL constructed branch throughout the ENTIRE initial canonical
interval. This is a proved class-specific lower bound, not an inference from
real root existence or real-axis regularity alone.

## Full endpoint and sums beyond the canonical interval

Since beta is finite and beta_real<f, the explicit actual quartic root is
analytic at beta_real. Overlap matching identifies the whole old left germ
with it (`maximal_endpoint_explicit_extension`). Therefore this single-tail
class has the UNIQUE full noncanonical endpoint limit without any assumed
endpoint regularity/full limit, even if that regularity has not been separately
certified. All approaching clusters equal the explicit limiting state.

`maximal_endpoint_physical_zero` identifies the earlier actual scalar physical
Fourier-zero cluster with that full limit. The explicit endpoint is an ACTUAL
BH root in canonical closure, is noncanonical, and has a true physical Baxter
factor zero at some real k, possibly zero. This is a statement about the genuine
limiting root, not the arbitrary M.path value at the excluded endpoint.

`maximal_endpoint_longer_root_prefix` retains ALL old values and constructs a
longer continuous actual ROOT branch analytic through beta_real. Later stable
islands do not alter the user-chosen initial canonical domain.

`maximal_taylor_sums_to_explicit_until_fold` uses the true same-seed coefficient
identity and the explicit analytic branch to prove that the HS Taylor series
sum to the EXPLICIT actual root for EVERY 0<=tau<f. Thus they converge AT the
excluded canonical endpoint and at real couplings beyond it. In particular
`maximal_endpoint_taylor_hasSum` gives the actual full limiting root as the
endpoint sum. No series identity is inferred from arbitrary out-of-domain
values of M.path. No verdict at tau=f is asserted; the interval remains open
at the fold.

`exists_hs_branch_with_strict_radius_and_limit` constructs M and these strict
radius, whole-initial-interval-sum, finite-endpoint, unique-limit and actual
analytic-extension conclusions from physical data alone.

## Still open and limits of scope

General finite MATRIX amplitude escape, full limits at general singular
noncanonical clusters, generic multi-tail complex Taylor-radius LOWER bounds,
and tail/all-density classification remain open. The single-attractive-tail
positive-density class now has its whole initial canonical interval and full
endpoint control proved. Vacuum has a separate affine root formula and is not
covered by the positive-density quartic argument in this module.

No first-instability-k=0 theorem, physical RDF positivity, extension of the
initial canonical domain, all-observable convergence, generic beta=R assertion,
or universal real-root/Taylor equivalence is inferred. The one-tail result is
instead beta<R=fold, and is consistent with Taylor sums beyond canonical loss.

## Validation and correspondence

PASS: 866 exact standard-three guards across 60 research modules plus root /
61 direct pinned compiler commands. All 28 new actual footprints were queried
before exact guards. Independent post-run audit checks EVERY input/source/
artifact/raw-log hash; ALL 58 previous module source/artifact/footprint records
remain unchanged. All 530 frozen source/config hashes, nine validated-paper /
seven Mathlib / two separately locked LeanCode source-cache import pins remain
unchanged. No new direct dependency import or shared/Lake build. Evidence:
`results/lean/validation.json`, `results/lean/build.log`; reproducible checker:
`python3 scripts/check_project.py`.

The main Markdown TODO records exact theorem names and proposed SI
correspondence after PASS. Cite the regular-cluster theorem with its
explicit actual partial-invertibility hypothesis; cite the data-only single-
attractive-tail constructor separately, where radius/sign/fold/limit premises
are internally discharged. Do not generalize this tail class to arbitrary
mixtures or competing tails. No paper/TeX build is run.
