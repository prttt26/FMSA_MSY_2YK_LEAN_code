# Actual canonical neighbourhoods, analytic germs and first Fourier-axis loss

Date: 2026-10-28. Isolated research over frozen foundation 1.0.17 / 06e3268.
No new mathematical axioms, foundation/TeX/numerical edits or merge-back.

CanonicalNeighborhood adds 12 theorems; ActualCanonicalBranch adds 19;
HolomorphicZeroPersistence adds 1; CanonicalFirstLoss adds 16: 48 in total.
These connect the actual nonnegative-density Jacobian theorem to genuine
local canonical continuation, intrinsic Taylor germs and the initial-interval
radius criterion. They also prove finite continuous first loss occurs on the
Fourier axis, and establish full canonicity along a connected path from a
canonical seed if EVERY real-frequency physical factor is a unit.

## Actual full canonicity is open

Fix positive rates and nonnegative diameters. Density signs are unrestricted
for this off-root analytic result. Let q(p) be the ACTUAL row-density causal
kernel and qhat(p,s) its honest Laplace integral. At fixed z/rho/sigma it is

    qhat_ij(p,s)=sum_b c_ijb(p)*K_ib(s),

where c are genuine smooth BH coefficients, and K are transforms of the
actual fixed recentered basis with row factor rho_i. Each basis has a PROVED
L1 mass M_ib; for EVERY Re(s)>=0, including zero, norm(K_ib(s))<=M_ib.
Consequently

    complexNormSum(qhat(p,s)-qhat(p0,s)) <= D(p,p0),
    D(p,p0)=sum_ijb abs(c_ijb(p)-c_ijb(p0))*M_ib.

This true finite budget is nonnegative, continuous in the EXISTING amplitude
norm, and zero at p=p0. Fixed-base full canonicity already supplies a uniform
bound C on (I-qhat(p0,s))^(-1) throughout that closed half-plane. When
(C+1)*D(p,p0)<1, a finite-matrix inverse perturbation proves I-qhat(p,s) is a
unit everywhere on the same domain. Such p form a neighbourhood of p0.
Thus `canonical_amplitudes_isOpen` proves the ACTUAL canonical amplitude set
is open. This requires a small CHANGE, not a small physical base kernel;
no density inverse, root, nearby canonicity hypothesis or norm alias is used.

## Actual local roots and continuation uniqueness

For root statements retain positive rates/diameters, rho>=0 (including
arbitrary tracers), nonzero actual free volume, symmetric prescribed K and an
actual BH root at arbitrary real coupling t0. Full base canonicity discharges
the actual residual amplitude `.IsInvertible` by the preceding tracer theorem.
The frozen polynomial residual is real analytic. Mathlib's analytic implicit
function theorem therefore CONSTRUCTS a two-sided local analytic root p with
p(t0)=a. Its continuity and proved canonical openness make it canonical on
a neighbourhood too. No root curve or nearby canonical family is supplied.

`exists_analytic_extension_of_relative_root` extends ANY continuous relative
root germ at a canonical base, including a one-sided endpoint germ. Genuine
IFT graph uniqueness proves the extension agrees on a relative neighbourhood.
`actual_canonical_roots_eqOn_of_preconnected` proves continuous root paths
agree everywhere on a preconnected parameter set after one meeting, assuming
only the FIRST path remains canonical. Continuous limiting endpoints agree
without assuming endpoint regularity or uniqueness there. These statements
construct local continuation and prove sheet matching; they do not prove an
arbitrary branch has a finite canonical limit or remains bounded globally.

## The single-sided branch and its true Taylor germ

The ordinary radius criterion applies to a branch already defined with a
two-sided root germ at zero. Its supplied Jacobian inverse is now replaced
by actual root/full-canonicity hypotheses, with no density positivity gap.

For a branch specified only on the initial interval, a stronger interface is
needed. With bound>0 (possibly infinity), assume only ContinuousOn p on

    initialCouplings(bound)={t : 0<=t and ofReal(t)<bound},

actual roots there and full canonicity there. Whole-line continuity at zero
and a two-sided root germ of the ORIGINAL p are NOT assumed. A true implicit
analytic germ q through p(0) is constructed. Relative IFT uniqueness proves
p=q on a right neighbourhood of zero. Define e(t)=p(t) for t>=0 and q(t)
for t<0. Then e is analytic at zero, equals p on the ENTIRE initial interval,
is analytic throughout it, and has a genuine two-sided canonical root germ.
Its common Taylor radius is strictly positive.

`exists_canonical_series_extension` gives the exact criterion

    AmplitudeHasSumTo e p bound <-> bound <= amplitudeRadius(branchCoefficients e).

Coefficients come from the TRUE analytic extension e, and the sums equal the
ORIGINAL prescribed p at every coupling of that interval. The arbitrary
negative-time values of p are not silently assumed analytic or differentiated
to define this series. Actual root-germ uniqueness proves coefficients and
radius independent of which analytic extension is chosen. For the HS-reference
series select p(0)=(0,baseSeed); the theorem does not impose that selection
implicitly. Equality at a finite endpoint is allowed since that endpoint is
excluded. An infinite endpoint requires an entire common Taylor germ.

This is an AMPLITUDE/root-branch criterion. It does not supply the complex
radius lower bound, claim real-root/Taylor equivalence or assert convergence
of every unexamined infinite-volume observable.

## Maximum modulus bypasses Hurwitz/Rouche

Pinned Mathlib's complex-analysis files have no named holomorphic Hurwitz/
Rouche theorem found in the local search. No such theorem is axiomatized.
`HolomorphicZeroPersistence.zero_free_at_closure` proves the needed zero-free
limit principle from EXISTING isolated zeros and reciprocal maximum modulus.

For a continuous parameter family F(p,s), let p lie in the closure of a
parameter set whose functions are holomorphic and zero-free on connected
open U. The actual limit function is assumed holomorphic and nontrivial,
and joint continuity is supplied at p and each point of U. If F(p,s0)=0,
isolated zeros and the identity principle give a small disc inside U with
zero-free boundary. Compactness gives a positive boundary minimum m.
Joint continuity gives nearby boundary modulus >m/2, while nearby centre
modulus is <m/2. Choose a zero-free parameter from the closure property.
Its reciprocal is holomorphic on that disc. Existing maximum modulus bounds
its centre inverse norm by 2/m, contradicting the small centre modulus.
This argument needs neither root counting nor an argument-principle API.

## Actual first loss lies on the Fourier axis

For d(p,s)=det(I-qhat(p,s)), the actual finite coefficient-distance bound
and fixed-amplitude frequency continuity prove JOINT parameter/frequency
continuity on Re(s)>0. Existing actual integral holomorphy proves d is
holomorphic there. The fixed-limit outside-compact unit theorem supplies
one nonzero positive-real-frequency value, so the limit determinant is NOT
identically zero. A UNIFORM nearby high-frequency cutoff is unnecessary.
All hypotheses of the generic zero-free closure theorem are discharged.

Thus closure of actual canonical amplitudes has no zero with Re(s)>0.
If a closure point is not fully canonical, its genuine closed-right zero
must have Re(s)=0, hence equals i*k for a real k, possibly zero.

`actual_first_loss_exists_real_frequency` assumes t*>0, ContinuousOn p on
[0,t*], full canonicity on [0,t*) and noncanonicity at t*. It proves an actual
imaginary-axis determinant zero. The positive prefix is essential: t*=0
would leave an empty prefix and cannot imply this conclusion. A finite
CONTINUOUS endpoint is explicit; existence of such a first-loss endpoint is
not supplied. This implements Claude 099 with the maximum-modulus route
reported in 100–101.

`kernel_unit_iff_physical_factor_unit` proves BOTH directions of the genuine
kernel/physical Baxter factor correspondence at EVERY real k, including zero
and zero-density species. Fixed phases are units, and Sylvester swapping uses
S*S=diag(rho) without inverting S. With rho>=0 the first-loss kernel zero is
therefore a physical Fourier-factor determinant zero at a real k.

A transverse actual BH fold cannot be canonical since the actual amplitude
Jacobian is surjective there if canonical. It has some closed-right zero;
that zero need not lie on the axis for an ARBITRARY fold after stability is
already lost. For the finite continuous FIRST loss, the axis conclusion and
its nonstrict ordering t*<=fold are proved together. STRICTNESS is not proved.
No sign change, winding sample or finite grid is used as mathematical proof.

## The full axis-to-canonicity path bridge

On ANY continuous amplitude path with preconnected real parameter set, the
canonical preimage is relatively open by proved canonical openness. Under
axis nonvanishing at every path point and EVERY real wave number, it is
also relatively closed: a noncanonical closure point would have the axis
zero just ruled out. A canonical seed and connectedness therefore make the
whole path canonical.

`canonical_path_of_physical_factor_units` expresses that bridge with genuine
physical Fourier factors, including k=0 and tracers. A pointwise axis test
at one amplitude alone is not substituted for full canonicity. A finite grid
cannot replace the all-wave-number premise.

`exists_series_extension_of_physical_axis_units` composes this actual path
bridge with the single-sided branch/Taylor construction. Its premises are a
continuous actual root branch on the initial interval, one FULL canonical
seed, and physical factor units at EVERY real k throughout the interval,
plus the original rate/diameter/density/volume/strength hypotheses. The true
series sums to the original branch exactly iff its common radius reaches the
endpoint. No Jacobian inverse or two-sided original branch germ is assumed.

## Remaining work and validation

Initial PY canonicity, global branch existence/continuation without finite
amplitude escape, endpoint control, all-wave-number parameter certificates,
complex Taylor-radius bounds and tail/all-density classification remain open.
The constructed local continuations and conditional finite first-loss/path
bridges do not supply these global premises. No RDF positivity or global-L2
amplitude-family smoothness is inferred, and no universal real-root/Taylor
convergence iff is claimed.

All 48 actual compiler footprints were queried before exact guards and are
exactly propext, Classical.choice, Quot.sound. Final combined validation: PASS, **651 exact standard-three guards across
42 research modules plus the root**, with 43 direct pinned compiler commands.
EVERY input/source/artifact/raw-log hash was independently checked; all 530
frozen source/configuration hashes, previous seven foundation/four Mathlib
pins and new two/two cached pins remain unchanged. Reproduce using
`python3 scripts/check_project.py` from this isolated research package.
Two cached validated FMSAPaper direct imports (StableIntervalRadius and
RegularContinuation) extend the previous seven pins to nine; all old pins
are preserved. Existing cached Mathlib AbsMax and Analytic.IsolatedZeros
extend the previous four direct pins to six. These artifacts are read only,
hashed before/after, and no Lake/shared dependency build is invoked.
