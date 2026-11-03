# Positive-density mixture amplitude escape excluded: actual covariance proof

2026-11-01. Research package only; foundation 1.0.17 and TeX remain untouched.
This follows the proved binary result in `codex_binary_kernel_escape_exclusion.md`.
Finite amplitude escape is now EXCLUDED for arbitrary fixed POSITIVE species
densities and positive diameters, finite signed/repeated positive tail rates,
reciprocal strengths, nonzero vacancy and actual full canonicity. The ORIGINAL
product/Pi amplitude norm is retained. No amplitude bound or new axiom is
assumed. Zero-density tracer amplitudes remain a distinct OPEN extension.

## Proved ingredients

`CompactSpectralTest` contains 11 public theorems, with actual queried footprints
exactly propext, Classical.choice and Quot.sound. For

    profile(r) = max(1-|r|,0)^2,
    f(x) = x*(2+cos x)-3*sin x,

the honest existing radial Fourier integral, away from zero, is

    radial_fourier(profile,k) = 8*pi*f(k)/k^5.

The sine integral is evaluated by an explicitly differentiated primitive and
the interval integral fundamental theorem. Strict positivity is proved at all
nonzero frequencies. Three derivative comparisons give f(x)>=x^5/120 on [0,1];
f(x)>=x/2 for x>=6. Positivity and compactness handle [1,6]. Hence there exists
c>0 such that

    c/(1+k^2)^2 <= radial_fourier(profile,k),  k != 0.

The positive spatial-dilation identity is proved for arbitrary radial data,
with the exact R^3 volume factor. It gives the same polynomial lower bound for
profile(r/R), at ANY R>0. The unit radial mass integral is exactly 1/30, before
angular and radius factors. These are integral theorems, not numerical grids.
The existing radial transform definition assigns zero at k=0; the positivity
and lower-bound statements explicitly exclude it. An eventual spectral
integral estimate may discard that singleton, but cannot assert pointwise
positivity at zero for this convention.

`ActualStructureCovariance` contains eight public theorems with the same
standard-three footprint. Full actual closed-right-half-plane canonicity
supplies actual excess decay and integrability. It replaces the old small
weighted-kernel-budget premise in the actual non-tangent h Fourier identities.
The genuine odd RDF moment is L1. Its actual half-line Fourier-axis transforms
have the finite excess/background representation. The excess plus its FINITE
rational background is exactly (2*pi)^(-1) times the completed J symbol.
Uncancelled affine G is not assigned a divergent imaginary-axis integral.

The actual h-moment transform retains the fixed -1/s^2 core term. Its
plus/minus frequency difference cancels that fixed term and proves

    actual radial Fourier h = completedRadial.

This is a VALUE identity, proved from the actual integrals; a tangent identity
is not substituted for it. At an actual symmetric-strength BH root, finite
OZ at the value and density conjugation then prove

    S(k) = I + sqrt(rho) * actual_hhat(k) * sqrt(rho), k != 0,

where S is the existing physical inverse denominator. Its strict positivity
therefore applies to the HONEST constructed covariance symbol. Diameters can
be unequal, tail matrices can be noncommuting, and densities may be zero.
There is no supplied covariance/OZ premise, small kernel norm, pointwise g>=0,
amplitude bound, or new axiom. Positive rates and diameters, nonnegative
fixed densities, nonzero vacancy, actual root equations with reciprocal K,
and full canonicity are the physical premises.

## Proved uniform covariance trace bound

`RadialCovarianceBounds` adds ten public theorems, again exactly standard-three.
It proves actual base h positive-radius L1 and odd-field global L1/L2 from
canonical excess decay. A genuine radial Parseval pairing is proved using
the honest integral Fourier transform and the existing L2/integral bridge.
The scaled compact test supplies its own L1/L2 premises. Whenever
0<R<sigma_ij, the ACTUAL h/test spectral pairing is exactly the fixed negative
hard-core moment, independent of amplitudes and strengths.

The test weight is itself proved L1: the unit weight is continuous, nonnegative
and has a quadratic high-frequency bound; a fixed integrable majorant and the
proved spatial dilation handle every positive scale. No test-integrability
hypothesis is passed to the physical estimate.

With Mathlib frequency w, define

    beta_R(w) = w^2 * radial_fourier(profile(r/R), 2*pi*w).

`actual_structure_weighted_trace_bound` proves, for EVERY actual canonical
reciprocal root at fixed nonnegative densities and positive diameters,

    Integrable(beta_R(w) * re(trace(S(2*pi*w)))),
    integral beta_R(w) * re(trace(S(2*pi*w)))
      <= N * integral beta_R(w).

The right side contains only the fixed test radius and species count. It
has no K or amplitude dependence. The proof uses the ACTUAL covariance identity
and actual hard-core Parseval pairing, treats w=0 almost everywhere, and
retains the original amplitude norm. Tracers are allowed in this estimate.
The exact evaluation of the frequency-only test mass is unnecessary; the
right side is already a finite constant supplied by a proved L1 theorem.

## Proved density-weighted inverse control

`CanonicalInverseCovariance` adds six standard-three theorems. The inverse
physical Gram trace is the exact sum of squared inverse entries. The actual
causal factor A and physical factor B obey a phase/density intertwining;
the intertwiner is never inverted. On the Fourier axis this gives the exact
identity

    rho_j * norm(A(i*k)^(-1)_ij)^2
      = rho_i * norm(B(k)^(-1)_ij)^2,

including zero densities. Thus the left side is bounded by rho_i*trace(S(k)).
The true causal inverse is continuous on the whole Fourier axis under full
canonicity. Combining this pointwise bound with the already proved actual
test-weight trace estimate yields integrability and the UNIFORM bound

    integral beta_R(w) * rho_j * norm(A(i*2*pi*w)^(-1)_ij)^2
      <= rho_i * N * integral beta_R(w).

This contains no strength or amplitude bound and covers nonnegative densities.
It controls weighted inverse boundary entries. Interior point values are
now proved below; the full unweighted amplitude norm for tracers stays open.

## Proved interior inverse and first-amplitude bounds

`CausalLaplaceL2`, `RegularizedInverseField` and
`CanonicalInteriorInverseBounds` add fourteen standard-three proofs. The
actual causal filter (1-t)*exp(-t) constructs an honest L1/L2 time field whose
Laplace transform is s/(s+1)^2 times the TRUE actual causal inverse. Integral
Fourier Plancherel and an explicitly proved positive-time Cauchy-Schwarz
estimate turn the uniform boundary budget into positive-real point bounds.
No Hardy-space axiom, supplied time field, amplitude bound or decay constant
is used. Density-weighted point bounds include zero densities; unweighted
inverse point bounds require every fixed density positive. At each fixed
s>0 the constant is independent of ALL K, D and G.

`MixtureFirstAmplitudeBounds` adds four standard-three proofs. The ORIGINAL
transposed first BH equation yields the exact identity

    D_u * rho = ((2*pi/z_u)*K_u) * rho * transpose(A(z_u)^(-1)).

The density intertwiner is not inverted in this identity. Positive fixed
densities and the derived inverse bound then give a uniform bound for the
ORIGINAL full first-amplitude Pi norm over bounded strengths. A finite
canonical prefix cannot escape through D alone. All finite signed/repeated
positive tail rates, unequal diameters and arbitrary reciprocal strength
matrices are covered. G is now controlled by the next stage.

## Proved second-amplitude bounds via an actual Yukawa convolution test

Six further modules add 29 public standard-three theorems:

- `YukawaConvolutionTest` (13): let f_R(t)=t*profile(t/R) and
  e_s(t)=exp(-s*abs(t)); H=e_s*f_R is an actual L1/L2 continuous odd field.
  Define psi(r)=H(r)/r, using the existing zero-division convention at r=0.
  Its odd radial field is EXACTLY H, including the origin. Actual integral
  Fourier convolution, with the correct Mathlib frequency, proves
  abs(radial_fourier(psi,k)) <= (integral e_s)*radial_fourier(profile(r/R),k)
  for k!=0. No guessed transform or supplied membership is used. For r>=R,
  H(r)=M*exp(-s*r), where M=integral exp(s*t)*f_R(t)>0. Reflection turns
  2*M into the integral of f_R(t)*(exp(s*t)-exp(-s*t)), a continuous
  nonnegative compact function strictly positive at R/2. Thus the test is
  EXACTLY a fixed positive Yukawa multiple outside the core. This replaces
  the proposed explicit linear patch; no patch Fourier estimate is assumed.
- `CovariancePairingBounds` (3): each inverse Gram entry has norm at most
  the real trace, including singular-inverse conventions. The actual covariance
  identity gives sqrt(rho_i*rho_j)*abs(hhat_ij)<=trace(S)+1. Honest radial
  Parseval and the uniform trace budget then uniformly bound every actual
  test pairing whose Fourier transform is dominated by the compact profile.
  The weighted estimate itself allows tracers and has no K/D/G dependence.
- `YukawaTestMoments` (3): the fixed correction
  q(r)=abs(r)*H(abs(r))-M*abs(r)*exp(-s*abs(r)) is continuous and compactly
  supported in [-R,R], and supplies its own L1. The hard core h=-1 implies

      integral_R r^2*h(abs(r))*psi(abs(r))
        = 2*M*integral_(r>0) r*h(r)*exp(-s*r)-integral_R q(r).

  This is an exact equality with a fixed correction, not a bounded unknown
  core error. No pointwise g>=0 hypothesis is used.
- `ActualGCanonicalIdentification` (3): actual canonical excess decay and the
  finite affine background identify the HONEST causal G Laplace integral
  with (2*pi)^(-1) times completed J on Re(s)>0. The ORIGINAL second BH
  residual identity and actual causal inverse at z_u recover exactly G_u.
  The actual h moment at that rate is therefore

      integral_(r>0) r*h_ij(r)*exp(-z_u*r)
        = -1/z_u^2+exp(-z_u*sigma_ij)*G_uij.

  This replaces the old small-weighted-kernel-budget premise by actual full
  canonicity, and applies even when densities vanish.
- `MixtureSecondAmplitudeBounds` (2): positive fixed densities allow division
  of the pairing weight. Exact core correction, M>0 and the actual G identity
  then uniformly bound every original G entry and its full original Pi norm.
  The constant is independent of ALL strengths and amplitudes.
- `MixtureCanonicalProperness` (5): combine G with the bounded-K original D
  bound to bound the original amplitude pair uniformly. Every finite canonical
  prefix is bounded, without seed/continuity/endpoint-value assumptions;
  finite amplitude escape is impossible. Every constructed maximal branch
  with finite endpoint has an ACTUAL root cluster with a genuine real-frequency
  physical Fourier determinant zero. For physical eta<1, the already proved
  HS seed theorem constructs such a maximal initial branch from DATA alone.

The conclusion covers arbitrary finite species count, unequal diameters and
compositions, noncommuting symmetric strength matrices and arbitrary finite
signed/repeated positive Yukawa rates. No eta<=0.8 restriction is needed.
The endpoint conclusion is a cluster theorem; it does not assert a unique
full endpoint limit or identify the complex Taylor radius with first loss.

## Proved active-bath and vacuum extensions

Four further modules add eight standard-three proofs:

- `WeightedMixtureAmplitudeBounds` (1) retains sqrt(rho_i)*sqrt(rho_j)
  through the ENTIRE original G estimate. It proves a uniform weighted G
  entry bound for nonnegative densities, with no density division or K bound.
- `ActiveMixtureAmplitudeBounds` (3) derives a uniform bound for EVERY
  original D entry whose COLUMN density is positive, including all tracer
  ROWS. It uses rho_l*norm(A(z_u)^(-1)_jl)^2<=rho_j*C and bounds
  rho_l*norm(A(z_u)^(-1)_jl)<=sqrt(rho_l*rho_j*C); zero terms remain zero.
  The entire active-active original G block is also uniformly bounded with
  retained tracers. Constants are uniform over roots; K is bounded only for D.
- `ActiveBathKernelBounds` (2) defines the ORIGINAL-amplitude projection
  keeping active-active pairs. At ALL amplitudes, with no root/canonicity,
  every active-active bhCoefficient is unchanged by this projection. The
  W/C cancellation and density-weighted M/N sums establish actual locality.
  The projected original amplitudes have bounded product/Pi norm; continuity
  on a compact ball then bounds the ACTUAL active bath finite coefficients
  uniformly over bounded K. Tracer amplitudes are not assumed bounded.
- `MixtureVacuumProperness` (2) proves arbitrary finite-species full-vacuum
  original root pairs uniformly bounded over bounded strengths and excludes
  finite vacuum escape, using the already proved unique explicit affine root.
  No canonicity, reciprocity, branch continuity or supplied bound is needed.

## Remaining partial-zero-density tracer extension

The unweighted full amplitude pair bound still requires every retained density
positive, apart from full vacuum which is now explicitly covered. The current
active-bath theorem does NOT bound zero-density D columns, cross-tracer G or
tracer-tracer G. Existing tracer Jacobian injectivity is uniqueness at a
canonical point, not a uniform estimate at a limiting noncanonical bath.
Deleting the retained tracer coordinates would change the statement.

A possible next quantitative route (NOT yet a Lean theorem) is an
inhomogeneous tracer energy estimate. For a tracer row i, write
x_a=sqrt(rho_a)*c_hat_ia and y_a=sqrt(rho_a)*h_hat_ia. Actual unweighted OZ
would give y=x*S, with S the physical active covariance. Choose the FIXED
trial h0_ia=-1 on the hard core and zero outside, and the known MSA exterior
cT_ia equal to the prescribed tail outside the core and zero inside. These
functions have disjoint supports; the actual closures imply

    <c,h> = <c,h0> + <cT,h>,

with the actual radial Parseval weight and active density factors. The energy
E=integral w^2*x*S*x^* is nonnegative. A weighted Cauchy-Schwarz argument
would give E<=sqrt(E)*(A+B), where A^2 uses h0*S^(-1)*h0^* and B^2 uses
cT*S*cT^*. Thus sqrt(E)<=A+B. The already proved bounded active bath
coefficients should bound S^(-1)=Bphysical*Bphysical^* uniformly, controlling A
by h0's genuine L2 norm. The exterior tail's exact transform should give
abs(cT_hat)<=C/(1+k^2), so B is controlled by the already proved compact-test
trace budget. No strict pointwise spectral gap at a limiting bath is needed.
A second Cauchy-Schwarz pairing with the ACTUAL smoothed Yukawa test would
then control every h_ia Yukawa moment, hence G_ia for active column a.
These steps need actual base-c L1/L2, unweighted value OZ identification,
exact closure/Parseval forcing, the two uniform forcing estimates and their
actual norm conventions checked; none has been assumed as an axiom.

`TracerAlgebraicProperness` now closes that remaining FINITE ALGEBRA (two
public standard-three proofs). Its all-amplitude column locality theorem needs
only equality of density-weighted G and the selected original D column; it
preserves the actual recentered transform and the actual second source, with
no root, canonicity or density-sign premise. Its capstone proves:

    for fixed bounded K and fixed C,
    [for every positive-density column j, ALL rows of G_uj are bounded by C]
      => [the ENTIRE ORIGINAL pair (D,G) has a uniform finite bound].

This is a CONDITIONAL properness theorem, not the missing cross-tracer G
estimate. The proof first masks inactive D/G columns and uses the proved
active D bound. Actual column locality and the ORIGINAL first equation
recover all D as a continuous finite map of bounded inputs. With all D
bounded, mask ONLY G columns; the same locality and the ORIGINAL second
normalization recover all G as another continuous finite map on a compact
ball. No tracer density is inverted, no full tracer-column bound is passed,
and no actual root neighbourhood or Jacobian inverse is needed.

Since the active-active G block is already uniformly bounded, the analytic
step still needed is precisely the original G entries with ZERO-density ROW
and POSITIVE-density COLUMN. The generic inhomogeneous energy route above
is still a proposed way to obtain it. Neither it nor general partial-tracer
no-escape has been silently assumed or marked complete.

## Validation

The 19 new raw proof bodies have passed and their exact actual footprint
guards have been generated. The prescribed one-run incremental package check ACTUALLY exited 0 at
2026-11-01T20:05:18.903569+00:00: 1527 exact guards / 138 research modules plus root /
139 recorded compiler commands. All 136 prior module artifacts were reused;
only the two new modules and root compiled. Frozen foundation 1.0.17, all 530
source/config hashes and direct import pins (paper10/raw2/Mathlib57) were preserved.
Evidence: `results/lean/validation.json` and `results/lean/build.log`.

A mathematical negative control changes the claimed radial Fourier prefactor
from 8*pi to 4*pi while preserving the actual integral and primitive. Lean
rejects the integral proof body; downstream lower-bound algebra also fails.
This is not a timeout or a guard-only mismatch. The actual prefactor is 8*pi.

The subsequent single incremental stage ACTUALLY exited 0 at 2026-11-01T20:20:58.675626+00:00:
1537 exact guards / 139 research modules plus root / 140 recorded commands.
All previous 138 modules reused; only RadialCovarianceBounds and root compiled.
Frozen foundation and all direct import pins preserved. The general amplitude
escape theorem is still open after this uniform trace estimate.

The inverse-control stage ACTUALLY exited 0 at 2026-11-01T20:33:05.310378+00:00:
1543 exact guards / 140 research modules plus root / 141 recorded commands.
All 139 prior modules reused; only CanonicalInverseCovariance and root compiled.
The frozen foundation and all existing import pins were preserved.


The interior-inverse stage ACTUALLY exited 0 at 2026-11-01T20:50:40.760721+00:00:
1557 exact guards / 143 research modules plus root / 144 recorded commands.
All 140 prior modules reused; the three new modules and root compiled.
Frozen foundation and existing direct import pins were preserved.


The first-amplitude stage ACTUALLY exited 0 at 2026-11-01T21:01:39.227910+00:00:
1561 exact guards / 144 research modules plus root / 145 recorded commands.
All 143 prior modules reused; only MixtureFirstAmplitudeBounds and root compiled.
The first integration attempt exposed an import placed after the root module
doc comment; moving it into the initial import block fixed the actual failure.
Frozen foundation and all existing direct import pins were preserved.


The complete positive-density properness stage ACTUALLY exited 0 at
2026-11-01T21:22:45.444983+00:00:1590 exact guards /150 research modules plus
root /151 recorded commands. All144 prior modules reused; only six new modules
and root compiled. All29 new actual footprints are standard-three. Frozen
foundation1.0.17,530 source/config hashes and all existing direct import pins
(paper10/raw2/Mathlib57) were preserved, with no shared dependency build.
Six nonfatal copyright-header style warnings follow the package's existing
header format; there were no proof errors or footprint-guard failures.
Evidence: results/lean/validation.json and results/lean/build.log.


The active-bath/full-vacuum extension ACTUALLY exited0 at
2026-11-01T21:36:52.566624+00:00:1598 exact guards /154 research modules plus
root /155 recorded commands. All150 prior modules reused; only four new
modules and root compiled. All eight new actual footprints standard-three.
Frozen1.0.17/530 source-config hashes and paper10/raw2/Mathlib57 pins preserved;
no shared dependency build. Four nonfatal existing-format header warnings,
no proof or exact-footprint failures. Partial-tracer unweighted properness
remains OPEN after this stage.


The conditional tracer-algebra stage ACTUALLY exited0 at
2026-11-01T21:45:03.551814+00:00:1600 exact guards /155 research modules plus
root /156 recorded commands. All154 prior modules reused; only the new module
and root compiled. Both new actual footprints standard-three. Frozen1.0.17,
530 source/config hashes and paper10/raw2/Mathlib57 import pins preserved;
no shared dependency build. One nonfatal existing-format header warning,
no proof or exact-footprint failures. Evidence: results/lean/validation.json
and results/lean/build.log. The partial-tracer analytic G estimate remains OPEN.


## Tracer exterior forcing: exact tail spectrum and spatial split

`TracerTailSpectralBound` adds seven standard-three proofs using the frozen
foundation's **actual** `cMSAtail` radial Fourier formula. For z>0 and contact
σ>0, the transform is bounded by a constant times `(1+k²)⁻¹` at every k≠0.
Its square is dominated by the already proved compact radial profile spectrum.
The constant is uniform for bounded signed K, and a finite sum of arbitrarily
signed, repeated positive-rate tails has the same uniform square domination.
This supplies the spectral majorant proposed for the tracer exterior forcing.

For any actual reciprocal BH root, the actual **ordered** radial DCF equals
that finite Yukawa sum at every radius outside contact. At every positive
noncontact radius, the **actual** product `c_ij(r) h_ij(r)` splits exactly into
`c_ij(r) h0(r) + cTail_ij(r) h_ij(r)`, with the fixed hard-core comparison
`h0=-1` inside contact and zero outside. This uses the real MSA closure and
actual hard-core h identity; it does not assume spatial OZ or an artificial
DCF field. The contact point remains a measure-zero issue for a later integral
identity.

**Still open:** the finite tail symbol must be identified with the Fourier
transform of its pointwise sum; actual c odd L1/L2 and the unweighted value OZ
must be assembled into the quantitative inhomogeneous Parseval energy estimate.
The uniform exterior bound alone does not control tracer G. No partial-tracer
full amplitude properness is claimed.

The stage check exited0 at 2026-11-01T22:27:37.466276+00:00:1607 exact guards /
156 research modules plus root /157 recorded commands. All155 prior modules
were reused. Frozen foundation1.0.17/530 hashes, direct import pins and no
shared dependency build were preserved. One nonfatal existing-format header
style warning; no proof/footprint failure. Evidence: results/lean/.


## Tracer exterior field: honest L1/L2 and finite Fourier linearity

`TracerTailField` adds eight exact standard-three proofs. For a single frozen
foundation `cMSAtail(K,z,σ)`, its positive radial moment is integrable and its
odd radial moment is genuinely both L1 and L2. These memberships extend by
finite sum to the **physical pointwise tail field**. The radial Fourier
integral of that field is proved equal to the finite tail symbol by real
set-integral linearity, with each summand's integrability discharged. Thus the
previous uniform compact-spectrum square bound now applies to the Fourier
transform of the actual function, including finite signed and repeated rates.
The actual ordered DCF exterior and its hard-core c*h split are restated using
that physical tail field.

This closes the earlier finite-sum Fourier linearity gap. Remaining: establish
actual base-c odd L1/L2, prove the unweighted value OZ row identity and
inhomogeneous energy pairing, control the inverse-bath trial field, then bound
tracer-row/active-column G and invoke conditional finite algebra. No uniform
tracer properness or Taylor-radius equality is asserted here.

The stage check ACTUALLY exited0 at 2026-11-01T22:35:01.725222+00:00:
1615 exact guards /157 research modules plus root /158 recorded commands;
all156 prior modules reused. Frozen1.0.17/530 hashes and direct import pins
preserved, no shared dependency build. One nonfatal existing-format header
style warning, no proof/footprint failure. Evidence: results/lean/.


## Tracer base-c field and actual unweighted OZ value

`TracerBaseCField` adds seven exact standard-three proofs. The frozen
foundation's actual finite numerator basis bounds `r*c_ij(r)` at any amplitudes,
including the ordered unequal-diameter choice. At an actual BH root, existing
positive-radius integrability plus this bound gives the honest odd radial
base-c field in L1∩L2. There is no supplied c-function or uniform amplitude
bound in this membership proof.

Automatic finite Wronskian admissibility of reciprocal actual roots yields
core reciprocity and identifies **the radial Fourier transform of the actual
ordered c** with the actual finite spectral C entry at every k≠0. Combining
this value equality with the previously proved actual h completion and value
OZ gives `H=C*(I+diag(rho)*H)` for the real constructed c/h Fourier matrices.
For nonnegative rho, `SqrtRho²=diag(rho)` then gives

    H*SqrtRho = (C*SqrtRho) * StructureMatrix.

This holds for ALL rows, including rows with rho_i=0; no tracer density is
inverted. The structure matrix is the actual positive covariance established
earlier, not an arbitrary positive matrix supplied by the caller.

The **quantitative** inhomogeneous energy estimate remains open: prove the
fixed-core trial field, its inverse-bath forcing bound, the spectral tail
forcing integral bound and the Parseval inequality that controls tracer h
Yukawa moments. These steps must use this actual value OZ and actual field
memberships. Full partial-tracer amplitude properness is not yet claimed.

Stage check exited0 at2026-11-01T22:43:24.291384+00:00:1622 exact guards /
158 research modules plus root/159 commands, all157 prior modules reused.
Frozen1.0.17/530 hashes and direct import pins preserved; no shared dependency
build. One nonfatal existing-format header style warning, no proof/footprint
failure. Evidence: results/lean/.

## Fixed core trial field and exact tracer pairing split

`TracerCoreTrialField` adds six exact standard-three proofs. The fixed hard-core
trial function has positive radial moment L1, an odd radial L1∩L2
representative, and an exact radial Parseval square identity. Products of two
odd L2 radial fields are integrable in the weighted spatial measure.

For the actual ordered c and h at a canonical BH root, the spatial c*h
pairing splits into a fixed-core c*h0 term and a physical exterior Yukawa
tail*h term. The same equality is proved between the three genuine radial
Fourier pairing integrals. Contact points are handled almost everywhere.
This is an exact energy identity; it does not itself give a uniform bound on
tracer-row G. The inverse-bath core forcing and covariance tail forcing
estimates remain open at this stage.

Stage check exited0 at2026-11-01T22:49:39.729018+00:00:1628 exact guards /
159 research modules plus root/160 commands, all158 prior modules reused.
Frozen foundation1.0.17/530 hashes and import pins preserved; no shared
dependency build. Evidence: results/lean/.

## Uniform physical inverse-bath trace at retained tracer states

`TracerBathFactorBound` adds eight exact standard-three proofs. The genuine
Fourier transform of each frozen Baxter Q basis is bounded by its real L1
mass. Finite basis expansion and the previously proved bounded active bath
coefficients give a uniform bound on every active-active physical Q entry,
for bounded K and all real frequencies. Multiplication by square-root
densities kills inactive entries; hence every entry of the actual physical
Baxter factor is uniformly bounded, with zero-density tracers retained.

The Gram trace is exactly the finite sum of squared factor entries, so the
actual radial denominator has a uniform trace bound. Canonicality makes that
Gram matrix positive definite, and Lean proves the inverse of the **actual
structure matrix** equals the denominator. Thus the actual inverse
covariance trace is uniformly bounded at every real frequency. This is the
quantitative inverse-bath input for the fixed-core forcing norm. The
inhomogeneous tracer energy inequality and cross-tracer G bound still require
further work; neither follows from this trace bound alone.

Stage check exited0 at2026-11-01T23:00:39.005156+00:00:1636 exact guards /
160 research modules plus root/161 commands, all159 prior modules reused.
Frozen foundation1.0.17/530 hashes and direct import pins preserved; no
shared dependency build. Evidence: results/lean/.

## Weighted positive-matrix energy Cauchy–Schwarz

`TracerEnergyCauchy` adds two exact standard-three proofs. Mathlib's
positive-matrix induced inner product gives, for any positive definite
complex matrix A and vectors x,y, a bound for `‖x†y‖` by the product of
the square roots of the A-energy of x and the inverse-A-energy of y. A
second theorem gives the corresponding real-part bound. The proof unfolds
the induced inner product, uses actual matrix invertibility, and has no
extra spectral assumption or species-density division.

This is the finite-dimensional energy inequality needed to combine the
actual tracer OZ row with the core/tail forcing split. The integrated
physical row identity, forcing integrability and tracer G bound remain
open; the abstract inequality alone does not establish them.

Stage check exited0 at2026-11-01T23:07:59.233368+00:00:1638 exact guards /
161 research modules plus root/162 commands, all160 prior modules reused.
Frozen foundation1.0.17/530 hashes and direct import pins preserved; no
shared dependency build. Evidence: results/lean/.

## Actual tracer-row spectral energy is nonnegative

`TracerEnergyCauchy.positive_row_energy` proves the correct finite row
quadratic form: right multiplication by a positive matrix acts on a column
row vector through its transpose, whose positive definiteness is preserved.
`TracerActualRowEnergy.actual_tracer_row_energy_nonneg` then instantiates this
with the **actual ordered MSA c and h radial Fourier transforms**, the actual
OZ row relation and the actual positive physical covariance. For each
nonzero real frequency and every row i, including rho_i=0,

    0 ≤ Σ_j rho_j ĉ_ij(k) ĥ_ij(k).

The proof uses exact sqrt(rho_j)^2=rho_j algebra and no density division or
externally postulated positivity. This is a pointwise energy sign, not yet a
uniform integrated energy bound. The two forcing budgets and tracer G remain
open.

Stage check exited0 at2026-11-01T23:14:48.646799+00:00:1640 exact guards /
162 research modules plus root/163 commands, all160 prior modules reused.
Frozen foundation1.0.17/530 hashes and direct import pins preserved; no
shared dependency build. Evidence: results/lean/.

## Actual inverse OZ tracer-row transfer

Two more exact standard-three proofs invert a positive right factor in a
matrix row equation and apply it to the actual MSA radial Fourier matrices.
At every nonzero real frequency, the physical source row `C√rho` equals the
actual response row `H√rho` times the **physical Gram denominator**. The
denominator is the true inverse structure matrix, with the uniform trace
bound established in `TracerBathFactorBound`. No species-density division
occurs, so zero-density tracer rows are included. This is the algebraic
input for estimating the hard-core forcing. The integrated forcing norm
and tracer G remain open.

Stage check exited0 at2026-11-01T23:17:59.542223+00:00:1642 exact guards /
162 research modules plus root/163 commands, all160 prior modules reused.
Frozen foundation1.0.17/530 hashes and direct import pins preserved; no
shared dependency build. Evidence: results/lean/.

## Genuine frequency-weighted radial spectral L2

`TracerSpectralL2` adds six exact standard-three proofs. For any genuine odd
radial L1 field, the weighted radial Fourier function `w fhat(2πw)` is
continuous, obtained from the imaginary part of its honest Fourier
integral. If that field is also L2, genuine radial Parseval makes the
weighted Fourier function L2. Concrete instances cover the fixed hard-core
trial, the actual finite signed Yukawa tail field, the actual ordered c and
the actual canonical h. These are individual-root memberships where
appropriate; no uniform amplitude bound is inferred from L2 membership.

This supplies measurable L2 factors for the pending integrated energy and
forcing terms. The quantitative uniform core/tail budgets and tracer G bound
remain open.

Stage check exited0 at2026-11-01T23:23:51.094944+00:00:1648 exact guards /
163 research modules plus root/164 commands, all162 prior modules reused.
Frozen foundation1.0.17/530 hashes and direct import pins preserved; no
shared dependency build. Evidence: results/lean/.

## Actual hard-core inverse-bath forcing is integrable

`TracerBathFactorBound` gains two exact standard-three proofs: every entry
of the true physical Gram denominator is uniformly bounded over bounded
K and all real frequencies, and each entry is continuous in real
frequency, including the correctly defined physical zero mode. The first
is a finite Gram sum of the bounded actual Baxter factor entries; the
second uses the frozen foundation's actual radial-symbol continuity.

`TracerForcingIntegrability` adds three exact standard-three proofs. Two
L2 complex fields with a bounded measurable multiplier have an integrable
product; this extends to finite matrix pairings. Combining that generic
result with the actual Gram denominator and the fixed-core spectral L2
gives an honest L1 **actual inverse-bath hard-core trial quadratic** at
every canonical root over bounded K, including retained tracers.

This establishes existence of its integral, not a uniform bound on that
integral. Uniform core and tail forcing budgets, the integrated energy
inequality and cross-tracer G remain open.

Stage check exited0 at2026-11-01T23:31:48.666935+00:00:1653 exact guards /
164 research modules plus root/165 commands, 159 prior modules reused
because the bath module and its descendants were rebuilt. Frozen
foundation1.0.17/530 hashes and direct import pins preserved; no shared
dependency build. Evidence: results/lean/.

## Actual hard-core inverse-bath forcing is uniformly bounded

`TracerCoreForcingBound` adds three exact standard-three proofs. A scalar
bounded multiplier between two L2 fields has an integral bounded by its
multiplier bound times the genuine L2–L2 Hölder product. Finite species
matrix pairing inherits the sum of those bounds. Instantiating the fixed
hard-core spectral vector and the actual physical Gram denominator yields
one finite constant, depending only on fixed mixture/rates/diameters and
the bounded-coupling radius, that bounds the absolute value of the **actual
inverse-bath core trial quadratic integral** for every canonical
reciprocal BH root in that set. Zero-density tracers remain included.

This closes the quantitative core forcing budget, not the tracer energy
estimate. The exterior-tail covariance forcing budget and integrated
positive energy closure remain open, as does cross-tracer G.

Stage check exited0 at2026-11-01T23:36:51.966201+00:00:1656 exact guards /
165 research modules plus root/166 commands, all164 prior modules reused.
Frozen foundation1.0.17/530 hashes and direct import pins preserved; no
shared dependency build. Evidence: results/lean/.

## Actual exterior-tail covariance forcing is uniformly bounded

Five new modules add eleven exact standard-three proofs. The induced
positive-matrix inner product bounds each covariance entry by its real
trace. Finite-dimensional Cauchy–Schwarz then bounds the true positive
quadratic by `N * trace(S) * sum_a |t_a|²`. The actual finite signed Yukawa
tail trial vector has a **uniform** squared norm bound by a fixed compact
test weight for bounded K, including unequal edge radii and repeated rates.
The actual physical structure matrix is continuous on the full real axis,
with the true zero mode, by continuity and canonical invertibility of its
Gram denominator. Thus the actual tail quadratic is measurable and its
absolute value is dominated by a constant times the compact weight times
the actual structure trace. The previously proved physical weighted trace
budget gives a **uniform integral bound** independent of BH amplitudes.

Both quantitative forcing budgets are now closed: hard-core inverse-bath
and exterior-tail covariance. The integrated inhomogeneous positive row
energy inequality, uniform tracer h Yukawa moments, cross-tracer G and
full retained-tracer noescape remain open. No Taylor-radius equality is
inferred.

Stage check exited0 at2026-11-01T23:51:50.750939+00:00:1667 exact guards /
170 research modules plus root/171 commands, all165 prior modules reused.
Frozen foundation1.0.17/530 hashes and direct import pins preserved; no
shared dependency build. Evidence: results/lean/.

## Cross-energy and integrated Young algebra

Four exact standard-three proofs now supply the finite-dimensional and
real-variable algebra for closing tracer energy. `TracerEnergyCauchy`
proves the positive covariance cross pairing bound and the exact equality
of transpose quadratic forms for real trial vectors. The transpose is
essential for right-multiplied OZ rows. `TracerEnergyYoung` proves
`sqrt(E)*sqrt(Q) ≤ E/4+Q` for nonnegative energies, and an abstract
integrated theorem: an exact energy split into two forcing terms satisfying
those quarter-energy bounds yields `∫E ≤ 2(M_core+M_tail)`.

These are genuine Lean implications, but the actual MSA integrated row
identity and its pointwise cross-term interfaces are not yet instantiated.
The full tracer energy and G bounds remain open.

Stage check exited0 at2026-11-01T23:58:30.761060+00:00:1671 exact guards /
171 research modules plus root/172 commands, 160 prior modules reused
because the energy module and descendants were rebuilt. Frozen foundation
1.0.17/530 hashes and direct import pins preserved; no shared dependency
build. Evidence: results/lean/.

## Actual retained-tracer row energy is uniformly bounded

Six new Lean modules provide nineteen exact standard-three proofs. Genuine
radial L1/L2/Parseval gives the integrated identity between the actual
physical c/h row energy and the hard-core plus finite Yukawa-tail forcing
integrals. At every nonzero frequency, the actual right-multiplied OZ row
acts through the transpose of the positive physical structure matrix. A
weighted matrix Cauchy–Schwarz and Young inequality bounds each true forcing
term by one quarter of the same row energy plus its corresponding physical
quadratic. Real trial vectors remove the transpose exactly; the hard-core
quadratic uses the true Gram denominator, and the tail quadratic uses the
true structure matrix. Both are integrable, and their previously certified
integrals are uniformly bounded over bounded K and all canonical roots.
The integrated row energy therefore has a uniform bound independent of D,G,
including a row whose density is zero.

This is an intermediate noescape estimate. It does not itself bound a
tracer h Yukawa moment or a cross-tracer G entry. The next analytic step is
to pair the actual h row with a localized Yukawa spectral test supported on
a positive-density column, using the same row energy and a compact-weighted
structure trace bound. Then apply the exact h moment/G identification and
the already proved finite-algebra `full_bound_of_active_second_columns`.
The result has no Taylor-radius implication.

Stage check exited0 at2026-11-02T00:20Z:1690 exact guards /177 research
modules plus root/178 commands; frozen foundation1.0.17/530 hashes and
direct import pins preserved, no shared dependency build. Evidence:
results/lean/.

## Full finite-mixture original-pair noescape, including retained tracers

Four new Lean modules provide sixteen exact standard-three proofs. For a
fixed row `i`, active column `j` (`rho j > 0`) and rate `z u`, the unit-tail
exterior Yukawa spectrum is placed in the `j` column of a real weighted
trial vector. The true structure covariance quadratic of that vector is
uniformly integrable over bounded reciprocal K. The physical row-energy
Cauchy–Schwarz and Young estimate gives a uniform bound on `rho j` times
the spectral h/test pairing. Radial Parseval and the original h moment
identity show this pairing equals twice the original `G u i j` plus an
explicit hard-core integral depending only on fixed `z,sigma`. Since
`rho j > 0` is fixed, every active-column original G entry is uniformly
bounded. Crucially, no row density is divided; the estimate applies when
`rho i = 0`. Finite `T × Fin N × Fin N` supplies one common active bound.

`TracerAlgebraicProperness.full_bound_of_active_second_columns` then
recovers every inactive-column G and every D entry from the root equations.
Thus `TracerActiveGUniform.actual_full_mixture_amplitude_properness`
uniformly bounds the full original pair for any finite mixture with
positive rates/diameters, nonnegative densities, `vacMix ≠ 0`, symmetric
bounded K and half-plane canonical factor units. It also covers the all-zero
density case. The auxiliary `R` is any fixed positive real smaller than all
finite species diameters. The branch corollary
`no_finite_mixture_amplitude_escape` directly rules out a finite-coupling
original amplitude blowup along a canonical reciprocal root prefix.
No branch continuity or Taylor-series premise is used. The theorem has no
Taylor-radius implication.

Full package PASS at2026-11-02T00:46:32Z:1706 exact guards /181 research
modules plus root/182 commands, all new guards with only propext,
Classical.choice and Quot.sound. Frozen foundation1.0.17/530 hashes and
direct import pins preserved; no shared dependency build. Evidence:
results/lean/.

## Actual maximal physical mixture endpoint, with no escape premise

`MixtureEndpointNoEscape` discharges the auxiliary small-radius premise of
the preceding properness theorem using a finite minimum of positive species
diameters, including the empty family. It then bounds the actual original
`M.path t` uniformly for `0 ≤ t < M.bound.toReal` whenever the constructed
maximal canonical branch has a finite endpoint. This uses only the actual
root and canonicity fields of `MaximalBranch`, symmetric K, and bounded
`t • K`; no path-specific amplitude bound is assumed.

`maximal_finite_mixture_endpoint_unique_physical_limit` applies the existing
actual bounded-endpoint theorem to obtain `∃! a, PhysicalEndpointLimit ... a`.
The uniqueness is **of the selected path limit**, not of every root in the
endpoint fiber. The `PhysicalEndpointLimit` record includes an original MSA
root at endpoint coupling, closure of the canonical set, failed canonicity,
full left limit of the original amplitudes, and a real Fourier-factor zero.
`exists_mixture_hs_maximal_branch_with_finite_endpoint_limit` constructs
the branch from physical HS data at packing fraction below one and gives
that endpoint result whenever its maximal bound is finite. No claim makes
the maximal bound finite or gives a Taylor-radius lower bound.

Full package PASS at2026-11-02T00:52:15Z:1710 exact guards /182 research
modules plus root/183 commands, standard-three axioms only. Foundation
1.0.17/530 hashes and direct import pins unchanged, no shared dependency
build. Evidence: results/lean/.

The added `actual_canonical_mixture_prefix_has_unique_finite_limit` applies
without maximality. For an arbitrary continuous canonical original root
prefix on `[0,b)`, the existing actual algebraic cluster theorem gives a
full limit whenever a finite cluster exists. The generic endpoint theorem
therefore leaves only full finite limit or norm tending to infinity. The
new full-mixture noescape theorem rejects the latter: a norm tending to
infinity would produce arbitrarily large values arbitrarily close to `b`,
contradicting its uniform bound. This proves unique finite left limit, but
without nonextendability does not force a Fourier zero or failed
canonicity at the endpoint. Full PASS 2026-11-02T00:57:32Z:1711 exact
standard-three guards /182 modules plus root/183 commands; frozen
foundation and pins unchanged.

The public `..._from_data` wrappers now eliminate the auxiliary exterior
test radius from the actual full-pair properness and finite-prefix noescape
statements themselves. The finite-diameter radius construction remains an
internal proof step. Both the maximal branch and arbitrary canonical
prefix limits use these wrappers. Full PASS 2026-11-02T00:59:59Z:1713
standard-three guards /182 modules plus root/183 commands; frozen
foundation 1.0.17 and direct pins unchanged.

`canonical_mixture_prefix_uniform_bound_at_eta_lt_one` states the stronger
physical prefix result explicitly: one bound controls the entire original
`(D,G)` path on each finite canonical interval `[0,b)`, with no continuity
premise and with retained zero-density tracers. Its proof applies the
already established full-pair properness to `‖t • K‖ ≤ b‖K‖`.
`no_finite_mixture_amplitude_escape_at_eta_lt_one` is now a direct corollary
of this bound. No complex-coupling or Taylor-radius conclusion follows.

The axis-loss interface now states explicitly what this noescape result
buys for the actual maximal initial branch. On every earlier branch state,
`canonical_mixture_prefix_no_physical_axis_zero` transfers full causal
factor invertibility to nonvanishing of the *physical* Fourier determinant
at every real wave number, including zero and tracer faces. At a finite
maximal endpoint,
`maximal_finite_mixture_endpoint_first_physical_axis_loss` supplies the
unique selected full limiting original MSA root with some real-frequency
zero. `exists_mixture_hs_maximal_branch_with_first_axis_loss_at_eta_lt_one`
packages this conclusion directly from physical mixture data. The word
"first" refers to the selected HS branch and its endpoint limit; it does
not compare other roots, give a numerical loss coupling, or bound the
Taylor radius.

The converse `supplied_first_physical_axis_loss_eq_maximal_bound` takes an
independent *actual* same-seed MSA root prefix on `[0,b)`. It requires
continuity there, nonvanishing of the physical Fourier determinant at every
real wave number before `b`, and a full left limit equal to a supplied
endpoint amplitude with a real-frequency zero. The no-axis-zero path theorem
makes that prefix canonical, so maximality gives `b ≤ maximalBound`.
If the maximal canonical branch extended past `b`, coherent same-seed
uniqueness would make it agree with the supplied prefix on `[0,b)`; the two
left limits would then make the Fourier-zero endpoint amplitude canonical,
a contradiction. Hence `maximalBound = b`. This is a conditional exact
identification of a certified first physical axis loss, not a certificate
for any numerical instance and not a Taylor-radius statement.

The strengthened certificate theorem
`supplied_first_physical_axis_loss_is_selected_physical_endpoint` also
identifies the supplied endpoint amplitude with the maximal branch's unique
selected physical limit. Its proof uses
`canonical_prefix_left_limit_is_selected_physical_endpoint`: coherent
same-seed agreement on the entire half-open interval makes the two left
limits equal, while the previously proved noescape endpoint theorem gives
the selected limiting amplitude as an original MSA root, in canonical
closure, noncanonical, and at a real physical Fourier zero. Thus the
certificate does **not** require the caller to establish the endpoint
root equation separately. It still requires the all-frequency prefix
nonvanishing and full left limit premises.

The public data-level wrapper
`exists_hs_maximal_branch_at_certified_first_axis_loss` takes physical
`etaMix < 1` mixture data, symmetric K and the independent first-loss
certificate on a root prefix through the literal HS seed. It constructs
the maximal branch itself, proves its bound is `ENNReal.ofReal b`, and
returns the supplied endpoint amplitude as the unique selected physical
MSA limit. There is no caller-supplied maximal branch, endpoint roothood,
or amplitude bound. This remains conditional on a genuinely all-frequency
prefix certificate and does not establish a Taylor-radius lower bound.

## Conditional endpoint Taylor sums identify the physical mixture limit

`MixtureEndpointTaylorIdentification` proves Abel's componentwise endpoint
transfer at any positive coupling `b`, including conditional convergence.
For the original maximal branch, componentwise `HasSum` at `b` implies
`b ≤ amplitudeRadius` by the actual common-radius definition. The exact
maximal-branch Taylor criterion then identifies the series with the actual
canonical root at every `0 ≤ t < b`. Abel's theorem makes this series tend
to its endpoint sum, while `MixtureEndpointNoEscape` makes the same path
tend to its unique selected physical endpoint root. Uniqueness of limits
identifies them. The resulting `PhysicalEndpointLimit` includes original
MSA root, canonical closure, failed canonicity and a real Fourier-factor
zero. `exists_mixture_hs_branch_with_conditional_endpoint_sum` constructs
the branch directly from physical HS mixture data.

This is deliberately conditional on every original component having a
finite endpoint sum. It does not imply that such sums exist, that the
Taylor radius reaches the initial canonicity endpoint in general, or that
any real solution forces convergence. Full package PASS at
2026-11-02T01:12:11Z:1718 exact standard-three guards /183 research
modules plus root/184 commands, foundation1.0.17/530 hashes and direct
import pins preserved. Evidence: results/lean/.

`maximal_strict_radius_endpoint_series_is_physical_limit` specializes the
conditional endpoint identification to a strict common-radius inequality.
The existing radius-inside HasSum theorem supplies each component sum at
`M.bound.toReal`; the conditional identification shows that vector sum is
`PhysicalEndpointLimit`. The inequality `M.bound < R` remains a hypothesis
and cannot be inferred from the real noescape/endpoint theorems. Full PASS
2026-11-02T01:16:03Z:1719 standard-three guards /183 modules plus
root/184 commands, foundation and direct pins unchanged.
