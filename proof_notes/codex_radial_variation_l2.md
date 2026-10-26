# Actual Jacobian-kernel DCF fields in L2 and their Fourier normalization

Date: 2026-10-26. Codex ownership; no manuscript TeX write.
This continues `codex_jacobian_bridge.md` and closes its c-side L2/Fourier
representation obligation without adding an axiom. The general canonical
Jacobian-regularity theorem is still incomplete.

## Exact arbitrary-amplitude variation

`FMSAPaper/JacobianL2.lean` uses the existing finite representation of the
actual convolution DCF. Its basis index consists of a single derivative
basis term or a species/two-basis convolution term. Each amplitude
coefficient is an actual polynomial in (Dt,G), and each spatial kernel is
independent of those amplitudes. Thus, at every fixed r,

    actual c(r;p) = sum_b a_b(p)*K_b(r)/(2*pi*r),
    actual delta-c(r;p,v) = sum_b Da_b(p)[v]*K_b(r)/(2*pi*r).

The second formula is proved for the actual Frechet derivative, not defined
as a replacement DCF and not inferred by differentiating an improper
integral. Finite sums and scalar products are differentiated after the
already proved integral-to-basis equality. It holds at arbitrary amplitudes,
including non-roots and arbitrary directions v; no root family is assumed.
At r=0 the existing totalized quotient conventions agree on both sides.
Weighted bounds handle that point separately, rather than cancel r there.

Every basis derivative is bounded and measurable. Every convolution basis
is uniformly bounded in r by

    sup |basisPrime| * integral |basisQ|.

The existing cross-rate integral theorems discharge absolute integrability;
rates need only be positive, and repeated rates are allowed. The finite
variation numerator is consequently measurable and uniformly bounded.
For all actual amplitudes and directions, r*delta-c is bounded on the
whole real axis. No free-volume sign or density sign assumption is needed
for these structural bounds with fixed physical parameters.

## Kernel support gives actual Lp fields

For an actual fixed-coupling BH amplitude-Jacobian kernel direction, the
1.0.15 off-root residual identity proves delta-c=0 outside each pair's
contact. The zero extension of r*delta-c from r>0 is measurable, bounded
and supported in [0,R_ij]. `kernel_positiveMoment_memLp` therefore proves
membership in every Lp, including L1, L2 and Linfinity. In particular,

    integral_0^infinity r^2*delta-c(r)^2 dr < infinity.

`kernel_radial_moment_integrable` also proves absolute integrability of
r^2*delta-c. This justifies the continuous physical zero-frequency symbol
of the variation. Only positive rates, nonnegative diameters and membership
in the actual Jacobian kernel are supplied; no integral bound is assumed.

`FMSAPaper/RadialVariationL2.lean` uses the existing actual odd radial lift

    oddVariation(r) = r*delta-c(|r|), cast to complex.

Its support lies in [-R_ij,R_ij], and it is bounded and measurable. It belongs
to every Lp. `oddVariationLp` and `weightedOddVariationLp` are constructed
from these actual functions using MemLp.toLp. Their a.e. representative
equalities are proved. The physical density weight is exactly
sqrt(rho_i)*sqrt(rho_j). Zero weighted L2 elements imply delta-c=0 a.e. on
the positive radial axis for active pairs with rho_i>0 and rho_j>0. No claim
of recovery from a zero density weight is made.

## Integral Fourier and abstract L2 Fourier agree

Mathlib's L2 Fourier transform is an isometry on equivalence classes;
the integral Fourier transform acts on actual functions. Equal notation
alone is not a proof that the two coincide.
`FMSAPaper/FourierL1L2.lean` proves their agreement a.e. for every complex
L1 intersect L2 function on any finite-dimensional real inner-product space.
It uses only Mathlib's existing theorems:

1. Fourier integral duality with every Schwartz test, by L1 Fubini.
2. Compatibility of L2 Fourier with tempered distributions and the exact
   integral defining the distribution of an L2 function.
3. The fundamental lemma for locally integrable functions tested against
   smooth compactly supported functions.

No integrability of the Fourier image, pointwise inversion, Plancherel
conclusion or new Fourier uniqueness axiom is a premise. The Fourier image
is locally integrable by continuity on the integral side and by L2 on the
abstract side. The resulting `L2_fourier_ae_integral` applies directly to
the actual compact odd DCF variation and its density-weighted version.

## Correct physical wave number and the zero mode

Mathlib uses frequency w in exp(-2*pi*i*w*r), while the physical radial
symbol uses wave number k in sin(k*r). The exact relation is k=2*pi*w.
For the actual field, `oddVariation_integral_fourier` proves

    Fourier(oddVariation)(w)
       = -i*w * radialSymbol(delta-c,2*pi*w).

The proof reduces the odd Fourier integral to its sine integral and checks
the factor 4*pi/k exactly. At w=0 both sides vanish because of the odd phase;
this does not identify a raw quotient value at zero with a physical limit.
The continuous sinc radialSymbol is used for the physical DCF value, and
its moment integrability/continuity is proved internally.

`actual_fourier_matrix` assembles the density weights and entrywise L2
Fourier equalities into

    Fourier U(w) = (-i*w) * radialVariationMatrix(2*pi*w)  a.e.

No factor derivative or implicit spectral-DCF identification is substituted
for this actual radial integral. In particular, a future tangent spectral
OZ theorem must evaluate the actual structure matrix at 2*pi*w, not w.

## Actual Parseval interface and remaining premises

`actual_spatialPair_zero` discharges the spatial L2 pairing between the
constructed U and any supplied L2 representation Q of the constructed h
variation. Its pointwise product is zero away from the two contact points,
using the actual kernel exterior zero and the actual h-core derivative.
Thus no spatial orthogonality is left as a caller hypothesis.

`actual_kernel_DCF_ae_zero_of_L2_OZ` combines actual BH root data, factor
invertibility, the actual U construction and the 1.0.15 positive matrix
Plancherel theorem. It concludes actual delta-c=0 a.e. for every active pair.
The remaining analytic premises are stated explicitly:

- a matrix L2 field Q representing the density-weighted odd constructed
  h variation; its existence, global differentiability and L2 control are
  still to be proved for canonical BH states;
- the actual tangent spectral relation Fourier Q=S*(Fourier U)*S a.e.,
  at physical k=2*pi*w, derived from the BH residual kernel by a valid
  off-root/operator transcription.

The constructed h's totalized Frechet derivative outside the core is not
silently certified as an actual physical tangent. Knowing nonlinear OZ only
on root curves does not discharge the residual-kernel transcription. The
canonical tangent-factor uniqueness/amplitude-recovery and the general
initial canonical continuation remain separate. No full no-fold ordering
or universal real-root/Taylor-convergence equivalence is claimed.

## Validation and reproduction

From the package root, run `lake build` and `python3 formalization/check.py`.
The three modules add 40 exact per-theorem standard-axiom guards. Their
versioned evidence is recorded under `formalization/results/baseline_1_0_16/`
with all checks PASS: 66 modules, 485 exact std3 guards, 528 frozen
source/config hashes; foundation 9078 jobs, workspace plus three compatibility
targets 9201 jobs; boundary/Git-ownership and three downstream locks PASS.
Independent full downstream proof builds are explicitly NOT_RERUN.
Manifest SHA256:
`228d82c79bc0a47d2ba90e3c5f8d05b71e503754c0d72f0d4882fbaa3fe39792`.
The complete 1.0.15 manifest is archived byte for byte, and all its existing
foundation proof modules remain unchanged.
