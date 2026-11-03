# Actual tracer DCF, h and full BH amplitude recovery

Date: 2026-10-28. Isolated research over frozen foundation 1.0.17 / 06e3268.
No new mathematical axioms, foundation/TeX/numerical edits or merge-back.

AdditiveDensityTangentOZ adds 8 theorems; ActualTracerDCFCancellation adds 26;
ActualTracerAmplitudeRecovery adds 15. The final theorem

    FMSA.Convergence.ActualTracerAmplitudeRecovery.actual_residual_partial_isInvertible

proves continuous invertibility of the GENUINE actual BH residual amplitude
partial for GENERAL NONNEGATIVE densities, allowing zero-density tracer
rows and columns. This closes the tracer gap of the earlier positive-density
result. Initial canonicity, branch existence/continuation, endpoint control
and tail/Taylor classification remain open.

## Exact hypotheses and interface

Species and tails are finite. Rates and diameters are strictly positive,
rho_i>=0, actual free volume is nonzero, prescribed K_u are symmetric,
p=(Dt,G) is an actual BH root at any real coupling t, and full canonicity
holds at this FIXED amplitude base point:

    I-qhat(s) is a unit for EVERY complex s with Re(s)>=0.

The kernel q and its transform are the actual frozen causal constructor and
honest Laplace integral. All derivatives are true Frechet derivatives in the
existing amplitude-space norm. No density matrix is inverted. No positive
lower density bound, root curve, neighbouring canonical family, supplied
Jacobian inverse, special tail sign or small physical kernel budget is used.
Repeated rates, empty finite tail families and even identically zero density
are allowed. The conclusion is the exact `.IsInvertible` residual-partial
interface used by the frozen local-branch theorem.

## Additive-density OZ algebra

Let S=diag(sqrt(rho)), R=S*S. At each nonzero physical wave number the
preceding actual modules provide the UNWEIGHTED finite equations

    (I-C*R)*H=C,
    (I-C*R)*dH=dC+dC*R*H.

Here H is the real radial completion; genuine actual integral derivatives
identify dH with the constructed h tangent and dC with the actual ordered
DCF tangent. Full canonicity supplies a positive physical denominator
A=I-S*C*S and T=A^(-1)=I+S*H*S. Sylvester determinant swapping gives a unit
I-C*R without inverting any species density. Finite noncommutative algebra
then proves the actual unweighted tangent solution

    dH=(I+H*R)*dC*(I+R*H).

Earlier actual active-pair cancellation supplies S*dC*S=0. It follows that

    dH*S=dC*S*T,     S*dH=T*S*dC,
    dH*S+S*dH = T*(dC*S+S*dC)*T.

No symmetry or Hermitian premise is required for this algebra. The entries
are weighted by sqrt(rho_i)+sqrt(rho_j). Since both square roots are
nonnegative, zero additive weight implies zero dC entry whenever either
species is active. The two consequences dC*S=0 and S*dC=0 are proved
SEPARATELY, not by invalid arbitrary cancellation of their sum.
`mixed_pair_additive_zero` explicitly checks the two cross entries for
weights (0,1), while asserting nothing about the (0,0) tracer-tracer entry.
These checks adopt Claude 093's ordering caution.

## True actual L2 fields and two positive Parseval passes

For ANY constant real entry weights a_ij, construct genuine complex L2 fields

    U_ij(r)=a_ij*r*dc_ij(abs(r)),
    W_ij(r)=a_ij*r*dh_ij(abs(r)).

DCF L2 membership follows from the actual Jacobian-kernel exterior support;
h L2 membership and actual positive-axis decay were proved upstream from
fixed-base full canonicity. Exact a.e. representatives are supplied. Their
honest whole-line integral and L2 Fourier dictionaries retain

    Fourier(U)(w) = -i*w * a_ij * dc_radial_ij(2*pi*w),
    Fourier(W)(w) = -i*w * a_ij * dh_radial_ij(2*pi*w).

Actual fixed-contact h variations vanish in the core and actual fixed-K c
variations vanish outside the core. The two contact points are null sets.
Consequently the spatial L2 pairing vanishes for ANY constant entry weights.
No contact value is inferred from an a.e. equality.

First take a_ij=sqrt(rho_i)+sqrt(rho_j). The additive OZ identity supplies
the ACTUAL positive-T sandwich. The existing positive_OZ_pairing_injective
applied to these actual fields eliminates every additive-weighted c field.
The actual c radial symbol vanishes even at zero frequency by the proved
spatial a.e.-zero dictionary. At nonzero frequencies its identification
with the spectral derivative gives both one-sided zeros separately.

Then dH=dC by the genuine unweighted tangent equation. Take a_ij=1 and
positive structure I. A second application of the SAME Parseval engine
eliminates the entire unweighted c field, including double-tracer pairs:

    actual_all_pair_DCF_ae_zero:
      dc_ij=0 a.e. on positive radii, for EVERY species pair.

The honest h Fourier representatives and h=c identify its unweighted L2
field as zero too, using Fourier norm preservation. Thus

    actual_all_pair_h_ae_zero:
      dh_ij=0 a.e. on positive radii, for EVERY species pair.

The actual r*dh Laplace integrand is therefore zero a.e. Its integral is
zero for every complex s; no nondecaying affine background is integrated.

## G-first amplitude recovery

For Y(s)=J(s)*(I-qhat(s))^(-1), the already proved genuine h-Laplace tangent
identity is the actual completed-J derivative sandwiched between fixed
nonzero contact phases and scaled by 1/(2*pi). Hence the zero actual integral
implies dY(s)=0 for Re(s)>=0, s!=0.

At s=z_u, the ALL-AMPLITUDE second BH residual identity is

    H_u*A_u-J(z_u),     H_u=2*pi*G_u, A_u=I-R*Q_u.

Its ROOT VALUE gives H_u*A_u=J(z_u), hence H_u=Y(z_u). Only the all-amplitude
residual identity is differentiated, yielding

    dH_u*A_u-H_u*dqhat(z_u)-dJ(z_u)=0.

The genuine finite completed-symbol derivative gives

    (dJ(z_u)+Y(z_u)*dqhat(z_u))*A_u^(-1)=0.

Unit cancellation implies dH_u=0, and 2*pi!=0 gives dG_u=0 for EVERY pair.
This recovers tracer G directly without building an unweighted logarithmic
canonical response or differentiating a root-only G moment identity.

## Honest column projection and complete Dt recovery

With G fixed, the actual root-transform column j depends on Dt only through
column j: the true W/C/M/N/A_j/qp_ij definitions all have this property.
`root_transform_column_local` proves this at ALL amplitudes by the actual
source definitions. Define an honest continuous linear projection L_j that
retains the entire G matrix and repeats Dt column j into all columns. Then

    actualRootTransform(p)_ij = actualRootTransform(L_j p)_ij

as an all-amplitude function identity. True Frechet composition through L_j
shows its derivative is zero whenever v.G=0 and v.Dt column j is zero.
The earlier first-BH theorem already supplies dDt*R=0, hence each active
Dt column is zero. With the newly recovered dG=0, column locality gives

    dQ_u*R=0

without the prior row-density factor. Transpose this to obtain R*dQ_u^T=0.
The genuine first BH derivative and dDt*R=0 separately then force dDt=0.
No root neighbourhood or norm alias is introduced.

Both amplitude components vanish for every actual Jacobian-kernel vector.
Finite-dimensional injectivity gives bijectivity, and the existing Banach
inverse construction returns continuous invertibility of the actual residual
partial derivative. Full zero-density tracer amplitude recovery is CLOSED.

## Limits and validation

This proves pointwise canonical-root regularity. It does not establish
initial canonicity, select a PY-connected branch, prove that branch exists
through the whole initial stable interval or control endpoint blowup. It
does not compare a complex Taylor radius with that interval or characterize
tail parameters. No universal real-root/Taylor iff, RDF positivity or
global-L2 amplitude-family smoothness is asserted.

All 49 new footprints were queried from the actual compiler before exact
guards; every report is exactly propext, Classical.choice, Quot.sound.
Final combined validation: PASS, **603 exact standard-three guards across
38 research modules plus the root**, with 39 direct compiler commands. EVERY
recorded input/source/artifact/raw-log hash was independently checked. All
530 frozen source/configuration hashes, seven prior direct FMSAPaper pins and
all four prior direct Mathlib pins are unchanged before and after. Reproduce
using `python3 scripts/check_project.py`. The same seven validated
FMSAPaper import artifacts and all four direct Mathlib artifacts are read
only and pinned before/after; there is no new direct import or shared build.


## Follow-up: actual canonical neighbourhoods and branch criteria (2026-10-28)

The later CanonicalNeighborhood, ActualCanonicalBranch,
HolomorphicZeroPersistence and CanonicalFirstLoss modules prove genuine full
canonicity openness; construct local analytic canonical root germs and relative
one-sided extensions; establish connected branch/endpoint matching; and give
the correct radius iff using intrinsic analytic-extension coefficients, with
sums to the ORIGINAL prescribed nonnegative branch. Finite continuous first
loss is localized to the Fourier axis without a Hurwitz/Rouche axiom. A full
canonical seed plus physical factor units at EVERY real wave number along a
continuous connected path imply full canonicity there. A supplied transverse
fold bounds first loss nonstrictly. See `codex_actual_canonical_branch.md`.
The global existence/finite-escape, initial PY canonicity and tail/radius
obligations in the limits paragraph above remain open.
