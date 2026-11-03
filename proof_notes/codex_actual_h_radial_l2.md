# Actual h tangent: global odd-radial L2 and honest Fourier representatives

Date: 2026-10-28. Isolated research package over frozen foundation 1.0.17.
No new mathematical axioms, foundation/TeX/numerical changes or merge-back.

`MSAConvergence/ActualHRadialL2.lean` adds 18 theorem guards. It targets the
exact hQ premise of the existing actual DCF cancellation engine, rather
than introducing an unconnected abstract L2 field.

## Actual positive-radius control

The existing actual hVariation is the justified pointwise amplitude Frechet
derivative. For positive pair contact R=edgeHi sigma i j, its proved
radius-weighted contact/shift identity is zero inside the core and equals
the existing causal/excess Frechet tangent at r-R outside, including contact.
This identity proves restricted measurability of the actual radial moment.

The previous actual excess tangent theorem gives epsilon>0,D>=0. The shift
now proves, for every r>0,

    |r*hVariation_ij(r)| <= B*exp(-epsilon*r),
    B = D*exp(epsilon*R).

The core case, contact and the exponential contact phase are handled
explicitly. This proves genuine GLOBAL positive-axis L1 and L2 of the
radius-weighted actual h tangent, and therefore

    IntegrableOn (r^2 * hVariation_ij(r)^2) (Ioi 0).

This is the actual physical radial square-integrability weight. It is not
being identified with unweighted dr-L2 of h itself or with a newly
constructed three-dimensional L2 representative.

## Actual whole-line field and representative

`oddHTangent` is DEFINED as

    HardSphere.oddRadialMoment (JacobianExterior.hVariation ... i j),

namely the genuine full-line field r*hVariation_ij(|r|), cast to complex.
The proved positive moment L1 supplies actual whole-line L1. Its actual
exponential envelope in |r| gives a global bound. The generic squared-norm
majorant proves that a genuinely L1, a.e. bounded field is L2. No supplied
unknown-tail bound, unknown L2 representative or small physical kernel
budget is used.

`actualHL2Field` constructs the density-weighted MatrixL2 element directly
from the actual field. `actual_h_l2_field_coe` proves its a.e. representative
is EXACTLY densityWeight_ij times the actual odd radial hVariation field.
This is precisely the hQ premise formerly left open by
`RadialVariationL2.actual_kernel_DCF_ae_zero_of_L2_OZ`.

The whole-line odd field is not the max-extended negative-time Volterra
representative. No global L1 claim for that max extension is inferred.

## Honest Fourier symbols, including the origin

`actual_odd_h_tangent_integral_fourier` proves the genuine integral Fourier
formula at every real w,

    Fourier(oddHTangent_ij)(w) = -i*w * radialSymbol(hVariation_ij)(2*pi*w).

Whole-line L1 has been proved. The frozen validated L1/L2 Fourier bridge
identifies the L2 Fourier transform with that actual integral a.e. The
density-weighted entry and full matrix statements retain the physical
wave number k=2*pi*w and correct matrix/species order.

The actual second radial moment r^2*hVariation is also proved L1, by
absorbing a linear factor in the true exponential envelope. Consequently
the sinc integrand defining the actual radial symbol is integrable at
every real frequency, including zero, and the actual density-weighted
radial h tangent matrix symbol is continuous at every real frequency.
Zero frequency is not justified merely by its zero odd-Fourier prefactor.

## Actual cancellation-engine connection and remaining premise

`actual_h_spatial_pair_zero` instantiates the existing proved spatial
orthogonality with the NEW ACTUAL h L2 field along a BH-Jacobian kernel
vector. No unknown h-L2 representation is retained.

`actual_kernel_DCF_ae_zero_of_radial_tangent_OZ` converts the two actual
radial integral Fourier matrix representatives into the L2 spectral OZ
premise and invokes the existing positive-pairing engine. It needs no
extra L2 h field or representative premise. Its remaining OZ premise is
EXPLICIT: the actual radial integral symbols must satisfy delta-H =
S*delta-C*S a.e. at k=2*pi*w. This is not yet derived from the residual.
The existing actual symmetric-strength root, Jacobian-kernel, nonnegative
density and physical Fourier-factor unit premises remain explicit for
this conditional active-pair DCF cancellation theorem.

## Hypotheses and limits

Positive rates, nonnegative diameters, nonzero free volume and full
closed-right-half-plane canonicity at the fixed amplitude base point are
explicit for decay/L2 control. Pair results assume positive pair contact;
the full MatrixL2 construction uses positive diameters to supply it for
all pairs. Repeated rates, empty finite families, zero/signed densities
and arbitrary actual amplitude directions are permitted for the L2 field.
Nonnegative densities are needed by the existing DCF positivity engine,
not by the field construction. No nearby canonicity, BH-root curve,
Jacobian inverse or amplitude/matrix norm-instance change is assumed.

This proves L2 membership of the actual justified pointwise Frechet tangent
at the fixed base point. It does not additionally assert differentiability
of an entire amplitude family as a map into global L2. Full actual tangent
OZ transcription from residual jets, canonical tangent-factor/amplitude
recovery (including tracers), initial canonicity/continuation, general
no-fold and Taylor/tail-shape classification remain open. No universal
real-root/Taylor equivalence is asserted.

## Validation

Actual compiler axiom reports are queried before adding exact guards.
The new direct import FMSAPaper.RadialVariationL2 is read-only and its
already validated artifact is pinned alongside the six prior direct
foundation artifacts. The two direct Mathlib artifact pins are unchanged.
Full validation and independent auditing are recorded below at completion.

Final combined validation: PASS, 390 exact guards across twenty-four
research modules plus the root. All 18 new compiler footprints contain
exactly the standard three axioms. Every recorded input/source/artifact/
raw-log hash was independently checked. All 530 frozen source/configuration
hashes, the six prior direct foundation artifact pins plus the validated
read-only RadialVariationL2 artifact pin, and both direct Mathlib artifact
pins match the pinned before/after audit. Foundation remains 1.0.17 /
06e3268. Reproduce with `python3 scripts/check_project.py`; no shared
dependency build was invoked.

## Follow-up: actual h finite boundary response proved (2026-10-28)

`ActualSourceBoundary` and `ActualHBoundaryResponse` now prove actual
cancelled-source boundary identities, true kernel integral derivative
interchange on the axis and actual q/dq finite J/L identification. The
actual h phase/forcing response is direct on Re(s)>=0 including zero; its
pure finite J/L form is proved away from zero. No nonintegrable affine
axis integral or unsupported boundary h-family derivative is used. The
remaining residual-to-radial-tangent OZ matrix algebra is not closed yet.
See `codex_actual_h_boundary_response.md`.
