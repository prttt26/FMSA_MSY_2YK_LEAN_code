# Actual excess amplitude tangent: cancelled source, decay and boundary transforms

Date: 2026-10-28. Isolated research package over frozen foundation 1.0.17.
No new mathematical axioms, foundation/TeX/numerical changes or merge-back.

## Genuine source derivative and exponential tail

`ActualExcessSourceTangent.lean` proves 18 theorems. The existing actual
nonlinearExcessSource is expanded in the fixed recentered Baxter dictionary
and fixed scalar background convolutions. The latter are continuous in
real time. Its amplitude smoothness and actual Frechet derivative are
proved from the finite dictionary; no improper-integral derivative
interchange is assumed.

`excessSourceVariation` is DEFINED as fderiv of the existing cancelled
source at p, applied to the actual amplitude direction v. Its proved
formula contains the existing sourceVariation and precisely the affine
background convolution with the genuine kernelVariation. It is continuous
in real time.

The frozen off-root tail identity for nonlinearExcessSource holds at all
amplitudes. Differentiating that FINITE IDENTITY gives a finite exponential
tail for the actual source derivative. Smoothness of its finite tail
coefficients is proved off root. This step does not differentiate a decay
inequality. A compact maximum and the actual finite exponential tail give
one global positive-axis exponential weight bound, for every delta less
than or equal to all tail rates. The same argument gives a true weight
bound for the actual kernelVariation; its row density is retained.

`actual_excess_tangent_renewal` then proves, with genuine existing fields,

    dX = dS + dX*q + X*dq,   t >= 0.

The already proved actual G tangent renewal is used, with G=X+affine
background and dG=dX. Actual interval integrability justifies the split;
the affine background convolutions combine EXACTLY into dS. There is no
curve of BH roots, independent tangent data or decay premise here.

## Actual forcing and resolvent identification

`ActualExcessTangentDecay.lean` proves 11 theorems. Define the actual forcing

    A = dS + X*dq.

All fields are the existing actual fields or their actual Frechet
derivatives. A is continuous. Under full closed-right-half-plane canonicity
at the fixed p and nonzero free volume, actual X decays (previous
checkpoint), and dS,dq have the genuine exponential tail bounds above.
A common positive rate is obtained by taking the minimum of the actual
X decay rate and a rate below every Yukawa rate. The true convolution
envelope includes its time factor, and half-rate absorption proves A
itself decays exponentially.

`right_renewal_eq_source_response` proves the response identity for any
continuous actual right renewal with an actual exponential-growth bound.
Kernel bound M and growth rate gamma compute the common damping
max(M+1,gamma)+2. All damped integrability, integrated matrix renewal and
unit control at strong damping are proved. Complex Laplace uniqueness
identifies that field with the concrete right Volterra constructor; the
previous genuine variation-of-constants theorem gives its source response.
This is a proved uniqueness consequence, not a new uniqueness axiom.

The actual excess Frechet tangent already has an internally computed
growth bound through the earlier block-jet renewal. The actual forcing
has the affine bound required above because its exponential decay was
proved. Therefore `actual_excess_tangent_resolvent_formula` proves

    dX = A + A*r,   t >= 0,

for the existing real canonical kernel resolvent r. Matrix orders and
all intermediate species are retained.

## Actual decay and honest Fourier-boundary integrals

`actual_excess_tangent_canonical_decay` transfers the actual forcing and
actual resolvent decay through this proved response. It obtains epsilon>0,
D>=0 and a genuine uniform bound

    |excessVariation_ij(t)| <= D*exp(-epsilon*t),   t >= 0.

The rate is internally obtained; no optimal rate is claimed.
`actual_excess_tangent_canonical_integrable` gives actual positive-axis
L1, real weighted L1 for every c>-epsilon, and honest complex Laplace L1
for every Re(s)>-epsilon. It therefore includes all Fourier frequencies,
including zero, with actual integrals of the existing Frechet derivative.

`actual_excess_tangent_boundary_laplace` proves for every Re(s)>=0

    (dX)hat(s) = Ahat(s) * (I-Q(s))^(-1).

The actual cancelled tangent renewal is integrated with its PROVED input
integrability; full base-point canonicity supplies the inverse. No integral
of an uncancelled affine G background is used at the Fourier boundary.
This is the actual integral of the existing Frechet tangent; a new
amplitude derivative/interchange theorem for the entire boundary-Laplace
family is not asserted by this base-point argument.

## Exact scope

Positive finite Yukawa rates, nonnegative diameters and nonzero free
volume are explicit. Full canonicity means IsUnit(I-Q(s)) for every
complex s with Re(s)>=0, at the FIXED base point p. Nearby canonicity,
a curve of roots, a BH-root premise, a Jacobian inverse and small physical
kernel budgets are not assumed. Repeated rates, signed/zero densities,
empty finite families and arbitrary actual amplitude directions are
allowed. No amplitude or matrix norm instance is changed.

Decay and identification concern the CLOSED causal half-line, including
zero. Global L1 of the max-extended negative-time representative is not
asserted. Global actual h-tangent L2 still needs the radial/contact/shift
interface; full Fourier-boundary tangent OZ needs its own transcription.
The precise next L2 interface is the existing
`RadialVariationL2.actual_kernel_DCF_ae_zero_of_L2_OZ` premise: construct
Q : MatrixL2 ℝ N whose actual representative is densityWeight_ij times
HardSphere.oddRadialMoment (JacobianExterior.hVariation ... i j). The
positive radial weighted moment and its full-line odd extension must be
connected explicitly; a local radial MemLp fact is not that field.

Canonical factor/amplitude recovery, initial canonicity/continuation,
general no-fold and Taylor/tail-shape classification remain open. No
universal real-root/Taylor-convergence equivalence is asserted.

## Validation

All new compiler axiom reports are queried before adding exact guards.
The combined build uses the pinned compiler directly and read-only
prevalidated imports; no Lake/shared dependency build. Completion auditing
and exact combined counts are recorded below after the full run.

Final combined validation: PASS, 372 exact guards across twenty-three
research modules plus the root. All 29 new actual compiler footprints
contain exactly the standard three axioms. Every recorded input/source/
artifact/raw-log hash was independently checked. All 530 frozen source/
configuration hashes, six direct validated FMSAPaper artifact pins and
two direct Mathlib import artifact pins match before/after. Foundation
remains 1.0.17 / 06e3268. Reproduce with `python3 scripts/check_project.py`;
no shared dependency build was invoked.

## Follow-up: actual global radial/odd h L2 bridge closed (2026-10-28)

`ActualHRadialL2` now proves the actual contact-shifted radial moment
L1/L2 and physical radius-squared square integrability, and constructs
the actual whole-line odd h tangent in L1/L2 with its density-weighted
MatrixL2 representative. This discharges the exact hQ premise identified
above. Honest physical Fourier symbols and their zero-frequency moments
are proved. Residual-to-tangent OZ transcription remains separate; so
does any further amplitude-family global-L2 differentiability claim.
See `codex_actual_h_radial_l2.md` for exact scope and validation.
