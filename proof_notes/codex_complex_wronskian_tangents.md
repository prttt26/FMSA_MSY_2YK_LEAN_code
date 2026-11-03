# Actual complex Wronskian and Fourier-source tangents

This extends the complete finite tangent certificate of f719230 in the
isolated research package. The new module is
`MSAConvergence/ComplexWronskianJets.lean`. Foundation 1.0.17 / 06e3268 remains
immutable; no TeX, SI integration, dependency build or merge-back is performed.

## Genuine complex evaluation of real coefficient derivatives

`variation_complex_eval_fderiv` proves that the existing bounded-degree
coefficient variation commutes with evaluation at any complex frequency s.
The amplitude derivative is over the reals; no holomorphic amplitude
assumption is made. A finite coefficient expansion and the bounded real-linear
embedding `Complex.ofRealCLM` prove the interchange. Coefficient regularity
and complex evaluation smoothness are discharged separately, with no norm
assigned to the infinite-dimensional polynomial ring.

`actual_kernel_complex_polynomial_eval_fderiv_zero` applies this to the actual
distinct U/V numerator constructors. Their genuine amplitude derivatives
vanish at every complex evaluation under the preceding complete finite
certificate's hypotheses. The coefficient index is a frequency-polynomial
index, not a coupling Taylor order.

## Off-root clearing of the actual rational Wronskians

For the distinct rate values r, put

    D(s) = s^2 product_r (s+r).

Every original tail label is retained in the actual J/L numerator sums;
repeated rates contribute only one denominator factor. The distinct factor
identity and the actual complex J/L definitions give, at arbitrary amplitudes,

    Jnum(s) = D(s) J(s),       Lnum(s) = D(s) L(s).

`distinctJNumerator_complex_eval` and `distinctLNumerator_complex_eval` prove
these identities before any root equations are imposed. They use positive
rates, nonzero s and Re(s)>=0. `distinctUPolynomial_complex_eval` and the V
version then give the actual complex Wronskian defects U_rat,V_rat:

    U_poly(s) = s D(s) D(-s) U_rat(s),
    V_poly(s) = s D(s) D(-s) V_rat(s).

The reflected identities apply when Re(s)=0 and s!=0. Positive rates prove
D(s) and D(-s) are nonzero internally. The clearing factor is independent of
amplitudes. Actual complex J/L and rational Wronskian entry smoothness is
proved in the real amplitudes, so differentiating the off-root equality and
cancelling the fixed factor yields

    delta-U_rat(s) = 0,       delta-V_rat(s) = 0

at every nonzero imaginary frequency. This is
`actual_kernel_complex_wronskian_fderiv_zero`. No root-only identity is
differentiated and no kernel vector is assumed to integrate to a root curve.
The pole exclusions belong to these physical clearing identities; the
smoothness statements concern amplitudes at a fixed frequency.

## Actual Fourier Q/C source defect

Let s=i*k for real k!=0, R=diag(rho), E(s)=rdfPhase(sigma,s), and

    Q(k) = existing nonlinearActualFourierQ(k),
    C(k) = existing nonlinearActualFourierC(k),
    B(s) = E(s) J(s)^T E(s).

Define the actual source defect

    S(k) = [I-Q(k)R] B(-s) - [I-Q(-k)R] B(s) - s C(k).

The existing all-amplitude Fourier-to-phase identity and phase Wronskian
algebra prove

    S(k) = E(-s) U_rat(s) E(s) + E(s) V_rat(s) E(s).

`actualSourceDefect_factorization` proves this for arbitrary amplitudes, with
positive rates and nonnegative diameters. The phases are fixed diagonal
matrices, independent of amplitudes. `actualSourceDefect_entry_contDiff`
proves genuine amplitude smoothness, and
`actual_kernel_sourceDefect_fderiv_zero` transfers the actual rational
Wronskian tangent cancellation to the actual Fourier Q/source relation.
Every contact phase, density orientation and original matrix order is retained.

## Actual spectral Baxter C variation is symmetric

`actualFourierQ_entry_contDiff` and `actualFourierC_entry_contDiff` prove the
actual Fourier entry derivatives exist off-root. The former uses the actual
phase representation; the latter uses the all-amplitude Baxter Q-product
identity and its finite species sums.

The existing C(-k)=C(k)^T identity holds at arbitrary amplitudes, and direct
algebra gives a second off-root identity:

    S(k) + S(-k) = s [C(k)^T - C(k)].

Differentiating both sides and using the source-defect kernel cancellation
at both signs of k proves

    delta-C(k)_ij = delta-C(k)_ji.

This is `actual_kernel_fourierC_fderiv_symmetric`. It is not obtained by
differentiating the root-only spectral reciprocity theorem.

## Exact hypotheses and remaining scope

The rational complex Wronskian cancellation requires finite species/tails,
positive rates, nonzero free volume, symmetric prescribed strengths, an
actual BH root at fixed coupling and a vector in the actual fixed-coupling
amplitudeJacobian kernel, with s!=0 and Re(s)=0. Repeated rates and zero
component densities are allowed. The actual Fourier/source/spectral-C results
add nonnegative diameters and nonzero real k. No Jacobian invertibility,
root curve, unknown-amplitude symmetry, canonical-state, kernel-smallness,
or caller-provided regularity/certificate premise is used.

The C in these statements is the existing *spectral Baxter C*. Its genuine
variation is now identified with the Fourier transform of the existing
ordered radial DCF variation by `RadialDCFTangent` (fe7c940), for every
species pair and nonzero real k under positive diameters. The actual h variation's global
integrability/L2 and its full tangent spectral OZ identity remain open.
Canonical tangent-factor recovery/amplitude uniqueness, general no-fold
continuation and tail-shape/global Taylor-convergence characterization also
remain open. No implication from real-root existence to universal Taylor
convergence is asserted. This Jacobian research remains outside the SI.

Validation: direct pinned Lean via `python3 scripts/check_project.py`, with
exact compiler axiom guards and source/artifact/log hashes in
`results/lean/validation.json`. The frozen foundation's 530 source/configuration
hashes and three direct import artifact pins are audited before/after; no
Lake/shared dependency build is invoked.

Verified isolated checkpoint (2026-10-28): PASS, 116 exact std3 theorem guards
across nine research modules plus the root, including 24 new guards here.
All 530 frozen source/configuration hashes and three direct import artifact
pins were unchanged before/after; no shared dependency build was invoked.
Foundation manifest SHA:
`09ade0691482098319e832c6c721b77ef70d99bb76cec5bc84b498357dd9219c`.

Subsequent completed checkpoint: `ActualPrimitiveTangent` proves the genuine
primitive derivative is globally L1, with actual Fourier derivative interchange,
primitive tangent reciprocity and a.e. evenness. `RadialDCFTangent` proves
an off-root cosine/sine identity before actual amplitude differentiation and
identifies the existing ordered radial DCF variation's Fourier transform.
The root-only radial identity is never differentiated along an assumed root
curve. Current combined validation: 150 exact guards across eleven modules
plus root, with all 530 frozen source/configuration hashes and six direct
import artifact pins unchanged. See `codex_actual_primitive_tangent.md`.
