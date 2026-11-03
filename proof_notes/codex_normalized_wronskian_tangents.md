# Complete actual tangent finite Wronskian certificate

This research closes the finite-polynomial tangent completion left open at
checkpoint d97b639. The foundation remains frozen at 1.0.17 / 06e3268.
New modules: `MSAConvergence/PolynomialMatrixJets.lean` and
`MSAConvergence/NormalizedWronskianJets.lean`. The results are not integrated
into the foundation or SI. No TeX is written; the one merge-back remains
deferred until the research finishes and the session is about to close.

## Result and exact premises

`actual_kernel_tangent_polynomials_zero` proves that the complete actual
coefficientwise tangent polynomials delta-U and delta-V are identically zero,
not merely zero at the finite reflected rates. The previous degree-five U /
degree-four V remainders are fully eliminated.

Premises are precisely: finite species and tail sets; positive rates; fixed
real densities and diameters with nonzero `vacMix`; symmetric prescribed tail
strengths K; an actual BH root at fixed coupling t; and an arbitrary amplitude
direction v annihilated by the actual `JacobianExterior.amplitudeJacobian`.
Repeated rates and zero component densities are allowed. No symmetry of the
unknown amplitudes, Jacobian invertibility, root curve, kernel-smallness
budget, canonical state, or caller-provided derivative/certificate is used.
The nonzero-free-volume premise is new for this completion step; the preceding
finite-pole factor step did not need it.

`actual_kernel_wronskian_coefficients_fderiv_zero` identifies the result with
the genuine amplitude Frechet derivative of *every* existing actual distinct
U/V polynomial coefficient. `actual_kernel_wronskian_eval_fderiv_zero` gives
zero genuine derivatives of the actual cleared U/V evaluations at *every*
real frequency, including zero. The actual coefficient and evaluation
regularity was proved off-root in the preceding modules.

## Coefficientwise matrix derivative

Let m be the number of distinct rates. `matrixVariation` applies the existing
finite `PolynomialJets.variation` entrywise. `PolynomialMatrixJets` proves
that this genuine coefficient derivative commutes with fixed left and right
polynomial-matrix multiplication, preserving their order, and with fixed
polynomial scalar multiplication. Coefficients are finite scalar convolutions;
there is no norm on the infinite-dimensional polynomial ring and no change
to the original BH amplitude-space norm.

The same module proves preservation of a sharper uniform degree bound, an
identically zero coefficient, a fixed rectangular projected coefficient
constraint, and skew symmetry of a coefficient matrix. Derivative existence
in the latter linear interchanges is supplied by the proved coefficient
smoothness. These are derivative statements about actual functions, not
formal replacements or derivatives of non-differentiable default values.

## Off-root normalization and its derivative

Write W(p) for the actual `intrinsicWronskianMatrix`, D(p) for the actual
`intrinsicNormalizedDefect`, A for the fixed `intrinsicNormalizationMatrix`,
and Q for the fixed `intrinsicRatePairPolynomial`. The frozen foundation has
an identity at *arbitrary* amplitudes p:

    X^10 D(p) = A [Q W(p)] A^T.

`normalizedDefect_matrixSmooth` takes coefficient n+10 of this equality to
identify coefficient n of D(p) with a fixed finite linear combination of the
already smooth actual U/V coefficients. It does not expand the complicated
normalized constructor and does not differentiate a root-only assertion.

The actual tangent matrices are

    delta-W = matrixVariation(2m+5, W, p,v),
    delta-D = matrixVariation(4m+1, D, p,v).

Uniform off-root bounds justify both cutoffs. `actual_tangent_normalization_transport`
proves the exact differentiated identity

    X^10 delta-D = A [Q delta-W] A^T.

The intermediate degree bounds are 4m+5 for QW, 4m+8 after left multiplication
by A, and 4m+11 after right multiplication by A^T. They justify every finite
coefficient reconstruction used by the matrix variation. `intrinsicTangent_blocks`
identifies delta-W with the actual tangent U/V blocks:

    [ -delta-V(-X)     delta-U   ]
    [ -delta-U^T      delta-V   ].

## Complete factor cancellation

The preceding checkpoint proves the fixed reflected-rate factor P divides
both delta-U and delta-V. The intrinsic block identity supplies
`delta-W = P W1` entrywise. Q and P each have degree 2m and nonzero constant
coefficient, because all rates are positive. Exact tangent transport and
coprimality with X cancel the origin power, so QP divides every delta-D entry:

    delta-D = (QP) F.

All of the following constraints are inherited from identities valid off-root:

- every delta-D entry has degree at most 4m+1;
- its lower-right block has degree at most 4m;
- coefficient zero is zero;
- `completionU(1)` times coefficient one is zero;
- coefficient one is skew symmetric.

`normalizedTangent_degrees` and `normalizedTangent_origin_constraints` prove
them internally. The existing `polynomial_matrix_factor_completion` now
forces F=0, hence delta-D=0. The fixed normalization has nonzero determinant
as a polynomial matrix. `polynomial_matrix_congruence_cancel` and Q != 0
recover delta-W=0. Its upper-right and lower-right blocks give delta-U=0 and
delta-V=0. No kernel direction was assumed to integrate to a curve of roots.

## Remaining obligations

The *complete actual tangent finite Wronskian polynomial certificate* is now
proved under the premises above. Its complex rational/source transcription
and actual spectral Baxter C tangent symmetry are now proved in
`ComplexWronskianJets` (the actual Fourier/source step adds nonnegative
diameters); see `codex_complex_wronskian_tangents.md`. Ordered-radial DCF
variation/Fourier identification is now proved in `RadialDCFTangent`; see
`codex_actual_primitive_tangent.md` (fe7c940). This result alone is not the
full tangent spectral OZ identity and does not establish global actual
h-tangent L2, canonical tangent factor recovery/amplitude uniqueness, Jacobian
invertibility, general no-fold/canonical continuation, or universal Taylor
convergence. Those remain open. The Jacobian research stays outside the SI.

Validation uses `python3 scripts/check_project.py`: direct pinned Lean only,
exact compiler footprint guards, and source/artifact/log hashes in
`results/lean/validation.json`. It checks the frozen foundation's 530 source/
configuration hashes and three direct import artifact pins before/after and
invokes no Lake or shared-dependency build.

Verified isolated checkpoint (2026-10-28): PASS, 92 exact standard-three-axiom
theorem guards across eight research modules plus the root; 25 new guards in
these two modules. All 530 frozen source/configuration hashes and three direct
import artifact pins were unchanged before/after. No shared dependency build
was invoked. Foundation manifest SHA:
`09ade0691482098319e832c6c721b77ef70d99bb76cec5bc84b498357dd9219c`.
