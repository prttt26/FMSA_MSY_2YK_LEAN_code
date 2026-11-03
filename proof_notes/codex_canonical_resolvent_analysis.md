# Actual resolvent holomorphy and vertical-line absolute integrability

Research module: `MSAConvergence/CanonicalResolventAnalysis.lean` (22 theorems),
over immutable foundation 1.0.17. This checkpoint remains outside the SI.
No new mathematical axiom or shared dependency build is used.

## Actual frequency variables and actual kernel

Let q=`nonlinearCausalKernel z rho sigma Dt G`, including row density, and
Q(s)=`rdfMatrixLaplace q s`, the existing positive-axis integral of
q(t)*exp(-s*t). The amplitudes are fixed; differentiability in this module
is genuine **complex-frequency** differentiability. It is not the real
amplitude differentiability proved in the earlier Laplace-jets modules.

Positive finite rates and nonnegative diameters suffice for the final
actual result, conditional on full closed-right-half-plane canonicity.
Repeated rates, signed/zero densities and arbitrary amplitudes are allowed.
No BH root, residual-kernel vector, root curve, free-volume hypothesis,
Jacobian inverse or physical small-kernel-budget premise is required here.
The finite rate and species families may be empty.

## Frequency holomorphy, including the true frequency origin

`complexJ_frequency_differentiableAt` and its L counterpart prove the
finite rational dictionaries complex differentiable away from displayed
poles, with tail denominators excluded by Re(s)+z_u>0.
`actual_kernel_frequency_differentiableAt_off_zero` uses a neighbourhood
identity between actual integrals and those exact J/L dictionaries. The
identity is available on a whole convergent half-plane, not only at one
frequency or at BH roots, so it legitimately transfers differentiability.

For delta>0 with delta<all z_u,
`actual_kernel_entry_analyticOnNhd` proves the actual integral Q_ij
holomorphic on Re(s)>-delta. At s=0 it applies mathlib's proved Riemann
removable-singularity theorem to the punctured differentiability and the
actual integral continuity from `CanonicalKernelEstimates`. The existing
integral value is retained; no rational default at zero is substituted.

Finite determinant and adjugate formulas prove complex differentiability
of the genuine finite nonsingular inverse at unit matrices. Consequently,
`actual_inverse_entry_analyticOnNhd` gives holomorphy of U(s)=(I-Q(s))^(-1)
on the open half-plane whenever I-Q is a unit on its closure. The inverse
is justified as an inverse throughout that domain, rather than relying on
totalized matrix-inverse values at singular matrices.

## Regularization retains the actual inverse

The definition `regularizedResolvent q b s` is exactly

    W_b(s) = (I-Q(s))^(-1)-I-[q_ij(0)/(s+b)]_ij.

It is a frequency remainder, not a surrogate RDF or an assumed time-domain
resolvent. The auxiliary b is chosen as delta+1 in the actual capstone, so
its pole -b is strictly left of the closed domain Re(s)>=-delta.

The scalar identity

    a/s-a/(s+b) = (a*b/(s+b))/s

and proved denominator estimates give an inverse-square norm bound.
Combining it with the actual unregularized remainder from the previous
module proves `actual_regularized_resolvent_high_frequency`: actual finite
R and B give |s|^2*sum_ij |W_b,ij(s)|<=B uniformly for Re(s)>=-delta and
|s|>=R. Generic high-frequency estimates do not assume canonicity inside
the compact frequency region. Continuity/holomorphy of W on the full domain
is asserted only with unit control there and an excluded regularizer pole.

At b=delta+1, |s+b|>=1 on the whole closed half-plane. The previous actual
uniform inverse bound therefore yields the global entry-norm-sum bound

    sum_ij |W_b,ij(s)| <= C_inverse+N+matrixAbsSum(q(0)) = M.

No matrix or amplitude norm instance is changed. Finite entry norm sums
bound each entry, respect negation, and satisfy the directly proved
triangle inequality.

## One integrable majorant for all allowed vertical lines

Define `verticalPoint a k`=a+i*k. Here k is angular frequency; no hidden
2*pi substitution into mathlib's Fourier convention is made.
Since |k|<=|a+i*k|, the uniform half-plane frequency bound implies
k^2*sum_ij |W_b,ij(a+i*k)|<=B outside |k|>=R.

`quadratic_tail_global_majorant` combines this with the global M bound.
For R>=1 a valid common constant is

    C = (1+R^2)*M+2*B.

It gives (1+k^2)*sum_ij |W_b,ij(a+i*k)|<=C for EVERY a>=-delta and k.
The constant is independent of the chosen vertical line. The comparison
function C/(1+k^2) is genuinely integrable on the full real axis, using
mathlib's `integrable_inv_one_add_sq`. Continuity supplies strong
measurability, and each actual complex entry is bounded by the norm sum.
`matrix_symbol_vertical_integrable` therefore proves genuine absolute
integrability of both the norm sum and every complex entry on each line.

`vertical_exponential_norm` computes

    |exp((a+i*k)*t)| = exp(a*t)

for every real a,k,t. The existing bounded-multiplier integrability theorem
then proves the actual inverse-transform integrands exp((a+i*k)*t)*W_b,ij
absolutely integrable for every fixed real t. This is integrability of the
frequency integral, not a statement that its value is the genuine time
resolvent.

## Actual canonical capstone and remaining obligations

`actual_canonical_regularized_resolvent_analysis` obtains delta>0,
delta<all z_u, b>delta, R>=1, B>=0 and C>=0 from the explicit premise

    forall s : Complex, 0<=Re(s) -> IsUnit(I-Q(s)).

It bundles the actual regularized symbol's open-half-plane holomorphy,
closed-half-plane continuity, inverse-square high-frequency estimate,
uniform vertical majorant, and all the absolute integrability statements
above. Pointwise Fourier stability is not substituted for this full
canonical premise. Its validity on the initial physical interval remains
part of the larger continuation problem.

STILL OPEN: equality of inversion integrals on different vertical lines.
Mathlib supplies the proved Cauchy-Goursat rectangle theorem; the horizontal
boundary estimates and passage to infinite vertical lines must still be
formalized. Fourier inversion must then identify the integral with the
constructed actual causal Volterra resolvent, retaining the 2*pi
normalization and the correct matrix order. Frequency analyticity alone
cannot replace this time-domain identification.

An explicitly UNPROVED next step can use
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` for
f(s)=exp(s*t)*W_b,ij(s), between -delta<a0<=a1 and imaginary endpoints
-K,K. Its boundary identity is

    H(-K)-H(K)+I*V_a1(K)-I*V_a0(K)=0,

where H(k) integrates along the horizontal segment and V_a(K) integrates
on the truncated vertical line. For t>=0 the common majorant should yield
|H(k)|<=(a1-a0)*exp(a1*t)*C/(1+k^2). The required limits at both imaginary
ends, followed by `intervalIntegral_tendsto_integral` for the already proved
vertical L1 integrands, would give line independence. These estimates and
limits have not yet been proved in this package.

Actual excess and tangent decay/global h-tangent L2, Fourier-boundary tangent
OZ, canonical factor/amplitude recovery (including tracer cases), general
no-fold continuation and tail-shape/Taylor classification remain open.
The next source application must retain the nonzero-free-volume premise
of the frozen actual excess-source tail theorem. No universal real-root/
Taylor-convergence equivalence is asserted.

## Validation

Each of the 22 declarations was individually compiled, and its actual
compiler axiom report queried. Every report contains only `propext`,
`Classical.choice`, `Quot.sound` and has an exact `#guard_msgs` check.
The complete run, compiler options, input/artifact/log hashes and frozen
foundation before/after audits are recorded in `results/lean/validation.json`.
The checker now additionally records and compares the artifact hash of the
direct Mathlib removable-singularity import before/after; it never builds
or writes that shared dependency.

Final combined validation: PASS, 280 exact guards across sixteen research
modules plus the root. Every recorded input/source/artifact/raw-log hash
was independently checked. The 530 frozen source/configuration hashes,
six direct validated FMSAPaper import artifact pins and the one direct
Mathlib removable-singularity artifact pin match before/after. Foundation
remains 1.0.17 / 06e3268. Reproduce with `python3 scripts/check_project.py`.
No shared dependency build, foundation/TeX/numerical edit or merge-back.

## Subsequent contour checkpoint (2026-10-28)

`CanonicalContourShift` now proves the previously open all-time rectangle
limit and line independence, plus continuous causal inversion integrals,
the zero-time endpoint and whole-time-axis weighted L1. See
`codex_canonical_contour_shift.md`. This supersedes the line-independence
open item above; the exact Fourier/Laplace bridge and identification with
the constructed actual time-domain resolvent remain open.
