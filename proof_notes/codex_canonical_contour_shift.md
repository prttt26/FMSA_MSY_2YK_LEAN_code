# All-time contour shifts and causal regularized inversion integrals

Research module: `MSAConvergence/CanonicalContourShift.lean` (13 theorems),
over immutable foundation 1.0.17. This checkpoint remains outside the SI.
It addresses Claude message 063; no new mathematical axiom is used.

## Genuine frequency integrals and their precise scope

For a scalar entry F(s) of the actual regularized symbol W_b(s), define

    V_a(t) = integral over k in Real of exp((a+i*k)*t)*F(a+i*k),
    H_k(t) = integral over a in a0..a1 of exp((a+i*k)*t)*F(a+i*k).

The Lean names are `verticalIntegral` and `horizontalIntegral`. V is
**unnormalized**: no 1/(2*pi) factor is included or silently converted to
mathlib Fourier conventions. Every vertical integral used in the shift has
actual absolute integrability, supplied by the previous module and its
proved phase-integrability lemma. F is not replaced by a totalized formula
for a divergent integral.

The generic results assume holomorphy on Re(s)>lower and one C such that
(1+k^2)*|F(a+i*k)|<=C for every a>=lower and k, together with genuine
vertical L1. The actual specialization obtains these inputs from the
existing nonlinear MSA kernel and full closed-right-half-plane canonicity.
Line equality is proved for **interior** lines a>lower. Integrability at
the closed boundary alone is not treated as boundary holomorphy.

## Both horizontal edges, for every real time

For a0<=a<=a1, `endpoint_exponential_bound` proves

    exp(a*t) <= max(exp(a0*t),exp(a1*t))

for every real t. The proof changes the maximizing endpoint when t<0,
explicitly addressing 063. The previous quadratic majorant and the exact
norm |exp((a+i*k)*t)|=exp(a*t) then give

    |H_k(t)| <= max(exp(a0*t),exp(a1*t))*C/(1+k^2)*|a1-a0|.

`horizontal_integrals_tendsto_zero` proves both H_K(t) and H_(-K)(t) tend
to zero as K tends to positive infinity. No decay of a single positive-time
edge is substituted for the other edge or for negative time.

## Finite Cauchy-Goursat identity and actual infinite-height limit

`rectangle_vertical_identity` applies mathlib's proved rectangle theorem
to exp(s*t)*F(s), with lower<a0<=a1 and imaginary endpoints -K,K. It retains
the correct I factors and orientations:

    H_(-K)(t)-H_K(t)+I*V_a1,K(t)-I*V_a0,K(t)=0.

The truncated vertical terms converge to their actual full-real-axis
integrals by `MeasureTheory.intervalIntegral_tendsto_integral`, using the
proved L1 integrands and endpoints -K to negative infinity, K to positive
infinity. The two horizontal terms have the separately proved zero limits.
Uniqueness of limits and cancellation of nonzero I prove
`vertical_integrals_eq_of_le`. Ordering the lines in either direction gives
`vertical_integrals_eq` for all interior lines and every real t.

This closes the rectangle/line-independence obligation that was explicitly
open at the previous checkpoint.

## Negative time, continuity and the zero-time endpoint

`vertical_integral_integrable_bound` proves genuine integrability and

    |V_a(t)| <= exp(a*t)*C*pi,

using the actual integral of 1/(1+k^2), equal to pi. Because C is independent
of a, line independence lets the same V_a(t) be bounded on arbitrarily far
right lines. For t<0, exp(a*t) tends to zero as a tends to positive infinity.
`vertical_integral_eq_zero_of_neg` therefore proves V_a(t)=0.

`vertical_integral_continuous` first factors out exp(a*t), then proves
continuity of the remaining imaginary-phase integral by dominated
continuity with bound |F(a+i*k)|. This avoids a nonexistent global-in-time
bound for the real exponential. Continuity and negative-time vanishing
give `vertical_integral_eq_zero_of_nonpos`, including V_a(0)=0.

These are properties of a genuine inversion integral, not a premise that
an unknown time-domain inverse already has causal support.

## Whole-time-axis L1, including exponential damping

`vertical_integral_weighted_integrable` proves, for every gamma>a>lower,

    t -> exp(-gamma*t)*V_a(t)

is genuinely L1 on the full real line. On t>0 its norm is bounded by
C*pi*exp((a-gamma)*t), which is integrable since gamma>a. On t<=0 it is
exactly zero by the proved support theorem. The proof extends the positive
majorant by its measurable indicator; it does not integrate an exponential
bound over the negative half-line where that bound might grow.

In the actual specialization, the internally chosen line a=-delta/2 is
strictly inside Re(s)>-delta and is negative. Thus V_a itself is L1 (take
gamma=0), with the exponential envelope pi*C*exp(-delta*t/2), and the
weighted L1 result holds for every gamma>-delta/2.

## Actual MSA interface and remaining identification

`actual_canonical_contour_integrals` applies all these results to each entry
of the exact frequency remainder

    W_b(s)=(I-Q(s))^(-1)-I-[q_ij(0)/(s+b)]_ij,
    Q(s)=rdfMatrixLaplace(nonlinearCausalKernel)(s).

It obtains delta>0 below every positive tail rate, b>delta and C>=0. For
every species pair it returns time continuity on each interior line,
all-time line equality, the integral bound, nonpositive-time vanishing,
whole-time L1 on a=-delta/2 and its damped versions, and the exponential
envelope on that line.

The assumptions are positive finite rates, nonnegative diameters and the
EXPLICIT full closed-right-half-plane unit premise for I-Q. Repeated rates,
signed/zero densities, empty finite families and arbitrary amplitudes are
allowed. No BH root, root curve, nonzero free volume, Jacobian inverse,
physical small-kernel budget or pointwise-stability substitute is used.

The identity term I was already subtracted in W_b. No Dirac-distribution
calculus is needed for this regularized remainder. Adding back the causal
q(0)*exp(-b*t) term is a future continuous-Volterra-resolvent step; support
alone does not prove equality with the existing constructed solution.

STILL OPEN: the exact 2*pi Fourier/Laplace normalization bridge and the
identification with the constructed actual time-domain resolvent or actual
renewal solutions. A possible next route, not yet proved here, uses
F_gamma(xi)=W_b(gamma+2*pi*i*xi). A genuine linear change of variables and
line independence should identify its standard inverse Fourier integral
with exp(-gamma*t)*V_(-delta/2)(t)/(2*pi). The time L1 needed for inverse
Fourier inversion has now been proved, but that normalization identity,
the Fourier/Laplace identity and renewal uniqueness still need Lean proofs.

No actual RDF/h-tangent decay or global h L2 is inferred from an unidentified
frequency inversion. Fourier-boundary tangent OZ, canonical factor/amplitude
recovery, initial canonicity/continuation, general no-fold and tail-shape/
Taylor classification remain open. The eventual excess-source application
must retain its nonzero-free-volume premise. No universal real-root/Taylor
convergence equivalence is asserted.

## Validation

All 13 new declarations were individually compiled and their actual axiom
reports queried; each uses only `propext`, `Classical.choice`, `Quot.sound`
and has an exact `#guard_msgs` check. Complete compiler commands, source/
artifact/log hashes, the immutable foundation audits and the direct Mathlib
artifact pin are recorded by `scripts/check_project.py`. No shared build,
foundation/TeX/numerical edit or merge-back is involved.

Final combined validation: PASS, 293 exact guards across seventeen research
modules plus the root. Every recorded input/source/artifact/raw-log hash
was independently checked. The 530 frozen source/configuration hashes,
six direct validated FMSAPaper artifact pins and one direct Mathlib artifact
pin match before/after. Foundation remains 1.0.17 / 06e3268. Reproduce with
`python3 scripts/check_project.py`; no shared dependency build was invoked.

## Subsequent Fourier/Laplace checkpoint (2026-10-28)

`CanonicalFourierLaplace` now proves the exact standard Fourier
normalization, actual positive-axis Laplace inversion, and the constructed
causal inverse field with restored leading exponential, whole-time L1 and
exponential decay. See `codex_canonical_fourier_laplace.md`. This closes
the normalization/transform open item above. Equality with the pre-existing
actual Volterra/RDF constructors remains an explicit obligation.
