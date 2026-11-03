# Actual kernel half-plane estimates and canonical resolvent control

Research module: `MSAConvergence/CanonicalKernelEstimates.lean` (35 theorems),
over immutable foundation 1.0.17. This checkpoint remains outside the SI.
No new axiom, shared dependency build, foundation edit, TeX edit or merge-back.

## Actual objects and hypotheses

Let q(t)=`nonlinearCausalKernel z rho sigma Dt G t`, including its existing
row-density factor, and Q(s)=`rdfMatrixLaplace q s`. Q is the existing
positive-axis complex Laplace integral, entry by entry. No formal rational
expression is substituted for a divergent integral.

The rate-domain and high-frequency results allow arbitrary real amplitudes,
signed or zero densities, nonnegative diameters, and finite tails/species.
Rates may repeat. The integral extension assumes the sufficient condition
Re(s)+z_u>0 for every tail; it does not require Re(s)>=0. The high-frequency
half-plane estimates require delta<z_u, for every u. Positive rates supply
an internally chosen delta>0, including when the tail family is empty.
No BH root, root curve, kernel direction, free-volume premise or physical
small-kernel budget is needed for these results.

## Integral extension and the two different origin values

`kernel_laplace_integrable_rate_domain` proves actual absolute integrability
using the frozen recentered kernel weighted integral. The full Q integral,
recentered transform and J/L identities are then re-proved on the wider rate
domain. For s!=0,

    s*Q_ij(s) = rho_i*(L_ij(s)-exp(-s*sigma_i)*J_ij(s)).

The lower-edge shift is retained in the derivation. Compact-core terms place
no convergence restriction on the real part. Every tail denominator is
proved nonzero from its strictly positive real part before division.

`kernel_zero_value` computes the time-origin coefficient
q_ij(0)=rho_i*nonlinearLowerQValue_ij. Separately,
`kernel_laplace_at_zero` computes the true frequency-zero value
Q_ij(0)=rho_i*nonlinearQMoment0_ij by integration. These are different
quantities; no 1/s formula is evaluated at s=0.

## Uniform high-frequency estimates on the full closed half-plane

The exact finite J/L dictionaries give, for Re(s)>=-delta and sufficiently
large |s|,

    |s|*|J_ij(s)| <= jDecayBound_ij,
    |s|*|L_ij(s)-nonlinearLowerQValue_ij| <= lDecayBound_ij.

The phase estimate |exp(-s*sigma_i)|<=exp(delta*sigma_i) uses the explicit
nonnegative diameter premise. The constants are finite sums of actual
amplitude coefficients, absolute values of rates, and this phase bound;
they are defined in the source, rather than supplied by a caller.
Consequently, entrywise and after summing all entries,

    |s|^2 * sum_ij |Q_ij(s)-q_ij(0)/s| <= B,
    |s|   * sum_ij |Q_ij(s)| <= matrixAbsSum(q(0))+B.

One explicit threshold is 1+2*sum_u |z_u|. The denominator estimate retains
all contact terms and repeated rates. No unjustified global C1 assumption
on the piecewise kernel is used.

The factor I-Q is a unit outside a computed compact region of that closed
half-plane, since its actual entry norm sum is then strictly below one.
This exterior statement alone says nothing about zeros inside that region.

The actual integral Q is continuous on the entire closed half-plane,
including s=0. The proof dominates the integral by
exp(delta*t)*|q_ij(t)|; it does not assert continuity merely from a singular
rational representation. `actual_kernel_negative_halfplane_control`
collects integrability, continuity, both frequency estimates and exterior
unit control with an internally chosen positive margin.

## Conditional canonical strip gap

The premise of `actual_canonical_kernel_strip_gap` is explicitly

    forall s : Complex, 0 <= Re(s) -> IsUnit(I-Q(s)).

It is full closed-right-half-plane canonicity, including the imaginary axis
and frequency zero. Pointwise real-wave-number stability is not substituted
for it. Establishing this premise on the initial physical interval remains
part of the larger problem.

`continuous_canonical_strip_gap` proves the general compactness argument.
Clamp Re(s) to the domain boundary -delta0 to form a globally continuous
matrix family. Its zero-determinant set inside the closed frequency ball is
compact. If nonempty, its maximum real part is strictly negative by the
stated canonical premise. Taking a smaller positive margin excludes it.
If empty, any sufficiently small positive margin works. Exterior unit
control handles the unbounded region. The actual specialization therefore
obtains delta>0, delta<all z_u and unit I-Q(s) for every Re(s)>=-delta.

The gap is existential; no uniform gap in temperature/density/composition or
through an instability endpoint is claimed.

## Genuine finite inverse and quadratic remainder

`complexNormSum` is the sum of the complex entry norms. It introduces no new
matrix or amplitude norm instance. Its additivity bound, submultiplicativity
and value N on the identity are proved directly from finite sums.
For sum_ij |Q_ij|<=1/2, the actual nonsingular inverse U=(I-Q)^(-1) satisfies

    U = I+U*Q,
    sum_ij |U_ij| <= 2*N,
    sum_ij |(U-I-Q)_ij| <= 2*N*(sum_ij |Q_ij|)^2.

These follow from the true matrix inverse identity. No Wiener inverse,
Neumann expansion convergence, or inverse bound is an added premise.
Combining them with the actual Q estimates proves
`actual_resolvent_halfplane_high_frequency`: for Re(s)>=-delta and large |s|,

    |s|^2 * sum_ij |(U(s)-I)_ij-q_ij(0)/s| <= B_res.

`actual_canonical_resolvent_control` combines the canonical gap, continuous
nonsingular inverse, compact-set boundedness at low frequency, and the
computed high-frequency bound. It obtains one closed negative-real-part
half-plane with continuous, globally uniformly bounded U and the stated
inverse-square remainder. It does not infer canonical behavior at new
amplitudes or beyond the initial branch.

## Remaining analytic obligations

These are frequency estimates, not a proof of time-domain exponential decay.
The next steps are to regularize q(0)/s as q(0)/(s+b), with b>delta, establish
holomorphy including the removable frequency origin and absolute integrability
on vertical lines, and justify Fourier inversion and contour shifting for
the genuine causal Volterra resolvent. The O(1/|s|^2) remainder is an input
to that argument; no contour theorem has yet been silently used.

For the later source connection, the frozen `nonlinearExcessSource_tail`
and `nonlinearExcessSource_weighted_bounded` already prove the true finite
exponential tail at arbitrary amplitudes, under positive rates, nonnegative
diameters and **nonzero free volume**. They do not require a BH root. That
extra free-volume premise must be retained when using them; it is absent
from the kernel/resolvent results above. The old actual-excess integrability
theorem still requires a physical weighted-kernel budget below one, so it
cannot replace the missing canonical resolvent argument. The concrete
`matBaxterPsiOuterFun` offers a constructed Volterra solution for the future
resolvent, with matrix transpose/order and causal extension to be proved.

Applying the actual resolvent to the genuine RDF excess and its actual
renewal derivative must still prove the required decay/global h-tangent L2.
The far-right-half-plane h formula from `ActualHLaplaceJets` cannot simply
be evaluated at the Fourier axis: its affine G pieces need not separately
have boundary integrals. Full Fourier tangent OZ, canonical factor and
amplitude recovery (including zero-density/tracer cases), general no-fold
continuation and tail-shape/Taylor classification remain open. No universal
real-root/Taylor-convergence equivalence is asserted.

## Validation

All 35 new declarations were individually compiled and their exact axiom
reports queried from the installed pinned Lean compiler. Every report uses
only `propext`, `Classical.choice`, `Quot.sound`; each is encoded as an exact
`#guard_msgs` check. The combined run and immutable dependency audits are
recorded in `results/lean/validation.json` and `results/lean/build.log`.

Final combined validation: PASS, 258 exact guards across fifteen research
modules plus the root. Every recorded source, input, compiled artifact and
raw-log hash was independently checked. The 530 frozen source/configuration
hashes and six direct validated FMSAPaper import artifact pins match before
and after compilation; foundation HEAD remains 06e3268. Reproduce with
`python3 scripts/check_project.py`. No shared dependency build was invoked.
