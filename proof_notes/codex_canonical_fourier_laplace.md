# Exact Fourier/Laplace normalization and the constructed causal inverse field

Research module: `MSAConvergence/CanonicalFourierLaplace.lean` (17 theorems),
over immutable foundation 1.0.17. This checkpoint remains outside the SI.
No new mathematical axiom or shared dependency build is used.

## Explicit normalization and real-versus-complex variables

`fourierScale` is the complex embedding of the real number 1/(2*pi).
`normalizedInverse F a t` is exactly that constant times the previously
proved unnormalized vertical integral V_a(t). `dampedField u gamma t`
is exp(-gamma*t)*u(t) with complex exponential, and

    scaledSymbol F gamma xi = F(gamma+2*pi*i*xi).

The auxiliary xi is mathlib's standard Fourier frequency; k=2*pi*xi is the
angular frequency of the actual Laplace symbol. Every scale and measure
factor is proved, rather than inferred from a convention or left implicit.

`vertical_integral_split_phase` proves the actual integral factorization
V_a(t)=exp(a*t)*integral exp(i*k*t)*F(a+i*k) dk.
`scaled_symbol_fourierInv` uses the real linear substitution k=2*pi*xi in
the actual Bochner integral. Its Jacobian is 1/(2*pi), since 2*pi>0. It proves

    IFFT(scaledSymbol F gamma)(t)
      = exp(-gamma*t)*normalizedInverse F gamma t.

This algebraic integral identity is used with the separately proved actual
frequency L1; it is not an assertion that arbitrary divergent integrals
converge. Cauchy line independence then replaces gamma by a fixed interior
reference a, proving `shifted_fourierInv_eq_damped` for gamma>a>lower.
The previous whole-time weighted L1 gives actual integrability of the
right-hand side and therefore of this standard inverse Fourier transform.

## Fourier inversion uses verified integrability

Mathlib's `Continuous.fourier_fourierInv_eq` requires the forward transform
of its argument to be L1. The available new estimate is L1 of the inverse
transform. `fourier_inversion_of_inverse_integrable` proves the needed
forward L1 by reflecting the real variable: IFFT(f)(-x)=FFT(f)(x), and
reflection preserves integrability. No missing forward-transform L1 is
added as a hypothesis of the actual model theorem.

`scaled_symbol_integrable` obtains frequency L1 by the actual nonzero
2*pi dilation. Holomorphy on the open half-plane supplies continuity of
the scaled symbol. Genuine Fourier inversion therefore applies to it.
There is no unverified interchange of the two bare oscillatory integrals;
mathlib's proved inversion theorem handles that analytic step.

## Actual full-time and positive-axis Laplace identities

`damped_laplace_integrand_eq` factors a complex Laplace integrand into a
unit-modulus imaginary exponential times the genuinely damped field. The
bounded-multiplier theorem proves its full-real-axis absolute integrability.
`fourier_damped_eq_laplace` computes the corresponding standard Fourier
integral at s=gamma+2*pi*i*xi with the exact phase and signs.

Apply the proved FFT/IFFT identity, evaluate xi=k/(2*pi) and cancel the
nonzero scale. The actual causal support, including t=0, reduces the full
integral to Ioi(0). `normalized_inverse_laplace` proves, for gamma>a>lower,

    integral over t>0 of normalizedInverse(F,a,t)*exp(-(gamma+i*k)*t)
      = F(gamma+i*k),

and separately proves full-real-axis absolute integrability before that
identity is used. This works also for negative gamma above the chosen
reference line, not just sufficiently large positive damping.

## Restore the leading causal exponential

`causalExponential v b t` is the Ici(0) indicator times v*exp(-b*t).
The value at zero is v; negative times are zero. The actual complex
exponential integral gives v/(s+b) when Re(s)+b>0, with absolute
integrability first proved on Ioi(0), extended to Ici(0) and then to the
whole real line by its measurable indicator.

`restoredInverse F v b a` adds this leading term to normalizedInverse.
`restored_inverse_laplace` proves both full-time Laplace L1 and the actual
positive-axis formula

    Laplace(restoredInverse)(s)=F(s)+v/(s+b).

Both summands are integrable before the integral is split. The field is
continuous on Ici(0), has value v at zero, and is zero for t<0. It need not
be globally continuous across zero when v!=0; no such claim is made.
If -b<=a, its norm on t>=0 is bounded by

    (|v|+|fourierScale|*C*pi)*exp(a*t).

## Actual canonical MSA kernel interface

Let q be the existing `nonlinearCausalKernel`, including row density, and
Q(s)=`rdfMatrixLaplace q s`. The actual specialization uses

    F_ij(s)=((I-Q(s))^(-1)-I)_ij-q_ij(0)/(s+b),
    v=q_ij(0), a=-delta/2.

`actual_canonical_resolvent_field` internally obtains delta>0 below every
tail rate, b>delta and one B>=0 for every species pair. The constructed
field r_ij(t)=restoredInverse(F_ij,v,b,a,t) satisfies:

- continuity on the closed causal half-line;
- r_ij(0)=q_ij(0), and exact zero values at negative times;
- genuine whole-real-line L1;
- |r_ij(t)|<=B*exp(-delta*t/2) for all t>=0;
- for EVERY s with Re(s)>-delta/2, genuine whole-time absolute Laplace
  integrability and the actual positive-axis formula

      integral over t>0 of r_ij(t)*exp(-s*t) = ((I-Q(s))^(-1)-I)_ij.

Thus the transform identity includes the Fourier axis and zero frequency
with honest integrals. No affine-G transform is evaluated at a divergent
boundary by totalization or by an unproved analytic-continuation step.
The time-origin coefficient is q(0), separately distinguished from Q(0)
in the preceding modules.

The hypotheses are positive finite tail rates, nonnegative diameters and
EXPLICIT full closed-right-half-plane unit control of I-Q. Repeated rates,
signed/zero densities, empty finite families and arbitrary amplitudes are
allowed. No BH root, root curve, nonzero free volume, Jacobian inverse,
physical small-kernel budget or pointwise-Fourier-stability substitute.
No amplitude or matrix norm instance changes.

## Remaining actual-field identification

The Fourier/Laplace normalization and causal inverse-field construction
obligations are now closed. Equality with the PRE-EXISTING actual Volterra
or RDF constructors is still open. The new field is explicitly constructed
and has the actual kernel's inverse transform, but this module does not
silently assert an unproved renewal equation or identify another constructor
from causal support alone. The next step can use Laplace uniqueness on a
common sufficiently damped line, or prove the actual renewal identity and
apply Volterra uniqueness. The earlier real-only fixed-damping uniqueness
interface may need a genuine complex/general-damping extension.

Actual excess/h-tangent decay and global h L2, Fourier-boundary tangent OZ,
canonical factor/amplitude recovery, initial canonicity/continuation,
general no-fold and Taylor/tail-shape classification remain open. The
later actual excess-source application must retain vacMix!=0. No universal
real-root/Taylor-convergence equivalence is asserted.

## Validation

All 17 new declarations were individually compiled and their actual axiom
reports queried. Every report uses only `propext`, `Classical.choice`,
`Quot.sound` and has an exact `#guard_msgs` check. The complete run records
compiler options, input/source/artifact/raw-log hashes, immutable foundation
audits and direct Mathlib import artifact pins. The newly explicit Fourier
inversion import is read-only and hashed before/after; it is never built
by this package. No foundation/TeX/numerical edit or merge-back.

Final combined validation: PASS, 310 exact guards across eighteen research
modules plus the root. Every recorded input/source/artifact/raw-log hash
was independently checked. The 530 frozen source/configuration hashes,
six direct validated FMSAPaper artifact pins and two direct Mathlib import
artifact pins match before/after. Foundation remains 1.0.17 / 06e3268.
Reproduce with `python3 scripts/check_project.py`; no shared build was invoked.

## Subsequent actual-kernel Volterra checkpoint (2026-10-28)

`CanonicalVolterraResolvent` now identifies the constructed inverse field
on Ici(0) with the existing concrete real kernel/source-q Volterra
constructor, using complex common-damping uniqueness. Actual kernel-
resolvent decay, real weighted L1 and Fourier-boundary transforms follow.
See `codex_canonical_volterra_resolvent.md`. The actual G/excess source
formula and propagation of decay to those RDF fields remain open.
