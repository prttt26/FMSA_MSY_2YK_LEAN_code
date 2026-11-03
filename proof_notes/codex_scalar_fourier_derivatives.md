# Actual Fourier frequency derivatives and closed-step matrix units

Full guarded validation and independent post-run audit passed:
**1127 exact standard-three guards / 103 research modules plus root /
104 pinned compiler commands.** All 23 new public proof bodies have ACTUAL
queries containing exactly propext, Classical.choice and Quot.sound. Exact
guards were inserted from those compiler messages. ALL 100 prior module
sources/artifacts/footprints, 530 frozen hashes and all 9 paper / 2 raw /
9 Mathlib import pins are unchanged.

Every derivative here differentiates the real wave number k with the physical
amplitudes fixed. The geometry is one species of unit diameter, an arbitrary
finite tail set, positive rates, arbitrary signed qp,A,W,C, and rho>=0.
Repeated/inactive tails and vacuum are allowed. No root, canonical seed,
supplied differentiability, moment integrability or derivative-interchange
identity is assumed.

## Exact moments and actual integrability

`ScalarFourierMoments` has10 public declarations. It proves, for EVERY n,

    integral_(0,infinity) r^n*exp(-z*r) = n! / z^(n+1),

and the integrability required to use that formula. Gamma's existing proved
natural values and a positive-rate change of scale give the exact formula;
polynomial/exponential decay proves L1 independently. No new external import
or Gamma axiom is introduced. A measure-preserving translation proves the
shifted exterior identity; n=2 and n=3 give

    integral_(1,infinity) r^2*exp(-z*(r-1)) = 1/z+2/z^2+2/z^3,
    integral_(1,infinity) r^3*exp(-z*(r-1)) = 1/z+3/z^2+6/z^3+6/z^4.

The compact basis moments are proved for arbitrary n:

    integral_0^1 r^n = 1/(n+1),
    integral_0^1 r^n*(1-r) = 1/((n+1)*(n+2)),
    integral_0^1 r^n*(r-1)^2/2 = 1/((n+1)*(n+2)*(n+3)).

`weighted_q_integrable` is about the ORIGINAL scalar Baxter q, not just a
formal basis. Its support is split into r<0, [0,1] and r>1; the left part is
zero, the compact part is a continuous exponential polynomial, and the
exterior is a finite sum of the proved weighted tails. Their union covers
the whole real line. Thus EVERY r^n*q(r) is L1 from the physical rate data.

## Genuine derivatives at every frequency, including zero

`ScalarFourierDerivatives` has11 public declarations. Define the honest
weighted integrals

    Phi_n(k) = integral_real r^n*q(r)*exp(-i*k*r),
    M_n = integral_real abs(r^n*q(r)).

Uniform unit phase modulus preserves their internally proved L1 bounds.
The dominated integral-derivative theorem, with the actual next absolute
moment as integrable majorant, proves

    HasDerivAt Phi_n (-i*Phi_(n+1)(k)) k

for EVERY real k. There is no removable-denominator formula in this proof.
The physical density-weighted matrix entry is exactly F=1-rho*Phi_0.
Consequently its true first derivative is rho*i*Phi_1 and its true second
derivative is rho*Phi_2. `factor_hasSecondDerivAt` explicitly differentiates
`deriv` of the existing physical factor. The second derivative has the
uniform bound rho*M_2; M_2 integrability is internally discharged.

## From point budgets to a whole physical frequency interval

`QuadraticFrequencyStep` has2 public declarations. It first bounds the
variation of a genuine first derivative by L*(t-a), then uses a variable
quadratic barrier L*(t-a)^2/2 in the proved derivative comparison theorem.
This gives the sharp1/2 Taylor remainder without assuming an integral
remainder identity or importing a weaker mean-value estimate.

For the actual physical factor, h>=0, and verified point budgets

    m <= abs(F(a)),  abs(F'(a)) <= d,
    m-d*h-(rho*M_2)*h^2/2 > 0,

`factor_interval_ne_zero` excludes zeros on the ENTIRE closed interval
[a,a+h]. `fourierFactor_interval_isUnit` returns units of the ORIGINAL
physical1-by1 Fourier MATRIX at every point of that interval. Derivatives,
the norm bound and integrability are not supplied by the caller.

The point budgets and strict numerical inequality remain explicit premises.
This is a proved analytic interval criterion, not a data-only numerical
M1/M3 instance. In particular, the actual absolute second moment has NOT yet
been bounded here by the external certificate's closed qp/A/W/C budget.
The exact basis moments above prepare that remaining triangle-bound proof.
Equality with a coefficient triangle budget would be false: with two tails
of rate1, W=(1,-1) and qp=A=C=0, the actual q and absolute second moment
vanish identically, while the separate W coefficient budget is4. Repeated
rates and cancellation remain allowed by the actual theorems.
Numerical Re/Im/derivative enclosures, amplitude hulls and the PY chain still
require kernel instances. No all-wave/full-half-plane canonicity, first-loss
frequency, root count, RDF positivity or coupling-Taylor radius follows.

## Negative mathematical controls

Three copied sources were compiled separately and all exited1 with their
FIRST errors in the mathematical proof bodies, before guard discrepancies:

- multiply the exact exponential moment by2;
- reverse the sign of the genuine weighted Fourier derivative;
- strengthen the quadratic remainder by changing its denominator2 to3.

The correct guarded versions of all three modules each exited0. The controls
were run before the complete1127/103 validation started; all125 pinned
Lean/checker inputs stayed unchanged throughout that full run. These controls supplement kernel
checking; they are not additional mathematical premises.

## Validation status and wider goal

All23 ACTUAL queries contain exactly propext, Classical.choice and Quot.sound.
The three modules import only existing research modules; the frozen
foundation and existing 9 paper / 2 raw / 9 Mathlib pins are unchanged. The
complete checker exited0. The independent post-run audit checked EVERY one
of the 125 input hashes, every source/artifact/root/raw-log hash and ALL 100
prior module sources/artifacts/footprints against the 1104 baseline. The same
9 generated prefixes / 37 pins are unchanged; the fresh compressed external
all-wave receipt's 25 pins are verified. No shared/Lake build was invoked. Evidence:
`results/lean/validation.json` and `results/lean/build.log`.

General mixture amplitude escape, nonisolated relevant endpoint fibers,
positive-density ideal certificates and multitailed complex Taylor LOWER
bounds/classification remain open. No new mathematical axiom, universal
real-root/Taylor equivalence, foundation write, TeX write or merge-back.
