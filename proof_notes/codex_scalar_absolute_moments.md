# Explicit absolute-moment budgets and original BH frequency steps

Full guarded validation and independent post-run audit passed:
**1136 exact guards /104 research modules plus root /105 compiler commands.**
All9 new ACTUAL queries contain exactly propext, Classical.choice and
Quot.sound. All103 prior module source/artifact/footprint fingerprints,
530 frozen hashes and existing9paper/2raw/9Mathlib import pins are unchanged.
The126 compiler input hashes and every source/artifact/root/raw-log hash
were independently verified. No new mathematical axiom or external import.

## Proved coefficient budgets

For the original unit-diameter scalar Baxter q, define its honest absolute
moment M_n=integral_real abs(r^n*q(r)). Positive rates and a finite tail set
internally imply integrability. Signed, repeated, inactive or empty tails
are allowed. Put

    S2=abs(qp)/12+abs(A)/60
       +sum(2abs(W)/z^3+abs(C)*(1/3+1/z+2/z^2+2/z^3)),
    S3=abs(qp)/20+abs(A)/120
       +sum(6abs(W)/z^4+abs(C)*(1/4+1/z+3/z^2+6/z^3+6/z^4)).

`absoluteMoment_two_le` proves M_2<=S2; `absoluteMoment_three_le` proves
M_3<=S3. These are triangle INEQUALITIES. For example repeated rate1,
W=(1,-1) and qp=A=C=0 gives q=M_2=0, while S2=4. This S2 is a moment
budget; the earlier Fourier-tail B2 has a separate definition.

The general `absoluteMoment_le_budget` treats every natural n. Its core
terms are abs(qp)/((n+1)(n+2)) and abs(A)/((n+1)(n+2)(n+3)); W contributes
abs(W)*n!/z^(n+1), while C contributes its core moment1/(n+1) plus its
honest shifted exterior moment. The latter is then evaluated exactly for
n=2 and3. No guessed integral value or integrability premise is supplied.

## Majorant and exact integral

The proof bounds abs(r^n*q(r)) pointwise by the sum of three NONNEGATIVE
indicator functions:

- Icc(0,1): abs(qp)*r^n*(1-r)+abs(A)*r^n*(r-1)^2/2+sum abs(C)*r^n;
- Ici(0): sum abs(W)*r^n*exp(-z*r);
- Ioi(1): sum abs(C)*r^n*exp(-z*(r-1)).

Literal q is zero to the left of0. The core and exterior formulas give
pointwise domination, including the actual values at0 and1. The W term is
kept on Ici0; its endpoint is removed only by the proved measure identity
when evaluating the integral. The C core/exterior split counts1 once.

All three terms are proved integrable internally: continuity on the compact
core, the positive-rate polynomial-exponential moment on Ici0, and the
shifted exterior moment on Ioi1. Integral monotonicity, finite-sum linearity
and the already proved exact moments evaluate the majorant. No root, seed,
canonical hypothesis, coefficient independence or new Mathlib import.

## True derivatives and complete closed steps

For nonnegative rho, the actual physical frequency second derivative obeys

    norm(F''(k))<=rho*M_2<=rho*S2

at EVERY real k, including0 and vacuum. `secondDerivative_norm_le_of_budget`
is this closed bound. `secondMomentBudget_le_of_bounds` replaces actual
absolute coefficients by verified qpU,AU,WU,CU. A density bound rho<=rhoU
then gives `secondDerivative_norm_le_of_bounds` with the explicit upper
budget rhoU*upperSecondMomentBudget. Its coefficient and density assumptions
internally imply the needed nonnegativity; no extra Hessian bound is given.

`fourierFactor_interval_isUnit_of_budget` and
`fourierFactor_interval_isUnit_of_bounds` combine that bound with actual
point budgets m<=norm(F(k0)), norm(F'(k0))<=d, h>=0, and

    L>=rhoU*upperSecondMomentBudget,
    m-d*h-L*h^2/2>0.

They conclude units of the ORIGINAL physical Fourier MATRIX at EVERY k in
the closed interval [k0,k0+h], using the proved sharp1/2 remainder. No
sampled-only inference is made.

The final `actual_interval_units_of_bounds` substitutes the ORIGINAL BH
amplitudeA, amplitudeQp, W and C from arbitrary Dt/G. The derivative premise
is written as deriv of the ACTUAL original Fourier matrix entry00. Fin1
extensionality and the genuine frequency derivative theorem discharge all
dictionary identifications internally. No supplied derivative equality,
root, inverse, canonicity, moment, L1 or interchange premise is required.
It retains one species/unit diameter and explicit verified point/coefficient
bounds; it does not assert those numerical inequalities from data alone.

## Remaining obligations

This completes the global-L2 analytic coefficient budget. The CURRENT
compressed173 march often uses Li=min(L2,H2(k_left))<L2, so these theorems
alone cannot instantiate its H2-limited steps. H2 still needs its genuine
actual second-derivative norm bound in Lean. Numerical point/coefficient
and hull enclosures and PY chains remain external, as do their current
first-loss brackets. No M1/M3 kernel numerical instance, first-loss frequency,
zero uniqueness, RDF positivity or coupling-Taylor radius follows.

The general-mixture matrix escape, positive-density ideal-certificate
construction, nonisolated relevant endpoint fibers and multitail complex
Taylor LOWER bounds/classification remain open. No eta<=.8 assumption,
universal real-root/Taylor equivalence, mathematical axiom, foundation/TeX
write or merge-back is introduced.

## Verification status

Four copied mathematical corruptions all exited1 with FIRST errors in the
proof bodies, before guard discrepancies: halve the qp contribution, halve
the A contribution, omit the C core contribution, or halve the W contribution.
The correct guarded module exited0. No supplied Hessian/moment premise was
introduced to rescue a corrupted formula.

The full checker actually exited0 and the independent post-run audit passed.
The prior103 module sources/artifacts/footprints, frozen530 and existing
imports9paper/2raw/9Mathlib, replay9prefixes/37pins and compressed first-loss
receipt's25 pins are unchanged. The separate newly promoted M3 monodromy
receipt has30 verified current inputs and remains explicitly EXTERNAL.
Evidence: `results/lean/validation.json` and `results/lean/build.log`.
The new module imports only ScalarFourierDerivatives. Exact guards were
created from the nine ACTUAL compiler reports, never inferred from imports.
