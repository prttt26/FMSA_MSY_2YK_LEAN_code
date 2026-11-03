# Actual BH amplitude recovery and positive-density canonical regularity

Date: 2026-10-28. Isolated research over frozen foundation 1.0.17 / 06e3268.
No new mathematical axioms, foundation/TeX/numerical edits or merge-back.

`ActualBHAmplitudeRecovery.lean` adds 12 theorems;
`PolynomialExponentialSeparation.lean` adds 4;
`ActualBHSecondAmplitudeRecovery.lean` adds 25. Together they prove
continuous invertibility of the genuine BH amplitude partial derivative
at every strictly positive-density canonical root satisfying the explicit
hypotheses below. This closes the positive-density pointwise
canonical-to-Jacobian bridge. Initial canonicity, branch continuation,
zero-density tracer recovery and tail-parameter classification remain open.

## Scope and actual interfaces

Fix finite species and tail families, positive rates z_u, positive diameters
sigma_i, nonnegative species densities rho_i, symmetric prescribed strength
matrices K_u and a real coupling t. Assume nonzero actual free volume
vacMix(rho,sigma), an actual BH root p=(Dt,G) for t*K, and full canonicity
at this fixed amplitude base point:

    I-qhat(s) is a unit for EVERY complex s with Re(s)>=0.

Here q is the frozen actual causal kernel and qhat its honest matrix Laplace
integral. For v in the kernel of the ACTUAL amplitude Jacobian, all weighted
statements below hold under nonnegative densities. Only the final full
recovery and inverse-interface conclusions require EVERY rho_i>0.

No assumption of a supplied Jacobian inverse, differentiable root curve,
neighbourhood canonicity, small physical kernel budget, distinct rates,
particular tail-strength signs or infinite-dimensional polynomial norm is
used. All Frechet derivatives use the existing amplitude-space norm.

## Recovering the first BH amplitudes

Let R=diag(rho) and let Q_u be the frozen root-recentered transform at z_u,
without the row-density factor. The honest real/complex Laplace dictionary
and all-amplitude actual kernel formula give

    qhat(z_u)=R*Q_u,
    dqhat(z_u)=R*dQ_u.

These are identities for the actual functions and their genuine Frechet
derivatives, not new definitions of their values. Actual whole-kernel
amplitude derivative interchange has already been proved upstream.
The preceding canonical-kernel module supplies dqhat(s)*R=0, including
s=z_u, and hence R*dQ_u*R=0.

The actual first BH residual identity holds at ALL amplitudes:

    firstLHS_u=Dt_u*(I-R*Q_u^T).

Its genuine derivative in the actual fixed-coupling Jacobian kernel gives

    dDt_u*(I-R*Q_u^T)-Dt_u*R*dQ_u^T=0.

Multiply on the right by R and use R*dQ_u^T*R=0. The remaining right factor
is (I-R*Q_u)^T, a unit by full base canonicity. Unit cancellation proves

    dDt_u*R=0.

Thus each positive-density column of dDt vanishes, including rows of
zero-density species. No symmetry of Dt or inverse density matrix is used.

## Actual J/L polynomial separation

For every positive real c, the honest actual kernel tangent dictionary is

    c*dqhat_ij(c)=rho_i*(dL_ij(c)-exp(-sigma_i*c)*dJ_ij(c)).

Multiply by rho_j and use dqhat(c)*R=0. The actual real-axis J/L derivative
dictionaries then give

    rho_i*rho_j*dL_ij(c)
       = exp(-sigma_i*c)*(rho_i*rho_j*dJ_ij(c)).

The true grouped-rate common denominator D(c) is nonzero for c>0. Actual
coefficientwise numerator derivatives have proved finite degree bounds
(card(distinct rates)+1 for J, +2 for L). The coefficient-derivative/evaluation
interchange already established in PolynomialJets yields

    dNumJ_ij(c)=D(c)*dJ_ij(c),
    dNumL_ij(c)=D(c)*dL_ij(c).

These use actual numerator coefficient smoothness and all-amplitude rational
identities. They impose no norm on the polynomial space. Repeated tail rates
remain grouped rather than being assumed distinct.

The new elementary separation theorem proves

    P(c)=exp(-a*c)*Q(c) for all c>0, a>0  ==>  P=Q=0.

Each monomial times the decaying exponential tends to zero. A finite sum
therefore does too, while a real polynomial tending to zero at infinity
must be zero by the proved leading-coefficient characterization. The second
polynomial then has infinitely many roots. Applying this with a=sigma_i
to the actual density-weighted tangent numerator polynomials proves both
vanish. Cancelling the genuine nonzero D(c) gives

    R*dJ(c)*R=0,       c>0.

The strict positive-diameter assumption is explicit and essential to this
separation step; no zero-decay-rate conclusion is asserted.

## Recovering the second BH amplitudes

The actual finite rational J evaluated at z_u equals the frozen secondRHS_u.
The genuine second residual identity at ALL amplitudes is therefore

    secondResidual_u=(2*pi*G_u)*(I-R*Q_u)-J(z_u).

Set H_u=2*pi*G_u. Differentiating along v gives

    dH_u*(I-R*Q_u)-H_u*R*dQ_u-dJ(z_u)=0.

Multiplication on the left and right by R and the previous two weighted
zero identities give

    (R*dH_u*R)*(I-Q_u*R)=0.

Sylvester's finite determinant identity transfers the unit of I-R*Q_u
to I-Q_u*R without inverting R. Unit cancellation and 2*pi!=0 prove

    R*dG_u*R=0.

Thus G tangent entries vanish on each positive-density species pair. This
weighted conclusion makes no assertion for pairs involving a tracer.

## Full positive-density regularity and the actual local-branch interface

If every rho_i>0, the two weighted amplitude recoveries give v.1=0 and
v.2=0. Hence the actual amplitude Jacobian has zero kernel. As a linear
self-map of the EXISTING finite-dimensional amplitude space it is bijective.
The Banach inverse construction provides a continuous linear equivalence.
The final theorem

    actual_residual_partial_isInvertible_of_positive_densities

returns exactly

    ((fderiv R_actual (t,p)).comp (ContinuousLinearMap.inr ...)).IsInvertible

with the real scalar field specified in Lean. This is the genuine residual
partial derivative interface consumed by the frozen local-branch theorem,
not an alternative norm, surrogate residual or assumed inverse.

Full fixed-base canonicity, nonzero free volume, positive rates/diameters,
symmetric prescribed strengths and an actual root remain explicit hypotheses.
The result is pointwise and allows arbitrary real t and repeated rates.
It does not itself select a PY-connected branch or establish canonicity
anywhere. A no-fold/analytic continuation theorem for the whole initial
stable interval still needs those branch hypotheses and their propagation.
Neither RDF positivity nor a universal real-root/Taylor-convergence iff is
claimed. Global-L2 amplitude-family differentiability is not inferred.

## Validation

All 41 new theorem footprints were obtained from the actual compiler before
exact guards were added; each is exactly propext, Classical.choice, Quot.sound.
Final combined validation: PASS, **554 exact standard-three guards across
35 research modules plus the root** (36 direct compiler commands). Every
recorded input/source/artifact/raw-log hash was independently checked. All
530 frozen source/configuration hashes and all seven previous direct
FMSAPaper artifact pins remain unchanged before and after. Reproduce with
`python3 scripts/check_project.py`.

There are no new direct FMSAPaper imports: the same seven validated artifacts
are read only. The new polynomial limit proof directly imports the existing
Mathlib.Analysis.Polynomial.Basic artifact, which is hashed before and after
the run as a fourth direct Mathlib pin. All three previous Mathlib pins are
preserved. No Lake or shared dependency build is invoked.


## Follow-up: full zero-density tracer recovery (2026-10-28)

The later AdditiveDensityTangentOZ, ActualTracerDCFCancellation and
ActualTracerAmplitudeRecovery modules close the tracer gap described above.
The genuine actual Jacobian residual partial is continuously invertible under
the same root/canonical/rate/diameter/free-volume/strength hypotheses with
rho>=0 ONLY, allowing zero-density species. The earlier positive-density
capstones remain valid special cases. See
`codex_actual_tracer_dcf_cancellation.md` for the true all-pair c/h fields,
two Parseval passes, G-first recovery and honest column-projection argument.
Initial canonicity, PY-connected branch continuation and tail classification
remain open in the combined package.
