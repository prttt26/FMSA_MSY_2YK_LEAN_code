# Actual RDF excess: variation of constants and canonical decay

Date: 2026-10-28. Research package only, over frozen foundation 1.0.17.
No new mathematical axioms. No foundation, TeX or numerical changes.

## Concrete identification

`CanonicalRenewalFormula.lean` proves the correctly ordered identity

    Y(t) = F(t) + (F*r)(t),  t >= 0,

for the existing real right-oriented matrix Volterra constructor. The
resolvent r is that same constructor instantiated with kernel/source q,q.
`sourceResolventResponse` retains F_im times r_mj and never commutes
matrix factors. Its scalar interval convolutions are continuous, and the
frozen weighted-convolution theorem proves their genuine complex Laplace
integrability and the exact transform Fhat+Fhat*rhat.

A bounded actual kernel with bound M and an affine source give an internally
computed growth bound M+1 for Y and true damped L1 beyond that cutoff. The
actual matrix renewal implies Yhat=Fhat*(I-Q)^(-1). At common damping M+2,
this equals the explicit response transform. Previously proved complex
Laplace uniqueness gives equality on the CLOSED causal half-line. No
separate assumed renewal uniqueness, damping-below-one constraint or
small physical kernel budget is introduced.

The actual `nonlinearRDFExcess` is definitionally this existing constructor
with the actual `nonlinearCausalKernel` and `nonlinearExcessSource`. The
frozen source bound with exponent zero supplies its affine bound, retaining
`vacMix rho sigma != 0`. Thus `actual_excess_resolvent_formula` proves the
actual field identity, not an identity for a supplied candidate field.
This identity itself needs no canonicity or BH-root premise.

## Actual decay and honest boundary transforms

`ActualExcessDecay.lean` proves the scalar estimate

    |(f*g)(t)| <= Cf*Cg*t*exp(-a*t),  t >= 0,

from the actual interval integral, sums over all intermediate species, and
absorbs the linear prefactor at half the positive decay rate. Explicitly,
for K=N*Cf*Cr, the source response is bounded by

    (Cf+K)*(1+(a/2)^(-1))*exp(-(a/2)*t).

Under full closed-right-half-plane canonicity of I-Q, the previous actual
kernel-resolvent theorem supplies delta>0 below every tail rate and actual
real resolvent decay at rate delta/2. The frozen cancelled excess source
has an exponential weight bound at that SAME rate, using nonzero free
volume. The actual field identity now gives actual excess decay at rate
delta/4, with a computed nonnegative uniform constant. This does not infer
decay for the uncancelled affine G background.

`actual_excess_canonical_integrable` proves actual excess positive-axis L1,
real exponentially weighted L1 for every c>-epsilon, and honest complex
Laplace integrability whenever Re(s)>-epsilon. Here epsilon is the actual
positive decay rate obtained above.

`actual_excess_canonical_laplace` also proves, on an internally obtained
negative half-plane Re(s)>-delta/2,

    Xhat(s) = Shat(s) * (I-Q(s))^(-1),

where X is the existing real excess and S is its actual cancelled source.
The proof uses genuine weighted input integrability and the actual source
response, then transfers both integrability and integrals by equality on
positive time. It covers the entire Fourier axis and zero frequency with
actual integrals. The transform half-plane can be wider than the simple
half-rate decay estimate; these two existential cutoffs are not identified.

## Hypotheses and limits

Rates are positive; diameters are nonnegative; free volume is explicitly
nonzero. Canonicity means IsUnit(I-Q(s)) at EVERY complex s with Re(s)>=0,
not just pointwise Fourier stability. Repeated rates, signed/zero densities,
empty finite families and arbitrary amplitudes are allowed. No BH root,
root curve, Jacobian inverse, physical small-kernel budget or altered norm
instance is assumed. Half-line conclusions include t=0. Global L1 of the
max-extended negative-time constructor is not asserted.

Actual amplitude-tangent excess decay, global actual h-tangent L2, full
Fourier-boundary tangent OZ, canonical factor/amplitude recovery, initial
canonicity/continuation, general no-fold and Taylor/tail-shape classification
remain open. No universal real-root/Taylor equivalence is asserted.

## Validation

The two modules have 10 and 8 theorems respectively. Their actual compiler
axiom reports are measured before adding exact guards. All reports use
only `propext`, `Classical.choice`, `Quot.sound`. Full combined validation
and independent artifact/hash auditing are recorded at completion below.

Final combined validation: PASS, 343 exact guards across twenty-one research
modules plus the root. Every recorded input/source/artifact/raw-log hash
was independently checked. All 530 frozen source/configuration hashes,
six direct validated FMSAPaper artifact pins and two direct Mathlib import
artifact pins match before/after. Foundation remains 1.0.17 / 06e3268.
Reproduce with `python3 scripts/check_project.py`; no shared build invoked.

## Follow-up: genuine amplitude-tangent decay closed (2026-10-28)

`ActualExcessSourceTangent` and `ActualExcessTangentDecay` prove the genuine
cancelled-source derivative and tail, actual linearized renewal, decaying
forcing A=dS+X*dq and actual Frechet tangent response dX=A+A*r. Actual
tangent decay, positive-axis/weighted L1 and honest boundary Laplace
integrability/formulas now follow at fixed full canonicity and nonzero
free volume, without nearby canonicity or a curve of BH roots. This closes
the tangent-decay item above. Global actual h-tangent L2 and full boundary
tangent OZ remain open. See `codex_actual_excess_tangent_decay.md`.
