# Actual concrete Volterra resolvent identification and decay

Research module: `MSAConvergence/CanonicalVolterraResolvent.lean` (15 theorems),
over immutable foundation 1.0.17. This checkpoint addresses Claude message
068 and remains outside the SI. No new mathematical axiom is used.

## Complex common-damping uniqueness

The frozen uniqueness interface was real-valued and fixed at damping 1.
`causal_laplace_injective` now handles f,g:Real->Complex at ANY common real
gamma, assuming actual L1 of exp(-gamma*t)*f(t),g(t) on Ioi(0), continuity
on Ici(0), and equality of their genuine positive-axis transforms at every
gamma+2*pi*i*xi. It concludes equality on Ici(0), including the endpoint.
It does not require global time continuity, positive gamma, or a real/
imaginary split of a complex-line transform hypothesis.

`causalDamping` is the explicit Ici(0) zero extension of the genuinely damped
complex field. Half-line L1 extends to full L1 since the endpoint is null.
The exact Fourier/Laplace normalization from the preceding module computes
its Fourier transform. The difference has zero Fourier transform; genuine
L1 and continuity at each positive time permit mathlib's proved inversion.
The complex exponential is nonzero, so the positive-time difference is zero.
For the endpoint, max-extensions f(max(0,t)),g(max(0,t)) are globally
continuous from the stated half-line continuity, and closure of Ioi(0)
gives equality at zero. No nonexistent global continuity of a causal jump
is assumed.

## The existing concrete real Volterra constructor

`rightVolterra q f hq hf` is not an assumed solution: it directly calls the
frozen `FMSA.MixtureOzStar.matBaxterPsiOuterFun` with transposed kernel and
source, then transposes the output. It proves actual continuity, the source
initial value, and the correctly ordered renewal

    Y_ij(t)=f_ij(t)+sum_m integral_0^t Y_im(u)*q_mj(t-u) du.

This transposition retains matrix order; scalar real entry multiplication
is commuted only to match the already proved frozen entrywise identity.
No commutativity of matrix products is assumed.

`kernelResolvent q hq` specializes the source to the same actual q. Thus
it is the classical concrete real right resolvent satisfying

    r=q+r*q,

with q as given, without a spectral premise or an unknown solution argument.

## Internally computed growth and far-right transforms

If the actual matrix entry-absolute-sum of q is globally bounded by M>=0
on the positive half-line, the already proved weighted Volterra estimate
computes

    exp(-(M+1)*t)*matrixAbsSum(r(t)) <= M*(M+1).

This preliminary exponential order allows growth. It is not a physical
small-kernel-budget condition. Transposition preserves the actual absolute
sum, and the source q bound gives the affine bound M*(1+t) internally.
Each actual entry therefore has real damped L1 at every c>M+1.

Actual kernel/source/resolvent integrability justifies the existing real
weighted-convolution Laplace theorem and the integrated matrix renewal

    rhat(s)*(I-Q(s))=Q(s), Re(s)>M+1.

Strong damping computes IsUnit(I-Q(s)) from the actual norm-sum bound;
no canonical premise is needed at this preliminary stage. Right multiplication
by the true finite inverse and the identity U=I+Q*U prove
`kernel_resolvent_laplace_eq`:

    rhat(s)=(I-Q(s))^(-1)-I.

All matrix positions are retained. No inverse-series axiom or undamped
convolution integrability is supplied by a caller.

## Actual MSA kernel identification

`actualKernelResolvent z rho sigma p` inserts the existing
`nonlinearCausalKernel`, including row density, into that concrete real
kernel/source-q Volterra constructor. `actual_kernel_resolvent_canonical`
then obtains an internal M from the proved actual finite-dictionary bound
and chooses the common damping gamma=M+2. This is larger than the actual
computed growth cutoff; it is never forced below 1 by a physical budget.

The previous `actual_canonical_resolvent_field` constructs a complex causal
inverse with the same genuine transform and exponential decay. Its domain
Re(s)>-delta/2 includes the chosen far-right line. Both fields have actual
common-damping L1 and half-line continuity. The new complex uniqueness
theorem identifies their values for every t>=0, including contact t=0.
The spectral field's reality on that half-line follows from this equality;
no separate unproved reality premise is inserted.

The actual theorem obtains delta>0 below every tail rate, b>delta and B>=0,
and for every species pair proves:

- equality on Ici(0) with the normalized/restored inverse field;
- |actualKernelResolvent_ij(t)|<=B*exp(-delta*t/2) for t>=0;
- actual real positive-axis L1;
- real weighted L1 of exp(-c*t)*actualKernelResolvent_ij(t) for EVERY
  c>-delta/2, including small negative damping;
- for EVERY Re(s)>-delta/2, actual positive-axis complex Laplace L1 and
  the exact formula rhat_ij(s)=((I-Q(s))^(-1)-I)_ij.

This includes the Fourier axis and frequency zero with honest actual
integrals. The real weighted interface matches the frozen convolution
transform theorem for the next variation-of-constants step.

The max-extended concrete Volterra representative is generally constant
at negative time. The spectral causal field is zero there. Only half-line
equality is proved, and global-real-line L1 of that max representative is
not asserted. Positive-axis Laplace transforms and the explicitly causal
zero extension preserve the intended meaning.

The model assumptions remain positive finite rates, nonnegative diameters
and EXPLICIT full closed-right-half-plane unit control of I-Q. Repeated
rates, signed/zero densities, empty finite families and arbitrary amplitudes
are allowed. No BH root, root curve, nonzero free volume, Jacobian inverse,
physical small-kernel budget or pointwise-stability substitute is used.
No amplitude or matrix norm instance changes.

## Remaining actual RDF connection

The kernel/source-q Volterra identification is now closed. The actual G,
RDF excess and genuine h tangent are DIFFERENT fields. Their decay has not
yet been inferred from decay of this kernel resolvent.

Claude 068's next route is the correctly ordered formula Y=F+F*r. Both the
actual right renewal and that explicit source convolution have matching
transforms at a sufficiently strong common damping. The frozen real-valued
weighted-convolution theorem can now be reused with this actual real r;
no new reality proof or complex convolution surrogate is needed. Continuity
and the proved complex common-damping uniqueness can establish the actual
formula. For decay, the actual excess source must first cancel the affine
background; its frozen tail bound requires vacMix!=0. This source connection
and the propagation to the genuine tangent remain unproved at this checkpoint.

Global actual h-tangent L2, full Fourier tangent OZ, canonical factor/
amplitude recovery, initial canonicity/continuation, general no-fold and
Taylor/tail-shape classification remain open. No universal real-root/
Taylor-convergence equivalence is asserted.

## Validation

All 15 new declarations were individually compiled and their actual axiom
reports queried. Every report contains only `propext`, `Classical.choice`,
`Quot.sound` and is checked with an exact `#guard_msgs` command. Full compiler
commands, input/source/artifact/raw-log hashes, frozen foundation audits
and the direct Mathlib artifact pins are recorded by `check_project.py`.
No shared build, foundation/TeX/numerical edit or merge-back is involved.

Final combined validation: PASS, 325 exact guards across nineteen research
modules plus the root. Every recorded input/source/artifact/raw-log hash
was independently checked. The 530 frozen source/configuration hashes,
six direct validated FMSAPaper artifact pins and two direct Mathlib import
artifact pins match before/after. Foundation remains 1.0.17 / 06e3268.
Reproduce with `python3 scripts/check_project.py`; no shared build was invoked.

## Follow-up: actual excess connection closed (2026-10-28)

`CanonicalRenewalFormula` and `ActualExcessDecay` now prove the actual
excess source response X=S+S*r, actual exponential decay and weighted L1,
plus honest boundary Laplace formulas under full canonicity and nonzero
free volume. This closes the excess connection left open above. Decay of
the genuine amplitude tangent and global actual h-tangent L2 remain open.
See `codex_canonical_excess_decay.md` for exact scope and validation.
