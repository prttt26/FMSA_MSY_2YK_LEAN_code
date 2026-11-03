# Actual canonical left response and weighted kernel-tangent recovery

Date: 2026-10-28. Isolated research over frozen foundation 1.0.17 / 06e3268.
No new mathematical axioms, foundation/TeX/numerical edits or merge-back.

`CausalFactorTangent.lean` adds 9 theorems;
`ActualCanonicalKernelTangent.lean` adds 20. The active-pair actual DCF
conclusion is now connected to a vanishing actual canonical left response
and to pointwise weighted kernel-tangent recovery on the closed causal
half-line. Full amplitude recovery and the tracer problem remain open.

## Actual left response with honest integrals

Let q be the actual row-density causal kernel, dq its genuine spatial
amplitude Frechet variation, and r the already constructed ACTUAL real
canonical kernel resolvent. Define

    L(t)=dq(t)+(r*dq)(t).

One transpose of the proved right source/resolvent formula preserves this
LEFT matrix order. L is a genuine continuous real field. Positive rates,
nonnegative diameters and full canonicity at the fixed amplitude base
point give honest positive-axis L1 and, at every Re(s)>=0,

    Lhat(s)=(I-qhat(s))^(-1)*dqhat(s).

Both inputs have proved real damped L1; integrability is supplied before
convolution transforms are multiplied. The underlying Volterra resolvent
is max-extended at negative time. Only its positive-axis L1 is used;
no global L1 assertion is made for that max extension. Full-line Fourier
fields below use an explicit causal zero extension followed by a shift.
There is no derivative of the whole resolvent parameter family here.

## Actual physical logarithmic response

Put R=diag(rho), S=diag(sqrt(rho)), P(s)=diag(exp(-s*sigma/2)) and
A(s)=I-qhat(s). For nonnegative densities S*S=R, even with zero entries.
Let F(k) be the actual physical density-weighted Baxter Fourier factor.
At arbitrary amplitudes,

    F(k)*F(-k)^T=I-S*C(k)*S,
    F(k)^T*S*P(s)=S*P(s)*A(s)^T,     s=i*k.

These are ALL-AMPLITUDE finite identities with the actual Q/C symbols.
The actual factor family has genuine entry derivatives. The preceding
actual active-pair DCF cancellation implies

    S*dC(k)*S=0,     k!=0.

For an active pair this follows from its actual a.e.-zero ordered DCF
variation and the proved radial derivative dictionary. For a pair with
zero density the square-root weight is zero; no density is divided.

Differentiate only the all-amplitude product identity. Full canonicity
already supplies units F(k) and F(-k). For B(k)=F(k)^(-1)*dF(k), finite
unit cancellation gives

    B(k)+B(-k)^T=0.

No root curve or differentiation of a root-only factor symmetry is used.
Differentiating the all-amplitude phase identity gives its legitimate
first-order counterpart. The density/phase transport lemma proves

    S*B(k)*S=P(s)^(-1)*(A(s)^(-1)*dA(s))*P(s)*R.

The crucial point is that S occurs only as a congruence: S is never
inverted. Actual kernel-integral derivative interchange gives
dA=-dqhat. Hence the HONEST actual response symbol

    X(s)=P(-s)*Lhat(s)*P(s)*R=-S*B(k)*S

satisfies X(s)+X(-s)^T=0 for every nonzero imaginary s.

## Touching causal supports and the source sign convention

The frozen source defines

    edgeLo sigma i j=(sigma j-sigma i)/2.

Claude 085 correctly requested a non-overlap check but wrote the
opposite lambda formula; 086 records this source-convention correction.
The actual matrix phase gives EXACTLY

    X(i*2*pi*w)_ij
      = Fourier(causalShift(rho_j*L_ij, edgeLo_ij))(w).

All matrix/species order and k=2*pi*w normalization are proved. The ij
shifted response has support [edgeLo_ij,infinity). The reflected TRANSPOSE
ji response has support (-infinity,-edgeLo_ji]=(-infinity,edgeLo_ij].
They touch at one point; they do not overlap on an interval.

`unequal_pair_touching_supports` explicitly checks sigma=(1,1/2), both
pair orders, both edge values (-1/4 and +1/4), and both reflected support
thresholds. This check would expose a transpose-before/after-reflection
or phase sign error which equal diameters would miss.

The generic uniqueness proof uses actual shifted L1 functions. The sum
of one field and the reflected other field has Fourier transform zero
a.e.; only w=0 is excluded. This transform is genuinely L1, so the proved
Fourier inversion theorem gives zero at actual continuity points.
Strictly beyond the touching point the reflected field is identically
zero on a neighbourhood. The actual continuous positive-time response
therefore vanishes for t>0. Closure and its proved one-sided continuity
then give zero at t=0 as well. No point mass, distributional delta or
endpoint value is inferred merely from an a.e. identity.

## Proved actual recovery capstones

`actual_weighted_left_response_zero` gives, on t>=0,

    rho_j*L_ij(t)=0

for every species pair. Its honest actual transform is therefore zero,
not a formally evaluated nonconvergent background. Left multiplication
by the actual canonical A and the honest response identity give

    dqhat(s)*R=0,      Re(s)>=0,

including zero. Common-damping Laplace uniqueness at gamma=0 then proves

    kernelVariationField(t)*R=0,      t>=0.

`actual_kernel_variation_active_column_zero` extracts the pointwise
consequence kernelVariation_ij(t)=0 when rho_j>0. This final corollary
divides only a PROVED positive column density. Zero-density columns are
not divided. The actual kernel already carries row densities; a tracer
row may therefore be identically zero without recovering its underlying
unweighted Baxter variation.

Main recovery hypotheses are positive finite rates, positive diameters,
nonnegative densities, nonzero free volume, symmetric strengths, an actual
fixed-tau BH root, a genuine actual BH-Jacobian kernel direction, and full
closed-right-half-plane canonicity at that fixed base point. Repeated
rates, empty finite tail families and zero-density species are allowed.
There is no independent hQ, radial tangent OZ, physical factor-unit or
antisymmetry premise; these are discharged through the actual proved
interfaces. No neighbouring root/canonical family, Jacobian inverse,
small physical kernel budget or norm change is assumed.

## Remaining work

This is WEIGHTED actual kernel recovery, not zero of the full amplitude
kernel vector. Unweighted tracer rows/columns and the Dt/G coordinates
still need recovery from the actual BH residual equations. General
Jacobian invertibility/no-fold is therefore not yet claimed. Initial
canonicity/continuation along the initial stable interval and Taylor/
tail-shape classification also remain open. No universal real-root/Taylor
iff, whole-h boundary amplitude-integral interchange, global-L2 smooth
parameter family or RDF positivity is asserted.

## Validation

All 29 actual compiler footprints are queried before exact guards.
Final combined validation: PASS, **513 exact standard-three guards across
32 research modules plus the root**. All 29 actual compiler reports were
queried before guards. Every recorded input/source/artifact/raw-log hash
was independently checked. All 530 frozen source/configuration hashes,
the same seven validated direct FMSAPaper artifact pins and all three
prior direct Mathlib pins remain unchanged before/after.
Reproduce with `python3 scripts/check_project.py`. The existing seven validated direct FMSAPaper artifact pins
and three direct Mathlib artifact pins remain the same. No shared/Lake
build is invoked.


## Follow-up: actual BH amplitude recovery (2026-10-28)

The next three modules, documented in
`codex_actual_bh_amplitude_recovery.md`, recover dDt*diag(rho)=0 and
 diag(rho)*dG*diag(rho)=0 from the actual all-amplitude BH residual equations.
Strictly positive species densities therefore close full pointwise actual
Jacobian kernel recovery and continuous invertibility of the genuine residual
partial derivative. The remaining-work paragraphs above describe this module
alone: full recovery with zero-density tracers, initial canonicity/continuation
and tail-shape classification remain open in the combined package.
