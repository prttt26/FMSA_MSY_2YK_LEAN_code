# Actual radial tangent OZ and active-pair DCF cancellation

Date: 2026-10-28. Research over frozen foundation 1.0.17 / 06e3268.
No new mathematical axioms, foundation/TeX/numerical edits or merge-back.

`FiniteTangentOZ.lean` adds 10 theorems;
`ActualRadialTangentOZ.lean` adds 17. The actual radial tangent OZ premise
of the earlier cancellation theorem is now discharged internally. The
independent physical Fourier-factor unit premise is also eliminated,
using full closed-right-half-plane canonicity at the fixed base point.

## Legitimate first variations of actual finite defects

`VanishingVariation F p v` contains actual entry differentiability,
F(p)=0 and the genuine real Frechet derivative DF(p)[v]=0. Addition,
subtraction, fixed complex rescaling and multiplication by any smooth
matrix family preserve it in their correct orders. No constraint is
assumed to hold on a neighbourhood or along a curve of roots.

At s=i*k, k!=0, write R=diag(rho), Qplus=actualFourierQ(k),
Qminus=actualFourierQ(-k), Cplus=actualFourierC(k), Cminus=actualFourierC(-k),

    Y(s)=J(s)*(I-qhat(s))^(-1),
    E(s)=P(s)*Y(s)*P(s),
    B(s)=P(s)*J(s)^T*P(s),
    Mplus=I-Qplus*R,       Nplus=I-Qplus^T*R,
    Mminus=I-Qminus*R,     Nminus=I-Qminus^T*R.

The actual renewal Y*A=J, A=I-qhat, and its genuine finite-family
variation are proved at each fixed unit frequency. The preceding
ActualReciprocityTangent module supplies Y^T=Y and (dY)^T=dY at the base
point and kernel direction. Transpose renewal and its variation, together
with the ALL-AMPLITUDE actual identity Nplus*P=P*A^T, therefore give

    Nplus*E(s)-B(s)=0,      d(Nplus*E(s)-B(s))=0,

and likewise at -s. This differentiates only global identities or genuine
local finite unit identities, never a root-only reciprocity statement.

The actual source defect has zero value by the base actual U/V
certificates and zero derivative by the genuine kernel U/V variations.
The ALL-AMPLITUDE sum of the defects at k and -k is s*(Cminus-Cplus),
so Cplus-Cminus also has zero value and true first variation.

## The exact finite OZ error identity

Put Tplus=I-Cplus*R. At arbitrary amplitudes, without any root constraint,

    Tplus*(E(-s)-E(s))-s*Cplus
      = Mplus*(Nminus*E(-s)-B(-s))
        - Mminus*(Nplus*E(s)-B(s))
        + actualSourceDefect(k)
        + (Cplus-Cminus)*R*E(s).

This is proved as an exact noncommutative finite identity, using the
actual all-amplitude Q product formula for Cplus and Cminus. All four
right-hand defects have zero value and genuine first variation at the
root/kernel direction. Therefore the left-hand defect has both properties.
Only after this is established do we normalize by the fixed nonzero s:

    Hfinite(k) = s^(-1)*(E(-s)-E(s)),
    (I-Cplus*R)*Hfinite=Cplus,
    (I-Cplus*R)*dHfinite=dCplus+dCplus*R*Hfinite.

The base Hfinite is a finite symbol. No actual whole-h amplitude-family
boundary derivative or base h integral representation is presumed here.
The base finite OZ identity is sufficient for the structure inverse step.

## Actual h integrals and the exact 2*pi normalization

Actual canonical tangent decay and the direct contact-phase theorem
already supply honest positive-radius h tangent integrals at both s and
-s. Before any finite substitution, the exponential difference identity
and justified subtraction of these L1 integrals prove

    radialSymbol(dh)(k)
      = (2*pi/s)*(Laplace(r*dh)(-s)-Laplace(r*dh)(s)).

The finite completed-phase symbol is genuinely locally amplitude-smooth
at these two fixed unit frequencies. Its derivative has the fixed phase
sandwich, and the already proved honest h boundary response gives

    Laplace(r*dh)(s) = dE(s)/(2*pi).

Consequently the actual radial h tangent integral equals the genuine
finite-family derivative dHfinite, for every nonzero real k and every
actual amplitude direction. This actual bridge is not postulated as a
radial OZ premise and does not claim a whole-h boundary integral
amplitude-interchange theorem. It is valid off root under full canonicity.

## Structure inverse and physical factor units, including tracers

For nonnegative densities set S=diag(sqrt(rho)), so S*S=R, including zero
entries. Multiplying the proved finite base/tangent equations by S gives

    A*X=Cweighted,      A*dX=dCweighted*(I+X),
    A=I-S*Cplus*S,      X=S*Hfinite*S.

A unit A implies I+X=A^(-1), hence

    dX=A^(-1)*dCweighted*A^(-1).

No inverse density or inverse square root occurs.

The needed physical factor unit is now PROVED from canonicity. For each
real k, including k=0, the all-amplitude phase identity and nonzero
exponential diagonal phase imply Nplus is a unit when I-qhat(i*k) is.
Transposition gives a unit I-R*Qplus. The finite determinant identity

    det(I-S*Qplus*S)=det(I-R*Qplus)

then proves the actual physical Baxter Fourier factor is a unit. This
step needs nonnegative densities, but no root, positive rate, diameter
or nonzero-frequency assumption. It therefore supplies the existing
physical Fourier-factor premise at every real frequency from full
base-point canonicity, without excluding tracer species.

At a symmetric-strength actual BH root the existing proved radial DCF
identification equates A with the actual radial denominator. The actual
spectral C derivative is the genuine ordered radial DCF derivative by
RadialDCFTangent. The strength argument in that amplitude derivative is
definitionally irrelevant, so the fixed-tau Jacobian and actual t*K root
use the correct K conventions. All species weights are retained.

## Proved actual capstones and precise scope

`actual_radial_tangent_OZ` proves, for every k!=0,

    radialHTangentMatrix(k)
      = structureMatrix(k)*radialVariationMatrix(k)*structureMatrix(k).

These are the ACTUAL existing radial integral symbols. Hypotheses are:
positive finite rates, positive diameters, nonnegative densities, nonzero
free volume, symmetric strengths, an actual fixed-tau BH root, a genuine
BH-Jacobian kernel direction, and full closed-right-half-plane canonicity
at that fixed amplitude base point. There is no supplied OZ equation,
independent physical Fourier-factor unit, neighbouring root/canonical
family, Jacobian inverse, physical small-kernel budget or norm change.
Repeated rates, empty finite tail families and zero-density species are
allowed. The finite source phase algebra itself also allows signed densities;
nonnegativity is added for square-root density weighting/positive pairing.

`actual_kernel_DCF_ae_zero` instantiates the existing spatial orthogonality,
L1/L2 Fourier representatives, positive matrix pairing and actual radial
OZ engine. The k=2*pi*w convention is retained. Nonzero k holds almost
everywhere by excluding only w=0, so no zero-frequency radial OZ theorem
is needed for this step. The result is

    orderedVariation_ij = 0 a.e. on Ioi(0)
    whenever rho_i>0 and rho_j>0.

This capstone has NO caller-supplied hQ field, tangent OZ or physical
Fourier-factor unit premise. Full canonicity remains explicit. It does
not assert cancellation on pairs involving zero-density tracer species.
Nor does it yet prove the entire amplitude kernel vector is zero.

## Remaining work

The actual radial tangent OZ and active-pair DCF cancellation gaps are
closed under the stated canonical hypotheses. Canonical factor and
amplitude recovery from this DCF conclusion, including tracer species,
remain open. In particular, a general no-fold/invertible-Jacobian theorem
is not inferred just from the active-pair result. Initial canonicity and
continuation along the initial stable interval, plus Taylor/tail-shape
classification, still require proof. No universal real-root/Taylor iff,
global-L2 amplitude-family smoothness or RDF positivity is asserted.

## Validation

Actual compiler footprints are queried before exact guards are added.
Final combined validation: PASS, **484 exact standard-three guards across
30 research modules plus the root**. All 27 new actual compiler reports
were queried before guards. Every recorded input/source/artifact/raw-log
hash was independently checked. All 530 frozen source/configuration
hashes, all seven prior validated direct FMSAPaper pins and all three
prior direct Mathlib artifact pins are unchanged before/after.
Reproduce with `python3 scripts/check_project.py`. The existing seven validated direct
FMSAPaper artifact pins and all three direct Mathlib pins remain the same;
the determinant-swap lemma is already available through existing imports.
No Lake/shared build is invoked.


## Follow-up: actual canonical weighted kernel recovery

The later ActualCanonicalKernelTangent module constructs the genuine L1
left response dq+r*dq and transports actual zero weighted C variation to
an anti-transpose physical logarithmic response. The exact shifted-causal
Fourier dictionary and the source edgeLo convention prove the reflected
supports touch without interval overlap; both unequal-diameter orders
are checked explicitly. Fourier uniqueness and one-sided continuity
force rho_j*leftResponse_ij(t)=0 on t>=0. Honest unit renewal and half-line
Laplace uniqueness then give kernelVariationField(t)*diag(rho)=0, hence
actual kernel-tangent zero in each positive-density column. This is
weighted kernel recovery: zero-density columns, unweighted tracer rows
and the full Dt/G amplitude vector are not recovered by this statement.
General no-fold remains open. See `codex_actual_canonical_kernel_tangent.md`.
