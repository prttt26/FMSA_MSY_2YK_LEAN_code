# Actual source and h boundary-tangent reciprocity

Date: 2026-10-28. Research over frozen foundation 1.0.17 / 06e3268.
No new mathematical axioms, foundation/TeX/numerical edits or merge-back.

## The gap addressed

The actual U/V tangent certificates are not syntactically the separate
`nonlinearComplexReciprocityResidual` tangent. The latter cannot be
obtained by differentiating an implication whose hypotheses hold only
at a BH root. A Jacobian-kernel vector need not be tangent to a supplied
curve of roots. This module proves the missing first-order implication
from base constraints and their genuine zero derivatives.

`SymplecticTangent.lean` contains 22 theorems;
`ActualReciprocityTangent.lean` contains 11. No amplitude norm instance
is changed. Matrix derivatives are entrywise genuine real Frechet
derivatives, assembled as finite complex matrices.

## First-order symplectic completion

At a fixed nonzero imaginary frequency, write P=diag(rho), with arbitrary
signed or zero densities, and use the actual J,L,J(-s),L(-s). Define

    A = I - s^(-1) P L,       B = s^(-1) J,
    M = -s^(-1) P J(-s) P,    D = I + s^(-1) L(-s) P.

The three all-amplitude block identities are

    A M^T - M A^T = s^(-1) P V(-s) P,
    A D^T - M B^T = I + s^(-1) P U(s),
    B D^T - D B^T = s^(-1) V(s).

At an actual symmetric-strength BH root the actual U,V,V(-s) values
vanish. Along every genuine fixed-coupling BH-Jacobian kernel vector,
their actual Frechet derivatives vanish by ComplexWronskianJets. Thus
the block matrix T=[[A,M],[B,D]] satisfies the base symplectic identity
and its genuine linearized constraint. Algebraic multiplication by the
base identity transfers the linearized identity to T^T Omega T, using
Omega^2=-I. Extracting its upper-left block proves

    d(A^T B - B^T A) = 0.

The all-amplitude identity

    A^T B - B^T A = s^(-1) nonlinearComplexReciprocityResidual

then proves the separate actual reciprocity residual derivative is zero.
The base block identity also proves its value is zero. This is a joint
value/derivative theorem, with matrix and entrywise derivative wrappers.
There is no division by species density, nearby root family, Jacobian
inverse, or physical kernel-budget premise.

The base actual result needs positive rates, nonzero free volume,
symmetric strengths, an actual BH root, a genuine Jacobian-kernel vector
and s!=0, Re(s)=0. It needs no diameter or canonicity hypothesis.

## A genuinely differentiable finite completed symbol

Define Y(a,s)=J(a,s)*(I-qhat(a,s))^(-1). This is a finite matrix function,
not the asserted integral of the uncancelled nondecaying affine G on the
imaginary axis. The actual kernel integral family is already proved
amplitude-smooth at each Re(s)>=0, including zero. At any fixed unit
frequency its determinant is nonzero on a derived amplitude neighbourhood.
Finite determinant/adjugate smoothness therefore proves actual local
amplitude C-infinity of Y and

    dY = (dJ + Y*dqhat)*(I-qhat)^(-1).

Only local invertibility at this single fixed frequency is derived; a
nearby physically canonical family is not assumed. This derivative
formula itself includes s=0 and uses no J/L divisions by frequency.

For s!=0 on the imaginary axis the frozen ALL-AMPLITUDE actual factor
identity identifies the reciprocity residual with

    Ahat^T J - J^T Ahat,       Ahat=I-qhat.

Its genuine derivative is differentiated as an all-amplitude identity.
The proved residual value and derivative, together with

    Y Ahat=J,   dY Ahat+Y dAhat=dJ,

give Y^T=Y and (dY)^T=dY by cancelling the unit Ahat and its transpose.
This adds nonnegative diameters and a unit at the single frequency; it
does not require full closed-half-plane canonicity.

## Transfer to the honest actual h tangent integral

The already proved actual finite boundary response is exactly

    Laplace(r*dh)(s) = (2*pi)^(-1) Pphase(s)*dY(s)*Pphase(s).

This equality holds for every s!=0, Re(s)>=0, with actual integrability
supplied by the existing canonical tangent decay and contact-shift
proofs. It is a bridge from an honest integral of the actual spatial
Frechet tangent to a genuine FINITE-symbol derivative. It does not
assert differentiation under the entire h boundary integral family.

The diagonal phase is transpose-symmetric. The completed-symbol tangent
reciprocity therefore proves transpose symmetry of the ACTUAL
Laplace(r*dh) matrix at every nonzero imaginary frequency along every
actual BH-Jacobian kernel vector at a symmetric-strength BH root.
This actual h transfer adds positive diameters and full closed-right-
half-plane canonicity at the fixed base point, not a nearby family.
Repeated rates, empty finite tail families and signed/zero densities
remain allowed. The reciprocity theorem is only claimed at nonzero
imaginary frequency; separate previous phase/forcing theorems cover
zero without asserting this new 1/s-based reciprocity argument there.

## Remaining work

The separate source-reciprocity tangent gap identified in handoff 079
is closed. Full actual radial tangent OZ delta-H=S*delta-C*S still needs
the residual/source-defect and contact-phase algebra connected to the
actual radial DCF derivative. The actual active-pair cancellation theorem
still retains its explicit tangent-OZ premise. The next route is to
linearize the all-amplitude factor-phase
and source-defect identities, using the newly proved completed-symbol
value and derivative reciprocity at the base point. The actual radial h
symbol still needs its honest plus/minus-frequency integral dictionary;
a root-only OZ identity must not be differentiated. For factor units
without inverse densities, Mathlib's Matrix.det_one_sub_mul_comm is an
available finite determinant route (not yet instantiated here).
No global-L2 amplitude-family differentiability or whole-h boundary
integral derivative interchange is inferred from fixed-base-point tangent membership.

Canonical factor/amplitude recovery including tracer species, initial
canonicity/continuation, general no-fold and Taylor/tail-shape
classification remain open. No universal real-root/Taylor equivalence.

## Validation

Exact compiler axiom reports are queried before guards are added.
Final combined validation: PASS, **457 exact standard-three guards across
28 research modules plus the root**. All 33 new compiler footprints were
queried before guards were added. Every recorded input, source, artifact
and raw-log hash was independently checked. All 530 frozen source/config
hashes and all seven prior validated direct FMSAPaper artifact pins are
unchanged. The two prior direct Mathlib pins are unchanged; the third
SymplecticGroup artifact is pinned before/after. No shared build.
Reproduce with `python3 scripts/check_project.py`. The existing seven validated FMSAPaper artifact
pins and two direct Mathlib artifact pins are retained. A third direct
read-only Mathlib pin, LinearAlgebra.SymplecticGroup, supplies its already
compiled finite matrix identity; no dependency is rebuilt.


## Follow-up: actual radial tangent OZ and active-pair cancellation

The later `ActualRadialTangentOZ.lean` now closes the full actual radial
tangent OZ gap described above. The exact all-amplitude finite OZ error
identity, actual phase/source/evenness first variations and honest
plus/minus-frequency h integrals give the actual radial tangent equation
at every nonzero real frequency. Full base canonicity also supplies all
physical Fourier-factor units, including zero frequency, by a density-free
finite determinant argument with nonnegative densities. The actual
active-pair DCF variation is therefore zero a.e. without a supplied hQ,
tangent OZ or independent physical factor-unit premise. Canonical factor/
amplitude recovery including tracers and general no-fold remain open.
Precise assumptions and validation: `codex_actual_radial_tangent_oz.md`.
