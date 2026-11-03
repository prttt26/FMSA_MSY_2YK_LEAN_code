# Actual h tangent boundary response and finite J/L transcription

Date: 2026-10-28. Isolated package over frozen foundation 1.0.17.
No new mathematical axioms, foundation/TeX/numerical edit or merge-back.

`ActualSourceBoundary.lean` adds 28 theorems;
`ActualHBoundaryResponse.lean` adds 6. This implements the direct h-phase
route suggested in Claude 077 and proves the additional actual cancelled-
source and kernel-variation interfaces needed for a pure finite formula.

## Direct actual h phase, including zero

The affine G background depends on radius and fixed contacts, not on the
amplitudes. The existing proved identity dG=dX is reused. The genuine
causal-shift integral theorem and the PROVED actual tangent boundary L1
therefore give, for every Re(s)>=0,

    Laplace(r*dh)(s) = P(s)*Laplace(dX)(s)*P(s).

P is the existing additive-contact diagonal phase. Actual absolute
integrability is included, and zero frequency is covered. No limiting
passage is needed for this phase step. The already proved actual
cancelled tangent renewal gives, on the same closed half-plane,

    Laplace(r*dh)(s) = P(s)*(Ahat(s)*U(s))*P(s),
    A = dS + X*dq,   U = (I-Qhat)^(-1).

This is not obtained by substituting zero damping into the earlier
far-right formula in ActualHLaplaceJets.

## Actual cancelled-source finite boundary formulas

The actual S, dS and dq have proved real weighted L1 for every nonnegative
real damping, using their genuine tail bounds and a finite positive rate
margin. They require no small physical kernel budget or BH-root curve.

The real affine background B(t)_ij=t+R_ij and its convolution with q are
transformed ONLY at positive damping. Every input is genuinely L1 there,
and the actual source definitions give

    Shat = J/(2*pi) - Bhat + Bhat*Qhat,
    dShat = dJ/(2*pi) + Bhat*dqhat.

On the imaginary boundary, Bhat is the EXPLICIT RATIONAL matrix
1/s^2+R_ij/s. It is not separately asserted to be the integral of a
nondecaying affine function there.

The actual finite J symbol is expanded in its fixed rational frequency
dictionary, and its genuine amplitude Frechet derivative uses the actual
coefficient derivatives. This proves the required frequency continuity of
dJ at each nonzero imaginary frequency. The actual L1 S,dS,dq fields have
proved Abel continuity of their genuine integrals. Consequently the two
formulas above extend to all Re(s)>=0, s!=0. Only integrable cancelled
fields are taken to that boundary. There is no boundary differentiation
of an amplitude integral in this source step.

## Actual kernel integral derivatives on the axis

Each fixed recentered kernel basis has a genuine exponential tail plus a
compact polynomial part. A compact maximum and the actual finite tail
prove its exponential weight bound. Thus every fixed basis integral is
L1 even on the Fourier axis, independently of its amplitude coefficient.

The actual kernel integral family is therefore amplitude C-infinity at
each fixed Re(s)>=0, including zero. Genuine differentiation of its whole
integral commutes with the fixed finite L1 dictionary. In this KERNEL
case boundary amplitude/integral interchange is actually proved, rather
than inferred from pointwise parameter smoothness. It gives, for s!=0,

    s*Qhat_ij = rho_i*(L_ij-exp(-s*sigma_i)*J_ij),
    s*dqhat_ij = rho_i*(dL_ij-exp(-s*sigma_i)*dJ_ij).

`finiteKernelSymbol` and `finiteKernelVariationSymbol` are these purely
finite J/L expressions divided by s. Both are proved equal to the honest
actual integral transforms on the closed right half-plane away from zero.
Row density and all species orders are retained.

## Pure finite actual h response

The actual forcing convolution theorem gives

    Ahat = dShat + Xhat*dqhat.

All its inputs have PROVED actual real weighted L1; this includes zero.
Canonical actual excess renewal supplies Xhat=Shat*U. At nonzero s in the
closed right half-plane the finite source formulas and (I-Qhat)*U=I give

    Xhat = J/(2*pi)*U-Bhat,
    Ahat = dJ/(2*pi)+J/(2*pi)*U*dqhat.

The Bhat*dqhat terms cancel algebraically AFTER actual integrability and
finite source identities are established. Matrix factors are never commuted.
Hence the actual integrated h Frechet tangent has the pure finite form

    Laplace(r*dh) =
      P * ((dJ/(2*pi)+J/(2*pi)*U*dK)*U) * P,
    U=(I-K)^(-1),

where K and dK are the actual finite J/L kernel symbols proved above.
This holds for EVERY Re(s)>=0, s!=0, not just a computed far-right cutoff.
At s=0 the direct forcing/phase theorems remain valid without J/L divisions.
The finite J/L formula with 1/s is not asserted at zero.

## Scope and remaining OZ step

Source and kernel boundary interfaces are off root. The actual h/excess
responses retain positive finite rates, nonzero free volume and full
closed-right-half-plane canonicity at the FIXED amplitude base point.
Nonnegative diameters are used for the source/kernel interfaces; positive
diameters supply positive pair contact for the full h phase. Repeated rates,
empty finite tail families, signed/zero densities and arbitrary actual
amplitude directions are allowed. No nearby canonical family, root curve,
Jacobian inverse, physical small-kernel budget or norm-instance change.

The actual h field uses its justified existing pointwise Frechet derivative.
A new amplitude derivative/interchange theorem for its entire boundary
integral family, or global-L2 amplitude-family smoothness, is not asserted.
The kernel finite-dictionary interchange above is a separate proved result.

The residual-kernel actualSourceDefect derivative already vanishes, but
its finite matrix algebra still has to be connected to THIS actual h
response and to the actual radial DCF Fourier derivative. Full actual
radial tangent OZ delta-H=S*delta-C*S is not yet proved by this checkpoint.
Any additional reciprocity tangent identity must be checked/proved off root;
root-only symmetry cannot be differentiated along an arbitrary residual-
Jacobian kernel vector. The U/V tangent certificates are not syntactically
the separate nonlinearComplexReciprocityResidual tangent, so that step
must not be silently assumed.
Active-pair DCF cancellation therefore still retains that explicit OZ
premise. Canonical factor/amplitude recovery including tracers, initial
canonicity/continuation, general no-fold and Taylor/tail-shape classification
remain open. No universal real-root/Taylor equivalence is asserted.

## Validation

Actual compiler axiom reports are queried before exact guards. Validation
uses the installed pinned compiler and read-only validated dependencies,
without Lake/shared builds. The seven direct validated FMSAPaper artifact
pins and two direct Mathlib artifact pins remain the existing set. Full
combined validation and independent hash auditing are recorded below.

Final combined validation: PASS, 424 exact guards across twenty-six research
modules plus the root. All 34 new compiler footprints contain exactly the
standard three axioms. Every recorded input/source/artifact/raw-log hash
was independently checked. All 530 frozen source/configuration hashes,
seven direct validated FMSAPaper artifact pins and both direct Mathlib
artifact pins match before/after. Foundation remains 1.0.17 / 06e3268.
Reproduce with `python3 scripts/check_project.py`; no shared dependency
build was invoked.

## Follow-up: the separate reciprocity tangent is now proved

The later `ActualReciprocityTangent.lean` closes the specific gap flagged
above. First-order symplectic completion uses actual U/V values and their
genuine zero derivatives, without differentiating a root-only implication.
The actual `nonlinearComplexReciprocityResidual` value and Jacobian-kernel
derivative vanish at every nonzero imaginary frequency. A genuinely
locally amplitude-smooth finite symbol Y=J*(I-Qhat)^(-1) has derivative
(dJ+Y*dqhat)*(I-Qhat)^(-1); source reciprocity transfers to both Y and dY.
The actual integrated h tangent is exactly P*dY*P/(2*pi), proving actual
h boundary-tangent reciprocity at these frequencies under full base-point
canonicity and positive diameters. Zero-frequency reciprocity is not
asserted by this additional argument. Full actual radial tangent OZ
remains open. See `codex_actual_reciprocity_tangent.md` for the precise
hypotheses and current validation.
