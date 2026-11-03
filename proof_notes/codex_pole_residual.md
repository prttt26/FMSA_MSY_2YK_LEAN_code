# Off-root pole residuals and genuine Jacobian-kernel variations

These declarations are isolated research in `MSAConvergence/PoleResidual.lean`
and `MSAConvergence/ResidualJets.lean`. The foundation remains frozen at
1.0.17 / 06e3268. They are not integrated, and this checkpoint is not the
end-of-research merge. No TeX is written.

## Exact off-root algebra

The frozen foundation already proves automatic finite Wronskian admissibility
at actual symmetric-strength BH roots for general finite species/tail sets.
An equality on that root set alone cannot be differentiated in an arbitrary
Jacobian-kernel direction: a kernel vector need not extend to a root curve.
The new result supplies the error terms away from the root set.

For arbitrary square matrices over a commutative ring, only P^T=P is needed.
Keep the displayed multiplication order. Set

    W = H P D,                 C = D - E W,
    J = H (I - P Q) + S,        L = Q + E J,
    B = D (I - P Q^T),          A = B^T - B,
    M = I - E H P.

`matrix_pole_errors` proves all four identities simultaneously:

    W^T - C P J^T - L P W^T
      = M A P H^T - C P S^T - E S P W^T,

    W - J P C^T - W P L^T
      = H P A^T M^T - S P C^T - W P S^T E^T,

    J P W^T - W P J^T
      = H P A P H^T + S P W^T - W P S^T,

    C - C^T + L P C^T - C P L^T
      = -M A M^T + E S P C^T - C P S^T E^T.

There is no symmetry premise on D, H, Q, W or C. The proof is exact
noncommutative polynomial normalization in Lean, not a numeric test.
The fourth off-root identity must retain the full -M A M^T term. A shorter
formula internal to the frozen root-only proof used A=0 and cannot be
promoted to a general off-root identity.

## Actual MSA transcription

For each existing tail label u, use the existing BH amplitudes p=(Dt,G):

    P = diag(rho),
    E = diag(exp(-z_u sigma_i)),
    D = Dt_u,                  H = (2 pi / z_u) G_u,
    Q = nonlinearRootRecenteredTransform(..., u),
    J = z_u^(-1) nonlinearRationalJ(..., z_u),
    L = z_u^(-1) nonlinearRationalL(..., z_u).

W and C are precisely the existing actual W/C constructors. For arbitrary
p, fixed coupling t and symmetric prescribed strengths K, the actual full
residual R=(R1,R2) supplies

    A = (R1_u)^T - R1_u,
    S = -z_u^(-1) R2_u.

`normalized_J_residual` and `first_skew_residual` prove those identities.
`actual_pole_residual_factorization` then identifies all four actual
`poleDefects` with `poleErrorLift(p,R(p))`, not merely their values at roots.
The lift depends polynomially on amplitudes and independent error data.
`poleErrorLift_zero` proves F(p,0)=0 for every p.

The construction permits repeated tail rates, any finite number of species,
and zero densities. Rates are positive for the actual rational transcription.
No free-volume inverse, kernel-smallness condition or amplitude symmetry
is used for these finite-pole conclusions.

## Actual differentiation

`residual_lift_kernel_fderiv` is a general chain-rule lemma. If R(p)=0,
DR(p)v=0, F is differentiable at (p,0) and F(a,0)=0 for every a, then

    D[a -> F(a,R(a))](p)v = 0.

The derivative of the graph a -> (a,R(a)) sends v to (v,0). The derivative
of the zero-error slice a -> F(a,0) annihilates that direction. The lemma
uses actual Frechet derivatives throughout and never posits a root curve.

`poleErrorLift_entry_contDiff` proves joint smoothness internally. Finite
matrix multiplication and transposition are treated in the local entry norm
using scalar entry maps and finite sums. This does not change the original
BH amplitude-space norm. Existing actual W/C smoothness supplies the
coefficient derivatives; there is no caller-provided smoothness premise.

`actual_kernel_poleDefects_fderiv_zero` applies the lemma to the genuine
fixed-coupling `JacobianExterior.amplitudeJacobian` and the full actual BH
residual. All four normalized pole-defect entry derivatives vanish at every
actual symmetric-strength root along every actual Jacobian-kernel vector.

`yukawaResidues` reproduces the frozen foundation's unnormalized four
residue matrices in the same order. `yukawaResidues_eq_rate_smul` proves
these equal z_u times the normalized defects. The corresponding theorem
`actual_kernel_yukawaResidues_fderiv_zero` therefore gives the genuine
unnormalized residue derivatives required by the finite Wronskian polynomial
interface. The actual normalized defect family is proved smooth off-root by
`actual_poleDefects_entry_contDiff`.

The subsequent `DistinctPoleJets`/`PolynomialJets`/`WronskianJets` modules now
complete the repeated-rate polynomial evaluation bridge and construct the
genuine coefficientwise tangent U/V polynomials. The full reflected-rate
factor divides both tangents, leaving degree-five U and degree-four V
remainders. See `codex_wronskian_tangents.md`. Their complete disappearance
is now proved in `NormalizedWronskianJets` under positive rates and nonzero
free volume; see `codex_normalized_wronskian_tangents.md`.

## Scope and next step

This is finite Yukawa-pole cancellation for actual tangents. The entire actual tangent finite Wronskian polynomial certificate is now
proved in `NormalizedWronskianJets`: origin coefficients, degree bounds and
polynomial factor completion are transcribed through the actual derivative. Vanishing finite-pole variations alone
must not be described as the complete tangent spectral OZ identity.

Global actual h-tangent L2 control, complete tangent OZ, canonical tangent
factor uniqueness/amplitude recovery and the general no-fold theorem remain
open. Existing local Lp and compact tangent-renewal results remain valid.
No universal equivalence between real roots and Taylor convergence is asserted.
No new axioms are introduced. The user decision to keep this Jacobian line
outside the SI remains in force.

Validation uses `python3 scripts/check_project.py`, with exact compiler axiom
footprints and source/artifact hashes in `results/lean/validation.json`.
It compiles only this research package against read-only validated foundation
imports, checking all 530 frozen source/configuration hashes before and after.
It invokes no Lake/shared-dependency build.

Verified isolated checkpoint: PASS, 34 exact standard-three-axiom theorem
guards across three research modules (13 new guards here), plus the root.
The foundation's 530 source/configuration hashes and all three directly
imported FMSAPaper artifact hashes were unchanged before/after compilation.
No shared dependency build was invoked. Foundation manifest pin:
`09ade0691482098319e832c6c721b77ef70d99bb76cec5bc84b498357dd9219c`.
