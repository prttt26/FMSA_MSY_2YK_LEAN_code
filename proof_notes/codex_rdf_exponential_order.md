# Actual RDF exponential order and tangent Laplace renewal

The research file `MSAConvergence/RDFExponentialOrder.lean` continues the
actual RDF tangent work over the immutable foundation 1.0.17. No foundation,
TeX or numerical file is changed; the coordinated merge remains deferred.

## Actual quantities

Let Y be the existing `nonlinearCausalG`, q the existing
`nonlinearCausalKernel` (including its row-density factor), and F the existing
`nonlinearGSource`. All deltas below are genuine real amplitude Frechet
derivatives at p applied to v, as defined in `ActualRDFTangent`. F here is the
G source, not the full BH residual. No root curve is supplied or inferred.

The actual equations, already established on every finite interval, are

    Y(r) = F(r) + integral_0^r Y(t) q(r-t) dt,
    delta Y(r) = delta F(r)
      + integral_0^r delta Y(t) q(r-t) dt
      + integral_0^r Y(t) delta q(r-t) dt.

The new results make their global growth and Laplace meaning explicit.

## Internally computed global bound

`kernelVariation_eq_basis` and `sourceVariation_eq_basis` prove exact
fixed-basis formulas for the genuine derivatives at every real r. They
retain every actual amplitude coefficient. `recenteredBasis_bounded_positive`
proves kernel basis bounds on the whole nonnegative axis, using compact
continuity and the actual exponential tail. `gSourceBasis_affine_bound`
proves source basis growth is at most affine. `matrix_dictionary_bound`
assembles a computed matrix entry-sum bound from the finite coefficients.

The arbitrary compact radius is removed in `causalVariation_continuousOn`.
The existing extension below zero satisfies `causalVariation_eq_max`, so the
actual derivative is globally continuous (`causalVariation_continuous`).

Use the upper triangular block matrices, with the actual right-oriented
renewal transposed:

    Qjet = [[q^T, delta q^T], [0, q^T]],
    Fjet = [[F^T, delta F^T], [0, F^T]],
    Yjet = [[Y^T, delta Y^T], [0, Y^T]].

`actual_jet_renewal` proves the exact left-oriented block renewal. Finite
indices are reindexed to Fin(N+N) to reuse the existing entry-sum matrix
estimate; this changes no multiplication order. The entry sum is
2*absSum(A)+absSum(delta A), as proved in `blockJet_absSum`.

The fixed dictionaries give finite constants M,C >= 0 such that Qjet is
bounded by M and Fjet by C*(1+r). The generic theorem
`matrix_renewal_exponential_order` then **chooses** damping gamma=M+1:

    integral_(r>0) exp(-gamma*r) absSum(Qjet(r)) <= M/(M+1) < 1,
    exp(-gamma*r) absSum(Fjet(r)) <= C,
    exp(-gamma*r) absSum(Yjet(r)) <= C*(M+1),  r>=0.

The strict bound is obtained by choosing damping from the actual finite M;
it is not a physical small-kernel hypothesis. The generic weighted renewal
estimate is used only after this bound is proved. No Wiener inversion axiom
or canonical decay assertion is used.

`actual_causal_jet_exponential_order` and
`actual_causal_entries_exponential_order` supply one constructed rate and
constant for all species entries of Y and delta Y. They hold at arbitrary
amplitudes and in arbitrary amplitude directions with positive rates and
nonnegative diameters. They require no BH root, Jacobian kernel, free-volume
inverse, density positivity, canonicity or preassigned kernel budget.
Repeated rates, empty finite families and zero component densities are
allowed by the statements.

## Honest Laplace integrals and the actual tangent equation

`exp_order_complex_integrable` and `exp_order_real_integrable` prove
absolute integrability after damping with Re(s)>gamma, with measurability
discharged for the actual fields. `actual_causal_laplace_integrable` gives
one right half-plane for all entries of actual Y and delta Y.

`weighted_hVariation_positive_indicator` identifies the genuine existing
r*`JacobianExterior.hVariation` on r>0 with the shifted causal derivative,
set to zero in the core. The fixed contact is included explicitly. Under
positive diameters, `actual_weighted_hVariation_laplace_integrable` proves
its positive-axis complex Laplace integral exists in a constructed right
half-plane. The contact indicator is measurable; no derivative at a moving
breakpoint or implicit contact atom is dropped.

`complex_matrix_tangent_renewal` applies the existing proved complex
convolution/Fubini theorem to each of the two tangent convolution terms,
with all source and convolution integrability checked. Its actual
specialization `actual_tangent_laplace_renewal` proves, throughout one
constructed sufficiently far right half-plane,

    Laplace(delta Y) * (I - Laplace(q))
      = Laplace(delta F) + Laplace(Y) * Laplace(delta q).

This is a genuine global integral transcription of the actual spatial
amplitude tangent equation. Neither a neighboring curve of BH roots nor a
root-only Fourier/OZ identity is differentiated. Both matrix orders are
retained.

## Scope still missing

The standalone growth estimate here depends on the fixed p and v. The
subsequent `ActualLaplaceJets` module closes the global Laplace parameter
derivative identification: a uniform parameter-neighbourhood bound and
off-root algebraic response uniqueness supply genuine whole-family
smoothness and derivative interchange in a far right half-plane. A finite
amplitude basis gives one cutoff for all directions. See
`codex_actual_laplace_jets.md`. This does not close the Fourier-boundary gap.

Exponential order permits growth. It is not decay, integrability at Re(s)=0,
global actual h-tangent L2, a complete Fourier-boundary tangent OZ identity,
or the canonical no-fold theorem. Boundary control/continuation, full tangent
OZ, canonical factor recovery/amplitude uniqueness and the general
convergence classification remain open. No universal real-root/Taylor
convergence equivalence is asserted.

## Reproduction and footprints

Run `python3 scripts/check_project.py` in this research package. The checker
uses the pinned installed Lean binary directly and prevalidated foundation
imports read-only; it invokes no shared Lake/dependency build. It audits the
530 frozen source/configuration hashes and the six directly imported
FMSAPaper artifact pins before/after. Exact compiler axiom guards and
source/artifact/log hashes are recorded in `results/lean/validation.json`.

Verified isolated checkpoint (2026-10-28): PASS, 182 exact standard-three-axiom
guards across twelve research modules plus the root, including 32 new guards
here. All source/artifact/log hashes match; all 530 frozen source/configuration
hashes and six direct validated import artifact pins are unchanged before/after.
No shared dependency build was invoked. Foundation manifest SHA:
`09ade0691482098319e832c6c721b77ef70d99bb76cec5bc84b498357dd9219c`.
