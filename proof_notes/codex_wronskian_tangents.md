# Actual distinct-rate Wronskian tangents and fixed finite remainders

This extends the isolated research checkpoint a73ffad. The foundation is
still frozen at 1.0.17 / 06e3268. All new declarations are in
`MSAConvergence/DistinctPoleJets.lean`, `PolynomialJets.lean` and
`WronskianJets.lean`. No foundation, TeX, or SI edit is made. The single
merge-back remains deferred until the research ends and the session closes.

## Off-root distinct-rate evaluation identity

Let f_r = {u : z_u = r}. The existing distinct-rate numerator constructors
retain all original tail-label contributions but use only one denominator
factor per rate value. Define four collected unnormalized residue matrices
R_r,k (k=0,1,2,3) in the same U(+r), U(-r), V(+r), V(-r) order as the frozen
foundation. `residueMatrices_sum` and `collectedResidues_eq_sum` prove

    R_r,k(p) = sum_{u in f_r} yukawaResidues_u,k(p).

This identity is off-root; it also covers an empty fibre. J(r) and L(r) are
common to the fibre, so each residue is linear in the collected W/C data.
No original tail label is discarded or divided by its multiplicity.

Put

    c_r = r^3 * nonlinearDistinctRatePolynomialExcept(z,r)(-r),
    d_r = nonlinearDistinctDenominator(z)(r).

For positive rates and every r in nonlinearDistinctRates(z),
`distinctValues_eq_collected_residues` proves, at arbitrary amplitudes p,

    U(p)( r)_ij = -c_r d_r R_r,0(p)_ij,
    U(p)(-r)_ij = -c_r d_r R_r,1(p)_ij,
    V(p)( r)_ij = -c_r d_r R_r,2(p)_ij,
    V(p)(-r)_ij = -c_r d_r R_r,3(p)_ij.

U/V here are exactly the existing `nonlinearDistinctUPolynomial` and
`nonlinearDistinctVPolynomial`, not auxiliary replacement polynomials.
`cleared_values_factorization` proves the scalar clearing algebra without
setting the residue errors to zero.

All collected actual entry maps are proved smooth, and actual Frechet
amplitude differentiation commutes with the fixed finite sum. The preceding
`ResidualJets.actual_kernel_yukawaResidues_fderiv_zero` therefore gives zero
actual derivatives of these four polynomial values along every actual BH
Jacobian-kernel vector at a symmetric-strength actual root. This is
`actual_kernel_distinct_wronskian_rates_fderiv_zero`. No root curve is assumed.

## A genuine polynomial of actual coefficient derivatives

The polynomial ring itself is not assigned an infinite-dimensional norm.
For a family f : P -> real polynomials with a uniform degree bound D, define

    variation(D,f,p,v) = sum_{n=0}^D monomial(n, D_amplitude(coeff_n f)(p)v).

`variation_coeff` proves every coefficient equals the actual Frechet
coefficient derivative, including n>D: those coefficient functions vanish
identically by the uniform degree bound. `variation_degree` proves degree
at most D. `variation_eval_fderiv` proves real evaluation commutes with this
actual derivative when coefficient derivatives exist. The coefficient
smoothness rules cover constants, smooth scalar coefficients, finite sums,
products, negation and substitution by a fixed polynomial. Fixed
substitution uses a finite expansion under the proven degree bound.

`actual_JNumerator_coeffSmooth`, `actual_LNumerator_coeffSmooth` and
`actual_distinct_wronskian_coeffSmooth` discharge all coefficient regularity
for the actual J/L/U/V numerators. The proof uses the existing actual
amplitudeA, amplitudeQp, W/C smoothness, with the exact finite polynomial
constructors. `actual_distinct_eval_contDiff` also proves genuine smoothness
of every real U/V evaluation. No caller supplies an unspecified derivative,
regularity assumption or root selection.

The actual tangent polynomials are

    delta-U = variation(2*card(distinctRates)+5, actual U, p,v),
    delta-V = variation(2*card(distinctRates)+4, actual V, p,v).

The cutoffs are the existing uniformly proved U/V degree bounds, not a
numerical truncation. `tangent_coefficients` identifies every coefficient,
and `tangent_eval_fderiv` identifies every real evaluation, with its genuine
actual derivative. These constructions need no BH root or rate-positivity
premise; positivity enters the physical pole evaluation transcription.

## Proven factors and the remaining completion

At every actual symmetric-strength BH root and along every actual amplitude
Jacobian-kernel vector, `actual_kernel_tangent_pole_factor` proves

    nonlinearDistinctPoleFactor(z) divides delta-U,
    nonlinearDistinctPoleFactor(z) divides delta-V.

The factor contains both signs of each distinct positive rate. Repeated
original rates are already collected. `actual_kernel_tangent_fixed_degree_remainders`
proves there exist qU,qV such that

    delta-U = nonlinearDistinctPoleFactor(z) * qU,    degree(qU) <= 5,
    delta-V = nonlinearDistinctPoleFactor(z) * qV,    degree(qV) <= 4.

The remainder bounds are independent of the number of tails. No nonzero
free-volume or kernel-budget condition is needed for this finite-factor step.
At checkpoint d97b639 these bounds did not yet prove the remainders vanish.
The subsequent `NormalizedWronskianJets` now eliminates both remainders under
positive rates and nonzero free volume, completing the actual finite tangent
certificate. See `codex_normalized_wronskian_tangents.md`.

The next concrete step at that checkpoint was to carry the frozen foundation's *off-root*
normalization transport, origin constraints and degree bounds into the
coefficientwise tangent, then reuse polynomial_matrix_factor_completion.
A useful way to avoid expanding the complicated normalized constructor is
its identity

    X^10 * normalizedDefect(p)
      = normalization * (ratePairPolynomial * intrinsicWronskian(p)) * normalization^T.

All normalization factors are independent of amplitudes. Taking coefficient
n+10 identifies coefficient n of normalizedDefect with a fixed linear
combination of actual U/V coefficients. Thus its coefficient smoothness can
be obtained from the already proved U/V smoothness, under positive rates
and nonzero free volume as required by the frozen transport identity.
No isolated-root identity needs to be differentiated. Coefficientwise
matrix variations are now proved to preserve that transport, the
uniform/lower-block degrees, the zero origin coefficient and the projected
skew first coefficient in `NormalizedWronskianJets`, where factor completion
is applied. This plan is retained as the derivation of the completed proof.

Full tangent spectral OZ, global actual h-tangent L2, canonical factor
recovery/amplitude uniqueness and the general no-fold result remain open.
Finite-factor cancellation and small remainder degree are not full tangent
OZ, and no universal real-root/Taylor-convergence equivalence is asserted.

Validation is the isolated `python3 scripts/check_project.py` workflow.
The authoritative compiler status, exact axiom footprints and input/output
hashes are in `results/lean/validation.json`. It audits all 530 frozen source/
configuration hashes and the three direct import artifact pins before/after,
and invokes no Lake/shared-dependency build.

Verified isolated checkpoint: PASS, 67 exact standard-three-axiom guards
across six research modules plus the root (33 new guards in these three
modules). All 530 frozen foundation source/configuration hashes and the
three directly imported artifact pins were unchanged before/after. No
shared dependency build was invoked. Foundation manifest pin:
`09ade0691482098319e832c6c721b77ef70d99bb76cec5bc84b498357dd9219c`.
