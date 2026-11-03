# Actual inverse dressing has removable origin poles

`PureFluidActualOriginRemoval.lean` completes the origin step for the
ORIGINAL pure-fluid finite-tail BH factor. It substitutes the exact
`P_actual,Shat_actual` local decompositions into the inverse frozen PY
basis. Two generic rational identities express each inverse coordinate
as an `s⁻²` coefficient, an `s⁻¹` coefficient, and an explicit regular
expression. `PureFluidActualOriginMoments.actual_origin_principal_algebra`
sets all four coefficients to zero using the true BH moment formulas
and the PY determinant relation.

For `xi ≠ 1` and every nonzero finite Yukawa rate, the module proves
pointwise equalities

    actualG(s) = actualRegularG(s),
    actualU(s) = actualRegularU(s)

whenever `s ≠ 0` and `s+z_t ≠ 0` for all tails. Both right-hand sides
are finite explicit rational expressions, continuous at zero. A finite
intersection of denominator neighborhoods gives the punctured limits
`actualG(s) → actualRegularG(0)` and
`actualU(s) → actualRegularU(0)` as `s→0`. Thus both zero-frequency
singularities are removable by the displayed continuous extensions.
No root equation, candidate H-function representation, or positivity
assumption is used. The totalized Lean values `actualU(0),actualG(0)`
are not asserted to equal the extension values.

This closes the origin-pole obstacle left by the true-root pole
relations and infinity normalization. Global finite-sum identification
still requires rational uniqueness and matching of the resulting
coefficients to the proposed candidate; positivity, `R=tau_f` and
endpoint Taylor summability remain separate.

Full checker PASS: 1863 exact standard-three theorem guards /203 research
modules; foundation 1.0.17 unchanged. No TeX file was written.
