# Actual pure-fluid theta and finite H equations

The Lean module `PureFluidActualThetaEquation` closes the value-level
Step 3–5 bridge for the ORIGINAL pure-fluid finite-tail BH equations.
The proof allows repeated positive rates. It uses the per-tail true-root
weight identity, the actual rational inverse-dressing coordinates, and
the hard-sphere node factor identity. It assumes no numerical input or
new mathematical axiom.

For each true root with nonzero positive-node factor and U, put
`w_t = actualWeight_t`, `U_t = actualU(z_t)`, `r_t = actualG(z_t)/U_t`,
`theta_t = w_t U_t`, and `H(s) = 1/U(s)`. Lean proves

    F(z_t) = F0(z_t) U_t (1 - kappa_t r_t),
    rho (2 pi K_t/z_t)/F0(z_t)^2 = theta_t (1 - kappa_t r_t)^2,
    1/H(s) = 1 - sum_t theta_t H(z_t)/(s+z_t),

for real `s` away from zero and the negative tail poles. The last
identity is an algebraic equality in Lean's totalized real inverse;
its usual analytic H-function reading needs U nonzero at `s`. The
node-U nonvanishing is explicit in the value theorem.

`exists_analytic_hs_root_germ_with_theta_h_equations` then constructs
the genuine analytic HS-seeded root from physical data and proves both
node equations eventually near coupling zero. Its node factor and U
nonvanishing follow from continuity at the seed, not a caller premise.

Still open: positivity of the Taylor coefficients of `r_s(theta)` and
`H_s(theta)` by a proved dispersion/integral or formal-series route;
Picard coefficient positivity and identification with the actual
analytic germ; strict all-order signs; and the first-fold radius theorem.
The value equations alone establish none of those sign or radius claims.
