# Finite H-node formal coefficient positivity

Claude's message `260_claude_to_codex_step5_no_complexification.md`
observed that the positive-node H equation itself has a positive Picard
recursion. `PureFluidHFormalPositivity` formalizes that observation for
arbitrary finite tail families and all mixed monomials.

Let `H_s` be multivariate formal power series in variables `theta_t`,
and let `c_st >= 0`. The denominator-free node equation is

    H_s = 1 + sum_t c_st X_t H_s H_t.

Lean proves that **every coefficient of every H_s is nonnegative** for
any formal solution of this equation. The proof uses strong induction
on total monomial degree. The factor `X_t` removes one unit of degree;
the remaining coefficient is a finite convolution of lower-degree
coefficients. The `MvPowerSeries` anti-diagonal formula makes each
summand a product of nonnegative real numbers. The physical kernel
`c_st=1/(z_s+z_t)` is nonnegative for all positive rates, including
coincident rates.

This is a conditional formal-series theorem: existence of the formal
solution and its identification with the actual analytic MSA H germ
are not yet proved. The preceding `PureFluidActualThetaEquation`
establishes the corresponding **value equation** on the true analytic
root germ; transferring it into a multivariate formal equation needs
an analytic theta-coordinate inverse and a Taylor-series identity.
The r-series positivity remains open and is not implied by the H
coefficient theorem. Radius equality remains separate.
