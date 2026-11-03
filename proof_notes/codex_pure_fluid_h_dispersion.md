# Actual pure-fluid finite H dispersion identity

`PureFluidHDispersion` proves the finite rational identity behind Step 5
of the paper's pure-fluid H-function route. It first reorganizes the
double sum in `U(s)U(-s)` by the symmetric two-pole partial fraction
and a finite index swap. No distinct-rate assumption appears. For
`U(s)=1-sum_t w_t/(s+z_t)` and `theta_t=w_t U(z_t)`:

    U(s) U(-s) = 1 - sum_t 2 z_t theta_t/(z_t^2-s^2)

at real `s` away from both sets of tail poles. A second theorem
substitutes the globally identified ACTUAL inverse-dressing coordinates
of the original BH amplitudes. This theorem is independent of a root
assumption because the partial-fraction identity itself is algebraic.

At a true root, `actual_theta_nonneg_of_nonneg_coupling` proves
`theta_t >= 0` for each nonnegative physical tail strength, from the
per-tail identity `w_t=Lambda_t U_t` and the actual first BH equation:

    theta_t = [rho (2 pi K_t/z_t)/F(z_t)^2] U_t^2.

It needs only nonzero factor nodes, positive density and positive rates;
node U may have either sign or vanish. This is **value positivity**.
It does not imply nonnegative Taylor coefficients of theta, r or H.

The next section closes the imaginary-axis rational identity. The
logarithmic and r integral formulas, coefficient positivity and Picard
inversion remain separate, as does the fold-radius theorem.

## Imaginary-axis completion

The finite double-pole algebra has now been generalized over any field.
Its complex specialization proves, with the actual real weights,

    normSq(U_complex(i k)) = 1 - sum_t 2 z_t theta_t/(z_t^2+k^2)

for every real k. Positive tail rates supply all complex denominator
nonvanishing. On a true root with nonnegative strengths, the discrete
characteristic belongs to `[0,1]` for every k. The norm-square identity
is valid for any original amplitude values; the lower bound uses the
actual root equation and nonnegative strengths.

`complexU_ne_zero_imaginary_of_small_characteristic` proves that
`sum_t 2 theta_t/z_t < 1` with theta_t nonnegative makes the complex U
factor nonzero simultaneously for all real k. At zero first amplitudes
all actual theta_t vanish. Continuity of the actual weights and U nodes
then gives the smallness condition on a common coupling neighbourhood.
`exists_analytic_hs_root_germ_with_uniform_axis_nonvanishing` applies it
to the genuine analytic HS-root germ constructed from physical data:
for nearby nonnegative coupling, `U_complex(i k) != 0` for every k.
Rates may coincide. This is a uniform imaginary-axis statement, not a
global half-plane zero-free theorem.

The earlier open item "complexifying the actual rational identity"
is therefore closed. Still required: the logarithmic and r Cauchy
integral representations with a controlled branch, coefficientwise
positivity, Picard inversion and its true-germ identification, and the
fold-radius theorem.
