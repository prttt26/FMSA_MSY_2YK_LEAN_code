# Independent multivariate pure-fluid r series and actual path

`PureFluidRFormalSolution` constructs `RSeries z s`, a formal
`MvPowerSeries` in the independent theta variables. It uses the unique
finite H-node series `physicalH z s` and defines each r coefficient by
recursion on monomial total degree. Every right-side term contains one
theta variable, so only lower-degree r coefficients occur. Lean proves
`RSeries_system` and `RSeries_unique`: this recursive family is the
unique solution of

```text
R_s = Σ_t (z_s+z_t)⁻¹ X_t H_s H_t (z_t-R_t).
```

`PureFluidRPathFormalSubstitution` proves that substituting any formal
theta path with zero constant term into `RSeries` solves the one-variable
r-node equation. Its uniqueness theorem identifies any such path with
the substitution when H is likewise the substituted `physicalH` series.

The strengthened end theorem
`PureFluidRActualTaylorIdentification.exists_actual_hs_root_germ_with_r_taylor_path`
then constructs an original BH/Exact MSA hard-sphere-seeded analytic root
germ, its actual theta, H, and r Taylor paths, and proves both path
identities:

```text
H_path,s = subst(theta_path, physicalH_s),
r_path,s = subst(theta_path, RSeries_s).
```

The r path locally sums to the true `actualNodeR` value. Positive tail
rates may coincide in the actual-root and formal statements. No new
axiom or edit to foundation 1.0.17 is used. Every theorem has an exact
standard-three axiom guard; verification runs one Lean compiler under
a 30 GiB RSS cap.

## Open sign and radius steps

This identifies the multivariate formal r solution with the actual
physical coupling Taylor germ **after formal theta-path substitution**.
It does not prove that the independent multivariate r coefficients
are nonnegative or equal to the explicit squarefree weight formula
`E_S(x)=|S|! W_S(x)`. The previously proved `W_S(x)≥0` has not yet been
transported to those coefficients, and repeated-rate limits of that
formula are still open. Physical-coupling Picard inversion and the
exact pure-fluid radius/fold equality remain open. No universal
real-root/Taylor equivalence is asserted.

## First coefficient bridge

`PureFluidRLowOrder.rCoeff_single` extracts the coefficient of one
independent theta variable directly from the recursive r equation:

```text
[theta_t] R_s = z_t/(z_s+z_t).
```

`RSeries_coeff_single` identifies this value with the singleton weight
`W_{t}(z_s)`, and `RSeries_coeff_single_pos` proves it strictly positive
for positive rates, including coincident rates and evaluation at a rate
node. This is the base case of the proposed squarefree coefficient
identity. The general multilinear identity and repeated-index cases
remain to be proved.

## Two distinct theta variables

`PureFluidRQuadraticBridge` proves the next squarefree case directly from
`RSeries_system`, rather than from a numerical coefficient check. For
`i ≠ j` and positive rates, even when `z_i = z_j`, Lean proves

```text
[theta_i theta_j] R_s =
  4 z_i z_j / ((z_s+z_i)(z_s+z_j)(z_i+z_j)) > 0.
```

When `z_i ≠ z_j`, `RSeries_coeff_two_eq_W` also proves this is exactly
`2 W_{ {i,j} }(z_s)`, with `W` expanded as the two-term finite sum and
product used in `PureFluidRWeightPositivity`. This is the `|S| = 2`
case of `E_S = |S|! W_S`; it does not assume rates distinct elsewhere
in the finite family. The proof uses a reusable first-order product
coefficient identity and an `X_t` selection rule for two-variable
monomials. Every new theorem has the exact standard-three axiom
footprint.

The repeated-variable case of total degree two is also proved:

```text
[theta_i^2] R_s = z_i/(z_s+z_i)^2 > 0.
```

Together, the two formulas cover both patterns of total degree two.
The cases of three or more variables, higher repeated-index patterns,
and global radius equality remain open.

## Reflection algebra route for arbitrary finite tails

`PureFluidRReflectionAlgebra` proves a rational pair identity and its
finite double-sum consequence with repeated rates allowed. Put
`q_t=z_t-r_t` and `k_t(x)=1/(x+z_t)-1/(z_t-x)`. The proved consequence is

```text
Σ_t Σ_u w_t w_u (q_u-q_t-x)/((x+z_t)(z_u-x))
  = Σ_t Σ_u w_t w_u (q_u+z_t-q_t)/(z_t+z_u) k_t(x).
```

This is the cross-term cancellation in the exact reflection defect
formula. Writing `U(x)=1-Σ_t w_t/(x+z_t)` and
`g(x)=Σ_t w_t q_t/(x+z_t)`, `reflection_defect_identity` proves

```text
g(x)U(-x)-g(-x)U(x)-x(U(x)U(-x)-1)
  = Σ_t w_t (g(z_t)-U(z_t)r_t) k_t(x).
```

The right-hand side vanishes under the proved node equation
`candidateG_node_eq_U_mul_r`. Lean therefore proves
`candidateG_reflection_of_nodeRLinearEquation`, then divides by the two
nonzero `U` factors and applies the existing finite dispersion theorem:

```text
r(x)-r(-x) = x * (1-(1-v(x))^(-1)),
v(x) = Σ_t 2 z_t theta_t/(z_t^2-x^2),
theta_t = w_t U(z_t), r(x) = g(x)/U(x).
```

`actualR_reflection_dispersion` transports this identity to the
**original BH/Exact MSA root** using `actualNodeR_solves_linear_system_all_rates`
and the actual global partial fractions. It permits coincident positive
rates. At the off-node frequency `x` it assumes `x ≠ 0`, no poles
`x+z_t=0` or `z_t-x=0`, and nonzero `actualU(x),actualU(-x)`; roothood,
factor nonvanishing and node `U` nonvanishing are explicit premises.
No new mathematical axiom is used. This proves the finite real rational
reflection step of the arbitrary-order argument. Extracting independent
formal theta coefficients and proving rational uniqueness for the
squarefree `W_S` formula remain open; the reflection identity alone
does not establish coefficient signs or radius equality.

## Independent-theta formal reflection

`PureFluidRFormalReflection` lifts the finite pair cancellation from real
node values to arbitrary coefficients in `MvPowerSeries T ℝ`. The pair
defect is affine in its two unknown node values, so the real identity at
the three scalar choices `(q,p)=(0,0),(1,0),(0,1)` proves the identity
for any two formal series. Finite double-sum symmetrization then gives
`formal_reflection_defect_identity`: the formal reflection defect is
exactly the weighted sum of formal node residuals, including repeated
positive tail rates.

For the independently constructed `physicalH` and `RSeries`, the module
sets `w_t=X_t H_t` and `q_t=z_t-R_t`. `formal_H_node_factor` proves
`H_s U(z_s)=1` directly from the formal H equation; `formal_R_node_G`
proves `R_s=H_s g(z_s)` from the formal r equation. Thus each node
residual vanishes, and `physical_formal_R_reflection` proves

```text
g(x) U(-x) - g(-x) U(x) = C(x) (U(x) U(-x) - 1)
```

as an identity in the independent multivariate theta series ring at
every real `x` away from the finite poles. This is denominator-free in
the formal series ring and does not assume invertibility of `U(x)`.
All new theorem guards check the standard three axioms. Coefficient
extraction, the general `E_S=|S|!W_S` formula, higher repeated-index
signs, physical-coupling Picard inversion, and `R=tau_f` remain open.
Full checker PASS: 2149 exact theorem guards / 237 research modules,
with one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.

## Formal U dispersion and r odd part

`PureFluidRFormalDispersion` proves the two-pole double-sum algebra over
the multivariate formal series ring. For arbitrary formal weights, the
finite even product is a node-weighted sum. Substituting the constructed
`w_t=X_t H_t` and the proved `H_t U(z_t)=1` eliminates every node
weight, giving the exact independent-theta identity

```text
U(x) U(-x) = 1 - sum_t C(2 z_t/(z_t^2-x^2)) X_t.
```

The same module proves that `U(x)` has constant coefficient one and is
formally invertible. Define the off-node formal rational coordinate
`r(x)=g(x)/U(x)` using this inverse. Combining the formal reflection
identity with the even product gives `physical_formal_R_odd_dispersion`:

```text
r(x)-r(-x) = C(x) * (1 -
  (1 - sum_t C(2 z_t/(z_t^2-x^2)) X_t)^(-1)).
```

The assumptions are positive finite rates and no off-node poles
`x+z_t=0` or `z_t-x=0`; coincident rates are allowed. This is a formal
series identity, not a convergence or radius assertion. General node
coefficient extraction and positivity still require an additional
rational uniqueness or residue argument.
Full checker PASS: 2157 exact theorem guards / 238 research modules,
with one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.

## All-order sign of the off-node odd part

`PureFluidROddCoeffSign` proves a generic recursive fact: if all `c_t`
are nonnegative, every coefficient of the formal inverse
`(1-Σ_t c_t X_t)⁻¹` is nonnegative. The proof uses its fixed-point
equation and induction on the total degree of a monomial, with the
`X_t` factor forcing strictly lower degree.

For `0≤x<z_t` at every tail, the explicit dispersion coefficients
`c_t=2z_t/(z_t²-x²)` are nonnegative. Combining the generic theorem
with `physical_formal_R_odd_dispersion` proves that every nonconstant
multivariate theta coefficient of `r(x)-r(-x)` is nonpositive. The
statement includes repeated rate values and repeated theta variables.
It does **not** assert that a node coefficient of `RSeries` has this
sign. Recovering node coefficients from the off-node odd part remains
the rational uniqueness/residue step.
Full checker PASS: 2163 exact theorem guards / 239 research modules,
with one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.

## Exact formal node identification and off-node recursion

`PureFluidRFormalDispersion.physicalFormalR_at_node` proves that the
formal rational coordinate `physicalFormalR z (z_s)` is exactly the
independently constructed node series `RSeries z s`, without an
additional nonvanishing hypothesis: the formal `U(z_s)` has constant
coefficient one. The proof combines `H_s U(z_s)=1` and `R_s=H_s g(z_s)`.

`physicalFormalR_fixed_point`, `physicalFormalR_series_recursion`, and
`physicalFormalR_coeff_recursion` express every off-node coefficient
through the same original node series and terms containing one `X_t`.
The explicit coefficient equation is

```text
[m] r(x) = sum_t (x+z_t)^(-1)
  [m] (X_t H_t (z_t - R_t + r(x))).
```

This is the degree-lowering input for a later rational partial-fraction
induction. The induction, general `E_S=|S|!W_S`, and node signs are not
yet proved by these interface lemmas.
Full checker PASS: 2167 exact theorem guards / 239 research modules,
with one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.

## Distinct-rate simple-pole uniqueness

`PureFluidRSimplePoleUniqueness` reuses the already proved finite
simple-pole residue limit to establish a precise uniqueness statement.
For a finite selected set `S` of positive, pairwise distinct rates,
if two expansions `Σ_{t∈S} a_t/(x+z_t)` have the same odd part for all
real `x` away from the poles at `±z_t`, then every `a_t=b_t`. The proof
only needs eventual equality in the punctured neighborhood of each
negative pole; it does not assume equality at a pole where Lean's
totalized inverse would be misleading. Rates outside `S` may coincide.

The same module proves the finite algebraic splitting of
`1/((x+z_t)(x+z_u))` when `z_t≠z_u`, and shows that multiplying a
simple-pole sum by a fresh pole leaves a sum of simple poles. These
lemmas supply the uniqueness and closure sides of the proposed
squarefree coefficient induction. What remains is to prove from
`physicalFormalR_coeff_recursion` that each squarefree coefficient
actually has this simple-pole shape, and to show the candidate `W_S`
has the required odd part. No general `E_S=|S|!W_S` is claimed yet.
Full checker PASS: 2177 exact theorem guards / 240 research modules,
with one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.

## All-order squarefree odd-part match

`PureFluidRWeightOddPart.multilinearWeight_odd_part_off_poles` proves
the proposed squarefree weight has the exact rational odd part

```text
W_S(x)-W_S(-x) =
  -x (prod_{t∈S} 2 z_t) / (prod_{t∈S} (z_t^2-x^2)).
```

The proof uses the previously Lean-proved Lagrange partial-fraction
identity, and it covers both positive and negative real frequencies
away from `±z_t`. Positive pairwise distinct rates are required only
on the selected set `S`.

`PureFluidRSquarefreeGeometric` defines the squarefree monomial index
of `S` and proves, by strong induction on `|S|`, the exact general
coefficient formula

```text
[theta^S] (1-sum_t c_t theta_t)^(-1)
  = |S|! prod_{t∈S} c_t.
```

Applied to the already proved formal r odd-part dispersion identity,
`physical_formal_squarefree_odd_eq_W_odd` gives for every nonempty
selected distinct-rate set `S`:

```text
[theta^S](r(x)-r(-x)) = |S|! (W_S(x)-W_S(-x)).
```

This is the exact all-order odd-part comparison. To infer
`[theta^S]r(x)=|S|!W_S(x)`, the one remaining squarefree step is to
prove that `[theta^S]r(x)` is a simple-pole sum supported on `S`.
The uniqueness theorem from the preceding section then applies.
Repeated-index coefficients and pure-fluid radius equality remain open.
Full checker PASS: 2189 exact theorem guards / 242 research modules,
with one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.

## Squarefree pole-shape induction interface

`PureFluidRSquarefreePoleRecursion` rewrites the exact off-node formal
r equation coefficientwise. For a finite selected set `S`, its
`physicalFormalR_coeff_squarefree_recursion` has the form

```text
[theta^S] r(x)
  = sum_{t in S} (x+z_t)^(-1)
      [theta^(S\{t})] (H_t (z_t - R_t + r(x))).
```

This is valid even at real pole frequencies in Lean's totalized
division notation; the eventual simple-pole conclusion will be used
only away from its selected poles. `coeff_X_mul_squarefree` supplies
the generator deletion step. `squarefree_antidiagonal_support` proves
that both factors in any Cauchy coefficient of the displayed product
are squarefree on subsets of `S\{t}`;
`squarefree_antidiagonal_strict` proves the r factor uses fewer than
`|S|` selected indices. The empty-set coefficient is exactly zero.

The remaining induction must package the resulting coefficients into
an x-independent finite simple-pole sum and invoke the already proved
fresh-pole splitting theorem. The full squarefree W identity, repeated
indices and radius equality are still open.
Full checker PASS: 2196 exact theorem guards / 243 research modules,
with one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.

## Full distinct-rate squarefree r coefficient formula

`PureFluidRSquarefreePoleSpan.physicalFormalR_squarefree_poleRep`
completes the strong induction proposed above. The predicate `PoleRep`
requires one x-independent residue family and equality at every real
frequency avoiding the selected negative poles. Its closure lemmas
cover finite sums, constant coefficients, support enlargement, and
multiplication by a fresh pole via the already proved two-pole split.
`poleRep_coeff_mul_fixed` applies these closures to the Cauchy-product
coefficient of the actual x-independent H series and formal r.

The global odd-part formula is initially available only where every
full-system denominator is nonzero. Unselected tails can share a rate
with a selected tail. The proof therefore establishes a punctured
neighborhood where all finitely many full-system denominators are
nonzero, without global rate injectivity. The existing genuine residue
limit then identifies the selected simple-pole coefficients from
equality on that narrower domain. This avoids asserting the odd-part
formula at an unselected pole, where totalized division can change its
literal value.

`physicalFormalR_squarefree_eq_weight_all` now states the full formula
for any finite selected `S`, including the empty set:

```text
[theta^S] r(x) = |S|! W_S(x)
```

The selected rates must be pairwise distinct, all full-system rates
positive, and `x+z_t` nonzero for each selected `t`. No distinctness
assumption is imposed on rates outside `S`. At positive x, `W_S`
positivity gives nonnegative squarefree r coefficients, strict
positivity away from the selected positive rates, and nonnegative
squarefree coefficients of the independently recursive node series.

This settles the distinct-rate squarefree coefficient identity but
does not cover repeated theta indices or coincident selected rates.
It is not a proof of pure-fluid Taylor radius/fold equality or of any
universal real-root/convergence equivalence.
Full checker PASS: 2213 exact theorem guards / 244 research modules,
with one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.

## All-order repeated-index positivity with one tail

`PureFluidRSingleTailAllOrder` specializes the independent formal H
and r equations to a one-element tail type. Algebraic elimination
proves `H_t (z_t-R_t)=z_t` as a formal series identity. The exact
off-node r recursion therefore reduces to

```text
r(x) = (x+z_t)^(-1) X_t (z_t + H_t r(x)).
```

For `z_t>0` and `x≥0`, the scalar prefactor is nonnegative. The
existing theorem that every H coefficient is nonnegative, together
with the explicit theta factor, lets strong induction on total degree
prove every coefficient of `r(x)` nonnegative. The established
off-node/node identification gives the same result for every
coefficient of the independently recursive `RSeries` at the node.
This includes all repeated powers of the sole tail variable, with
no fixed truncation order.

The cancellation is special to one tail. In a multitailed system,
`H_t(z_t-R_t)` need not have nonnegative mixed coefficients, so this
proof does not imply the general repeated-index claim. Neither the
physical coupling inversion nor radius/fold equality follows here.
Full checker PASS: 2217 exact theorem guards / 245 research modules,
with one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.

## Repeated multiindex kernel candidate and exact coefficient checks

For a nonzero multiindex `m`, positive tail rates `z_t`, and `x>0`,
the candidate formula for the *actual* formal off-node r coefficient is

```text
[theta^m] r(x)
  = multinomial(m) 2^|m| (prod_t z_t^m_t) / pi
    * integral_0^infinity
        k^2 / ((k^2+x^2) prod_t (k^2+z_t^2)^m_t) dk.
```

The integrand and prefactor are positive. If established for every
multiindex, the formula would give strict positivity of every
nonconstant formal r coefficient for `x>0`, even when rates coincide.
It also suggests a route to the independently recursive node series
via the already proved off-node/node identification. The formula is
an open conjecture, not a proved identity. It is stated for positive
`x`: the integral depends on `x^2`, whereas the r rational function
uses the positive analytic branch and has different values at `-x`.

`scripts/certificates/codex_pure_fluid_repeated_integral.py` performs
two independent exact-rational computations. One follows the formal
H, R and off-node r recursions by multiindex convolution. The other
reduces the proposed kernel integral to partial fractions in `k^2`,
solves the polynomial identity over rational numbers and integrates
each repeated quadratic pole with its closed beta-integral value.
All seven chosen cases match exactly, including repetitions, equal
rates, and `x` equal to a rate. The JSON records the exact fractions.
Finite checks cannot establish the general identity or validate the
closed integral formula inside Lean.

`PureFluidRGeometricAllOrder.geometricTheta_coeff_recursion` proves
the exact predecessor recurrence for every nonzero multiindex of the
geometric inverse, with no squarefree or rate-distinctness condition.
`physical_formal_R_odd_coeff_geometric` identifies the actual formal
r odd coefficient with `-x` times this geometric coefficient away
from the full-system poles. Both results have exact axiom guards and
the standard three axioms only. They give an induction interface for
the odd part, but do not determine the positive-frequency r coefficient
without an additional analytic or rational-function argument.

### A route from the proved squarefree identity to repeated indices

The candidate has a direct polarization and coalescence route from
the proved squarefree identity:

1. Replace each original tail `t` by `m_t` labelled copies `(t,j)`.
   `PureFluidRDistinctRateApprox` now constructs positive pairwise
   distinct approximations converging to *any* positive copied rate
   family. Include the labelled copy set `S` of size `N=|m|`.
2. For distinct positive rates and positive `x` distinct from the
   rates, `PureFluidRWeightIntegral` now proves directly in Lean that
   the *actual* squarefree r coefficient equals its factorial weight
   times the positive kernel integral, with the denominator product
   displayed explicitly. Algebraically,
   this is `W_S(x)=2^N (prod_(t,j) z_(t,j))/pi` times the integral
   with denominator `(k²+x²) prod_(t,j)(k²+z_(t,j)²)`.
   `PureFluidRKernelContinuity` now extends this identity to every
   `x>0`, including `x=z_t`, by an explicit integrable Cauchy majorant,
   dominated convergence and dense-set uniqueness.
3. `PureFluidRCoeffRateContinuity` now proves that every fixed-degree
   formal H, R-node, and off-node r coefficient is continuous in all
   positive rate parameters, including at coincidences. It uses
   strong induction on total degree and the exact degree-lowering
   recursions. On the integral side,
   `kernelProduct_le_rate_box_majorant` proves an explicit locally
   uniform integrable bound, and
   `kernelProduct_integral_continuousAt_rate` proves genuine
   continuity of the half-line integral at every positive rate
   family, including coincidences, by dominated convergence.
4. At exactly coincident labelled rates, substitute
   `theta_t = sum_(j=1)^(m_t) phi_(t,j)` in the original formal system.
   Formal uniqueness should identify its solution with the copied
   system. Extracting the full squarefree `phi` coefficient multiplies
   `[theta^m]r` by `prod_t m_t!`: precisely `m_t!` permutations use
   all `m_t` copies once. Dividing `N!` by this factor gives
   `multinomial(m)` in the candidate formula.

This is a proof route, not yet a repeated-index Lean theorem.
`physicalFormalR_squarefree_eq_kernel_any_rates` now proves the
actual squarefree r coefficient integral formula for **all** positive
finite rate families, including coincident selected rates, by the
distinct-rate approximation and the proved continuity of both sides.
The kernel integral is strictly positive, so every nonempty
squarefree coefficient of the actual r series at `x>0` and of the
independently recursive R node at positive rates is strictly
positive, without any selected-rate distinctness assumption.
`PureFluidRLabelSubstitution` now proves the formal-variable substitution
part for the *actual* off-node r series. Splitting each original variable
into a sum over its labelled copies transports the H and R node systems
and the off-node r equation to the copied system. Uniqueness identifies
all three copied series, including when the copy rates coincide. The
remaining Lean gap for general repeated-index positivity is the
combinatorial coefficient extraction: the full copied squarefree
coefficient must equal `prod_t m_t!` times the original `m` coefficient.
Full checker PASS: 2256 exact theorem guards / 251 research modules,
one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.
The auxiliary `coeff_squarefree_sum_X_pow` now establishes the
factorial coefficient for a single labelled fibre. It remains to
combine the fibres and collapse `MvPowerSeries.coeff_subst` to the
unique original multiindex. Full checker PASS: 2259 guards / 251
modules under one 30 GiB-capped Lean compiler.
That remaining factorial extraction is now proved as
`PureFluidRLabelSubstitution.coeff_splitTheta_full_squarefree` for an
arbitrary formal series. The proof expands the general substitution
coefficient, shows that only the copy-count multiindex contributes,
and calculates its full squarefree copied coefficient as the product
of fibre factorials. Combined with copied-series identification and
the all-rate squarefree positive integral, `physicalFormalR_coeff_pos_all`
proves **strict positivity of every nonconstant actual formal r
coefficient at x>0** for arbitrary finite positive rates, including
repeated theta indices and coincident rates. `RSeries_coeff_pos_all`
does the same for every independent R node. This is positivity in
formal theta coordinates; physical-coupling Picard inversion and
the radius/fold identity are still separate open steps.
Full checker PASS: 2282 exact theorem guards / 251 modules,
one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.
`PureFluidRRepeatedKernel.physicalFormalR_repeated_kernel_integral_normalized`
now proves the candidate from the seven exact rational diagnostics
for **all** nonzero multiindices, arbitrary finite positive rates,
and every x>0. In original tail labels the coefficient is
`multinomial(m) * (2^|m| / π) * (prod_t z_t^m_t)` times the positive
half-line integral of
`k² / ((k²+x²) * prod_t (k²+z_t²)^m_t)`.
`RSeries_repeated_kernel_integral_normalized` gives the node formula.
The proof goes through the actual copied squarefree identity and
the exact factorial extraction; no proposed kernel equality remains
assumed. It still concerns the formal theta-coordinate series.
Full checker PASS: 2289 exact theorem guards / 252 modules under
one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.

### Next physical-coupling interface

`PureFluidActualThetaEquation.actual_theta_equation_all_rates` gives,
on the genuine HS-seeded root germ,
`alpha_t * tau = theta_t(tau) * (1 - kappa_t * r_t(tau))^2`,
where `alpha_t = rhoOf(xi) * (2*pi*K_t/z_t) / F0(xi,z_t)^2`.
`PureFluidRActualTaylorIdentification` already identifies each actual
`r_t` Taylor path with substitution of `RSeries` along the actual
theta Taylor path. The next formal bridge must transfer this theta
equation to one-variable `PowerSeries` and identify the Taylor series
of the identity map with `PowerSeries.X`. For `K_t>0`, positive xi,
and positive rates, `alpha_t` and `hardKappa(xi,z_t)` are positive.
The resulting zero-seeded fixed point is
`theta_t = alpha_t * X * (1 - kappa_t * subst theta RSeries_t)^(-2)`.
Its coefficientwise nonnegative solution would make the positive
theta-coordinate r coefficients contribute with one sign to the
physical-coupling path. The actual germ now supplies a solution
identified with the physical Taylor path, as proved below. Formal
fixed-point uniqueness and coefficientwise positivity are still open;
the exact repeated-index kernel formula alone does not assert
physical-coupling Taylor positivity or radius/fold equality.
Full checker PASS: 2246 exact theorem guards / 250 research modules,
with one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.

### Actual physical-coupling theta Taylor equation

`PureFluidThetaCouplingTaylor.exists_actual_hs_root_germ_with_theta_coupling_taylor`
now combines the genuine HS-seeded MSA root germ with local nonvanishing
of the BH factor and inverse-dressing nodes. It proves that the actual
theta and r-node Taylor paths satisfy, for each tail label `t`, the
formal identity `C(alpha_t) * X = thetaS_t * (1 - C(kappa_t) * RS_t)^2`,
where `RS_t = subst thetaS (RSeries z t)`. The same theorem proves the
equivalent zero-seeded Picard fixed-point identity
`thetaS_t = C(alpha_t) * X * (1 - C(kappa_t) * RS_t)^(-2)`.
Here `alpha_t = rhoOf(xi) * (2*pi*K_t/z_t) / F0(xi,z_t)^2`;
`physicalAlpha_pos` verifies `alpha_t>0` for positive physical data.
The inversion is valid because the actual `RS_t` has zero constant
term at the HS seed. This is an exact bridge from the true MSA root,
not an independent formal ansatz. Coefficientwise positivity is
proved in the next section; uniqueness among all formal fixed points
and the radius/fold identity remain open.
Full checker PASS: 2294 exact theorem guards / 253 research modules,
one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.

### Physical-coupling coefficient signs

`PureFluidPositiveSubstitution.coeffNonneg_subst` proves that finite
multivariate formal substitution preserves coefficientwise
nonnegativity when each zero-seeded input series has nonnegative
coefficients. Its bounded-degree form permits a strong induction
without assuming the desired theta signs in advance. Combining the
strictly positive multivariate `RSeries` coefficients at every
nonzero repeated index with the degree-lowering factor `X` in the
actual Picard equation, `theta_fixed_point_coeffNonneg` proves every
coefficient of the zero-seeded physical theta fixed point is
nonnegative for nonnegative source and kappa.

`exists_actual_hs_root_germ_with_nonnegative_theta_r_taylor` applies
this to the genuine positive-coupling MSA root germ: every physical
tau Taylor coefficient of each actual theta node and r node is
nonnegative, including repeated indices and coincident positive
rates. Both one-variable series sum to their actual node values on
some neighborhood of zero. These sign and local identification
results are now Lean theorems. Formal fixed-point uniqueness is
proved in the next section; the physical Taylor radius/fold identity remains open. The
theorem does not assert the false universal real-root/Taylor
equivalence for mixtures.
Full checker PASS: 2314 exact theorem guards / 254 research modules,
one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.

### Unique physical theta fixed point

`PureFluidThetaFixedPointUniqueness.theta_fixed_point_unique` proves
that two zero-seeded formal theta paths satisfying the same physical
Picard equation agree coefficient by coefficient. Its proof transports
bounded-degree equality through finite multivariate substitution and
geometric inversion, then uses the explicit `X` factor to lower the
theta degree. This purely formal uniqueness needs no coefficient sign
or rate sign assumption. `exists_unique_physical_theta_fixed_point`
uses the actual HS-seeded MSA germ to provide existence and therefore
proves `∃!` for physical pure-fluid parameters. The unique formal
solution is the actual local MSA Taylor path. The remaining main
claim is the exact global Taylor-radius/fold identity.
Full checker PASS: 2323 exact theorem guards / 255 research modules,
one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.

### Pringsheim continuation interface

`PureFluidThetaPringsheimRoute` identifies the algebraic Taylor
coefficients with the canonical analytic jets. It then applies the
already formalized `FMSAPaper.Pringsheim` route, through
`AnalyticTaylor.le_jet_radius_of_signed_analytic_branch`, to prove a
conditional lower bound: if the original-amplitude path remains
analytic on `[0,b)`, each actual theta node with the nonnegative
Taylor coefficients established above has Taylor radius at least
`b`. The theorem `actualTheta_radius_lower_bound_of_analytic_amplitude_branch`
discharges theta analyticity from amplitude analyticity at every
point of that interval. No new mathematical axiom is used.

The required global analytic continuation of the selected HS branch
up to its first endpoint, and the matching upper bound at a
transverse endpoint, have not yet been linked to this pure-fluid
theta coordinate. The current result is explicitly conditional on
the amplitude-path continuation; it does not declare a numerical
or universal radius/fold identity.
Full checker PASS: 2327 exact theorem guards / 256 research modules,
one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.

### Exact scalarization of the constructed maximal branch

`PureFluidScalarMixtureBridge` proves the exact single-species,
unit-diameter dictionary between `MultiTailMixture` and `MultiTail`.
The equality covers the packing fraction, vacancy, HS Baxter slope
and curvature, each tail weight and moment, both dressed amplitudes,
the full Baxter transform, the two residual sides, and `IsRoot` in
both directions. `baseSeed_eq_pure` identifies the matrix PY seed with
the explicit pure-fluid `G0` using the proved zero-coupling root
equation and nonvanishing HS factor. `maximalBranch_pure_path` then
projects every constructed one-species maximal branch to an analytic
pure-fluid BH root path with that seed throughout its initial
interval. All 25 theorems have exact standard-axiom guards.

`PureFluidMaximalThetaTransfer` proves that local identification:
after lifting the independently constructed positive HS root germ to
the matrix system, canonical regular-root uniqueness identifies it
with the maximal branch near zero. Its actual theta Taylor series
therefore has nonnegative coefficients. For any `b>0` with
`ofReal b ≤ M.bound`, Pringsheim gives radius at least `b` for every
theta node. The all-interior-bound result further gives radius at
least `M.bound`, including when the bound is infinite. Analytic
uniqueness proves its series sums to the
selected maximal-branch theta value at every `0≤τ<b`. Physical data
alone construct the required maximal branch and these lower bounds.

`PureFluidSingleTailLossCounterexample` makes the first-loss
upper-bound proposal untenable: with one positive tail, physical
unit-diameter data construct a canonical maximal branch whose
original-amplitude and actual theta-node Taylor radii both strictly
exceed its first canonical loss. The proof uses the explicit branch
analytic to its fold, two-sided HS-germ identification, and
Pringsheim for the positive theta coefficients. The theta radius is
at least the fold. The constructed maximal branch's original `Dt/G`
Taylor series and theta-node series both sum to the explicit Exact MSA
root throughout `[0, fold)`, also past first canonical loss. The next exact-radius
question is which analytic or complex singularity limits the series;
the present theta-node theorem does not imply convergence of every
original `Dt/G` amplitude series for arbitrary finite tails.
Full checker PASS: 2364 exact theorem guards / 259 research modules,
one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.
Full checker PASS: 2359 exact theorem guards / 258 research modules,
one 30 GiB-capped Lean compiler; foundation 1.0.17 unchanged.
