# Pure fluid: all mixed Taylor coefficients in the tail strengths are nonnegative

Modules, in dependency order: `PureFluidMixedPicard`, `PureFluidMixedRay`, `PureFluidMixedAmplitude`,
`PureFluidMixedTheorem`, `PureFluidMixedStrict`. Main statements: `mixed_coefficients_nonneg` and
`ray_germ_coeff_pos` in `FMSA.Convergence.PureFluidMixedTheorem`, and `mixed_coefficients_exact` in
`FMSA.Convergence.PureFluidMixedStrict`. This formalizes Step 6 and the sign part of the theorem in
`claude_two_tail_convergence.md`. The radius part is `claude_pure_fluid_taylor_radius_fold.md`.

## Statement

Take `0 < xi < 1`, a finite tail set and every `z_t > 0`. Rates may coincide, and no sign is assumed
on `K`.

`mixed_coefficients_nonneg` gives an analytic `Φ : K ↦ (D, G)` near `K = 0`, with
`Φ 0 = (0, G0)`, an actual `MultiTail.IsRoot` at every small `K`, and series `P` at 0, together with
explicit series `dK t`, `gK t` in the tail strengths such that, for every `K`, `n`, `t`,

    (P n (K, ..., K)).1 t = Σ_{|m| = n} coeff m (dK t) · K^m,
    (P n (K, ..., K)).2 t = Σ_{|m| = n} coeff m (gK t) · K^m.

So `dK`, `gK` are the Taylor expansion of the germ, monomial by monomial, and:

- every coefficient of `dK t` is nonnegative;
- every coefficient of `dK t` at a monomial without `K_t` is exactly 0;
- every coefficient of `gK t` at `m ≠ 0` is nonnegative.

`mixed_coefficients_exact` sharpens the three signs into the exact pattern:

- a coefficient of `dK t` at `m` is 0 if `m t = 0` and strictly positive if `m t ≠ 0`;
- a coefficient of `gK t` at `m ≠ 0` is strictly positive.

So the sign theorem cannot be improved, and this replaces the numerical record of 113434 coefficients
in `claude_two_tail_convergence.md` for positive rates. It holds at coincident rates too, with the
tails kept as separate labels.

`ray_germ_coeff_pos`: if all `K_t > 0`, then for any root germ along `τ K` through the hard-sphere
seed that is continuous at 0, every Taylor coefficient of `D_t` and `G_t` in `τ` of order at least 1
is strictly positive. It applies to the germ of `taylor_radius_is_fold`.

The paper note uses `τ_t = τ · 2π K_t/z_t` as variables. That is a positive diagonal rescaling of `K`,
so the signs are the same.

## What it does not say

- That `G_t` stops at `R`, and the items listed in `claude_pure_fluid_taylor_radius_fold.md`.
- Anything about mixtures, or tails of mixed sign beyond the polynomial identity above: for `K` of
  mixed sign the identity still holds, but it gives no sign.

## Route

**Formal solution (`PureFluidMixedPicard`).** The equation

    θ_t = a_t K_t (1 - κ_t r_t(θ))^(-2),   r_t(θ) = subst θ (RSeries z t),

is solved in `MvPowerSeries T ℝ`. Mathlib has no general fixed-point theorem for this, so the solution
comes from iterating from 0. The explicit variable `K_t` raises the total degree in which two inputs
agree by one (`pic_eqBelow`), so coefficients of degree `< k` are frozen from iterate `k` on, and
`thetaM` reads each coefficient from the first iterate where it is frozen. Nonnegativity holds for
every iterate, using `RSeries_coeff_pos_all` and `physical_HSeries_coeff_nonneg`, so it passes to the
limit.

**Amplitudes.** With `q_t = (1 - κ_t r_t)^(-1)`,

    D_t = (F0_t/ρ) a_t K_t H_t q_t,   G_t = G0-node + r_t q_t/(2π ρ F0_t^2).

The first form is why `D_t` is positive: `θ H (1 - κ r)` has a negative factor, but
`θ(1 - κ r) = α K q`. It also shows the factor `K_t` directly.

**Restriction to a ray (`PureFluidMixedRay`).** Substituting `K_t τ` for the variable `K_t` is a ring
map. It sends the multivariate equation to the one-variable Picard equation of that ray, and
`theta_fixed_point_unique` identifies the result with the Taylor series of the actual `θ` along the
ray (`res_theta_eq`). `coeff_res` writes the coefficient of `τ^n` as the polynomial above.

**Actual germ on a ray (`PureFluidMixedAmplitude`).** `exists_ray_germ` uses the closed forms at a root
near `τ = 0`, for any real `K`, to show that the restricted series are the Taylor series of `D_t`, `G_t`.

**Joint germ (`PureFluidMixedTheorem`).** The implicit function theorem at the seed, with the same
triangular partial as on a ray, gives `Φ`. Then `τ ↦ Φ(τ K)` is a root germ through the seed, so
`seed_germ_unique` matches it with the ray germ, and `ray_taylor_of_joint` reads its Taylor coefficient
as `P n (K, ..., K)`.

**Strictness.** `θ_t` dominates `α_t X` coefficientwise, so `θ_t^n` has coefficient at least `α_t^n` at
order `n`. The single term `m = single t n` of the substitution gives
`[τ^n] r_t ≥ [θ_t^n] RSeries · α_t^n > 0`. Then `q_t = 1 + κ_t r_t q_t` and `H_t(0) = 1` carry this to
`G_t` and `D_t`.

**Every monomial (`PureFluidMixedStrict`).** The ray argument lifts to several variables. `θ_u`
dominates `a_u K_u` coefficientwise, so the monomial `θ^m` has coefficient at least `∏ a_u^(m_u)` at
`K^m` (`nn_sub_prod`, `coeff_prod_C_mul_X`). The term `m` of the substitution then gives
`[K^m] r_t ≥ [θ^m] RSeries · ∏ a_u^(m_u) > 0` for every `m ≠ 0` (`rK_coeff_pos`). Next,
`q_t = 1 + κ_t r_t q_t` makes every coefficient of `q_t` positive, `H_t(0) = 1` carries this to
`H_t q_t`, and `D_t = c_t a_t K_t H_t q_t`, `G_t - G0 = r_t q_t/(2π ρ F0^2)` finish.

## Evidence

Lean, standard axioms only. Full checker: 2625 guards, 283 research modules, foundation 1.0.17
unchanged.
