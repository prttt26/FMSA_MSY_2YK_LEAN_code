# Pure fluid: the Taylor radius of the original amplitudes is where the analytic path ends

Modules, in dependency order: `PureFluidSeriesEval`, `PureFluidNodeBounds`, `PureFluidFoldCore`,
`PureFluidFoldBridge`, `PureFluidFoldClosedForm`, `PureFluidFoldRadius`, `PureFluidFoldPath`,
`PureFluidFoldEnd`, `PureFluidFoldSigns`, `PureFluidFoldTheorem`. Main statement:
`FMSA.Convergence.PureFluidFoldTheorem.taylor_radius_is_fold`.

## Statement

Take `0 < xi < 1`, a finite nonempty tail set, every `z_t > 0` and every `K_t > 0`. Rates may
coincide. There are a germ `p`, a path `P` and a real `R > 0` such that:

1. `p` is the analytic hard-sphere root germ, with `p 0 = (0, G0)`. By `seed_germ_unique` every root
   germ through that seed which is continuous at 0 is the same germ. `P = p` near 0.
2. `P` is analytic and an actual `MultiTail.IsRoot` at coupling `τ K` for every `τ` in `[0,R)`, and is
   continuous on `[0,R]`. `R ≤ z_t/(2 α_t)` for each `t`, with `α` the physical coupling.
3. `P R` is a root at coupling `R K`.
4. The amplitude partial of the original `MultiTail.residual` is not invertible at `(R, P R)`.
5. No analytic germ at `R` agrees with `P` on the left.
6. For the Taylor series `DS_t`, `GS_t` of the germ: every `DS_t` has radius exactly `R`, every `GS_t`
   at least `R`; each converges absolutely on `|τ| ≤ R`, and on `[0,R]` the sums are `P`. So the
   endpoint is decided: the series converge at `τ = R`.
7. Along the ray all coefficients of `DS_t` are nonnegative, and those of `GS_t` from order one.

`K_t > 0` cannot simply be relaxed: a wholly passive tail has a simple pole before the fold.

## What it does not say

- The Jacobian is not shown to be invertible on the open ray `[0,R)`. "First fold" here means first
  in the sense that the real analytic continuation ends at `R`. A singular Jacobian at an interior
  point that the path passes through analytically is not excluded.
- No square-root normal form at `R`.
- No canonicity, on the ray or at `R`. The proof does not use it and it is not asserted.
- `GS_t` is not shown to stop at `R`, only to reach it. This would follow from a coefficient bound of
  `r_s` below by a multiple of `θ_t`, which I did not formalize.
- The signs in item 7 are for one variable `τ` on each ray, not for the mixed coefficients in the
  separate tail strengths. Those stay on paper in `claude_two_tail_convergence.md`; `RSeries_coeff_pos_all`
  is the mixed statement in the `θ` variables.
- Nothing about mixtures. General PSD `K_t` has the external counterexample in
  `claude_two_tail_convergence.md`.

## Route

The proof avoids the M-matrix and divergence argument of the paper's Step 7. It works with one
variable `τ` on the ray, and the only analytic input is Pringsheim for nonnegative coefficients.

**Node family (`PureFluidFoldCore`).** Series `θ_t`, `H_t`, `r_t` in `τ`, with nonnegative
coefficients, satisfying

    α_t τ = θ_t (1 - κ_t r_t)^2,
    H_s (1 - Σ_t θ_t H_t/(z_s + z_t)) = 1.

The physical germ gives such a family through the existing positivity chain
(`PureFluidFoldBridge.exists_germ_nodeFamily`).

**Bounds on the ray, with no closure beyond the two equations.** With `w_t = θ_t H_t` and
`U(x) = 1 - Σ w_t/(x + z_t)`:

- `U(0)^2 = 1 - Σ 2 θ_t/z_t` is a finite algebraic identity (`dispersion_at_zero`).
- `θ` increases along the ray, so `U(0)^2` decreases; `U(0) = 1` at `τ = 0` and continuity give
  `U(0) ≥ 0`. Hence `θ_t ≤ z_t/2`.
- `U(x) ≥ x/(x + Z)` for `Z ≥ max z_t`, so `H_s ≤ (z_s + Z)/z_s`.
- `1 - κ_t r_t` cannot reach 0 while `α_t τ > 0`, so it stays positive and `r_t ≤ 1/κ_t`.
- `α_t τ ≤ θ_t ≤ z_t/2` makes `R` finite.
- Bounded partial sums of nonnegative terms give summability at `R` (`endpoint_summable`).

**The path (`PureFluidFoldPath`).** Let `R` be the smallest of the node radii, finite and positive by
the above. The closed forms at a root (`PureFluidFoldClosedForm`) suggest

    D_t = F0_t θ_t H_t f_t/ρ,   G_t = G0-node + r_t/(f_t · 2π ρ F0_t^2),   f_t = 1 - κ_t r_t.

They hold on the germ. The right sides are analytic on `[0,R)` because `f_t > 0` there. The residual
and the node values of `w`, `U`, `g` are entire in the amplitudes (`residual_analyticAt`, `weight_an`,
`nodeU_an`, `nodeG_an`), so the identity theorem on `[0,R)` extends "is a root" and the identification
of `θ, H, r` with the actual coordinates. Analyticity is only needed at points of the half-open ray,
including 0, so negative `τ` never enters.

**The endpoint (`PureFluidFoldEnd`).** `α_t R = θ_t(R) f_t(R)^2 > 0` forces `f_t(R) > 0`. So `P` is
continuous up to `R` and `P R` is a root with `U(z_t) H_t = 1` there, hence `U(z_t) ≠ 0`.
`no_extension`: given an analytic `q` at `R` agreeing with `P` on the left, `actualTheta ∘ q`,
`actualH ∘ q`, `actualNodeR ∘ q` are analytic at `R` and continue the three nonnegative series, so by
Pringsheim all their radii pass `R`, against the choice of `R`. `jacobian_singular`: an invertible
partial would give such a `q` by the implicit function theorem, and its local uniqueness matches `q`
with `P` on the left.

**The amplitude series (`PureFluidFoldTheorem`).** `D` is an algebraic product of absolutely
convergent series. For `G`, `Q = r/(1 - κ r)` has nonnegative coefficients by induction on
`Q = r + κ r Q`, with `r` vanishing at 0; Pringsheim gives its radius, and bounded sums give the
endpoint.

**Signs and comparisons (`PureFluidFoldSigns`).** `θ = α X (1 + κ Q)^2` is positive term by term, and
so is `θ H (1 - κ r) = α X H (1 + κ Q)`, although `1 - κ r` itself has negative coefficients. This
gives the sign of `D_t`. Differences with nonnegative coefficients then order the radii, up to a
shift by `X` and a positive constant:

    rad D_t ≤ rad H_t,   rad H_s ≤ rad H_u,   rad H_s ≤ rad θ_t,   rad θ_t ≤ rad r_t.

So all `H` radii agree, and once one node radius stops at `R` they all stop there, hence every `D_t`.

## Evidence

Lean, standard axioms only. Full checker: 2536 guards, 278 research modules, foundation 1.0.17
unchanged. The earlier paper proof is in `claude_two_tail_convergence.md`.
