# Abstract one-tail system: Loewner coefficient positivity fails at order two

This is an **abstract matrix-system** result, not a physical MSA
counterexample and not evidence that `R < τ_f`. It rules out one
tempting replacement for entrywise coefficient positivity in the
frustrated `T=1, N≥3` problem.

In the checked one-tail system

```text
p = X + p²,     h = I + κ p h,     X = τ h K hᵀ,
p(0) = 0,       h(0) = I,
```

the first coefficients are `p₁ = K`, `h₁ = κK`, and therefore
`p₂ = K² + κK² + K²κ`. This follows by taking coefficients of `τ`
and `τ²` in the three equations. Take `K = [[1,1],[1,1]]`, a rank-one
PSD matrix, and `κ = diag(1, 1/2)`, with both eigenvalues strictly
between zero and two. Then

```text
p₂ = [[6,5],[5,4]],
(4,-5) p₂ (4,-5)ᵀ = -4.
```

In fact for `κ = diag(a,b)` and this `K`,
`det p₂ = -4(a-b)²`; any `a ≠ b` makes the coefficient indefinite.

`MSAConvergence/T1LoewnerSignObstruction.lean` checks exactly that
the chosen `K` has nonnegative quadratic form for every real vector,
that the diagonal values of `κ` lie in `(0,2)`, and that the displayed
`p₂` has quadratic value `−4`. It also proves the direct negation of
quadratic nonnegativity for this coefficient. The extraction of
`p₁,h₁,p₂` from the full formal system is recorded algebraically here;
the Lean module checks the forced second-order expression and its
sign, but does not import or connect to a physical MSA root. Claude's
`claude_lean/T1PositiveSystem.lean` gives the separate entrywise sign
theorem under a sign-flippable `K`.

The result shows why a matrix-valued Pringsheim argument based on
coefficient PSD order cannot directly cover frustrated strengths.
It does **not** rule out a different analytic proof of `R = τ_f` for
physical frustrated one-tail mixtures.

Validation: full package PASS, 2409 exact axiom guards / 266 research
modules, standard three axioms only. One Lean compiler under the
30 GiB RSS cap; frozen foundation 1.0.17 and TeX unchanged.
