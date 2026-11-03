# Pure-fluid rational r weight: positive finite-node kernel

The three Lean modules `PureFluidRPartialFraction`,
`PureFluidRKernelIntegral`, and `PureFluidRWeightPositivity` formalize the
distinct-node algebraic and real-integral part of the pure-fluid `r`
coefficient route proposed in Claude handoff 288. Let `s` be a nonempty
finite set, `z_i>0` pairwise distinct, and `x>0` different from every
`z_i`. The final theorem `rational_W_core_pos` proves

```text
0 < Σ_{i∈s} 1/(x+z_i) · Π_{j∈s\{i}} 1/(z_j²-z_i²).
```

Lagrange interpolation first proves the reciprocal square-difference
partial fraction identity and the decomposition

```text
k²/Π_i(k²+z_i²)
  = Σ_i (-z_i²)·Π_{j≠i}(z_j²-z_i²)⁻¹·(k²+z_i²)⁻¹.
```

Mathlib's arctangent integral and a positive-support argument then prove
that the integral of the left side over `k>0` exists and is strictly
positive. Integrating the decomposition yields the strict positivity of
the symmetric divided difference

```text
A(z) = -Σ_i z_i·Π_{j≠i}(z_j²-z_i²)⁻¹.
```

The theorem `divided_difference_A_integral_identity` exposes the exact
normalization `∫₀∞ k²/Π_i(k²+z_i²) dk = (π/2) A(z)`; the strict sign
theorem follows from that identity and positivity of the integral.

`extended_A_eq_expanded` applies this result after adjoining `x` as a
new node and expands its finite sum and products. The Lagrange reciprocal
identity shows the expanded expression equals the stated rational core.
This proves the cancellation and sign uniformly for arbitrary finite
sets of distinct positive rates; no numerical sampling is involved.
`multilinear_W_pos` also proves the complete weight

```text
W_s(x) = Σ_{i∈s} z_i/(x+z_i) · Π_{j∈s\{i}} 2z_j/(z_j²-z_i²) > 0.
```

The proof factors out `2^(|s|-1) Π_i z_i > 0` and applies the core theorem.
`multilinear_W_nonneg` removes the restriction that `x` avoid the rate
nodes. It uses continuity of the complete weight for `x>0` and the
density of the complement of the finite rate set. Thus the sign needed
at physical evaluation nodes `x=z_s` is available, although the theorem
asserts nonnegativity rather than strict positivity there.

Every new theorem has an exact standard-three axiom guard. The modules
use no new axiom and do not write to the frozen foundation package.

## Remaining identification

This is the rational weight lemma, not yet a theorem that all Taylor
coefficients of the actual MSA `r_s(theta)` are nonnegative. That requires
deriving its coefficient expression from the true `r` equation, including
the multinomial factor and positive prefactors, and linking the formal
solution to the physical HS-root germ. Repeated rates *within the tail
family* require a separate continuity or merging argument. The
subsequent Picard inversion and
`R=τ_f` proof remain open. The false universal real-root/Taylor
equivalence is not used.
