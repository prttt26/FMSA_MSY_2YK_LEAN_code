# Actual pure-fluid r nodes: value and Taylor path

`PureFluidRActualNodeBridge` rewrites the finite `nodeRLinearEquation`
as a value equation in the same `theta` and `H` coordinates used by the
pure-fluid Chandrasekhar system:

```text
r_s = H_s Σ_t theta_t H_t (z_t-r_t)/(z_s+z_t).
```

`actual_RNodeValue_all_rates` proves this equation for the **original
Blum–Høye MSA root**, using its genuine inverse-dressing `actualNodeR`,
`actualTheta`, and `actualH`. Positive tail rates may coincide. The
theorem requires the actual node factor and U values to be nonzero;
`exists_actual_hs_root_germ_with_RNodeValue` constructs a physical
hard-sphere-seeded root germ where those conditions hold locally. The
same module proves that `actualG` and `actualNodeR` are analytic on that
germ from the original finite BH moment expressions.

`PureFluidRFormalPath` defines the one-variable formal equation obtained
from the displayed value equation and proves its solution is unique
whenever each theta path has zero constant term and the H path is fixed.
`PureFluidRActualTaylorIdentification` transfers the actual analytic
value equation to that formal system. Its end theorem
`exists_actual_hs_root_germ_with_r_taylor_path` constructs the actual
theta, H, and r Taylor series along the physical coupling germ, proves
that the r series is the unique solution of the formal path system, and
proves its local sum equals the true MSA r node.

All new theorems have exact standard-three axiom guards. No new axiom
and no modification of foundation 1.0.17 is involved. Lean is validated
with one compiler under a 30 GiB RSS cap.

## Subsequent coefficient result

The subsequent `PureFluidRFormalSolution` and
`PureFluidRPathFormalSubstitution` modules construct the independent
multivariate theta-series for `r` and identify its formal substitution
with this actual path. See
`proof_notes/codex_pure_fluid_r_multivariate_solution.md`.
`PureFluidRRepeatedKernel` now proves the exact positive integral formula
for every nonzero theta multiindex and arbitrary positive repeated rates.
Coefficient nonnegativity after theta-to-physical-coupling inversion
and `R=τ_f` remain open. The false universal real-root/Taylor
equivalence is not used.
