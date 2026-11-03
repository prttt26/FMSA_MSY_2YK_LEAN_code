# Individual actual H-function weights at coincident rates

`PureFluidActualPerTailWeights.lean` closes the individual-weight gap
left by comparing only the **combined** pole limits. Two exact field
identities show that the explicit per-tail `alpha,beta` from the global
partial fractions satisfy, for any nonzero rate `z`,

```text
alpha(z, Lambda*S, Lambda*P) = -Lambda*dressingU(z,P,S)
beta(z, Lambda*S, Lambda*P) =
  Lambda*(z*dressingU(z,P,S)-dressingG(z,P,S)).
```

For a genuine original pure-fluid MSA root, the already proved node
identities are `rho*W_t=Lambda_t*Shat_actual(z_t)` and
`rho*C_t=Lambda_t*P_actual(z_t)`. Substitution into those two algebraic
identities gives **each individual tail**

```text
actualWeight_t = Lambda_t*U_actual(z_t)
actualGNumerator_t = Lambda_t*(z_t*U_actual(z_t)-g_actual(z_t)).
```

No rate injectivity is used. In particular, equal-rate tails remain
separately identified by their original BH amplitudes, even though a
pole limit alone only observes their sum. If every positive-node
`U_actual(z_t)` is nonzero, each actual ratio
`r_t=g_actual(z_t)/U_actual(z_t)` satisfies the coefficient equation;
the original `g_actual` equals the paper's finite candidate, the
actual ratios solve its finite `r` system, and the ORIGINAL BH factor
equals the candidate H-function dressing away from zero and finite
negative poles. `PureFluidActualNodeGerm` and
`PureFluidActualAnalyticGerm` now use these stronger all-rate theorems,
so their local data-level conclusions cover coincident rates as well.

This does not identify all-order Taylor coefficient signs, prove
weights positive, or show radius equality. At repeated rates the
physical factor depends on aggregate contributions, but the individual
weight identities above are still valid for the specified original
tail representation.

Eight declarations have exact axiom guards showing only
`[propext, Classical.choice, Quot.sound]`. Full project validation:
`PYTHONDONTWRITEBYTECODE=1 python3 scripts/check_project.py -j 4`
passed with 1916 guards/208 research modules; frozen foundation
1.0.17 unchanged. No TeX was edited.
