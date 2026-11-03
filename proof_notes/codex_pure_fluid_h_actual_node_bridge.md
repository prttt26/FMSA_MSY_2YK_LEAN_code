# Actual pure-fluid H nodes and the formal finite system

`PureFluidHActualNodeBridge` connects the original MSA amplitude variables to the finite node equation used by `PureFluidHFormalSolution`. For every positive finite family of Yukawa rates, including repeated rates, `actual_HNodeValue_all_rates` proves that the true inverse-dressing values `H_s=1/U(z_s)` and `theta_t=actualWeight_t U(z_t)` satisfy

`H_s = 1 + sum_t theta_t H_s H_t/(z_s+z_t)`

whenever the node values `U(z_t)` are nonzero. This is an algebraic identity for the actual BH amplitudes; it does not assume a supplied MSA root. `actual_hs_seed_nodes` proves `theta_t=0` and `H_s=1` at zero first amplitudes.

The module also proves that the actual weight, `U(z_s)`, `theta_t`, and `H(z_s)` are analytic along every analytic original-amplitude path through a nonzero-U seed. Its final theorem constructs the physical HS-seeded MSA root germ from `0<xi<1` and positive rates, with analytic original amplitudes, analytic actual `theta` and `H` nodes, and the finite node equation near zero coupling.

The formal `HSeries` is unique as a **multivariate formal solution in independent theta variables**. This module supplies a **one-dimensional analytic path** `tau -> theta(tau)`. The later `PureFluidHActualTaylorIdentification` proves equality of the physical H coupling Taylor series with formal substitution of `HSeries` along that path and its local sum; see `codex_pure_fluid_h_actual_taylor_identification.md`. Independent multivariate theta convergence, the integral proof of nonnegative `r` coefficients, physical-coupling Picard inversion, and `R=tau_f` remain open. Nothing here implies the false universal real-root/Taylor convergence equivalence.

Seven new Lean theorem guards check the exact standard-three axiom footprint. The module is imported by the package root. Full checker PASS: 2049 exact theorem guards / 222 research modules, with one compiler and a 30 GiB per-process RSS cap. Foundation 1.0.17 remains frozen. No TeX files were changed.
