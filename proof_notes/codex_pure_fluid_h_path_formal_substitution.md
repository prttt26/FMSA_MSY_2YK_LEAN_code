# Formal theta-path substitution for pure-fluid H nodes

`PureFluidHPathFormalSubstitution` closes the algebraic part of comparing the actual one-parameter H germ with the unique multivariate formal solution. For an arbitrary finite tail index set, real kernel `c`, and one-variable formal series `theta_t(tau)` with zero constant term, `HSeries_subst_path_system` uses Mathlib's `MvPowerSeries.HasSubst` to substitute the theta path into each `PureFluidHFormalSolution.HSeries c s`. The resulting series satisfy the finite one-variable H-node equation.

`HNodePathSystem_unique` proves uniqueness of that one-variable formal system. Its coefficient induction uses the zero constant term of each theta series: the degree-n coefficient of `theta_t * H_s * H_t` depends only on H coefficients of degrees below n. Consequently `HNodePathSystem_eq_HSeries_subst` proves that **any** one-variable formal H-node solution equals substitution of the unique multivariate `HSeries` along theta.

The previous `PureFluidHActualNodeBridge` supplies actual analytic functions along a physical HS-root germ and the same value equation, with theta(0)=0 and H(0)=1. The later `AnalyticScalarTaylorPowerSeries` and `PureFluidHActualTaylorIdentification` modules now supply the checked Taylor algebra map and actual pathwise identification; see `codex_pure_fluid_h_actual_taylor_identification.md`. Independent multivariate convergence and the `r`-coefficient/fold-radius steps remain open.

Five theorem guards check the exact standard-three axiom footprint. Full checker PASS: 2054 exact theorem guards / 223 research modules, with one Lean compiler and a 30 GiB process RSS cap. Foundation 1.0.17 is unchanged; no TeX files were changed.
