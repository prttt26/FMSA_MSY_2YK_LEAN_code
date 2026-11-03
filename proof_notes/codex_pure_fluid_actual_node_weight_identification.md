# Actual pure-fluid H-function node weights

`PureFluidActualNodeWeightIdentification.lean` compares two independent
descriptions of the same actual BH inverse-dressing pole. One is the
global finite partial-fraction representation proved in
`PureFluidActualGlobalPartialFractions`; the other is the local
true-root pole equation proved in `PureFluidActualDressingPoles`.

For a genuine finite-tail MSA root with positive rates and a nonzero
actual factor at every positive rate, the finite sum of explicit
`alpha` coefficients over all indices sharing `z_t` equals
`-Lambda_group * U_actual(z_t)`. The analogous sum of `beta`
coefficients equals
`Lambda_group * (z_t U_actual(z_t)-g_actual(z_t))`. These are
unconditional with respect to repeated rates and node U values. The
proof first establishes that the global partial-fraction identity
holds eventually near each punctured negative rate, then applies the
finite coincident-pole limit theorem and uniqueness of real limits.
This pole-limit method alone does not identify individual coefficients
at repeated rates; the later `PureFluidActualPerTailWeights` module does.

When rates are injective, the grouped sums reduce to individual terms:

```text
actualWeight_t = Lambda_t * U_actual(z_t)
actualGNumerator_t = Lambda_t * (z_t U_actual(z_t)-g_actual(z_t)).
```

Here `actualWeight=-alpha`. If, in addition, every `U_actual(z_t)` is
nonzero, define `actualNodeR_t=g_actual(z_t)/U_actual(z_t)`. Lean proves
`actualWeight_t*(z_t-actualNodeR_t)=actualGNumerator_t`; hence the
original `g_actual` equals `candidateG` away from zero and tail poles.
The already unconditional `U_actual=candidateU` gives the paper's finite
`r` linear system for these actual node ratios. The original BH
`rationalPart`, `exponentialPart`, and factor then equal their candidate
dressing expressions on that same punctured real domain.

The node-nonvanishing condition is a real remaining hypothesis. A
nonzero factor value at a positive node alone has not been shown to
imply `U_actual(z_t)≠0`. Likewise this module does not prove positivity
of the weights, identify an all-order Taylor series, or prove a
Taylor-radius equality. The repeated-rate case supplies only the
combined identities **by this pole-limit method**. The later per-tail
algebra uses the original BH equations to identify every coefficient
without rate injectivity.

All 14 declarations have exact `#print axioms` guards showing only
`[propext, Classical.choice, Quot.sound]`. Verification uses
`PYTHONDONTWRITEBYTECODE=1 python3 scripts/check_project.py -j 4` in
the research package, with the frozen foundation fixed at 1.0.17.
