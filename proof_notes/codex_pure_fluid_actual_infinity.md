# Actual BH dressing normalization at positive infinity

`MSAConvergence/PureFluidActualInfinity.lean` proves the positive-infinity
limits of the **actual** finite-tail BH rational and exponential pieces and
their inverse hard-sphere dressing coordinates. It imports the frozen
foundation through the research package and uses no root hypothesis.

For arbitrary finite real amplitudes, `actual_rational_tendsto_one_atTop`
gives `P_actual(s) → 1`. For nonnegative finite tail rates,
`actual_scaled_exponential_tendsto_zero_atTop` gives
`s Shat_actual(s) → 0`. The intermediate exact identity is

    s Shat_actual(s) = rho A/s² + rho q/s
      + sum_t rho C_t z_t/(s+z_t)

for nonzero `s` and `s+z_t`. The physical positive-rate regime satisfies
the eventual denominator condition. Consequently `Shat_actual(s) → 0`.
The same scaled estimate at zero tail amplitude gives
`s hardShat(s) → 0`. The inverse unimodular PY formulas then yield
`U_actual(s) → 1` and `g_actual(s) → 0`.

All nine declarations have exact standard-three axiom guards. Full
`scripts/check_project.py -j 4` passes with 1843 guards /200 research
modules; foundation 1.0.17 is unchanged. No TeX file was written.

These limits close the infinity-normalization step in the proposed
candidate/actual dressing identification. Local pole equations were proved
previously. Cancellation of possible origin poles, rational uniqueness,
coefficient matching and positivity remain separate tasks. The result does
not imply Taylor-radius equality or endpoint series summability.
