# Actual pure-fluid dressing coordinates: pole equations

`PureFluidActualDressingPoles.lean` derives the negative-rate pole data
of the inverse coordinates defined in `PureFluidActualDressingCoordinates`.
It uses only the ACTUAL BH root equations, the full finite-pole formulas
for the true `P,Shat`, and continuity of the frozen PY basis away from
the origin.

For one rate value `z_t`, define `Lambda_group` as the sum of
`dressedStrength_u = rho D_u/F(z_u)` over every tail index `u` with
`z_u=z_t`. Lean proves the punctured real-axis scaled limits

    lim_(s → -z_t, s ≠ -z_t) (s+z_t) U_actual(s)
      = -Lambda_group U_actual(z_t),

    lim_(s → -z_t, s ≠ -z_t) (s+z_t) g_actual(s)
      = Lambda_group [z_t U_actual(z_t)-g_actual(z_t)].

The proof factors the combined true `P,Shat` coefficients through the
same-rate strength sum, then applies the inverse PY basis. It allows
repeated positive rates and cancellations within a group. For injective
rates, Lean supplies direct corollaries with `Lambda_group=Lambda_t`.

These are exactly the pole coefficients the proposed finite sums would
have under `w_t=Lambda_t U_actual(z_t)` and
`r_t=g_actual(z_t)/U_actual(z_t)` when those quotients exist. They are
not yet an equality of functions. Establishing the global finite-sum
H-function form still requires controlling possible origin poles,
normalization at infinity, and the corresponding rational uniqueness
argument; candidate/actual HS-branch identification and all-order
positivity remain open.

Full project validation: PASS, 1834 exact standard-three theorem guards /
199 research modules. Frozen foundation 1.0.17 unchanged; no TeX write
or new axiom.
