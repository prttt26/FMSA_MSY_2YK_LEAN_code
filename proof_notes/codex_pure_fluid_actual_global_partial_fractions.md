# Actual pure-fluid inverse dressing: global partial fractions

`MSAConvergence/PureFluidActualGlobalPartialFractions.lean` connects the
inverse hard-sphere dressing coordinates directly to the **original**
finite-tail Blum–Høye factor. The proof does not assume an MSA root.

For each rate `z t`, set `w_t = rhoOf xi * W_t` and
`c_t = rhoOf xi * C_t`, with `W_t,C_t` taken from the actual BH
amplitudes. The module defines explicit real coefficients
`tailAlpha (hardA xi) (hardQ xi) (z t) w_t c_t` and
`tailBeta (hardA xi) (hardQ xi) (z t) w_t c_t`. For `xi ≠ 1`, nonzero
rates, and real `s` away from zero and every `-z t`, Lean proves

```text
U_actual(s) = 1 + Σ_t alpha_t / (s + z_t)
g_actual(s) =     Σ_t beta_t  / (s + z_t).
```

These are global pointwise identities. Repeated rates are allowed: their
coefficients add in the same denominator. In particular, there is no
remaining appeal to an unproved rational uniqueness theorem for this
explicit `alpha,beta` representation.

The proof has three concrete steps. First, `actual_tailM_identity` and
`actual_tailN_identity` rewrite each original BH moment using `W,C`.
Second, `actual_rational_tail_sum` and `actual_exponential_tail_sum`
split the **actual** rational and exponential BH pieces into the hard
sphere seed plus a finite sum of per-tail pieces. Third,
`generic_tailU_partial_fraction` and `generic_tailG_partial_fraction`
reduce each dressed tail by exact field algebra. Their possible extra
`s^-2` term is a multiple of
`a²-4aq-8a+4q²+8q`, which vanishes by the proved hard-sphere PY
coefficient relation. All these steps are Lean equalities, with no
symbolic-computation oracle in the proof term.

`actualWeight=-alpha` makes `actualU` equal the existing `candidateU`
with that explicit weight. For `candidateG`, the module proves equality
**conditional** on a supplied node parameter `r` satisfying
`actualWeight_t * (z_t-r_t) = beta_t`. It does not prove that condition,
identify `actualWeight_t` with the paper's `Lambda_t U(z_t)`, establish
node nonvanishing or positivity, or derive Taylor convergence and radius
equality. Those true-root node identifications remain separate tasks.

Validation: `PYTHONDONTWRITEBYTECODE=1 python3 scripts/check_project.py -j 4`
passed with 1884 exact theorem guards across 204 research modules,
including the two physical mixture interfaces added at `e84b6f3`.
All 19 declarations in this module have exact axiom guards reporting
`[propext, Classical.choice, Quot.sound]`. The frozen foundation remains
version 1.0.17. No TeX was edited.
