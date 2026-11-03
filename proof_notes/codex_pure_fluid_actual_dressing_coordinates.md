# Actual pure-fluid BH factor: inverse hard-sphere dressing coordinates

`PureFluidActualDressingCoordinates.lean` uses the already kernel-proved
hard-sphere matrix determinant one to invert its two-by-two dressing
basis. For arbitrary real factor-piece values `P,S` and nonzero real
frequency `s`, define

    d = P0(s) S − Shat0(s) P,
    U = P0(−s) P − Shat0(−s) S + d,
    g = s d.

For every `xi≠1`, Lean proves the exact reconstruction

    P = (U − g/s) P0(s) + (g/s) Shat0(−s),
    S = (U − g/s) Shat0(s) + (g/s) P0(−s),

and proves `U,g` are unique among representations of this form. No
root, finite-tail positivity or distinct-rate premise is needed for
this linear algebra.

Applying the inverse coordinates to the ACTUAL frozen BH
`rationalPart` and `exponentialPart` gives an exact representation of
both pieces and of the original `MultiTail.factor` at every nonzero
real frequency. The off-diagonal coordinate also obeys

    g_actual(s) = s [Shat(s) F0(s) − Shat0(s) F_actual(s)].

At any node of a genuine `MultiTail.IsRoot` with positive rates, this
becomes an identity involving the original second amplitude:

    g_actual(z_t) = F_t [rho 2 pi G_t F0_t − z_t Shat0(z_t)].

When the original tail amplitudes vanish, the inverse coordinates
are exactly `U=1,g=0`, the hard-sphere seed.

The inverse coordinates are defined from the actual BH pieces and may
depend on density and frequency. This theorem does **not** prove they
equal the paper's proposed density-independent finite sums `U,g`, that
the candidate node system is solvable, or that the actual branch has
positive coefficients. The remaining Step 2 task is precisely to
identify these inverse coordinates with the finite-sum candidate under
the correct physical root conditions and moment relations.

Full project validation: PASS, 1825 exact standard-three theorem guards /
198 research modules. Frozen foundation 1.0.17 unchanged; no TeX write
or new axiom.
