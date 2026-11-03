# Pure-fluid Step 3 node formulas: actual BH interfaces

`PureFluidNodeClosedForm.lean` closes the finite algebra of the paper's
Step 3 while leaving the global dressing representation explicit.
For scalar values `U,r`, the proposed dressed factor satisfies

    Fd(z) = F0(z) U (1 - kappa(z) r)

at every nonzero node. The proof uses the ACTUAL frozen `F0`, including
its reflected value, and the `kappa` proved positive in
`PureFluidHardSphereNodePositivity`.

`actual_factor_of_dressing_basis` states the exact missing interface:
if the actual `rationalPart` and `exponentialPart` of a BH amplitude
equal the proposed hard-sphere dressing basis, then the ACTUAL
`MultiTail.factor` equals `Fd`. No claim that every root has this basis
is hidden in the theorem.

Under those basis identities and `dressedStrength = w/U`, the module
proves for an ACTUAL `MultiTail.IsRoot`:

    rho D_t = F0(z_t) w (1-kappa_t r),
    rho (2 pi K_t/z_t) / F0(z_t)^2
      = (w U) (1-kappa_t r)^2.

The second line uses the already proved ACTUAL first root equation
`dressedStrength_eq_coupling`, so it is the paper's
`tauhat_t = theta_t (1-kappa_t r_t)^2` with `theta_t=w_t U_t`.

For the second amplitude, `hardG0Node` is defined from the actual PY
`hardShat` and `F0`. `actual_zero_tail_G_eq_hardG0Node` proves that this
is the `G_t` value of any actual zero-tail BH root. The actual second
root node equation, the previously proved unimodular cross identity,
and the same dressing-basis hypotheses then give

    2 pi rho F0(z_t)^2 (G_t-hardG0Node_t)
      = r_t/(1-kappa_t r_t).

The hypotheses include physical `0<xi<1`, positive rates, nonzero
factor at the node, and `U_t≠0`; the latter two are needed for the
displayed divisions. These are conditional Step 3 interfaces. The
remaining work is to prove the proposed `U,g` dressing basis and
`dressedStrength=w/U` for the actual HS-seeded branch from the BH
system, including the coefficient/moment identities. No all-order
positivity or radius equality is concluded here.

Full package validation: PASS, 1774 exact standard-three theorem guards /
191 research modules, nine new guarded theorems. Frozen foundation
1.0.17 unchanged; no TeX write or added axiom.
