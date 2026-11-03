# Pure-fluid candidate dressing: exact finite node equation

`PureFluidDressingCandidates.lean` defines the paper's finite-sum
candidate functions, with `candidateG` denoting the lowercase `g` of
the paper rather than the BH second amplitude:

    U(s) = 1 - sum_t w_t/(s+z_t),
    g(s) = sum_t w_t(z_t-r_t)/(s+z_t).

The paper's finite linear system

    r_u - sum_t w_t(r_u-r_t)/(z_u+z_t)
      = sum_t w_t z_t/(z_u+z_t)

is proved equivalent in Lean to all node identities
`g(z_u)=U(z_u)r_u`. The proof is exact finite-sum algebra, valid even
for repeated rates and totalized denominator zeros; no root existence
or sign assumption is hidden. The module also defines the proposed
hard-sphere `P,Shat` dressing and proves their explicit node forms
after substituting the finite-sum functions and linear system.

This supplies concrete candidate expressions to compare with
`PureFluidExactResidueForm`, which is already proved for actual BH
roots. The global comparison is still open: matching poles, the origin
moment coefficients, and asymptotic normalization, then proving the
candidate equals the actual HS-seeded branch. The module does not
assert existence or uniqueness of `r` for all `w`, coefficient
positivity, or radius equality.

Full validation: PASS, 1782 exact standard-three theorem guards /
193 research modules. Six new guarded theorems; frozen foundation
1.0.17 unchanged, no TeX write or extra axiom.
