# Pure-fluid H-function route: actual-root node residue coefficients

`PureFluidNodeResidues.lean` connects the Step 1 rational/exponential
split to the ORIGINAL finite-tail BH root equations. Define at a node
`z_t` with `F_t ≠ 0`:

    Lambda_t = rhoOf(xi) * D_t / F_t.

The second original root equation and
`PureFluidExponentialSplit.exponentialPart_eq_secondRHS` give the exact
node identity for `Shat_t`. With the frozen `MultiTail.W`, Lean proves
`rho W_t = Lambda_t Shat(z_t)`. The frozen identity
`W_t + C_t exp(z_t) = D_t exp(z_t)` and the proved actual factor split
then give `rho C_t = Lambda_t P(z_t)`. The first original root equation
identifies `Lambda_t = rho (2 pi K_t/z_t)/F_t²`.

These five guarded theorems require positive rates for the source/node
equation and nonzero `F_t` for `Lambda_t`; the latter is explicit rather
than inferred from a generic root. No distinct-rate assumption is needed
for the node identities. When rates coincide, the rational functions have
shared poles and analytic residues combine; this module has not proved a
separate analytic-residue theorem or the later dressing representation.

The identities use the ACTUAL `MultiTail.IsRoot` and original `D,G,W,C`
definitions. They are neither assumptions nor an external symbolic check.
No H-function coefficient positivity or radius equality follows yet.

Full research validation: 1739 exact theorem guards /187 modules, five
new declarations with only `propext`, `Classical.choice`, `Quot.sound`;
foundation 1.0.17 unchanged. No TeX write.
