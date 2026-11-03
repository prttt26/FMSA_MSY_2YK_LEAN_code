# Pure-fluid H-function proof: exact Step 1 interface

`PureFluidExponentialSplit.lean` starts the requested Lean verification of
the paper proof in `proof_notes/claude_two_tail_convergence.md`, *Pure
fluids: all-order positivity*. It imports the frozen actual one-component
multi-tail BH definitions through the research package; the foundation is
read only.

For arbitrary finite tail index `T`, density parameter `xi`, rates `z`,
and original amplitudes `D,G`, `factor_split` proves the literal actual
factor identity

    factor(xi,z,D,G,s) = rationalPart(xi,z,D,G,s)
                           + exp(-s) * exponentialPart(xi,z,D,G,s)

at every nonzero real `s`. Both parts are explicit finite rational sums in
the actual `amplitudeA`, `amplitudeQp`, `W` and `C`. The proof separately
checks the two φ head terms and every tail term before reassembling the
finite sum. No root equation, sign, physical-density or distinct-rate
assumption is used.

`exponentialPart_eq_secondRHS` identifies this coefficient with the
ACTUAL second BH source, `rhoOf xi * secondRHS(xi,z,D,G,s)/s`, whenever
`s ≠ 0` and each `s + z_t ≠ 0`. Thus this is the claimed `S-hat = rho S/s`
identity, with the same source as the frozen MSA system. It is not merely
a newly defined surrogate source.

This is the exponential split portion of Step 1. The following
`PureFluidHardSphereUnimodular` module proves the hard-sphere determinant.
The later `PureFluidNodeResidues` module proves the dressed-variable
identities at each actual root node. Separate analytic residues at
coincident poles, Laurent constraints, H-function positivity, Picard
induction and fold-radius equality remain to be formalized. In particular no coefficient
positivity or convergence theorem follows yet.

Full project validation: 1726 exact theorem guards across 185 research
modules, both new declarations with only `propext`, `Classical.choice` and
`Quot.sound`. Frozen foundation 1.0.17 and direct import pins unchanged;
no TeX write.
