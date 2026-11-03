# Pure-fluid H-function route: hard-sphere determinant and dressing cancellation

`PureFluidHardSphereUnimodular.lean` verifies the next finite algebra step of
the paper proof in `proof_notes/claude_two_tail_convergence.md`.

The rational PY basis uses the ACTUAL frozen density formulas:
`hardA = rhoOf xi * bA0 xi`, `hardQ = rhoOf xi * qp0 xi`,
`hardP(s) = 1 - hardA/s³ + (hardA-hardQ)/s² + (hardQ-hardA/2)/s`, and
`hardShat(s) = hardA/s³ + hardQ/s²`. Lean proves directly that
`hardA² - 4 hardA hardQ - 8 hardA + 4 hardQ² + 8 hardQ = 0`
when `xi ≠ 1`. A separate rational identity then gives

    hardP(s) hardP(-s) - hardShat(s) hardShat(-s) = 1

for every `s ≠ 0`. This is the determinant-one identity for the proposed
hard-sphere dressing matrix, with no determinant premise imported.

`rationalPart_zero` and `exponentialPart_zero` connect the preceding
`PureFluidExponentialSplit` definitions to this basis when all original
tail amplitudes D are zero. `actual_F0_split` then proves the frozen actual
PY factor is `hardP(s) + exp(-s) hardShat(s)`.

Finally, `dressed_cross_identity` proves the denominator-free algebraic
identity behind Step E: for any two-by-two dressing with off-diagonal entry
`d`, the cross difference `S F0 - S0 F` equals `d`. Its
`actual_hard_dressed_cross_identity` specialization uses the actual PY
factor and determinant. This establishes the cancellation conditional on
the displayed dressing form; the existence of that form for every actual
multi-tail BH root is still an open interface.

The later `PureFluidNodeResidues` module proves the actual root node
coefficient equations, while analytic residues at repeated poles and the
Laurent constraints remain open. This module does not prove coefficient
positivity or radius equality. The physical range `0 < xi < 1`
implies the weaker algebraic premise `xi ≠ 1`; the theorem itself works for
all real `xi` away from one.

Full research validation: 1734 exact theorem guards /186 modules, eight
new guarded declarations with only `propext`, `Classical.choice`,
`Quot.sound`; foundation 1.0.17 unchanged. No TeX write.
