# Pure-fluid dressing: algebra of the low Laurent jets

`PureFluidLaurentJetAlgebra.lean` proves the finite algebra needed after
extracting Laurent coefficients from the proposed dressed rational
functions. The module defines explicit candidate formulas for the two
moment combinations and the new `a,q` coefficients in terms of the first
Taylor jets `u0,u1,g0,g1` of `U,g`. The definitions are the simplified
results of an independent symbolic expansion that included higher jets
through `u4,g4`; the later high-order terms canceled from both moment
combinations. That independent expansion is an audit, not a Lean premise.

In Lean the exact defects factor as

    Anew - a(1+M) - 4(a-q)N
      = (u1-g1)(a²-4aq-8a+4q²+8q)/2,
    qnew - q(1+M) - aN
      = -g1(a²-4aq-8a+4q²+8q)/4.

The existing actual PY coefficient theorem makes the common factor zero.
`hard_B_relation` separately proves `-4 rho bB0 = 4(a-q)` from the frozen
PY formulas. `actual_hard_jet_constraints` therefore discharges the two
candidate relations with the ACTUAL hard-sphere coefficients.

**Scope:** the candidate jet formulas are explicit definitions in this
module. The theorem does not yet prove they are the Laurent coefficients
of arbitrary analytic `U,g`, nor that the resulting dressing solves the
entire actual BH system. The coefficient-extraction bridge is the next
formal step. No positivity or radius conclusion follows.

Full validation: 1745 exact standard-three theorem guards /188 research
modules; six new guards use only `propext`, `Classical.choice`,
`Quot.sound`; foundation 1.0.17 unchanged. No TeX write.
