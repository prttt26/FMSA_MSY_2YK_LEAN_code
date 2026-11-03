# Pure-fluid dressing: exact polynomial Laurent polar bridge

`PureFluidLaurentPolynomialBridge.lean` replaces the paper script's
truncated Laurent expansion by an identity valid for arbitrary polynomial
`U,g`. The doubled cleared numerators `dressedPNum2` and `dressedSNum2`
represent `2 s^4 P_dressed(s)` and `2 s^4 Shat_dressed(s)`.

Lean proves the master identity

    2 Pnum2 + (2 - 2 X + X²) Snum2
      = X⁴ [(2 q + 4) U + (a - 2 q - 4 + 2 X) g].

It holds even when the coefficient arguments `a,q` are arbitrary
polynomials. Therefore every coefficient below degree four on the left
vanishes. This packages the required order-four pole cancellation and
the three lower Laurent polar-shape relations into one exact identity.

The module then specializes `a,q` to `Polynomial.C (hardA xi)` and
`Polynomial.C (hardQ xi)` from the frozen PY data. Six additional Lean
theorems prove that evaluating the cleared numerators at any `s ≠ 0`
returns `2 s³` times the actual `hardP`, `hardShat` (at `s` or `-s`),
and `2 s⁴` times the proposed dressed functions formed from `U(s),g(s)`.
Thus the polynomial identity is tied to the actual hard-sphere rational
basis, rather than being an unrelated formal polynomial exercise.

The remaining bridge is to arbitrary analytic `U,g`: identify their
Taylor jets with suitable polynomial truncations and prove that these
four low coefficient relations and the candidate moment formulas from
`PureFluidLaurentJetAlgebra` follow for the analytic dressing. The
full dressed representation of actual BH roots, H-function positivity,
Picard induction and radius equality remain open. No numerical input or
extra axiom was used.

Later progress: `PureFluidCandidateOriginConstraint` evaluates the
master polar combination pointwise for arbitrary real dressing values
and proves its punctured origin limit for the finite-sum candidate.
Individual Laurent jet and actual BH moment identification remain open;
see `codex_pure_fluid_candidate_origin_normalization.md`.

Full research validation: 1754 exact standard-three theorem guards /
189 modules; nine new declarations use only `propext`, `Classical.choice`,
`Quot.sound`. Foundation 1.0.17 unchanged; no TeX write.
